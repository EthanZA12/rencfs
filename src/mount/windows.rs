use crate::crypto::Cipher;
use crate::encryptedfs::{
    CreateFileAttr, EncryptedFs, FileAttr, FileType, FsError, FsResult, PasswordProvider,
    SetFileAttr, ROOT_INODE,
};
use crate::mount;
use crate::mount::{MountHandleInner, MountPoint};
use async_trait::async_trait;
use shush_rs::{ExposeSecret, SecretString};
use std::ffi::{c_void, OsStr};
use std::future::Future;
use std::io;
use std::path::PathBuf;
use std::pin::Pin;
use std::str::FromStr;
use std::sync::{mpsc, Arc, Mutex};
use std::task::{Context, Poll};
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tokio::runtime::Runtime;
use tokio::sync::oneshot;
use winfsp::filesystem::{
    DirInfo, DirMarker, FileInfo, FileSecurity, FileSystemContext, OpenFileInfo, VolumeInfo,
    WideNameInfo,
};
use winfsp::host::{FileSystemHost, FineGuard, VolumeParams};
use winfsp::{FspError, U16CStr};

const FILE_ATTRIBUTE_DIRECTORY: u32 = 0x10;
const FILE_ATTRIBUTE_ARCHIVE: u32 = 0x20;
const FILE_DIRECTORY_FILE: u32 = 0x0000_0001;

const FILE_READ_DATA: u32 = 0x0000_0001;
const FILE_WRITE_DATA: u32 = 0x0000_0002;
const FILE_APPEND_DATA: u32 = 0x0000_0004;
const GENERIC_READ: u32 = 0x8000_0000;
const GENERIC_WRITE: u32 = 0x4000_0000;

const ERROR_FILE_NOT_FOUND: u32 = 2;
const ERROR_ACCESS_DENIED: u32 = 5;
const ERROR_WRITE_PROTECT: u32 = 19;
const ERROR_INVALID_PARAMETER: u32 = 87;
const ERROR_DISK_FULL: u32 = 112;
const ERROR_DIR_NOT_EMPTY: u32 = 145;
const ERROR_ALREADY_EXISTS: u32 = 183;
const ERROR_DIRECTORY: u32 = 267;
const ERROR_IO_DEVICE: u32 = 1117;

const WINDOWS_EPOCH_OFFSET_SECS: u64 = 11_644_473_600;
const HUNDRED_NS_PER_SEC: u64 = 10_000_000;

fn fs_error(err: FsError) -> FspError {
    match err {
        FsError::NotFound(_) | FsError::InodeNotFound => FspError::WIN32(ERROR_FILE_NOT_FOUND),
        FsError::AlreadyExists | FsError::AlreadyOpenForWrite => {
            FspError::WIN32(ERROR_ALREADY_EXISTS)
        }
        FsError::ReadOnly => FspError::WIN32(ERROR_WRITE_PROTECT),
        FsError::InvalidInput(_) => FspError::WIN32(ERROR_INVALID_PARAMETER),
        FsError::InvalidInodeType => FspError::WIN32(ERROR_DIRECTORY),
        FsError::NotEmpty => FspError::WIN32(ERROR_DIR_NOT_EMPTY),
        FsError::MaxFilesizeExceeded(_) => FspError::WIN32(ERROR_DISK_FULL),
        _ => FspError::WIN32(ERROR_IO_DEVICE),
    }
}

fn io_error(err: impl std::fmt::Display) -> FsError {
    io::Error::other(err.to_string()).into()
}

fn system_time_to_filetime(value: SystemTime) -> u64 {
    let duration = value.duration_since(UNIX_EPOCH).unwrap_or(Duration::ZERO);
    (duration.as_secs() + WINDOWS_EPOCH_OFFSET_SECS) * HUNDRED_NS_PER_SEC
        + u64::from(duration.subsec_nanos()) / 100
}

fn filetime_to_system_time(value: u64) -> Option<SystemTime> {
    if value == 0 {
        return None;
    }

    let total_secs = value / HUNDRED_NS_PER_SEC;
    if total_secs < WINDOWS_EPOCH_OFFSET_SECS {
        return None;
    }
    let secs = total_secs - WINDOWS_EPOCH_OFFSET_SECS;
    let nanos = ((value % HUNDRED_NS_PER_SEC) * 100) as u32;
    Some(UNIX_EPOCH + Duration::new(secs, nanos))
}

fn windows_attributes(attr: &FileAttr) -> u32 {
    match attr.kind {
        FileType::Directory => FILE_ATTRIBUTE_DIRECTORY,
        FileType::RegularFile => FILE_ATTRIBUTE_ARCHIVE,
    }
}

fn fill_file_info(attr: &FileAttr, out: &mut FileInfo) {
    out.file_attributes = windows_attributes(attr);
    out.reparse_tag = 0;
    out.file_size = attr.size;
    out.allocation_size = attr.size.div_ceil(4096) * 4096;
    out.creation_time = system_time_to_filetime(attr.crtime);
    out.last_access_time = system_time_to_filetime(attr.atime);
    out.last_write_time = system_time_to_filetime(attr.mtime);
    out.change_time = system_time_to_filetime(attr.ctime);
    out.index_number = attr.ino;
    out.hard_links = 0;
    out.ea_size = 0;
}

fn path_components(file_name: &U16CStr) -> Vec<String> {
    file_name
        .to_string_lossy()
        .split(|ch| ch == '\\' || ch == '/')
        .filter(|component| !component.is_empty())
        .map(str::to_owned)
        .collect()
}

fn access_modes(granted_access: u32, read_only: bool) -> (bool, bool) {
    let write =
        !read_only && granted_access & (FILE_WRITE_DATA | FILE_APPEND_DATA | GENERIC_WRITE) != 0;

    // Keep an internal read handle for writable files. EncryptedFs uses
    // read/modify/write semantics for encrypted content and Windows cached
    // I/O may require reads during a writable file lifecycle. WinFSP still
    // enforces the caller's original Windows access mask.
    let read = true;

    (read, write)
}

fn file_attr() -> CreateFileAttr {
    CreateFileAttr {
        kind: FileType::RegularFile,
        perm: 0o666,
        uid: 0,
        gid: 0,
        rdev: 0,
        flags: 0,
    }
}

fn dir_attr() -> CreateFileAttr {
    CreateFileAttr {
        kind: FileType::Directory,
        perm: 0o777,
        uid: 0,
        gid: 0,
        rdev: 0,
        flags: 0,
    }
}

struct HandleState {
    parent: Option<u64>,
    name: Option<String>,
    delete_on_close: bool,
}

pub struct WinFileContext {
    ino: u64,
    fh: u64,
    kind: FileType,
    state: Mutex<HandleState>,
}

enum HostEvent {
    Stop,
    DispatcherStopped,
}

struct WinFsContext {
    fs: Arc<EncryptedFs>,
    runtime: Runtime,
    event_tx: mpsc::Sender<HostEvent>,
    read_only: bool,
}

impl WinFsContext {
    fn resolve(&self, file_name: &U16CStr) -> FsResult<FileAttr> {
        let components = path_components(file_name);
        let fs = self.fs.clone();
        self.runtime.block_on(async move {
            let mut attr = fs.get_attr(ROOT_INODE).await?;
            for component in components {
                attr = fs
                    .find_by_name(
                        attr.ino,
                        &SecretString::from_str(component.as_str()).unwrap(),
                    )
                    .await?
                    .ok_or(FsError::NotFound("path component"))?;
            }
            Ok(attr)
        })
    }

    fn resolve_parent(&self, file_name: &U16CStr) -> FsResult<(u64, String)> {
        let mut components = path_components(file_name);
        let name = components
            .pop()
            .ok_or(FsError::InvalidInput("root has no parent"))?;
        let fs = self.fs.clone();

        self.runtime.block_on(async move {
            let mut parent = ROOT_INODE;
            for component in components {
                let attr = fs
                    .find_by_name(parent, &SecretString::from_str(component.as_str()).unwrap())
                    .await?
                    .ok_or(FsError::NotFound("parent path component"))?;
                if attr.kind != FileType::Directory {
                    return Err(FsError::InvalidInodeType);
                }
                parent = attr.ino;
            }
            Ok((parent, name))
        })
    }

    fn make_context(&self, attr: FileAttr, fh: u64, file_name: &U16CStr) -> WinFileContext {
        let (parent, name) = self
            .resolve_parent(file_name)
            .map_or((None, None), |(parent, name)| (Some(parent), Some(name)));

        WinFileContext {
            ino: attr.ino,
            fh,
            kind: attr.kind,
            state: Mutex::new(HandleState {
                parent,
                name,
                delete_on_close: false,
            }),
        }
    }
}

impl FileSystemContext for WinFsContext {
    type FileContext = WinFileContext;

    fn get_security_by_name(
        &self,
        file_name: &U16CStr,
        _security_descriptor: Option<&mut [c_void]>,
        _reparse_point_resolver: impl FnOnce(&U16CStr) -> Option<FileSecurity>,
    ) -> winfsp::Result<FileSecurity> {
        let attr = self.resolve(file_name).map_err(fs_error)?;
        Ok(FileSecurity {
            reparse: false,
            sz_security_descriptor: 0,
            attributes: windows_attributes(&attr),
        })
    }

    fn open(
        &self,
        file_name: &U16CStr,
        _create_options: u32,
        granted_access: u32,
        file_info: &mut OpenFileInfo,
    ) -> winfsp::Result<Self::FileContext> {
        let attr = self.resolve(file_name).map_err(fs_error)?;
        let fh = if attr.kind == FileType::Directory {
            0
        } else {
            let (read, write) = access_modes(granted_access, self.read_only);
            let fs = self.fs.clone();
            self.runtime
                .block_on(async move { fs.open(attr.ino, read, write).await })
                .map_err(fs_error)?
        };

        fill_file_info(&attr, file_info.as_mut());
        Ok(self.make_context(attr, fh, file_name))
    }

    fn close(&self, context: Self::FileContext) {
        if context.fh != 0 {
            let fs = self.fs.clone();
            let _ = self
                .runtime
                .block_on(async move { fs.release(context.fh).await });
        }
    }

    fn create(
        &self,
        file_name: &U16CStr,
        create_options: u32,
        granted_access: u32,
        file_attributes: u32,
        _security_descriptor: Option<&[c_void]>,
        _allocation_size: u64,
        _extra_buffer: Option<&[u8]>,
        _extra_buffer_is_reparse_point: bool,
        file_info: &mut OpenFileInfo,
    ) -> winfsp::Result<Self::FileContext> {
        if self.read_only {
            return Err(FspError::WIN32(ERROR_ACCESS_DENIED));
        }

        let (parent, name) = self.resolve_parent(file_name).map_err(fs_error)?;
        let is_directory = create_options & FILE_DIRECTORY_FILE != 0
            || file_attributes & FILE_ATTRIBUTE_DIRECTORY != 0;
        let (read, write) = if is_directory {
            (false, false)
        } else {
            access_modes(granted_access, false)
        };
        let attr = if is_directory {
            dir_attr()
        } else {
            file_attr()
        };
        let secret_name = SecretString::from_str(name.as_str()).unwrap();
        let fs = self.fs.clone();

        let (fh, attr) = self
            .runtime
            .block_on(async move { fs.create(parent, &secret_name, attr, read, write).await })
            .map_err(fs_error)?;

        fill_file_info(&attr, file_info.as_mut());

        Ok(WinFileContext {
            ino: attr.ino,
            fh,
            kind: attr.kind,
            state: Mutex::new(HandleState {
                parent: Some(parent),
                name: Some(name),
                delete_on_close: false,
            }),
        })
    }

    fn cleanup(&self, context: &Self::FileContext, _file_name: Option<&U16CStr>, _flags: u32) {
        let target = {
            let mut state = context.state.lock().unwrap();
            if !state.delete_on_close {
                return;
            }
            state.delete_on_close = false;
            state.parent.zip(state.name.clone())
        };

        let Some((parent, name)) = target else {
            return;
        };

        let secret_name = SecretString::from_str(name.as_str()).unwrap();
        let fs = self.fs.clone();
        let kind = context.kind;
        let _ = self.runtime.block_on(async move {
            if kind == FileType::Directory {
                fs.remove_dir(parent, &secret_name).await
            } else {
                fs.remove_file(parent, &secret_name).await
            }
        });
    }

    fn flush(
        &self,
        context: Option<&Self::FileContext>,
        file_info: &mut FileInfo,
    ) -> winfsp::Result<()> {
        let Some(context) = context else {
            return Ok(());
        };

        if context.fh != 0 {
            let fs = self.fs.clone();
            self.runtime
                .block_on(async move { fs.flush(context.fh).await })
                .map_err(fs_error)?;
        }

        let fs = self.fs.clone();
        let attr = self
            .runtime
            .block_on(async move { fs.get_attr(context.ino).await })
            .map_err(fs_error)?;
        fill_file_info(&attr, file_info);
        Ok(())
    }

    fn get_file_info(
        &self,
        context: &Self::FileContext,
        file_info: &mut FileInfo,
    ) -> winfsp::Result<()> {
        let fs = self.fs.clone();
        let attr = self
            .runtime
            .block_on(async move { fs.get_attr(context.ino).await })
            .map_err(fs_error)?;
        fill_file_info(&attr, file_info);
        Ok(())
    }

    fn overwrite(
        &self,
        context: &Self::FileContext,
        _file_attributes: u32,
        _replace_file_attributes: bool,
        _allocation_size: u64,
        _extra_buffer: Option<&[u8]>,
        file_info: &mut FileInfo,
    ) -> winfsp::Result<()> {
        if self.read_only {
            return Err(FspError::WIN32(ERROR_ACCESS_DENIED));
        }

        let fs = self.fs.clone();
        self.runtime
            .block_on(async move { fs.set_len(context.ino, 0).await })
            .map_err(fs_error)?;
        self.get_file_info(context, file_info)
    }

    fn read_directory(
        &self,
        context: &Self::FileContext,
        _pattern: Option<&U16CStr>,
        marker: DirMarker,
        buffer: &mut [u8],
    ) -> winfsp::Result<u32> {
        if context.kind != FileType::Directory {
            return Err(FspError::WIN32(ERROR_DIRECTORY));
        }

        let fs = self.fs.clone();
        let mut entries = self
            .runtime
            .block_on(async move {
                let mut iter = fs.read_dir_plus(context.ino).await?;
                let mut entries = Vec::new();
                for entry in &mut iter {
                    entries.push(entry?);
                }
                Ok::<_, FsError>(entries)
            })
            .map_err(fs_error)?;

        entries.sort_by(|a, b| {
            let a_name = a.name.expose_secret();
            let b_name = b.name.expose_secret();
            a_name.as_str().cmp(b_name.as_str())
        });

        let marker = marker.inner().map(String::from_utf16_lossy);
        let mut cursor = 0u32;

        for entry in entries {
            let name = entry.name.expose_secret();
            if marker
                .as_ref()
                .is_some_and(|marker| name.as_str() <= marker.as_str())
            {
                continue;
            }

            let mut dir_info = DirInfo::<255>::new();
            fill_file_info(&entry.attr, dir_info.file_info_mut());
            dir_info.set_name(OsStr::new(name.as_str()))?;
            if !dir_info.append_to_buffer(buffer, &mut cursor) {
                break;
            }
        }

        let _ = DirInfo::<255>::finalize_buffer(buffer, &mut cursor);
        Ok(cursor)
    }

    fn rename(
        &self,
        context: &Self::FileContext,
        _file_name: &U16CStr,
        new_file_name: &U16CStr,
        _replace_if_exists: bool,
    ) -> winfsp::Result<()> {
        if self.read_only {
            return Err(FspError::WIN32(ERROR_ACCESS_DENIED));
        }

        let (old_parent, old_name) = {
            let state = context.state.lock().unwrap();
            state
                .parent
                .zip(state.name.clone())
                .ok_or(FspError::WIN32(ERROR_INVALID_PARAMETER))?
        };
        let (new_parent, new_name) = self.resolve_parent(new_file_name).map_err(fs_error)?;
        let old_secret = SecretString::from_str(old_name.as_str()).unwrap();
        let new_secret = SecretString::from_str(new_name.as_str()).unwrap();
        let fs = self.fs.clone();

        self.runtime
            .block_on(async move {
                fs.rename(old_parent, &old_secret, new_parent, &new_secret)
                    .await
            })
            .map_err(fs_error)?;

        let mut state = context.state.lock().unwrap();
        state.parent = Some(new_parent);
        state.name = Some(new_name);
        Ok(())
    }

    fn set_basic_info(
        &self,
        context: &Self::FileContext,
        _file_attributes: u32,
        creation_time: u64,
        last_access_time: u64,
        last_write_time: u64,
        last_change_time: u64,
        file_info: &mut FileInfo,
    ) -> winfsp::Result<()> {
        if self.read_only {
            return Err(FspError::WIN32(ERROR_ACCESS_DENIED));
        }

        let mut set_attr = SetFileAttr::default();
        if let Some(value) = filetime_to_system_time(creation_time) {
            set_attr = set_attr.with_crtime(value);
        }
        if let Some(value) = filetime_to_system_time(last_access_time) {
            set_attr = set_attr.with_atime(value);
        }
        if let Some(value) = filetime_to_system_time(last_write_time) {
            set_attr = set_attr.with_mtime(value);
        }
        if let Some(value) = filetime_to_system_time(last_change_time) {
            set_attr = set_attr.with_ctime(value);
        }

        let fs = self.fs.clone();
        self.runtime
            .block_on(async move { fs.set_attr(context.ino, set_attr).await })
            .map_err(fs_error)?;
        self.get_file_info(context, file_info)
    }

    fn set_delete(
        &self,
        context: &Self::FileContext,
        _file_name: &U16CStr,
        delete_file: bool,
    ) -> winfsp::Result<()> {
        if self.read_only {
            return Err(FspError::WIN32(ERROR_ACCESS_DENIED));
        }

        context.state.lock().unwrap().delete_on_close = delete_file;
        Ok(())
    }

    fn set_file_size(
        &self,
        context: &Self::FileContext,
        new_size: u64,
        _set_allocation_size: bool,
        file_info: &mut FileInfo,
    ) -> winfsp::Result<()> {
        if self.read_only {
            return Err(FspError::WIN32(ERROR_ACCESS_DENIED));
        }

        let fs = self.fs.clone();
        self.runtime
            .block_on(async move { fs.set_len(context.ino, new_size).await })
            .map_err(fs_error)?;
        self.get_file_info(context, file_info)
    }

    fn read(
        &self,
        context: &Self::FileContext,
        buffer: &mut [u8],
        offset: u64,
    ) -> winfsp::Result<u32> {
        if context.kind == FileType::Directory {
            return Err(FspError::WIN32(ERROR_DIRECTORY));
        }

        let fs = self.fs.clone();
        let len = self
            .runtime
            .block_on(async move { fs.read(context.ino, offset, buffer, context.fh).await })
            .map_err(fs_error)?;
        Ok(len as u32)
    }

    fn write(
        &self,
        context: &Self::FileContext,
        buffer: &[u8],
        offset: u64,
        write_to_eof: bool,
        constrained_io: bool,
        file_info: &mut FileInfo,
    ) -> winfsp::Result<u32> {
        if self.read_only {
            return Err(FspError::WIN32(ERROR_ACCESS_DENIED));
        }
        if context.kind == FileType::Directory {
            return Err(FspError::WIN32(ERROR_DIRECTORY));
        }

        let fs = self.fs.clone();
        let current_attr = self
            .runtime
            .block_on({
                let fs = fs.clone();
                async move { fs.get_attr(context.ino).await }
            })
            .map_err(fs_error)?;

        let offset = if write_to_eof {
            current_attr.size
        } else {
            offset
        };

        let data = if constrained_io {
            if offset >= current_attr.size {
                return Ok(0);
            }
            let max_len = (current_attr.size - offset) as usize;
            &buffer[..buffer.len().min(max_len)]
        } else {
            buffer
        };

        let len = self
            .runtime
            .block_on(async move { fs.write(context.ino, offset, data, context.fh).await })
            .map_err(fs_error)?;

        self.get_file_info(context, file_info)?;
        Ok(len as u32)
    }

    fn get_volume_info(&self, out_volume_info: &mut VolumeInfo) -> winfsp::Result<()> {
        out_volume_info.total_size = 1_u64 << 40;
        out_volume_info.free_size = 1_u64 << 39;
        out_volume_info.set_volume_label("rencfs");
        Ok(())
    }

    fn set_volume_label(
        &self,
        _volume_label: &U16CStr,
        volume_info: &mut VolumeInfo,
    ) -> winfsp::Result<()> {
        volume_info.set_volume_label("rencfs");
        Ok(())
    }

    fn dispatcher_stopped(&self, _normally: bool) {
        let _ = self.event_tx.send(HostEvent::DispatcherStopped);
    }
}

#[allow(clippy::struct_excessive_bools)]
pub struct MountPointImpl {
    mountpoint: PathBuf,
    data_dir: PathBuf,
    password_provider: Option<Box<dyn PasswordProvider>>,
    cipher: Cipher,
    _allow_root: bool,
    _allow_other: bool,
    read_only: bool,
}

#[async_trait]
impl MountPoint for MountPointImpl {
    fn new(
        mountpoint: PathBuf,
        data_dir: PathBuf,
        password_provider: Box<dyn PasswordProvider>,
        cipher: Cipher,
        allow_root: bool,
        allow_other: bool,
        read_only: bool,
    ) -> Self {
        Self {
            mountpoint,
            data_dir,
            password_provider: Some(password_provider),
            cipher,
            _allow_root: allow_root,
            _allow_other: allow_other,
            read_only,
        }
    }

    async fn mount(mut self) -> FsResult<mount::MountHandle> {
        let fs = EncryptedFs::new(
            self.data_dir,
            self.password_provider.take().unwrap(),
            self.cipher,
            self.read_only,
        )
        .await?;

        let mountpoint = self.mountpoint;
        let read_only = self.read_only;
        let (event_tx, event_rx) = mpsc::channel::<HostEvent>();
        let context_event_tx = event_tx.clone();
        let (ready_tx, ready_rx) = oneshot::channel::<Result<(), String>>();
        let (done_tx, done_rx) = oneshot::channel::<io::Result<()>>();

        std::thread::spawn(move || {
            let mut ready_tx = Some(ready_tx);
            let result = (|| -> Result<(), String> {
                winfsp::winfsp_init().map_err(|err| err.to_string())?;

                let runtime = Runtime::new().map_err(|err| err.to_string())?;
                let context = WinFsContext {
                    fs,
                    runtime,
                    event_tx: context_event_tx,
                    read_only,
                };

                let mut volume_params = VolumeParams::new();
                volume_params
                    .sector_size(512)
                    .sectors_per_allocation_unit(8)
                    .max_component_length(255)
                    .volume_creation_time(system_time_to_filetime(SystemTime::now()))
                    .volume_serial_number(0x5245_4E43)
                    .file_info_timeout(1000)
                    .case_sensitive_search(true)
                    .case_preserved_names(true)
                    .unicode_on_disk(true)
                    .persistent_acls(false)
                    .read_only_volume(read_only)
                    .filesystem_name("rencfs");

                let mut host =
                    FileSystemHost::<WinFsContext, FineGuard>::new(volume_params, context)
                        .map_err(|err| err.to_string())?;
                host.mount(&mountpoint).map_err(|err| err.to_string())?;
                host.start().map_err(|err| err.to_string())?;

                if let Some(ready_tx) = ready_tx.take() {
                    let _ = ready_tx.send(Ok(()));
                }

                match event_rx.recv() {
                    Ok(HostEvent::Stop) => {
                        host.stop();
                        host.unmount();
                    }
                    Ok(HostEvent::DispatcherStopped) | Err(_) => {
                        host.unmount();
                    }
                }

                Ok(())
            })();

            if let Err(err) = &result {
                if let Some(ready_tx) = ready_tx.take() {
                    let _ = ready_tx.send(Err(err.clone()));
                }
            }

            let _ = done_tx.send(result.map_err(io::Error::other));
        });

        let ready = ready_rx.await.map_err(io_error)?;
        ready.map_err(io_error)?;

        Ok(mount::MountHandle {
            inner: MountHandleInnerImpl {
                event_tx: Some(event_tx),
                done_rx: Some(done_rx),
            },
        })
    }
}

pub(in crate::mount) struct MountHandleInnerImpl {
    event_tx: Option<mpsc::Sender<HostEvent>>,
    done_rx: Option<oneshot::Receiver<io::Result<()>>>,
}

impl Unpin for MountHandleInnerImpl {}

impl Future for MountHandleInnerImpl {
    type Output = io::Result<()>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let done_rx = self
            .done_rx
            .as_mut()
            .expect("mount completion receiver missing");

        match Pin::new(done_rx).poll(cx) {
            Poll::Ready(Ok(result)) => Poll::Ready(result),
            Poll::Ready(Err(err)) => Poll::Ready(Err(io::Error::other(err.to_string()))),
            Poll::Pending => Poll::Pending,
        }
    }
}

impl Drop for MountHandleInnerImpl {
    fn drop(&mut self) {
        if let Some(event_tx) = self.event_tx.take() {
            let _ = event_tx.send(HostEvent::Stop);
        }
    }
}

#[async_trait]
impl MountHandleInner for MountHandleInnerImpl {
    async fn unmount(mut self) -> io::Result<()> {
        if let Some(event_tx) = self.event_tx.take() {
            let _ = event_tx.send(HostEvent::Stop);
        }

        let done_rx = self
            .done_rx
            .take()
            .ok_or_else(|| io::Error::other("mount completion receiver missing"))?;

        match done_rx.await {
            Ok(result) => result,
            Err(err) => Err(io::Error::other(err.to_string())),
        }
    }
}

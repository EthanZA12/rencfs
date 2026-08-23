#[cfg(target_os = "windows")]
fn main() {
    winfsp::build::winfsp_link_delayload();
}

#[cfg(not(target_os = "windows"))]
fn main() {}

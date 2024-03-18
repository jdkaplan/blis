use std::path::{Path, PathBuf};

/// Return the path relative to the Cargo manifest.
pub(crate) fn relative_path(path: &Path) -> String {
    let crate_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let relative = path.strip_prefix(crate_root).unwrap();
    relative.to_string_lossy().to_string()
}

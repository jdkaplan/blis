use std::collections::HashMap;
use std::path::{Path, PathBuf};

use once_cell::sync::Lazy;
use regex::Regex;

/// Return the path relative to the Cargo manifest.
pub(crate) fn relative_path(path: &Path) -> String {
    let crate_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let relative = path.strip_prefix(crate_root).unwrap();
    relative.to_string_lossy().to_string()
}

pub(crate) fn snapshot_name(path: &Path, name: &str) -> String {
    format!("{}.{}", relative_path(path), name)
}

pub(crate) fn replace_object_ids(original: String) -> String {
    let mut ids = HashMap::new();
    let mut counter = 0u64;
    let mut out = String::with_capacity(original.len());

    static RE: Lazy<Regex> =
        Lazy::new(|| Regex::new(r"<(?<ty>.*?) (?<id>0x[0-9a-fA-F]+)>").unwrap());

    let mut last = 0;
    for cap in RE.captures_iter(&original) {
        // Add in anything between the previous match and this one.
        let matched = cap.get(0).expect("full match");
        out.push_str(&original[last..matched.start()]);
        last = matched.end();

        // Add in the replacement from this match.
        let ty = cap.name("ty").expect("named group").as_str();
        let old = cap.name("id").expect("named group").as_str();
        let new = ids.entry(old).or_insert_with(|| {
            counter += 1;
            counter
        });
        out.push_str(&format!("<{} 0x{:012x}>", ty, new));
    }

    // Keep anything after the last match.
    if last < original.len() {
        out.push_str(&original[last..]);
    }

    out
}

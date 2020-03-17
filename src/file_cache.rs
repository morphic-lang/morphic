use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

#[derive(Clone, Debug)]
pub struct FileCache {
    files: BTreeMap<PathBuf, String>,
}

impl FileCache {
    pub fn new() -> Self {
        FileCache {
            files: BTreeMap::new(),
        }
    }

    pub fn read(&mut self, path: impl AsRef<Path>) -> io::Result<&str> {
        let canonical = path.as_ref().canonicalize()?;
        if !self.files.contains_key(&canonical) {
            let content = fs::read_to_string(&canonical)?;
            self.files.insert(canonical.clone(), content);
        }
        Ok(&self.files[&canonical])
    }

    pub fn read_cached(&self, path: impl AsRef<Path>) -> io::Result<&str> {
        let canonical = path.as_ref().canonicalize()?;
        Ok(&self.files[&canonical])
    }
}

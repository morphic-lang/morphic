use id_collections::{id_type, IdVec};
use std::collections::btree_map::Entry;
use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

#[id_type]
pub struct FileId(pub usize);

#[derive(Clone, Debug)]
pub struct FileCache {
    paths: BTreeMap<PathBuf, FileId>,
    files: IdVec<FileId, String>,
}

impl FileCache {
    pub fn new() -> Self {
        FileCache {
            paths: BTreeMap::new(),
            files: IdVec::new(),
        }
    }

    pub fn read(&mut self, path: impl AsRef<Path>) -> io::Result<(FileId, &str)> {
        let canonical = path.as_ref().canonicalize()?;
        match self.paths.entry(canonical.clone()) {
            Entry::Vacant(entry) => {
                let content = fs::read_to_string(canonical)?;
                let file_id = self.files.push(content);
                entry.insert(file_id);
                Ok((file_id, &self.files[file_id]))
            }
            Entry::Occupied(entry) => {
                let file_id = *entry.get();
                Ok((file_id, &self.files[file_id]))
            }
        }
    }

    pub fn read_cached(&self, path: impl AsRef<Path>) -> io::Result<(FileId, &str)> {
        let canonical = path.as_ref().canonicalize()?;
        let file_id = self.paths[&canonical];
        Ok((file_id, &self.files[file_id]))
    }
}

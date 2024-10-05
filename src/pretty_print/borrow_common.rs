use crate::data::mode_annot_ast2::{Interner, LocalLt, Lt, LtParam, Mode, Path};
use std::io::{self, Write};
use std::{fmt, str};

pub fn write_mode(w: &mut dyn Write, m: &Mode) -> io::Result<()> {
    match m {
        Mode::Owned => write!(w, "●"),
        Mode::Borrowed => write!(w, "&"),
    }
}

pub fn write_lifetime_param(w: &mut dyn Write, lt: &LtParam) -> io::Result<()> {
    write!(w, "'{}", lt.0)
}

pub fn write_local_lifetime(w: &mut dyn Write, lt: &LocalLt) -> io::Result<()> {
    match lt {
        LocalLt::Final => write!(w, "★"),
        LocalLt::Seq(child, i) => {
            write!(w, "↓{i} ")?;
            write_local_lifetime(w, child)?;
            Ok(())
        }
        LocalLt::Alt(branches) => {
            write!(w, "(")?;
            assert!(!branches.is_empty());
            for (i, branch) in branches.iter().enumerate() {
                if let Some(branch) = branch {
                    write_local_lifetime(w, branch)?;
                } else {
                    write!(w, "-")?;
                }
                if i < branches.len() - 1 {
                    write!(w, " ‖ ")?;
                }
            }
            write!(w, ")")?;
            Ok(())
        }
    }
}

pub struct DisplayLocalLt<'a>(&'a LocalLt);

impl fmt::Display for DisplayLocalLt<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut w = Vec::new();
        write_local_lifetime(&mut w, self.0).unwrap();
        f.write_str(str::from_utf8(&w).unwrap())
    }
}

impl LocalLt {
    pub fn display(&self) -> DisplayLocalLt {
        DisplayLocalLt(self)
    }
}

pub fn write_lifetime(w: &mut dyn Write, lt: &Lt) -> io::Result<()> {
    match lt {
        Lt::Empty => write!(w, "∅"),
        Lt::Local(lt) => {
            write!(w, "{{ ")?;
            write_local_lifetime(w, lt)?;
            write!(w, " }}")?;
            Ok(())
        }
        Lt::Join(params) => {
            for (i, param) in params.iter().enumerate() {
                write_lifetime_param(w, param)?;
                if i < params.len() - 1 {
                    write!(w, " ⨆ ")?;
                }
            }
            Ok(())
        }
    }
}

pub struct DisplayLt<'a>(&'a Lt);

impl fmt::Display for DisplayLt<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut w = Vec::new();
        write_lifetime(&mut w, self.0).unwrap();
        f.write_str(str::from_utf8(&w).unwrap())
    }
}

impl Lt {
    pub fn display(&self) -> DisplayLt {
        DisplayLt(self)
    }
}

pub fn write_path(w: &mut dyn Write, path: &Path) -> io::Result<()> {
    write_lifetime(w, &path.as_lt(&Interner::empty()))
}

pub struct DisplayPath<'a>(&'a Path);

impl fmt::Display for DisplayPath<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut w = Vec::new();
        write_path(&mut w, self.0).unwrap();
        f.write_str(str::from_utf8(&w).unwrap())
    }
}

impl Path {
    pub fn display(&self) -> DisplayPath {
        DisplayPath(self)
    }
}

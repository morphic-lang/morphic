use std::ffi::OsStr;
use std::path::PathBuf;

#[derive(Clone, Debug)]
pub struct ArtifactDir {
    pub dir_path: PathBuf,
    pub filename_prefix: PathBuf,
}

impl ArtifactDir {
    pub fn artifact_path(&self, extension: &(impl AsRef<OsStr> + ?Sized)) -> PathBuf {
        self.dir_path
            .join(self.filename_prefix.with_extension(extension))
    }
}

#[derive(Clone, Copy, Debug)]
pub enum PurityMode {
    Checked,
    Unchecked,
}

#[derive(Clone, Copy, Debug)]
pub enum LlvmConfig {
    Native,
    Wasm,
}

#[derive(Clone, Copy, Debug)]
pub enum MlConfig {
    Sml,
    Ocaml,
}

#[derive(Clone, Copy, Debug)]
pub enum TargetConfig {
    Llvm(LlvmConfig),
    Ml(MlConfig),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SymbolName(pub String);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SpecializationMode {
    Specialize,
    Single,
}

impl Default for SpecializationMode {
    fn default() -> Self {
        Self::Specialize
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RcStrategy {
    Default,
    Perceus, // Linear type inference. Everything is inferred as owned.
}

impl Default for RcStrategy {
    fn default() -> Self {
        Self::Default
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ArrayKind {
    Cow,
    Persistent,
}

impl Default for ArrayKind {
    fn default() -> Self {
        Self::Persistent
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum GcKind {
    None,
    Bdw,
}

impl Default for GcKind {
    fn default() -> Self {
        Self::None
    }
}

#[derive(Clone, Debug, Default)]
pub struct PassOptions {
    pub defunc_mode: SpecializationMode,
    pub rc_strat: RcStrategy,
    pub array_kind: ArrayKind,
    pub gc_kind: GcKind,
}

pub fn default_llvm_opt_level() -> inkwell::OptimizationLevel {
    inkwell::OptimizationLevel::Aggressive
}

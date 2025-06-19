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
        SpecializationMode::Specialize
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum RcStrategy {
    Default,
    Perceus, // Linear type inference. Everything is inferred as owned.
}

impl Default for RcStrategy {
    fn default() -> Self {
        RcStrategy::Default
    }
}

#[derive(Clone, Debug)]
pub struct PassOptions {
    pub defunc_mode: SpecializationMode,
    pub rc_strat: RcStrategy,
}

impl Default for PassOptions {
    fn default() -> Self {
        Self {
            defunc_mode: SpecializationMode::default(),
            rc_strat: RcStrategy::default(),
        }
    }
}

pub fn default_llvm_opt_level() -> inkwell::OptimizationLevel {
    inkwell::OptimizationLevel::Aggressive
}

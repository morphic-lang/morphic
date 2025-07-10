use crate::progress_ui;
use crate::pseudoprocess::{Stdio, ValgrindConfig};
use clap::builder::PossibleValue;
use clap::ValueEnum;
use std::ffi::OsStr;
use std::fs::File;
use std::path::{Path, PathBuf};

pub trait ValueEnumExt {
    fn default_as_str() -> String;
}

impl<T: ValueEnum + Default> ValueEnumExt for T {
    fn default_as_str() -> String {
        T::default().to_possible_value().unwrap().get_name().into()
    }
}

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

/// Dropping this may delete the underlying file!
pub enum OutFile {
    Temp(tempfile::NamedTempFile),
    Artifact(PathBuf, File),
}

impl OutFile {
    pub fn create(
        artifact_dir: Option<&ArtifactDir>,
        extension: &(impl AsRef<OsStr> + ?Sized),
    ) -> Result<Self, std::io::Error> {
        if let Some(artifact_dir) = artifact_dir {
            let path = artifact_dir.artifact_path(extension);
            let file = File::create(&path)?;
            Ok(Self::Artifact(path, file))
        } else {
            let tempfile = tempfile::Builder::new().suffix(extension).tempfile_in("")?;
            Ok(Self::Temp(tempfile))
        }
    }

    pub fn path(&self) -> &Path {
        match self {
            Self::Temp(tempfile) => tempfile.path(),
            Self::Artifact(path, _file) => path,
        }
    }

    pub fn file_mut(&mut self) -> &mut File {
        match self {
            Self::Temp(tempfile) => tempfile.as_file_mut(),
            Self::Artifact(_path, file) => file,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SymbolName(pub String);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProfileMode {
    RecordRc,
    NoRecordRc,
}

impl Default for ProfileMode {
    fn default() -> Self {
        Self::NoRecordRc
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PurityMode {
    Checked,
    Unchecked,
}

impl Default for PurityMode {
    fn default() -> Self {
        Self::Checked
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum DefuncMode {
    Specialize,
    Single,
}

impl Default for DefuncMode {
    fn default() -> Self {
        Self::Specialize
    }
}

impl DefuncMode {
    pub fn to_str(&self) -> &'static str {
        match self {
            Self::Specialize => "specialize",
            Self::Single => "single",
        }
    }
}

impl ValueEnum for DefuncMode {
    fn value_variants<'a>() -> &'a [Self] {
        &[Self::Specialize, Self::Single]
    }

    fn to_possible_value(&self) -> Option<clap::builder::PossibleValue> {
        Some(PossibleValue::new(self.to_str()))
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

impl RcStrategy {
    pub fn to_str(&self) -> &'static str {
        match self {
            Self::Default => "default",
            Self::Perceus => "perceus",
        }
    }
}

impl ValueEnum for RcStrategy {
    fn value_variants<'a>() -> &'a [Self] {
        &[Self::Default, Self::Perceus]
    }

    fn to_possible_value(&self) -> Option<clap::builder::PossibleValue> {
        Some(PossibleValue::new(self.to_str()))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ArrayKind {
    Cow,
    Persistent,
}

impl Default for ArrayKind {
    fn default() -> Self {
        Self::Cow
    }
}

impl ArrayKind {
    pub fn to_str(&self) -> &'static str {
        match self {
            Self::Cow => "cow",
            Self::Persistent => "persistent",
        }
    }
}

impl ValueEnum for ArrayKind {
    fn value_variants<'a>() -> &'a [Self] {
        &[Self::Cow, Self::Persistent]
    }

    fn to_possible_value(&self) -> Option<clap::builder::PossibleValue> {
        Some(PossibleValue::new(self.to_str()))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum GcKind {
    Rc,
    Bdw,
}

impl Default for GcKind {
    fn default() -> Self {
        Self::Rc
    }
}

impl GcKind {
    pub fn to_str(&self) -> &'static str {
        match self {
            Self::Rc => "rc",
            Self::Bdw => "bdw",
        }
    }
}

impl ValueEnum for GcKind {
    fn value_variants<'a>() -> &'a [Self] {
        &[Self::Rc, Self::Bdw]
    }

    fn to_possible_value(&self) -> Option<clap::builder::PossibleValue> {
        Some(PossibleValue::new(self.to_str()))
    }
}

pub fn default_llvm_opt_level() -> inkwell::OptimizationLevel {
    inkwell::OptimizationLevel::Aggressive
}

#[derive(Clone, Copy, Debug)]
pub enum TargetConfig {
    Native,
    Wasm,
}

impl Default for TargetConfig {
    fn default() -> Self {
        Self::Native
    }
}

#[derive(Clone, Copy, Debug)]
pub struct LlvmConfig {
    pub rc_strat: RcStrategy,
    pub gc_kind: GcKind,
    pub array_kind: ArrayKind,
    pub opt_level: inkwell::OptimizationLevel,
    pub target: TargetConfig,
}

impl Default for LlvmConfig {
    fn default() -> Self {
        Self {
            rc_strat: RcStrategy::default(),
            gc_kind: GcKind::default(),
            array_kind: ArrayKind::default(),
            opt_level: default_llvm_opt_level(),
            target: TargetConfig::default(),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum CompilationStage {
    Typed,
    Mono,
    FirstOrder,
}

impl Default for CompilationStage {
    fn default() -> Self {
        Self::FirstOrder
    }
}

impl CompilationStage {
    pub fn to_str(&self) -> &'static str {
        match self {
            Self::Typed => "typed",
            Self::Mono => "mono",
            Self::FirstOrder => "first_order",
        }
    }
}

impl ValueEnum for CompilationStage {
    fn value_variants<'a>() -> &'a [Self] {
        &[Self::Typed, Self::Mono, Self::FirstOrder]
    }

    fn to_possible_value(&self) -> Option<clap::builder::PossibleValue> {
        Some(PossibleValue::new(self.to_str()))
    }
}

#[derive(Clone, Copy, Debug)]
pub enum MlVariant {
    Sml,
    OCaml,
}

impl MlVariant {
    pub fn to_str(&self) -> &'static str {
        match self {
            Self::Sml => "sml",
            Self::OCaml => "ocaml",
        }
    }

    pub fn extension(&self) -> &'static str {
        match self {
            Self::Sml => "sml",
            Self::OCaml => "ml",
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct MlConfig {
    pub variant: MlVariant,
    pub stage: CompilationStage,
}

#[derive(Clone, Copy, Debug)]
pub enum BackendOptions {
    Llvm(LlvmConfig),
    Ml(MlConfig),
}

impl Default for BackendOptions {
    fn default() -> Self {
        Self::Llvm(LlvmConfig::default())
    }
}

#[derive(Clone, Debug)]
pub enum RunMode {
    Compile { valgrind: Option<ValgrindConfig> },
    Interpret,
}

#[derive(Clone, Debug)]
pub struct RunConfig {
    pub src_path: PathBuf,
    pub progress: progress_ui::ProgressMode,
    pub purity_mode: PurityMode,
    pub defunc_mode: DefuncMode,
    pub llvm_config: LlvmConfig,

    pub run_mode: RunMode,

    // This controls the stdio capture behavior of the *user* program.  Logging and error messages
    // from the compiler itself are unaffected.
    //
    // When invoking the compiler from the command line this should always take the value 'Inherit'.
    // The 'Piped' variant exists only for use within the internal testing framework.
    pub stdio: Stdio,
}

#[derive(Debug)]
pub struct BuildConfig {
    pub src_path: PathBuf,
    pub progress: progress_ui::ProgressMode,
    pub purity_mode: PurityMode,
    pub defunc_mode: DefuncMode,
    pub backend_opts: BackendOptions,

    pub profile_syms: Vec<SymbolName>,
    pub profile_mode: ProfileMode,
    pub output_path: PathBuf,
    pub artifact_dir: Option<ArtifactDir>,
}

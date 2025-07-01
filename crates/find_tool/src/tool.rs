use std::ffi::OsString;
use std::fmt;
use std::path::{Path, PathBuf};
use std::process::Command as Cmd;
use std::rc::Rc;

#[derive(Debug, Clone)]
struct ToolName(String);

impl fmt::Display for ToolName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone)]
struct ValidatorName(String);

impl fmt::Display for ValidatorName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone)]
enum Message {
    CheckingEnvVar(OsString),
    EnvVarFound(OsString, String),
    EnvVarInvalid(OsString, std::env::VarError),

    RunningWhich(OsString),
    WhichSuccess(OsString, PathBuf),
    WhichFailure(OsString, which::Error),

    FindingTool(ToolName),
    ToolFailure(ToolName, String),

    RunningValidator(ValidatorName),
    IsValid(ToolName),
    IsInvalid(ToolName, String),
}

impl fmt::Display for Message {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Message::CheckingEnvVar(var) => {
                write!(f, "Checking environment variable '{}'", var.display())
            }
            Message::EnvVarFound(var, val) => {
                write!(f, "Environment variable found: {}={}", var.display(), val)
            }
            Message::EnvVarInvalid(var, err) => {
                write!(
                    f,
                    "Environment variable '{}' invalid: {}",
                    var.display(),
                    err
                )
            }

            Message::RunningWhich(exe) => {
                write!(f, "Checking executable '{}'", exe.display())
            }
            Message::WhichSuccess(exe, path) => {
                write!(
                    f,
                    "Executable '{}' found: path is '{}'",
                    exe.display(),
                    path.display()
                )
            }
            Message::WhichFailure(exe, err) => {
                write!(f, "Executable '{}' invalid: {err}", exe.display())
            }

            Message::FindingTool(tool) => write!(f, "Finding tool '{tool}'"),
            Message::ToolFailure(tool, err) => write!(f, "Tool '{tool}' failed: {err}"),

            Message::RunningValidator(validator) => write!(f, "Running validator '{validator}'"),
            Message::IsValid(tool) => write!(f, "Validation succeeded for tool '{tool}'"),
            Message::IsInvalid(tool, err) => {
                write!(f, "Validation failed for tool '{tool}': {err}")
            }
        }
    }
}

#[derive(Debug, Clone)]
struct Log {
    indent: usize,
    messages: Vec<(usize, Message)>,
}

impl Log {
    fn new() -> Self {
        Self {
            indent: 0,
            messages: Vec::new(),
        }
    }

    fn nest<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.indent += 1;
        let result = f(self);
        self.indent -= 1;
        result
    }

    fn push(&mut self, message: Message) {
        self.messages.push((self.indent, message));
    }
}

impl fmt::Display for Log {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (indent, message) in &self.messages {
            writeln!(f, "{:indent$}- {message}", "", indent = indent * 2)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct Tool {
    name: ToolName,
    path: PathBuf,
}

impl Tool {
    pub fn new(name: &str, path: &Path) -> Self {
        Self {
            name: ToolName(name.to_owned()),
            path: path.to_owned(),
        }
    }

    pub fn name(&self) -> &str {
        &self.name.0
    }

    pub fn path(&self) -> &Path {
        &self.path
    }
}

#[derive(Clone)]
pub struct StrategyProvider(Rc<dyn Fn(&Tool) -> Result<Strategy, String>>);

impl fmt::Debug for StrategyProvider {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "StrategyProvider {{ .. }}")
    }
}

impl StrategyProvider {
    pub fn new(f: impl Fn(&Tool) -> Result<Strategy, String> + 'static) -> Self {
        Self(Rc::new(f))
    }
}

#[derive(Debug, Clone, Copy)]
pub enum EnvVarKind {
    /// If the env var is defined but does not point to a valid tool, try further strategies.
    Soft,
    /// If the env var is defined but does not point to a valid tool, don't try further strategies.
    Hard,
}

#[derive(Debug, Clone)]
pub enum Strategy {
    EnvVar(OsString, EnvVarKind),
    Which(OsString),
    Tool(ToolFinder, StrategyProvider),
    TryEach(Vec<Strategy>),
}

#[derive(Clone)]
pub struct Validator {
    name: ValidatorName,
    f: Rc<dyn Fn(&Tool) -> Result<(), String>>,
}

impl Validator {
    pub fn new(name: &str, f: impl Fn(&Tool) -> Result<(), String> + 'static) -> Self {
        Self {
            name: ValidatorName(name.to_owned()),
            f: Rc::new(f),
        }
    }
}

impl fmt::Debug for Validator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Validator {{ .. }}")
    }
}

#[derive(Debug, Clone)]
pub struct ToolFinder {
    name: ToolName,
    search_strategies: Vec<Strategy>,
    validators: Vec<Validator>,
    print_log: bool,
}

impl ToolFinder {
    pub fn new(name: &str) -> Self {
        Self {
            name: ToolName(name.to_owned()),
            search_strategies: Vec::new(),
            validators: Vec::new(),
            print_log: false,
        }
    }

    pub fn with_strategy(mut self, strategy: Strategy) -> Self {
        self.search_strategies.push(strategy);
        self
    }

    pub fn with_validator(mut self, validator: Validator) -> Self {
        self.validators.push(validator);
        self
    }

    pub fn set_print_log(mut self, print_log: bool) -> Self {
        self.print_log = print_log;
        self
    }

    fn is_valid(&self, log: &mut Log, tool: &Tool) -> bool {
        for validator in &self.validators {
            log.push(Message::RunningValidator(validator.name.clone()));
            if let Err(err) = (validator.f)(tool) {
                log.push(Message::IsInvalid(tool.name.clone(), err));
                return false;
            }
        }
        if self.validators.len() > 0 {
            log.push(Message::IsValid(tool.name.clone()));
        }
        true
    }

    fn try_strategy(&self, log: &mut Log, strategy: &Strategy) -> Option<Option<Tool>> {
        match strategy {
            Strategy::EnvVar(var, kind) => {
                log.push(Message::CheckingEnvVar(var.clone()));
                match std::env::var(var) {
                    Ok(val) => {
                        let tool = Tool {
                            name: self.name.clone(),
                            path: PathBuf::from(val.clone()),
                        };
                        log.push(Message::EnvVarFound(var.clone(), val));
                        match (self.is_valid(log, &tool), kind) {
                            (true, _) => Some(Some(tool)),
                            (false, EnvVarKind::Soft) => None,
                            (false, EnvVarKind::Hard) => Some(None),
                        }
                    }
                    Err(err) => {
                        log.push(Message::EnvVarInvalid(var.clone(), err));
                        None
                    }
                }
            }
            Strategy::Which(exe) => {
                log.push(Message::RunningWhich(exe.clone()));
                match which::which(exe) {
                    Ok(path) => {
                        log.push(Message::WhichSuccess(exe.clone(), path.clone()));
                        let tool = Tool {
                            name: self.name.clone(),
                            path,
                        };
                        if self.is_valid(log, &tool) {
                            Some(Some(tool))
                        } else {
                            None
                        }
                    }
                    Err(err) => {
                        log.push(Message::WhichFailure(exe.clone(), err));
                        None
                    }
                }
            }
            Strategy::Tool(tool_finder, strategy_provider) => {
                log.push(Message::FindingTool(tool_finder.name.clone()));
                let tool = log.nest(|log| tool_finder.try_each_strategy(log))??;
                let strategy = match (strategy_provider.0)(&tool) {
                    Ok(strategy) => strategy,
                    Err(err) => {
                        log.push(Message::ToolFailure(tool_finder.name.clone(), err));
                        return None;
                    }
                };
                self.try_strategy(log, &strategy)
            }
            Strategy::TryEach(items) => items.iter().find_map(|item| self.try_strategy(log, item)),
        }
    }

    fn try_each_strategy(&self, log: &mut Log) -> Option<Option<Tool>> {
        self.search_strategies
            .iter()
            .find_map(|strategy| self.try_strategy(log, strategy))
    }

    pub fn find_tool(&self) -> Result<Tool, String> {
        let mut log = Log::new();
        let result = self
            .try_each_strategy(&mut log)
            .flatten()
            .ok_or_else(|| log.to_string());
        if self.print_log {
            println!("{}", log);
        }
        result
    }
}

pub fn display_cmd(cmd: &Cmd) -> String {
    std::iter::once(cmd.get_program())
        .chain(cmd.get_args().into_iter())
        .map(|s| s.to_string_lossy())
        .collect::<Vec<_>>()
        .join(" ")
}

pub fn get_cmd_out(cmd: &mut Cmd) -> Result<String, String> {
    let out = cmd
        .output()
        .map_err(|err| format!("Cannot execute '{}': {}", display_cmd(cmd), err))?;
    if out.status.success() {
        Ok(String::from_utf8(out.stdout)
            .map_err(|err| format!("Cannot parse output from '{}': {}", display_cmd(cmd), err))?
            .trim()
            .to_owned())
    } else {
        Err(format!(
            "Command failed '{}': {}",
            display_cmd(cmd),
            out.status
        ))
    }
}

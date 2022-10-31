use std::{borrow::Cow, time::Duration};

use crate::util::progress_logger::{ProgressLogger, ProgressSession};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProgressMode {
    Hidden,
    Visible,
}

#[derive(Clone, Debug)]
pub struct ProgressBarLogger {
    name: String,
    mode: ProgressMode,
}

pub fn bar(mode: ProgressMode, name: impl ToString) -> ProgressBarLogger {
    ProgressBarLogger {
        name: name.to_string(),
        mode,
    }
}

#[derive(Clone, Debug)]
pub struct ProgressBarSession {
    bar: indicatif::ProgressBar,
}

impl ProgressLogger for ProgressBarLogger {
    type Session = ProgressBarSession;

    fn start_session(self, count: Option<usize>) -> Self::Session {
        let bar = indicatif::ProgressBar::with_draw_target(
            count.map(|count| count as u64),
            match self.mode {
                ProgressMode::Hidden => indicatif::ProgressDrawTarget::hidden(),
                ProgressMode::Visible => indicatif::ProgressDrawTarget::stderr(),
            },
        );
        const TICK_STRINGS: &[&str] = &["⠉", "⠘", "⠰", "⠤", "⠆", "⠃", "✔"];
        if count.is_some() {
            bar.set_style(
                indicatif::ProgressStyle::default_bar()
                    .template(
                        "{spinner:.cyan} [{elapsed_precise}] [{bar:.cyan/blue}] {pos}/{len} {msg}",
                    )
                    .unwrap()
                    .progress_chars("=> ")
                    .tick_strings(TICK_STRINGS),
            );
        } else {
            bar.set_style(
                indicatif::ProgressStyle::default_spinner()
                    .template("{spinner:.cyan} [{elapsed_precise}] {msg}")
                    .unwrap()
                    .tick_strings(TICK_STRINGS),
            );
        }
        bar.set_message(Cow::Owned(self.name));
        bar.enable_steady_tick(Duration::from_millis(100));
        ProgressBarSession { bar }
    }
}

impl ProgressSession for ProgressBarSession {
    fn update(&mut self, inc: usize) {
        self.bar.inc(inc as u64);
    }

    fn finish(self) {
        self.bar.finish();
    }
}

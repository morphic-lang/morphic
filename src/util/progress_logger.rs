pub trait ProgressLogger {
    type Session: ProgressSession;
    fn start_session(self, total_count: Option<usize>) -> Self::Session;
}

pub trait ProgressSession {
    fn update(&mut self, progress: usize);
    fn finish(self);
}

#[derive(Clone, Copy, Debug)]
pub struct Hidden;

#[derive(Clone, Copy, Debug)]
pub struct HiddenSession;

impl ProgressLogger for Hidden {
    type Session = HiddenSession;
    fn start_session(self, _total_count: Option<usize>) -> Self::Session {
        HiddenSession
    }
}

impl ProgressSession for HiddenSession {
    fn update(&mut self, _progress: usize) {}
    fn finish(self) {}
}

#[derive(Debug)]
pub struct DropBomb {
    msg: &'static str,
    defused: bool,
}

impl DropBomb {
    pub fn new(msg: &'static str) -> DropBomb {
        DropBomb {
            msg,
            defused: false,
        }
    }

    pub fn defuse(&mut self) {
        self.defused = true;
    }
}

impl Drop for DropBomb {
    fn drop(&mut self) {
        if !self.defused {
            panic!("{}", self.msg);
        }
    }
}

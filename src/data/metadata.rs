#[derive(Clone, Debug, Default)]
pub struct Metadata {
    pub comments: Vec<String>,
}

impl Metadata {
    pub fn add_comment(&mut self, comment: String) {
        self.comments.push(comment);
    }
}

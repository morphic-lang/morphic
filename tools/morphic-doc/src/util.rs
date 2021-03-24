pub trait IteratorStringExt {
    fn join_strings(self, delim: &str) -> String;
}

impl<I, T> IteratorStringExt for I
where
    I: Iterator<Item = T>,
    T: AsRef<str>,
{
    fn join_strings(self, delim: &str) -> String {
        let mut res = self.fold(String::new(), |a, b| a + b.as_ref() + delim);
        res.truncate(res.len().saturating_sub(delim.len()));
        res
    }
}

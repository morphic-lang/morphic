macro_rules! lines {
    () => {
        ""
    };

    ($line:expr) => {
        concat!($line, "\n")
    };

    ($line:expr, $($tail:expr),* $(,)?) => {
        concat!(concat!($line, "\n"), lines!($($tail),*))
    };
}

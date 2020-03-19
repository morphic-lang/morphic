use ansi_term::Color;
use std::io;
use std::path::Path;
use std::path::PathBuf;
use textwrap::{NoHyphenation, Wrapper};

use crate::file_cache::FileCache;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ByteIdx(usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct LineIdx(usize);

#[derive(Clone, Debug)]
struct Lines<'a> {
    content: &'a str,
    line_starts: Vec<ByteIdx>,
}

impl<'a> Lines<'a> {
    fn new(content: &'a str) -> Self {
        let mut line_starts = vec![ByteIdx(0)];
        for (byte_idx, c) in content.char_indices() {
            if c == '\n' {
                line_starts.push(ByteIdx(byte_idx + 1));
            }
        }

        Lines {
            content,
            line_starts,
        }
    }

    fn content(&self) -> &'a str {
        self.content
    }

    fn line_idx(&self, byte_idx: ByteIdx) -> LineIdx {
        match self.line_starts.binary_search(&byte_idx) {
            Ok(exact_idx) => LineIdx(exact_idx),
            Err(next_idx) => {
                debug_assert!(next_idx > 0);
                LineIdx(next_idx - 1)
            }
        }
    }

    fn line_idx_before(&self, byte_idx: ByteIdx) -> LineIdx {
        match self.line_starts.binary_search(&byte_idx) {
            Ok(0) => LineIdx(0),
            Ok(exact_idx) => LineIdx(exact_idx - 1),
            Err(next_idx) => {
                debug_assert!(next_idx > 0);
                LineIdx(next_idx - 1)
            }
        }
    }

    fn line(&self, line_idx: LineIdx) -> &'a str {
        let start = self.line_starts[line_idx.0].0;
        let end = if let Some(next_start) = self.line_starts.get(line_idx.0 + 1) {
            // Guaranteed to point to a valid UTF-8 code point, because a line start is always
            // immediately after a '\n'.
            next_start.0 - 1
        } else {
            self.content().len()
        };

        let line = &self.content[start..end];
        if line.ends_with('\r') {
            &line[..line.len() - 1]
        } else {
            line
        }
    }

    fn col_idx(&self, line_idx: LineIdx, byte_idx: ByteIdx) -> usize {
        let line_start = self.line_starts[line_idx.0];
        byte_idx.0 - line_start.0
    }
}

fn line_digits(src: &Lines) -> usize {
    let mut digits = 1;
    let mut max_line = 9;
    while max_line < src.line_starts.len() {
        digits += 1;
        max_line = 10 * max_line + 9;
    }
    digits
}

fn format_snippet(
    dest: &mut impl io::Write,
    src: &Lines,
    lo: ByteIdx,
    hi: ByteIdx,
) -> io::Result<()> {
    let lo_line = src.line_idx(lo);
    let hi_line = src.line_idx_before(hi);

    let digits = line_digits(src);

    let line_num_style = Color::Blue.bold();
    let indicator_style = Color::Red.bold();

    if lo_line == hi_line {
        let content = src.line(lo_line);

        let start_col = src.col_idx(lo_line, lo);
        let num_cols = hi.0 - lo.0;

        writeln!(
            dest,
            "{}",
            line_num_style.paint(format!(" {empty:>digits$} |", empty = "", digits = digits))
        )?;
        writeln!(
            dest,
            "{runner} {content}",
            runner = line_num_style.paint(format!(
                " {num:>digits$} |",
                num = lo_line.0 + 1,
                digits = digits
            )),
            content = content
        )?;
        writeln!(
            dest,
            "{runner} {empty:start_col$}{indicator}",
            runner =
                line_num_style.paint(format!(" {empty:>digits$} |", empty = "", digits = digits)),
            empty = "",
            start_col = start_col,
            indicator = indicator_style.paint("^".repeat(num_cols)),
        )?;
    } else {
        let start_col = src.col_idx(lo_line, lo);
        let num_cols_on_last_line = src.col_idx(hi_line, hi);

        debug_assert!(num_cols_on_last_line > 0);

        // This range is exclusive because we only want to make the indicator large enough to
        // accomodate every line *in* the indicated source range.  This doesn't include characters
        // on the last line past the end of the indicated range.
        let max_content_len = (lo_line.0..hi_line.0)
            .map(|line_idx| src.line(LineIdx(line_idx)).len())
            .max()
            .unwrap();

        debug_assert!(max_content_len > start_col);

        writeln!(
            dest,
            "{runner} {empty:start_col$}{indicator}",
            runner =
                line_num_style.paint(format!(" {empty:>digits$} |", empty = "", digits = digits)),
            empty = "",
            start_col = start_col,
            indicator = indicator_style.paint(format!(
                "*{}",
                // Notice that, when you count the contribution of the leading '*', we extend one
                // character beyond `max_content_len - start_col`.  This is intentional, as it
                // visually indicates continuation onto multiple lines.
                "~".repeat(max_content_len - start_col)
            )),
        )?;

        for line_idx in lo_line.0..=hi_line.0 {
            let content = src.line(LineIdx(line_idx));

            writeln!(
                dest,
                "{runner} {content}",
                runner = line_num_style.paint(format!(
                    " {num:>digits$} |",
                    num = line_idx + 1,
                    digits = digits
                )),
                content = content
            )?;
        }

        writeln!(
            dest,
            "{runner}{indicator}",
            runner =
                line_num_style.paint(format!(" {empty:>digits$} |", empty = "", digits = digits)),
            indicator = indicator_style.paint(format!("{}*", "~".repeat(num_cols_on_last_line))),
        )?;
    }

    Ok(())
}

#[derive(Clone, Copy, Debug)]
pub struct Report<'a> {
    pub path: Option<&'a Path>,
    pub span: Option<(usize, usize)>,
    pub title: &'a str,
    pub message: Option<&'a str>,
}

const TITLE_LEADING_DASHES: usize = 10;
const TITLE_TOTAL_COLS: usize = 60;
const MESSAGE_WIDTH: usize = 60;

pub fn report_error(
    dest: &mut impl io::Write,
    files: &FileCache,
    report: Report,
) -> io::Result<()> {
    let title_style = Color::Blue.bold();
    let path_style = Color::Yellow.normal();

    // Write title
    writeln!(
        dest,
        "\n{}",
        title_style.paint(format!(
            "{leading} {title} {trailing}",
            leading = "-".repeat(TITLE_LEADING_DASHES),
            title = report.title,
            trailing = "-".repeat(
                TITLE_TOTAL_COLS.saturating_sub(2 + report.title.len() + TITLE_LEADING_DASHES)
            ),
        ))
    )?;

    match (report.path, report.span) {
        (Some(path), Some((lo, hi))) => {
            let src = Lines::new(files.read_cached(path)?);
            let lo_line = src.line_idx(ByteIdx(lo));
            let lo_col = src.col_idx(lo_line, ByteIdx(lo));

            writeln!(
                dest,
                "{}",
                path_style.paint(format!(
                    "{}:{}:{}",
                    path.display(),
                    lo_line.0 + 1,
                    lo_col + 1
                ))
            )?;

            writeln!(dest)?;

            format_snippet(dest, &src, ByteIdx(lo), ByteIdx(hi))?;
        }

        (Some(path), None) => {
            writeln!(dest, "{}", path_style.paint(path.display().to_string()))?;
        }

        (None, _) => {}
    }

    if let Some(message) = report.message {
        writeln!(dest)?;
        for line in message.lines() {
            let indentation = line.chars().take_while(|&c| c == ' ').count();
            let indent_str = &line[..indentation];

            let wrapped = Wrapper::with_splitter(MESSAGE_WIDTH, NoHyphenation)
                .initial_indent(indent_str)
                .subsequent_indent(indent_str)
                .wrap(&line[indentation..]);

            if wrapped.is_empty() {
                writeln!(dest)?;
            } else {
                for wrapped_line in wrapped {
                    writeln!(dest, "{}", wrapped_line)?;
                }
            }
        }
    }

    writeln!(dest)?;

    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Locate<E> {
    pub path: Option<PathBuf>,
    pub span: Option<(usize, usize)>,
    pub error: E,
}

impl<E> From<E> for Locate<E> {
    fn from(error: E) -> Self {
        Locate {
            path: None,
            span: None,
            error,
        }
    }
}

// These functions are curried for convenient usage with 'map_err'.

pub fn locate_path<'a, E>(
    path: &'a (impl AsRef<Path> + ?Sized),
) -> impl FnOnce(Locate<E>) -> Locate<E> + 'a {
    move |err| Locate {
        path: Some(err.path.unwrap_or_else(|| path.as_ref().to_owned())),
        ..err
    }
}

pub fn locate_span<E>(lo: usize, hi: usize) -> impl FnOnce(Locate<E>) -> Locate<E> {
    move |err| Locate {
        span: Some(err.span.unwrap_or((lo, hi))),
        ..err
    }
}

impl<E> Locate<E> {
    pub fn report_with<Title, Msg>(
        &self,
        dest: &mut impl io::Write,
        files: &FileCache,
        reporter: impl FnOnce(&E) -> (Title, Msg),
    ) -> io::Result<()>
    where
        Title: AsRef<str>,
        Msg: AsRef<str>,
    {
        let (title, message) = reporter(&self.error);

        report_error(
            dest,
            files,
            Report {
                path: self.path.as_ref().map(|path| path.as_ref()),
                span: self.span,
                title: title.as_ref(),
                message: Some(message.as_ref()),
            },
        )
    }
}

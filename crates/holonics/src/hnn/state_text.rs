//! [definition; agent-inferred, October 4; the reception carry §10] **The saved state's lines**:
//! the readers each owner's part of a continuing state uses
//! ([`crate::hnn::constitution::ContinuingState`]). A part reads its lines from `next`, which
//! refuses at the text's end; every refusal is typed by what was being read.

use std::str::FromStr;

use crate::hnn::HnnError;

/// The text's next line, drawn by the state's reader.
pub(crate) type Next<'n, 'a> = &'n mut dyn FnMut(&'static str) -> Result<&'a str, HnnError>;

pub(crate) fn refused<T>(what: &'static str) -> Result<T, HnnError> {
    Err(HnnError::ContinuingState { what })
}

/// A line's words after its key, refused when the key differs.
pub(crate) fn keyed<'a>(line: &'a str, key: &str, what: &'static str) -> Result<Vec<&'a str>, HnnError> {
    let mut words = line.split_whitespace();
    if words.next() != Some(key) {
        return refused(what);
    }
    Ok(words.collect())
}

/// One word read as a value.
pub(crate) fn value<T: FromStr>(word: Option<&&str>, what: &'static str) -> Result<T, HnnError> {
    word.and_then(|w| w.parse().ok())
        .ok_or(HnnError::ContinuingState { what })
}

/// Words read as values.
pub(crate) fn values<T: FromStr>(words: &[&str], what: &'static str) -> Result<Vec<T>, HnnError> {
    words.iter().map(|w| value(Some(w), what)).collect()
}

/// A keyed line's values, exactly `count` of them.
pub(crate) fn counted<T: FromStr>(
    line: &str,
    key: &str,
    count: usize,
    what: &'static str,
) -> Result<Vec<T>, HnnError> {
    let words = keyed(line, key, what)?;
    if words.len() != count {
        return refused(what);
    }
    values(&words, what)
}

/// Values written on one line after their key.
pub(crate) fn line<T: ToString>(s: &mut String, key: &str, values: impl IntoIterator<Item = T>) {
    *s += key;
    for value in values {
        s.push(' ');
        *s += &value.to_string();
    }
    s.push('\n');
}

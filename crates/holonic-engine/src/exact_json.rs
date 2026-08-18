//! **A minimal exact scanner for the JSON containers a foreign map arrives in.**
//!
//! Written out rather than pulled in for one reason that is not taste: **every value this project
//! reads out of such a container is a non-negative integer array or a string**, and a general parser
//! admits a float. A safetensors header carries shapes and byte offsets. It has no place a float
//! could enter, and this scanner has no path that would decode
//! one — so the workspace's no-float law is held by the reader's own shape rather than by
//! discipline downstream.
//!
//! It returns **spans** rather than a tree, so a caller reads only the fields it needs.

/// `(key, value_span)` pairs of the outermost object, in declaration order.
pub fn top_level_pairs(text: &str) -> Result<Vec<(String, &str)>, String> {
    let bytes = text.as_bytes();
    let mut at = 0usize;
    skip_space(bytes, &mut at);
    if bytes.get(at) != Some(&b'{') {
        return Err("the header does not open with an object".to_owned());
    }
    at += 1;
    let mut pairs = Vec::new();
    loop {
        skip_space(bytes, &mut at);
        match bytes.get(at) {
            None => return Err("the header ends inside its object".to_owned()),
            Some(b'}') => return Ok(pairs),
            Some(b',') => {
                at += 1;
                continue;
            }
            Some(b'"') => {}
            Some(other) => return Err(format!("unexpected octet {:?} in the header", *other)),
        }
        let key = read_string(bytes, &mut at)?;
        skip_space(bytes, &mut at);
        if bytes.get(at) != Some(&b':') {
            return Err(format!("the key {key:?} carries no value"));
        }
        at += 1;
        skip_space(bytes, &mut at);
        let from = at;
        skip_value(bytes, &mut at)?;
        pairs.push((key, &text[from..at]));
    }
}

/// A field of one flat object, returned as its raw span.
pub fn field<'a>(object: &'a str, key: &str) -> Option<&'a str> {
    let pairs = top_level_pairs(object).ok()?;
    pairs
        .into_iter()
        .find(|(name, _)| name == key)
        .map(|(_, span)| span)
}

pub fn as_string(span: &str) -> Option<String> {
    let bytes = span.as_bytes();
    let mut at = 0usize;
    skip_space(bytes, &mut at);
    if bytes.get(at) != Some(&b'"') {
        return None;
    }
    read_string(bytes, &mut at).ok()
}

/// Every non-negative integer inside a `[...]` span, in order. An empty array returns an empty
/// vector, which is the whole point: `"shape":[]` is a rank-0 tensor and not a missing field.
pub fn as_u64_array(span: &str) -> Option<Vec<u64>> {
    let trimmed = span.trim();
    let inner = trimmed.strip_prefix('[')?.strip_suffix(']')?;
    if inner.trim().is_empty() {
        return Some(Vec::new());
    }
    let mut out = Vec::new();
    for piece in inner.split(',') {
        out.push(piece.trim().parse::<u64>().ok()?);
    }
    Some(out)
}

fn skip_space(bytes: &[u8], at: &mut usize) {
    while matches!(bytes.get(*at), Some(b' ' | b'\t' | b'\n' | b'\r')) {
        *at += 1;
    }
}

fn read_string(bytes: &[u8], at: &mut usize) -> Result<String, String> {
    if bytes.get(*at) != Some(&b'"') {
        return Err("expected a string".to_owned());
    }
    *at += 1;
    let mut out = String::new();
    loop {
        match bytes.get(*at) {
            None => return Err("a string is unterminated".to_owned()),
            Some(b'"') => {
                *at += 1;
                return Ok(out);
            }
            Some(b'\\') => {
                let escaped = *bytes.get(*at + 1).ok_or("a trailing escape")?;
                match escaped {
                    b'b' => {
                        out.push('\u{0008}');
                        *at += 2;
                    }
                    b'f' => {
                        out.push('\u{000c}');
                        *at += 2;
                    }
                    b'n' => {
                        out.push('\n');
                        *at += 2;
                    }
                    b't' => {
                        out.push('\t');
                        *at += 2;
                    }
                    b'r' => {
                        out.push('\r');
                        *at += 2;
                    }
                    b'"' => {
                        out.push('"');
                        *at += 2;
                    }
                    b'\\' => {
                        out.push('\\');
                        *at += 2;
                    }
                    b'/' => {
                        out.push('/');
                        *at += 2;
                    }
                    b'u' => {
                        let high = read_hex_quad(bytes, *at + 2)?;
                        *at += 6;
                        let scalar = if (0xd800..=0xdbff).contains(&high) {
                            if bytes.get(*at) != Some(&b'\\') || bytes.get(*at + 1) != Some(&b'u') {
                                return Err("a high surrogate carries no low surrogate".to_owned());
                            }
                            let low = read_hex_quad(bytes, *at + 2)?;
                            if !(0xdc00..=0xdfff).contains(&low) {
                                return Err("a high surrogate is followed by a non-low surrogate"
                                    .to_owned());
                            }
                            *at += 6;
                            0x1_0000 + (((high as u32 - 0xd800) << 10) | (low as u32 - 0xdc00))
                        } else if (0xdc00..=0xdfff).contains(&high) {
                            return Err(
                                "a low surrogate appears without a high surrogate".to_owned()
                            );
                        } else {
                            high as u32
                        };
                        out.push(char::from_u32(scalar).ok_or("a unicode escape is not a scalar")?);
                    }
                    _ => return Err(format!("unknown JSON escape \\{}", escaped as char)),
                }
            }
            Some(other) => {
                if *other < 0x20 {
                    return Err("a string contains an unescaped control octet".to_owned());
                }
                // Multi-octet UTF-8 sequences pass through whole.
                let width = utf8_width(*other).ok_or("a string has an invalid UTF-8 lead octet")?;
                let end = at.checked_add(width).ok_or("a UTF-8 extent overflowed")?;
                let piece = std::str::from_utf8(
                    bytes
                        .get(*at..end)
                        .ok_or("a string ends inside a UTF-8 sequence")?,
                )
                .map_err(|_| "a string holds invalid UTF-8".to_owned())?;
                out.push_str(piece);
                *at = end;
            }
        }
    }
}

fn read_hex_quad(bytes: &[u8], from: usize) -> Result<u16, String> {
    let digits = bytes
        .get(from..from + 4)
        .ok_or("a unicode escape is truncated")?;
    let mut value = 0u16;
    for digit in digits {
        value = value
            .checked_mul(16)
            .and_then(|held| {
                let nibble = match digit {
                    b'0'..=b'9' => digit - b'0',
                    b'a'..=b'f' => digit - b'a' + 10,
                    b'A'..=b'F' => digit - b'A' + 10,
                    _ => return None,
                };
                held.checked_add(u16::from(nibble))
            })
            .ok_or("a unicode escape contains a non-hex digit")?;
    }
    Ok(value)
}

fn utf8_width(lead: u8) -> Option<usize> {
    match lead {
        0x00..=0x7f => Some(1),
        0xc2..=0xdf => Some(2),
        0xe0..=0xef => Some(3),
        0xf0..=0xf4 => Some(4),
        _ => None,
    }
}

fn skip_value(bytes: &[u8], at: &mut usize) -> Result<(), String> {
    skip_space(bytes, at);
    match bytes.get(*at) {
        None => Err("a value is missing".to_owned()),
        Some(b'"') => {
            read_string(bytes, at)?;
            Ok(())
        }
        Some(b'{') | Some(b'[') => {
            let mut closes = Vec::new();
            loop {
                match bytes.get(*at) {
                    None => return Err("a nested value is unterminated".to_owned()),
                    Some(b'"') => {
                        read_string(bytes, at)?;
                        continue;
                    }
                    Some(b'{') => closes.push(b'}'),
                    Some(b'[') => closes.push(b']'),
                    Some(octet @ (b'}' | b']')) => {
                        if closes.pop() != Some(*octet) {
                            return Err("a nested value closes with the wrong delimiter".to_owned());
                        }
                        *at += 1;
                        if closes.is_empty() {
                            return Ok(());
                        }
                        continue;
                    }
                    Some(_) => {}
                }
                *at += 1;
            }
        }
        Some(_) => {
            while matches!(bytes.get(*at), Some(octet) if !matches!(octet, b',' | b'}' | b']')) {
                *at += 1;
            }
            Ok(())
        }
    }
}


/// A signed integer field, exactly. **There is no float path here and that is the point.**
pub fn as_i64(span: &str) -> Option<i64> {
    span.trim().parse::<i64>().ok()
}

pub fn as_bool(span: &str) -> Option<bool> {
    match span.trim() {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

/// The raw spans of a `[...]` array's elements, in order, without allocating a tree.
pub fn array_elements(span: &str) -> Result<Vec<&str>, String> {
    let bytes = span.as_bytes();
    let mut at = 0usize;
    skip_space(bytes, &mut at);
    if bytes.get(at) != Some(&b'[') {
        return Err("the span does not open with an array".to_owned());
    }
    at += 1;
    let mut out = Vec::new();
    loop {
        skip_space(bytes, &mut at);
        match bytes.get(at) {
            None => return Err("the array ends without closing".to_owned()),
            Some(b']') => return Ok(out),
            Some(b',') => {
                at += 1;
                continue;
            }
            Some(_) => {}
        }
        let from = at;
        skip_value(bytes, &mut at)?;
        out.push(&span[from..at]);
    }
}

/// Every string element of a `[...]` span, in order.
pub fn as_string_array(span: &str) -> Option<Vec<String>> {
    array_elements(span)
        .ok()?
        .into_iter()
        .map(as_string)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn an_empty_array_is_a_rank_zero_shape_and_not_a_missing_field() {
        assert_eq!(as_u64_array("[]"), Some(Vec::new()));
        assert_eq!(as_u64_array("[2, 3]"), Some(vec![2, 3]));
        assert_eq!(as_u64_array("not an array"), None);
    }

    #[test]
    fn nested_arrays_and_escaped_strings_are_walked_without_a_tree() {
        let text = r#"{"a":"x\"y","b":{"c":[3]},"d":"\u03bb\ud83d\ude00\b\f"}"#;
        let pairs = top_level_pairs(text).expect("scanned");
        assert_eq!(pairs.len(), 3);
        assert_eq!(as_string(pairs[0].1).as_deref(), Some("x\"y"));
        assert_eq!(field(pairs[1].1, "c").and_then(as_u64_array), Some(vec![3]));
        assert_eq!(
            as_string(pairs[2].1).as_deref(),
            Some("λ😀\u{0008}\u{000c}")
        );
    }

    #[test]
    fn a_malformed_container_refuses_rather_than_guessing() {
        assert!(top_level_pairs("[1,2]").is_err());
        assert!(top_level_pairs("{\"a\"}").is_err());
        assert!(top_level_pairs("{\"a\":[1,2}}").is_err());
        assert!(as_string(r#""\q""#).is_none());
        assert!(as_string(r#""\ud800""#).is_none());
    }
}

//! Exact JSON record incidence without a numeric interpretation.
//!
//! This is an exterior codec mouth. It validates JSON strings and number spellings, but it never
//! converts a number to a machine scalar. The returned tree knows only situated nodes, ordered
//! parent/child incidence and exact content. Object-key names remain codec faces; no name routes
//! the native contact law.

use sha2::{Digest, Sha256};

use super::{Digest32, FieldFace, NodeKind, RecordNode};

pub(super) struct ParsedRecord {
    pub nodes: Vec<RecordNode>,
    pub fields: Vec<FieldFace>,
    pub scalar_nodes: Vec<u32>,
    pub root_digest: Digest32,
}

pub(super) fn parse_record(bytes: &[u8]) -> Result<ParsedRecord, String> {
    let mut parser = Parser {
        bytes,
        at: 0,
        nodes: Vec::new(),
        fields: Vec::new(),
        scalar_nodes: Vec::new(),
    };
    parser.space();
    let (_, root_digest) = parser.value(None, 0)?;
    parser.space();
    if parser.at != bytes.len() {
        return Err(format!(
            "a JSON record carries trailing material at octet {}",
            parser.at
        ));
    }
    Ok(ParsedRecord {
        nodes: parser.nodes,
        fields: parser.fields,
        scalar_nodes: parser.scalar_nodes,
        root_digest,
    })
}

struct Parser<'a> {
    bytes: &'a [u8],
    at: usize,
    nodes: Vec<RecordNode>,
    fields: Vec<FieldFace>,
    scalar_nodes: Vec<u32>,
}

impl Parser<'_> {
    fn value(&mut self, parent: Option<u32>, position: u32) -> Result<(u32, Digest32), String> {
        self.space();
        match self.bytes.get(self.at) {
            Some(b'{') => self.object(parent, position),
            Some(b'[') => self.array(parent, position),
            Some(b'"') => self.string_value(parent, position),
            Some(_) => self.atom(parent, position),
            None => Err("a JSON value is missing".to_owned()),
        }
    }

    fn object(&mut self, parent: Option<u32>, position: u32) -> Result<(u32, Digest32), String> {
        let node = self.open_node(parent, position, NodeKind::Object)?;
        self.at += 1;
        let mut children = Vec::new();
        let mut member = 0u32;
        loop {
            self.space();
            if self.take(b'}') {
                break;
            }
            if member != 0 {
                self.expect(b',', "between object members")?;
                self.space();
            }
            let (key_raw, key_text) = self.string()?;
            let raw_key_sha256 = Digest32::of(key_raw);
            let key_position = member
                .checked_mul(2)
                .ok_or_else(|| "an object member position overflowed".to_owned())?;
            let key_digest = digest_scalar(NodeKind::Key, &key_text);
            let key_node = self.push_node(Some(node), key_position, NodeKind::Key, key_digest)?;
            children.push((key_position, key_digest));
            self.space();
            self.expect(b':', "after an object key")?;
            let value_position = key_position
                .checked_add(1)
                .ok_or_else(|| "an object value position overflowed".to_owned())?;
            let (value_node, value_digest) = self.value(Some(node), value_position)?;
            children.push((value_position, value_digest));
            self.fields.push(FieldFace {
                key_node,
                value_node,
                key: key_text,
                raw_key_sha256,
            });
            member = member
                .checked_add(1)
                .ok_or_else(|| "an object member population overflowed".to_owned())?;
        }
        let digest = digest_composite(NodeKind::Object, &children);
        self.nodes[node as usize].content = digest;
        Ok((node, digest))
    }

    fn array(&mut self, parent: Option<u32>, position: u32) -> Result<(u32, Digest32), String> {
        let node = self.open_node(parent, position, NodeKind::Array)?;
        self.at += 1;
        let mut children = Vec::new();
        let mut child = 0u32;
        loop {
            self.space();
            if self.take(b']') {
                break;
            }
            if child != 0 {
                self.expect(b',', "between array members")?;
            }
            let (_, digest) = self.value(Some(node), child)?;
            children.push((child, digest));
            child = child
                .checked_add(1)
                .ok_or_else(|| "an array member population overflowed".to_owned())?;
        }
        let digest = digest_composite(NodeKind::Array, &children);
        self.nodes[node as usize].content = digest;
        Ok((node, digest))
    }

    fn string_value(
        &mut self,
        parent: Option<u32>,
        position: u32,
    ) -> Result<(u32, Digest32), String> {
        let (_, text) = self.string()?;
        let digest = digest_scalar(NodeKind::String, &text);
        let node = self.push_node(parent, position, NodeKind::String, digest)?;
        self.scalar_nodes.push(node);
        Ok((node, digest))
    }

    fn atom(&mut self, parent: Option<u32>, position: u32) -> Result<(u32, Digest32), String> {
        let from = self.at;
        while matches!(self.bytes.get(self.at), Some(octet) if !matches!(octet, b' ' | b'\t' | b'\r' | b'\n' | b',' | b']' | b'}'))
        {
            self.at += 1;
        }
        let raw = self
            .bytes
            .get(from..self.at)
            .ok_or_else(|| "a JSON atom range is invalid".to_owned())?;
        if !matches!(raw, b"true" | b"false" | b"null") && !valid_number(raw) {
            return Err(format!("an invalid JSON atom begins at octet {from}"));
        }
        let digest = digest_raw(NodeKind::Atom, raw);
        let node = self.push_node(parent, position, NodeKind::Atom, digest)?;
        self.scalar_nodes.push(node);
        Ok((node, digest))
    }

    fn string(&mut self) -> Result<(&[u8], String), String> {
        let from = self.at;
        self.expect(b'"', "at a string opening")?;
        let mut text = String::new();
        loop {
            let Some(octet) = self.bytes.get(self.at).copied() else {
                return Err("a JSON string is unterminated".to_owned());
            };
            match octet {
                b'"' => {
                    self.at += 1;
                    return Ok((&self.bytes[from..self.at], text));
                }
                b'\\' => self.escape(&mut text)?,
                0x00..=0x1f => return Err("a JSON string carries an unescaped control".to_owned()),
                _ => {
                    let width = utf8_width(octet)
                        .ok_or_else(|| "a JSON string carries an invalid UTF-8 lead".to_owned())?;
                    let end = self
                        .at
                        .checked_add(width)
                        .ok_or_else(|| "a JSON UTF-8 range overflowed".to_owned())?;
                    let piece = std::str::from_utf8(
                        self.bytes
                            .get(self.at..end)
                            .ok_or_else(|| "a JSON string ends inside UTF-8".to_owned())?,
                    )
                    .map_err(|_| "a JSON string carries invalid UTF-8".to_owned())?;
                    let scalar = piece
                        .chars()
                        .next()
                        .ok_or_else(|| "a JSON string ends inside UTF-8".to_owned())?;
                    text.push(scalar);
                    self.at = end;
                }
            }
        }
    }

    fn escape(&mut self, text: &mut String) -> Result<(), String> {
        self.at += 1;
        let escaped = self
            .bytes
            .get(self.at)
            .copied()
            .ok_or_else(|| "a JSON string ends after an escape".to_owned())?;
        self.at += 1;
        match escaped {
            b'"' => text.push('"'),
            b'\\' => text.push('\\'),
            b'/' => text.push('/'),
            b'b' => text.push('\u{0008}'),
            b'f' => text.push('\u{000c}'),
            b'n' => text.push('\n'),
            b'r' => text.push('\r'),
            b't' => text.push('\t'),
            b'u' => {
                let high = self.hex_quad()?;
                let scalar = if (0xd800..=0xdbff).contains(&high) {
                    if self.bytes.get(self.at..self.at + 2) != Some(b"\\u") {
                        return Err("a high surrogate carries no low surrogate".to_owned());
                    }
                    self.at += 2;
                    let low = self.hex_quad()?;
                    if !(0xdc00..=0xdfff).contains(&low) {
                        return Err(
                            "a high surrogate is followed by a non-low surrogate".to_owned()
                        );
                    }
                    0x1_0000 + (((u32::from(high) - 0xd800) << 10) | (u32::from(low) - 0xdc00))
                } else if (0xdc00..=0xdfff).contains(&high) {
                    return Err("a low surrogate appears without a high surrogate".to_owned());
                } else {
                    u32::from(high)
                };
                text.push(
                    char::from_u32(scalar)
                        .ok_or_else(|| "a JSON escape is not a scalar".to_owned())?,
                );
            }
            _ => return Err("a JSON string carries an unknown escape".to_owned()),
        }
        Ok(())
    }

    fn hex_quad(&mut self) -> Result<u16, String> {
        let digits = self
            .bytes
            .get(self.at..self.at + 4)
            .ok_or_else(|| "a unicode escape is truncated".to_owned())?;
        let mut value = 0u16;
        for digit in digits {
            let nibble = match digit {
                b'0'..=b'9' => u16::from(*digit - b'0'),
                b'a'..=b'f' => u16::from(*digit - b'a' + 10),
                b'A'..=b'F' => u16::from(*digit - b'A' + 10),
                _ => return Err("a unicode escape carries a non-hex digit".to_owned()),
            };
            value = value
                .checked_mul(16)
                .and_then(|held| held.checked_add(nibble))
                .ok_or_else(|| "a unicode escape overflowed".to_owned())?;
        }
        self.at += 4;
        Ok(value)
    }

    fn open_node(
        &mut self,
        parent: Option<u32>,
        position: u32,
        kind: NodeKind,
    ) -> Result<u32, String> {
        self.push_node(parent, position, kind, Digest32::ZERO)
    }

    fn push_node(
        &mut self,
        parent: Option<u32>,
        position: u32,
        kind: NodeKind,
        content: Digest32,
    ) -> Result<u32, String> {
        let ordinal = u32::try_from(self.nodes.len())
            .map_err(|_| "a JSON record carries more than u32 nodes".to_owned())?;
        self.nodes.push(RecordNode {
            parent,
            position,
            kind,
            content,
        });
        Ok(ordinal)
    }

    fn expect(&mut self, wanted: u8, where_: &str) -> Result<(), String> {
        if self.take(wanted) {
            Ok(())
        } else {
            Err(format!(
                "JSON expected {:?} {where_} at octet {}",
                wanted as char, self.at
            ))
        }
    }

    fn take(&mut self, wanted: u8) -> bool {
        if self.bytes.get(self.at) == Some(&wanted) {
            self.at += 1;
            true
        } else {
            false
        }
    }

    fn space(&mut self) {
        while matches!(self.bytes.get(self.at), Some(b' ' | b'\t' | b'\r' | b'\n')) {
            self.at += 1;
        }
    }
}

fn digest_scalar(kind: NodeKind, text: &str) -> Digest32 {
    digest_raw(kind, text.as_bytes())
}

fn digest_raw(kind: NodeKind, raw: &[u8]) -> Digest32 {
    let mut digest = Sha256::new();
    digest.update([kind.wire()]);
    digest.update((raw.len() as u64).to_le_bytes());
    digest.update(raw);
    Digest32::from_sha(digest.finalize())
}

fn digest_composite(kind: NodeKind, children: &[(u32, Digest32)]) -> Digest32 {
    let mut digest = Sha256::new();
    digest.update([kind.wire()]);
    digest.update((children.len() as u64).to_le_bytes());
    for (position, child) in children {
        digest.update(position.to_le_bytes());
        digest.update(child.octets());
    }
    Digest32::from_sha(digest.finalize())
}

/// JSON number grammar, recognized as a word. No numeric value is ever constructed.
fn valid_number(raw: &[u8]) -> bool {
    let mut at = 0usize;
    if raw.get(at) == Some(&b'-') {
        at += 1;
    }
    match raw.get(at) {
        Some(b'0') => at += 1,
        Some(b'1'..=b'9') => {
            at += 1;
            while matches!(raw.get(at), Some(b'0'..=b'9')) {
                at += 1;
            }
        }
        _ => return false,
    }
    if raw.get(at) == Some(&b'.') {
        at += 1;
        let from = at;
        while matches!(raw.get(at), Some(b'0'..=b'9')) {
            at += 1;
        }
        if at == from {
            return false;
        }
    }
    if matches!(raw.get(at), Some(b'e' | b'E')) {
        at += 1;
        if matches!(raw.get(at), Some(b'+' | b'-')) {
            at += 1;
        }
        let from = at;
        while matches!(raw.get(at), Some(b'0'..=b'9')) {
            at += 1;
        }
        if at == from {
            return false;
        }
    }
    at == raw.len()
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

#[cfg(test)]
mod tests {
    use super::parse_record;

    #[test]
    fn exact_tree_normalizes_space_but_not_occurrence() {
        let left = parse_record(br#"{"a":[1,"x"],"b":"\u0078"}"#).unwrap();
        let right = parse_record(br#" { "a" : [ 1 , "x" ] , "b" : "x" } "#).unwrap();
        assert_eq!(left.root_digest, right.root_digest);
        assert_eq!(left.nodes.len(), right.nodes.len());
        assert_eq!(left.scalar_nodes.len(), 3);
    }

    #[test]
    fn a_number_is_checked_as_a_word_and_never_cast() {
        assert!(parse_record(br#"[-12,0,3.5,8e-2]"#).is_ok());
        assert!(parse_record(br#"[01]"#).is_err());
        assert!(parse_record(br#"[1.]"#).is_err());
    }
}

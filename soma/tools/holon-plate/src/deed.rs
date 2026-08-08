//! The deed wire — one further deed, presented at a re-lit body's mouth.
//!
//! A deed is exact octets. There is no text parser, no JSON, and no inferred field: a deed that
//! does not decode is refused rather than partially applied.
//!
//! Every deed carries the tag of the schema it is addressed to, so a deed written for a training
//! ecology cannot be presented to a live current body. That is the same typed refusal the plate
//! head enforces, at the other mouth.
//!
//! ```text
//!   0   4   magic         b"HDED"
//!   4   4   schema_tag    the schema this deed is addressed to
//!   8   4   deed_version  u32 = 1
//!   12  ..  schema body   see each schema's `deed_shape()`
//! ```

use crate::plate::SchemaTag;

pub const DEED_MAGIC: [u8; 4] = *b"HDED";
pub const DEED_VERSION: u32 = 1;
pub const DEED_HEAD_OCTETS: usize = 12;

/// Open a deed head, returning the body octets. Refuses a deed addressed elsewhere.
pub fn open_deed<'a>(deed: &'a [u8], expected: SchemaTag) -> Result<Cursor<'a>, String> {
    if deed.len() < DEED_HEAD_OCTETS {
        return Err(format!(
            "{} octets cannot be a deed; the deed head alone is {DEED_HEAD_OCTETS}",
            deed.len()
        ));
    }
    if deed[0..4] != DEED_MAGIC {
        return Err("not a deed; octets 0..4 do not open `HDED`".to_owned());
    }
    let tag_octets: [u8; 4] = deed[4..8].try_into().expect("four");
    let tag = SchemaTag::new(tag_octets)
        .ok_or_else(|| "the deed's schema tag is malformed".to_owned())?;
    if tag != expected {
        return Err(format!(
            "this deed is addressed to schema {tag}; the re-lit body is {expected}. \
             A deed is not re-addressed by guessing."
        ));
    }
    let version = u32::from_le_bytes(deed[8..12].try_into().expect("four"));
    if version != DEED_VERSION {
        return Err(format!(
            "deed wire version {version} is not held; this reader holds {DEED_VERSION}"
        ));
    }
    Ok(Cursor::new(&deed[DEED_HEAD_OCTETS..]))
}

/// Start a deed body for one schema.
pub fn deed_head(tag: SchemaTag) -> Vec<u8> {
    let mut octets = Vec::new();
    octets.extend_from_slice(&DEED_MAGIC);
    octets.extend_from_slice(&tag.octets());
    octets.extend_from_slice(&DEED_VERSION.to_le_bytes());
    octets
}

/// Append one length-prefixed octet run.
pub fn put_bytes(octets: &mut Vec<u8>, run: &[u8]) {
    octets.extend_from_slice(&(run.len() as u64).to_le_bytes());
    octets.extend_from_slice(run);
}

/// Append one exact little-endian `u64`.
pub fn put_u64(octets: &mut Vec<u8>, value: u64) {
    octets.extend_from_slice(&value.to_le_bytes());
}

/// Append one exact little-endian `i64`, two's complement.
pub fn put_i64(octets: &mut Vec<u8>, value: i64) {
    octets.extend_from_slice(&value.to_le_bytes());
}

/// An exact reader over a deed body. Every take is bounds-checked and the tail must be consumed.
pub struct Cursor<'a> {
    octets: &'a [u8],
    at: usize,
}

impl<'a> Cursor<'a> {
    pub fn new(octets: &'a [u8]) -> Self {
        Self { octets, at: 0 }
    }

    pub fn take(&mut self, extent: usize) -> Result<&'a [u8], String> {
        let end = self
            .at
            .checked_add(extent)
            .filter(|end| *end <= self.octets.len())
            .ok_or_else(|| {
                format!(
                    "the deed declares {extent} octets with {} remaining",
                    self.octets.len() - self.at
                )
            })?;
        let taken = &self.octets[self.at..end];
        self.at = end;
        Ok(taken)
    }

    pub fn u64(&mut self) -> Result<u64, String> {
        let row = self.take(8)?;
        Ok(u64::from_le_bytes(row.try_into().expect("eight")))
    }

    pub fn i64(&mut self) -> Result<i64, String> {
        let row = self.take(8)?;
        Ok(i64::from_le_bytes(row.try_into().expect("eight")))
    }

    pub fn usize(&mut self) -> Result<usize, String> {
        usize::try_from(self.u64()?)
            .map_err(|_| "a deed extent does not fit this machine's usize".to_owned())
    }

    pub fn bytes(&mut self) -> Result<Vec<u8>, String> {
        let extent = self.usize()?;
        Ok(self.take(extent)?.to_vec())
    }

    pub fn utf8(&mut self, what: &str) -> Result<String, String> {
        String::from_utf8(self.bytes()?).map_err(|_| format!("the deed's {what} is not UTF-8"))
    }

    pub fn finish(&self) -> Result<(), String> {
        if self.at == self.octets.len() {
            Ok(())
        } else {
            Err(format!(
                "the deed carries {} trailing octets after its last declared field",
                self.octets.len() - self.at
            ))
        }
    }
}

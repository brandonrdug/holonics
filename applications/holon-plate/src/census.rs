//! The census — the plate's second frame.
//!
//! A census is the **declared shape** of the form a plate holds: a canonical, strictly increasing
//! table of ASCII field names against exact `u64` values. It is written by the depositor from the
//! body it deposited, and it is recomputed on resume from the body that was re-lit. The two must
//! agree field for field.
//!
//! This is not a summary and it is not a receipt. `CLAUDE.md` §0: *"An invariant is only visible
//! across two frames."* A digest proves that octets did not move; it cannot prove that the octets
//! are the body the header says they are, because a forger who recomputes the digest satisfies it.
//! The census is the second frame, and every field in it is derived from the mounted body rather
//! than read out of the file.
//!
//! A census value may never be a floating point number, a ratio, a score, or a rate. It is an
//! exact count or an exact ordinal of the mounted structure, and nothing else.

use std::fmt;

/// The widest name a census field may carry.
pub const MAXIMUM_NAME_OCTETS: usize = 64;

/// One census: canonical, strictly increasing by name, exact `u64` values.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Census(Vec<(String, u64)>);

impl Census {
    /// Found a census from rows in any order. Refuses a malformed or repeated name; the stored
    /// order is always ascending by name so that two censuses of the same body are byte-identical
    /// regardless of how the schema listed them.
    pub fn found<N: Into<String>>(
        rows: impl IntoIterator<Item = (N, u64)>,
    ) -> Result<Self, CensusRefusal> {
        let mut rows: Vec<(String, u64)> = rows
            .into_iter()
            .map(|(name, value)| (name.into(), value))
            .collect();
        for (name, _) in &rows {
            check_name(name)?;
        }
        rows.sort_by(|left, right| left.0.cmp(&right.0));
        for pair in rows.windows(2) {
            if pair[0].0 == pair[1].0 {
                return Err(CensusRefusal::RepeatedName {
                    name: pair[0].0.clone(),
                });
            }
        }
        Ok(Self(rows))
    }

    pub fn rows(&self) -> &[(String, u64)] {
        &self.0
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn value(&self, name: &str) -> Option<u64> {
        self.0
            .iter()
            .find(|(field, _)| field == name)
            .map(|(_, value)| *value)
    }

    /// The exact wire. Length-prefixed names, little-endian values, ascending order.
    pub fn encode(&self) -> Vec<u8> {
        let mut octets = Vec::new();
        octets.extend_from_slice(&(self.0.len() as u64).to_le_bytes());
        for (name, value) in &self.0 {
            octets.extend_from_slice(&(name.len() as u64).to_le_bytes());
            octets.extend_from_slice(name.as_bytes());
            octets.extend_from_slice(&value.to_le_bytes());
        }
        octets
    }

    /// Reopen one census wire. Trailing material, a non-ascending name, a repeated name, or a
    /// malformed name each refuse; nothing is inferred and nothing is reordered on the way in.
    pub fn decode(octets: &[u8]) -> Result<Self, CensusRefusal> {
        let mut cursor = Cursor::new(octets);
        let entries =
            usize::try_from(cursor.u64()?).map_err(|_| CensusRefusal::ExtentOverruns {
                field: "entries",
                declared: u64::MAX,
                remaining: 0,
            })?;
        let mut rows: Vec<(String, u64)> = Vec::new();
        for _ in 0..entries {
            let name_octets = cursor.u64()?;
            if name_octets == 0 || name_octets > MAXIMUM_NAME_OCTETS as u64 {
                return Err(CensusRefusal::NameExtent {
                    declared: name_octets,
                });
            }
            let name = String::from_utf8(cursor.take(name_octets as usize)?.to_vec())
                .map_err(|_| CensusRefusal::NameNotAscii)?;
            check_name(&name)?;
            let value = cursor.u64()?;
            if let Some((previous, _)) = rows.last() {
                if previous.as_str() >= name.as_str() {
                    return Err(CensusRefusal::NotAscending {
                        previous: previous.clone(),
                        found: name,
                    });
                }
            }
            rows.push((name, value));
        }
        if !cursor.is_finished() {
            return Err(CensusRefusal::TrailingOctets {
                octets: cursor.remaining(),
            });
        }
        Ok(Self(rows))
    }

    /// The one comparison the census exists for: does the declaration agree with the body?
    ///
    /// Returns the first disagreement in ascending field order. Both directions are named — a
    /// declared field the body does not carry, and a body field the plate never declared — so a
    /// plate cannot pass by declaring less than it holds.
    pub fn first_disagreement(&self, relit: &Self) -> Option<CensusDisagreement> {
        for (field, declared) in &self.0 {
            match relit.value(field) {
                None => {
                    return Some(CensusDisagreement::FieldUnheld {
                        field: field.clone(),
                    })
                }
                Some(found) if found != *declared => {
                    return Some(CensusDisagreement::Drift {
                        field: field.clone(),
                        declared: *declared,
                        relit: found,
                    })
                }
                Some(_) => {}
            }
        }
        for (field, _) in &relit.0 {
            if self.value(field).is_none() {
                return Some(CensusDisagreement::FieldUndeclared {
                    field: field.clone(),
                });
            }
        }
        None
    }

    /// One line, `name=value` in ascending order, for a terminal.
    pub fn render(&self) -> String {
        self.0
            .iter()
            .map(|(name, value)| format!("{name}={value}"))
            .collect::<Vec<_>>()
            .join(" ")
    }
}

/// A named disagreement between the plate's declaration and the re-lit body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CensusDisagreement {
    Drift {
        field: String,
        declared: u64,
        relit: u64,
    },
    FieldUnheld {
        field: String,
    },
    FieldUndeclared {
        field: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CensusRefusal {
    NameExtent {
        declared: u64,
    },
    NameNotAscii,
    NameMalformed {
        name: String,
    },
    RepeatedName {
        name: String,
    },
    NotAscending {
        previous: String,
        found: String,
    },
    ExtentOverruns {
        field: &'static str,
        declared: u64,
        remaining: u64,
    },
    TrailingOctets {
        octets: usize,
    },
}

impl fmt::Display for CensusRefusal {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NameExtent { declared } => write!(
                out,
                "a census field name declares {declared} octets; the held range is 1..={MAXIMUM_NAME_OCTETS}"
            ),
            Self::NameNotAscii => write!(out, "a census field name is not ASCII"),
            Self::NameMalformed { name } => write!(
                out,
                "the census field name `{name}` is malformed; names are 1..={MAXIMUM_NAME_OCTETS} \
                 octets of [a-z0-9_]"
            ),
            Self::RepeatedName { name } => {
                write!(out, "the census repeats the field `{name}`")
            }
            Self::NotAscending { previous, found } => write!(
                out,
                "the census is not canonical: `{found}` follows `{previous}`, which does not ascend"
            ),
            Self::ExtentOverruns {
                field,
                declared,
                remaining,
            } => write!(
                out,
                "the census field `{field}` declares {declared} octets with {remaining} remaining"
            ),
            Self::TrailingOctets { octets } => write!(
                out,
                "the census carries {octets} trailing octets after its last declared field"
            ),
        }
    }
}

impl std::error::Error for CensusRefusal {}

fn check_name(name: &str) -> Result<(), CensusRefusal> {
    if name.is_empty()
        || name.len() > MAXIMUM_NAME_OCTETS
        || !name
            .bytes()
            .all(|octet| octet.is_ascii_lowercase() || octet.is_ascii_digit() || octet == b'_')
    {
        return Err(CensusRefusal::NameMalformed {
            name: name.to_owned(),
        });
    }
    Ok(())
}

struct Cursor<'a> {
    octets: &'a [u8],
    at: usize,
}

impl<'a> Cursor<'a> {
    fn new(octets: &'a [u8]) -> Self {
        Self { octets, at: 0 }
    }

    fn take(&mut self, extent: usize) -> Result<&'a [u8], CensusRefusal> {
        let end = self
            .at
            .checked_add(extent)
            .filter(|end| *end <= self.octets.len())
            .ok_or(CensusRefusal::ExtentOverruns {
                field: "row",
                declared: extent as u64,
                remaining: (self.octets.len() - self.at) as u64,
            })?;
        let taken = &self.octets[self.at..end];
        self.at = end;
        Ok(taken)
    }

    fn u64(&mut self) -> Result<u64, CensusRefusal> {
        let row = self.take(8)?;
        Ok(u64::from_le_bytes([
            row[0], row[1], row[2], row[3], row[4], row[5], row[6], row[7],
        ]))
    }

    fn is_finished(&self) -> bool {
        self.at == self.octets.len()
    }

    fn remaining(&self) -> usize {
        self.octets.len() - self.at
    }
}

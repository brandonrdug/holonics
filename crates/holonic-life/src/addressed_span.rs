//! Exact addressed memory spans whose storage cuts do not become causal cuts.
//!
//! A fragment is exterior carriage.  Its only admitted join is equality between the next source
//! coordinate and the fragment's `from` boundary.  Successful closure moves the one reconstructed
//! body onward; refusal retains both the assembly and the rejected fragment.  No filename, codec,
//! media family, callback ordinal, or semantic face participates in the law.

use serde::Serialize;
use sha2::{Digest, Sha256};

pub const ADDRESSED_MEMORY_SPAN_SCHEMA: &str = "soma-life.addressed-memory-span.v1";

#[derive(Debug, PartialEq, Eq)]
pub struct MemorySpanFragment {
    pub occurrence: String,
    pub from: u64,
    pub body: Vec<u8>,
}

impl MemorySpanFragment {
    pub fn new(occurrence: impl Into<String>, from: u64, body: Vec<u8>) -> Self {
        Self {
            occurrence: occurrence.into(),
            from,
            body,
        }
    }

    pub fn to(&self) -> Result<u64, AddressedSpanDefect> {
        self.from
            .checked_add(u64::try_from(self.body.len()).map_err(|_| AddressedSpanDefect::Extent)?)
            .ok_or(AddressedSpanDefect::Extent)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MemorySpanJoin {
    pub predecessor_from: u64,
    pub predecessor_to: u64,
    pub successor_from: u64,
    pub successor_to: u64,
    pub joining_coordinate: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MemorySpanFragmentReceipt {
    pub from: u64,
    pub to: u64,
    pub source_octets_presented: u64,
    pub retained_join_population: u64,
}

/// The one cold reconstruction fibre while its addressed source span is still open.
///
/// This type is intentionally not `Clone`: branch inspection cannot duplicate the continuing
/// source body.  The body remains exterior to Athena morphology and is moved at closure.
#[derive(Debug)]
pub struct AddressedMemorySpan {
    occurrence: String,
    expected_octets: u64,
    expected_sha256: String,
    body: Vec<u8>,
    joins: Vec<MemorySpanJoin>,
    fragment_population: u64,
    largest_fragment_octets: u64,
}

impl AddressedMemorySpan {
    pub fn found(
        occurrence: impl Into<String>,
        expected_octets: u64,
        expected_sha256: impl Into<String>,
    ) -> Result<Self, AddressedSpanDefect> {
        let occurrence = occurrence.into();
        let expected_sha256 = expected_sha256.into();
        if occurrence.is_empty() {
            return Err(AddressedSpanDefect::Occurrence);
        }
        if expected_octets == 0 {
            return Err(AddressedSpanDefect::EmptySpan);
        }
        if expected_sha256.len() != 64
            || !expected_sha256
                .bytes()
                .all(|octet| octet.is_ascii_hexdigit())
        {
            return Err(AddressedSpanDefect::SourceIdentity);
        }
        let capacity = usize::try_from(expected_octets).map_err(|_| AddressedSpanDefect::Extent)?;
        Ok(Self {
            occurrence,
            expected_octets,
            expected_sha256,
            body: Vec::with_capacity(capacity),
            joins: Vec::new(),
            fragment_population: 0,
            largest_fragment_octets: 0,
        })
    }

    pub fn occurrence(&self) -> &str {
        &self.occurrence
    }

    pub fn next_coordinate(&self) -> u64 {
        self.body.len() as u64
    }

    pub fn expected_octets(&self) -> u64 {
        self.expected_octets
    }

    pub fn reconstructed_octets(&self) -> u64 {
        self.next_coordinate()
    }

    pub fn fragment_population(&self) -> u64 {
        self.fragment_population
    }

    pub fn largest_fragment_octets(&self) -> u64 {
        self.largest_fragment_octets
    }

    pub fn joins(&self) -> &[MemorySpanJoin] {
        &self.joins
    }

    /// Admit one consecutive source fragment.  Every validation precedes mutation, so a refusal
    /// returns the unchanged assembly and the complete rejected fragment.
    pub fn admit(
        mut self,
        fragment: MemorySpanFragment,
    ) -> Result<(Self, MemorySpanFragmentReceipt), AddressedSpanRefusal> {
        let to = match fragment.to() {
            Ok(to) => to,
            Err(defect) => return Err(AddressedSpanRefusal::new(defect, self, Some(fragment))),
        };
        let expected_from = self.next_coordinate();
        let defect = if fragment.occurrence != self.occurrence {
            Some(AddressedSpanDefect::ForeignOccurrence {
                expected: self.occurrence.clone(),
                supplied: fragment.occurrence.clone(),
            })
        } else if fragment.body.is_empty() {
            Some(AddressedSpanDefect::EmptyFragment { at: fragment.from })
        } else if fragment.from != expected_from {
            Some(AddressedSpanDefect::Nonconsecutive {
                expected_from,
                supplied_from: fragment.from,
            })
        } else if to > self.expected_octets {
            Some(AddressedSpanDefect::BeyondExpectedBoundary {
                expected_to: self.expected_octets,
                supplied_to: to,
            })
        } else {
            None
        };
        if let Some(defect) = defect {
            return Err(AddressedSpanRefusal::new(defect, self, Some(fragment)));
        }

        if expected_from > 0 {
            let predecessor_from = self.joins.last().map_or(0, |join| join.successor_from);
            self.joins.push(MemorySpanJoin {
                predecessor_from,
                predecessor_to: expected_from,
                successor_from: fragment.from,
                successor_to: to,
                joining_coordinate: expected_from,
            });
        }
        let fragment_octets = to - fragment.from;
        self.body.extend(fragment.body);
        self.fragment_population += 1;
        self.largest_fragment_octets = self.largest_fragment_octets.max(fragment_octets);
        let receipt = MemorySpanFragmentReceipt {
            from: fragment.from,
            to,
            source_octets_presented: self.next_coordinate(),
            retained_join_population: self.joins.len() as u64,
        };
        Ok((self, receipt))
    }

    pub fn close(self) -> Result<CompleteAddressedMemorySpan, AddressedSpanRefusal> {
        if self.next_coordinate() != self.expected_octets {
            let defect = AddressedSpanDefect::OpenGap {
                missing_from: self.next_coordinate(),
                expected_to: self.expected_octets,
            };
            return Err(AddressedSpanRefusal::new(defect, self, None));
        }
        let source_sha256 = hex(Sha256::digest(&self.body));
        if source_sha256 != self.expected_sha256 {
            let expected = self.expected_sha256.clone();
            return Err(AddressedSpanRefusal::new(
                AddressedSpanDefect::SourceIdentityMismatch {
                    expected,
                    returned: source_sha256,
                },
                self,
                None,
            ));
        }
        Ok(CompleteAddressedMemorySpan {
            schema: ADDRESSED_MEMORY_SPAN_SCHEMA.to_owned(),
            occurrence: self.occurrence,
            source_sha256,
            source_octets: self.expected_octets,
            body: self.body,
            joins: self.joins,
            fragment_population: self.fragment_population,
            largest_fragment_octets: self.largest_fragment_octets,
        })
    }
}

/// Closed source body and its complete addressed join fibre.  This is also deliberately not
/// `Clone`; a downstream codec consumes or borrows the one body.
#[derive(Debug)]
pub struct CompleteAddressedMemorySpan {
    pub schema: String,
    pub occurrence: String,
    pub source_sha256: String,
    pub source_octets: u64,
    pub body: Vec<u8>,
    pub joins: Vec<MemorySpanJoin>,
    pub fragment_population: u64,
    pub largest_fragment_octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "defect", rename_all = "kebab-case")]
pub enum AddressedSpanDefect {
    Occurrence,
    EmptySpan,
    SourceIdentity,
    Extent,
    ForeignOccurrence {
        expected: String,
        supplied: String,
    },
    EmptyFragment {
        at: u64,
    },
    Nonconsecutive {
        expected_from: u64,
        supplied_from: u64,
    },
    BeyondExpectedBoundary {
        expected_to: u64,
        supplied_to: u64,
    },
    OpenGap {
        missing_from: u64,
        expected_to: u64,
    },
    SourceIdentityMismatch {
        expected: String,
        returned: String,
    },
}

#[derive(Debug)]
pub struct AddressedSpanRefusal {
    pub defect: AddressedSpanDefect,
    pub assembly: AddressedMemorySpan,
    pub rejected_fragment: Option<MemorySpanFragment>,
}

impl AddressedSpanRefusal {
    fn new(
        defect: AddressedSpanDefect,
        assembly: AddressedMemorySpan,
        rejected_fragment: Option<MemorySpanFragment>,
    ) -> Self {
        Self {
            defect,
            assembly,
            rejected_fragment,
        }
    }
}

fn hex(bytes: impl AsRef<[u8]>) -> String {
    bytes
        .as_ref()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn digest(body: &[u8]) -> String {
        hex(Sha256::digest(body))
    }

    fn assemble(body: &[u8], cuts: &[usize]) -> CompleteAddressedMemorySpan {
        let mut span = AddressedMemorySpan::found("span/test", body.len() as u64, digest(body))
            .expect("exact span");
        let mut from = 0usize;
        for &to in cuts {
            (span, _) = span
                .admit(MemorySpanFragment::new(
                    "span/test",
                    from as u64,
                    body[from..to].to_vec(),
                ))
                .expect("consecutive fragment");
            from = to;
        }
        span.close().expect("complete span")
    }

    #[test]
    fn resegmentation_preserves_the_complete_source_body() {
        let body = b"storage cuts do not cut the caused source span";
        let whole = assemble(body, &[body.len()]);
        let fragmented = assemble(body, &[1, 2, 9, 17, body.len()]);
        assert_eq!(whole.body, fragmented.body);
        assert_eq!(whole.source_sha256, fragmented.source_sha256);
        assert_eq!(whole.source_octets, fragmented.source_octets);
        assert_eq!(whole.joins.len(), 0);
        assert_eq!(fragmented.joins.len(), 4);
    }

    #[test]
    fn dropout_and_reorder_return_the_first_exact_coordinate() {
        let body = b"addressed";
        let mut span = AddressedMemorySpan::found("span/test", body.len() as u64, digest(body))
            .expect("exact span");
        (span, _) = span
            .admit(MemorySpanFragment::new("span/test", 0, body[..3].to_vec()))
            .expect("prefix");
        let refused = span
            .admit(MemorySpanFragment::new("span/test", 4, body[4..].to_vec()))
            .expect_err("one missing coordinate must refuse");
        assert_eq!(
            refused.defect,
            AddressedSpanDefect::Nonconsecutive {
                expected_from: 3,
                supplied_from: 4,
            }
        );
        assert_eq!(refused.assembly.next_coordinate(), 3);
        assert_eq!(refused.rejected_fragment.unwrap().from, 4);
    }
}

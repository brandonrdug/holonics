//! Exact finite conditional-section release (Refs #73 #148 #386).
//!
//! [derived; agent-inferred consuming join] A caller supplies the actual native class oracle at
//! one immutable query opening, conditioned on the entire hypothesized prefix. The chain rule is
//! `P(x_0..x_(m-1)) = product_j P(x_j | x_<j)`: this is not a product of marginal faces. If a
//! prefix mass is enclosed by `[L,U]`, every extension has mass at most U because conditional
//! probabilities lie in [0,1]. Thus a complete candidate's lower bound strictly above every
//! other complete candidate and unresolved prefix upper bound certifies its unique dominance
//! over the whole finite declared section. The search expands the largest upper bound first.
//! It discards only exact-zero branches, never a beam, and never renormalizes the candidate family.
//!
//! The oracle must return the same conditional expression at a prefix and precision, without
//! publishing ingestion/deposition or changing the original query opening. The Alpha caller
//! realizes a hypothesis on a fresh query fork and reads its retained R/tree scored face; this
//! module cannot authenticate an arbitrary closure's provenance. All exact producing operands
//! remain the oracle owner's responsibility. One prefix is queried once, so the retained frontier
//! is a bounded unique-prefix cache within this call, not native retention or a source archive.
//!
//! No pump or Floquet bank is created. This is a finite causal-model joint-section receiver,
//! not bank joint-field dynamics or variable-length reply completion. The caller declares the
//! byte aperture and precision; work exhaustion, native refusal or unresolved dominance returns
//! Incomplete with the whole unresolved family. No EOS, softened margin or enlarged budget is
//! inferred. Only a certified whole section reaches the byte decoder. The formal chain-rule /
//! frontier-bound consuming join remains owed in #62; the tests are finite controls.
//!
//! This reads faces/placement and the finite tower thread of a helical pair receiver; its clock,
//! contacts, cell holonomy and tube belong to the supplied native oracle. The recorded failures
//! of a fixture standing in for capability, arbitrary backoff and marginal picks standing in for
//! whole release are kept separate by this declared finite scope and explicit incomplete return.

use num_traits::{One, Zero};
use thiserror::Error;

use crate::hnn::HnnError;
use crate::ratio::{Rat, algebraic::ExactInterval};

use super::byte_release::{Base4Bytes, ByteBoundary, ByteBoundaryError};

/// Exterior per-call limits. Prefixes count root plus every child considered, including zero
/// branches; oracle calls count actual invocations. Neither limit changes probability or release.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SectionWorkBudget {
    pub max_prefixes: usize,
    pub max_oracle_calls: usize,
}

/// A finite byte receiving aperture and exact oracle reading precision, never an EOS rule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeSectionRequest {
    bytes: usize,
    cells: usize,
    reading_bits: u32,
    budget: SectionWorkBudget,
}

impl NativeSectionRequest {
    pub fn declare(
        bytes: usize,
        reading_bits: u32,
        budget: SectionWorkBudget,
    ) -> Result<Self, NativeSectionError> {
        let cells = bytes
            .checked_mul(4)
            .ok_or(NativeSectionError::InvalidDeclaration)?;
        if bytes == 0
            || reading_bits == 0
            || budget.max_prefixes == 0
            || budget.max_oracle_calls == 0
        {
            return Err(NativeSectionError::InvalidDeclaration);
        }
        Ok(Self {
            bytes,
            cells,
            reading_bits,
            budget,
        })
    }

    pub fn bytes(&self) -> usize {
        self.bytes
    }
    pub fn cells(&self) -> usize {
        self.cells
    }
    pub fn reading_bits(&self) -> u32 {
        self.reading_bits
    }
    pub fn budget(&self) -> SectionWorkBudget {
        self.budget
    }
}

#[derive(Debug, Error)]
pub enum NativeSectionError {
    #[error(
        "a native byte section needs a positive finite byte aperture, precision and work budget"
    )]
    InvalidDeclaration,
    #[error("the native conditional face has {found} classes; the declared byte chart needs four")]
    Alphabet { found: usize },
    #[error(
        "the native conditional face is not an enclosure of a normalized nonnegative probability family"
    )]
    InvalidProbabilities,
    #[error(transparent)]
    ByteBoundary(#[from] ByteBoundaryError),
}

/// One prefix or complete placement and its exact chain-rule mass enclosure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SectionCandidate {
    pub classes: Vec<usize>,
    pub joint_mass: ExactInterval,
}

#[derive(Debug)]
pub enum IncompleteSection {
    /// All nonzero complete candidates are known, but their enclosures do not certify one mode.
    Plural,
    PrefixBudget,
    OracleBudget,
    /// The actual oracle refused this prefix. It remains in the frontier unchanged.
    NativeRefusal {
        prefix: Vec<usize>,
        error: Box<HnnError>,
    },
}

#[derive(Debug)]
pub enum NativeSectionDecision {
    Released {
        classes: Vec<usize>,
        joint_mass: ExactInterval,
        competitor_upper: Rat,
        decoded: ByteBoundary,
    },
    Incomplete {
        reason: IncompleteSection,
        complete_candidates: Vec<SectionCandidate>,
        frontier: Vec<SectionCandidate>,
    },
}

/// Exterior receipt of one finite conditional-section read. Complete candidate lists/frontiers
/// are returned for an incomplete call, never kept in the resident constitution.
#[derive(Debug)]
pub struct NativeSectionRead {
    pub declared_bytes: usize,
    pub declared_cells: usize,
    pub reading_bits: u32,
    pub budget: SectionWorkBudget,
    pub prefixes_considered: usize,
    pub oracle_calls: usize,
    pub decision: NativeSectionDecision,
}

fn admitted(face: &[ExactInterval]) -> Result<(), NativeSectionError> {
    if face.len() != 4 {
        return Err(NativeSectionError::Alphabet { found: face.len() });
    }
    let mut lower = Rat::zero();
    let mut upper = Rat::zero();
    for mass in face {
        if mass.lower < Rat::zero() || mass.upper > Rat::one() || mass.lower > mass.upper {
            return Err(NativeSectionError::InvalidProbabilities);
        }
        lower += &mass.lower;
        upper += &mass.upper;
    }
    if lower > Rat::one() || upper < Rat::one() {
        return Err(NativeSectionError::InvalidProbabilities);
    }
    Ok(())
}

/// Release a whole declared finite byte section only under exact global dominance. The oracle
/// sees every complete hypothesized prior prefix, at the same caller-declared precision. No
/// winning prefix is ever published as output while the remaining section is unresolved.
pub fn release_native_section(
    request: &NativeSectionRequest,
    mut oracle: impl FnMut(&[usize], u32) -> Result<Vec<ExactInterval>, HnnError>,
) -> Result<NativeSectionRead, NativeSectionError> {
    let mut frontier = vec![SectionCandidate {
        classes: Vec::new(),
        joint_mass: ExactInterval::point(Rat::one()),
    }];
    let mut complete: Vec<SectionCandidate> = Vec::new();
    let (mut prefixes, mut calls) = (1usize, 0usize);
    let decision = loop {
        if let Some((best, candidate)) = complete
            .iter()
            .enumerate()
            .max_by(|(_, a), (_, b)| a.joint_mass.lower.cmp(&b.joint_mass.lower))
        {
            let competitor_upper = complete
                .iter()
                .enumerate()
                .filter(|(at, _)| *at != best)
                .map(|(_, other)| &other.joint_mass.upper)
                .chain(frontier.iter().map(|other| &other.joint_mass.upper))
                .max()
                .cloned()
                .unwrap_or_else(Rat::zero);
            if candidate.joint_mass.lower > competitor_upper {
                break NativeSectionDecision::Released {
                    classes: candidate.classes.clone(),
                    joint_mass: candidate.joint_mass.clone(),
                    competitor_upper,
                    decoded: Base4Bytes::decode(&candidate.classes, request.cells)?,
                };
            }
        }
        let incomplete = if frontier.is_empty() {
            Some(IncompleteSection::Plural)
        } else if calls == request.budget.max_oracle_calls {
            Some(IncompleteSection::OracleBudget)
        } else if prefixes
            .checked_add(4)
            .is_none_or(|count| count > request.budget.max_prefixes)
        {
            Some(IncompleteSection::PrefixBudget)
        } else {
            None
        };
        if let Some(reason) = incomplete {
            break NativeSectionDecision::Incomplete {
                reason,
                complete_candidates: complete,
                frontier,
            };
        }
        let best = frontier
            .iter()
            .enumerate()
            .max_by(|(_, a), (_, b)| {
                a.joint_mass
                    .upper
                    .cmp(&b.joint_mass.upper)
                    .then_with(|| b.classes.cmp(&a.classes))
            })
            .map(|(at, _)| at)
            .expect("a frontier prefix exists");
        let prefix = frontier.remove(best);
        calls += 1;
        let conditional = match oracle(&prefix.classes, request.reading_bits) {
            Ok(face) => face,
            Err(error) => {
                let at = prefix.classes.clone();
                frontier.push(prefix);
                break NativeSectionDecision::Incomplete {
                    reason: IncompleteSection::NativeRefusal {
                        prefix: at,
                        error: Box::new(error),
                    },
                    complete_candidates: complete,
                    frontier,
                };
            }
        };
        admitted(&conditional)?;
        prefixes += 4;
        for (class, probability) in conditional.iter().enumerate() {
            let joint_mass = ExactInterval {
                lower: &prefix.joint_mass.lower * &probability.lower,
                upper: &prefix.joint_mass.upper * &probability.upper,
            };
            if joint_mass.upper.is_zero() {
                continue;
            }
            let mut classes = prefix.classes.clone();
            classes.push(class);
            let next = SectionCandidate {
                classes,
                joint_mass,
            };
            if next.classes.len() == request.cells {
                complete.push(next);
            } else {
                frontier.push(next);
            }
        }
    };
    Ok(NativeSectionRead {
        declared_bytes: request.bytes,
        declared_cells: request.cells,
        reading_bits: request.reading_bits,
        budget: request.budget,
        prefixes_considered: prefixes,
        oracle_calls: calls,
        decision,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::{integer, rat};
    use std::collections::BTreeSet;

    fn request(prefixes: usize, calls: usize) -> NativeSectionRequest {
        NativeSectionRequest::declare(
            1,
            32,
            SectionWorkBudget {
                max_prefixes: prefixes,
                max_oracle_calls: calls,
            },
        )
        .unwrap()
    }

    fn points(values: [Rat; 4]) -> Vec<ExactInterval> {
        values.into_iter().map(ExactInterval::point).collect()
    }

    // This finite causal control has mode 1100 (mass 2/5). Marginal/greedy first-cell choice is
    // zero, but each of its two completions has mass 3/10. It is a receiver-law test, not learning.
    fn conditional(prefix: &[usize]) -> Vec<ExactInterval> {
        match prefix {
            [] => points([rat(3, 5), rat(2, 5), integer(0), integer(0)]),
            [0] => points([rat(1, 2), rat(1, 2), integer(0), integer(0)]),
            [1] => points([integer(0), integer(1), integer(0), integer(0)]),
            _ => points([integer(1), integer(0), integer(0), integer(0)]),
        }
    }

    #[test]
    fn joint_conditional_mode_differs_from_the_first_marginal_and_releases_one_whole_byte() {
        let mut seen = BTreeSet::new();
        let read = release_native_section(&request(100, 100), |prefix, bits| {
            assert_eq!(bits, 32);
            assert!(
                seen.insert(prefix.to_vec()),
                "a prefix must be queried once"
            );
            Ok(conditional(prefix))
        })
        .unwrap();
        assert_eq!(seen.len(), read.oracle_calls);
        match read.decision {
            NativeSectionDecision::Released {
                classes,
                joint_mass,
                competitor_upper,
                decoded,
            } => {
                assert_eq!(classes, vec![1, 1, 0, 0]);
                assert_eq!(joint_mass, ExactInterval::point(rat(2, 5)));
                assert_eq!(competitor_upper, rat(3, 10));
                assert_eq!(decoded.bytes, b"P");
            }
            _ => panic!("the exact joint mode must release"),
        }
    }

    #[test]
    fn exact_joint_ties_hold_without_a_byte_or_a_tie_break() {
        let read = release_native_section(&request(100, 100), |prefix, _| {
            Ok(if prefix.is_empty() {
                points([rat(1, 2), rat(1, 2), integer(0), integer(0)])
            } else {
                points([integer(1), integer(0), integer(0), integer(0)])
            })
        })
        .unwrap();
        match read.decision {
            NativeSectionDecision::Incomplete {
                reason: IncompleteSection::Plural,
                complete_candidates,
                frontier,
            } => {
                assert!(frontier.is_empty());
                assert_eq!(complete_candidates.len(), 2);
                assert!(
                    complete_candidates
                        .iter()
                        .all(|candidate| candidate.joint_mass == ExactInterval::point(rat(1, 2)))
                );
            }
            _ => panic!("an exact tie must remain incomplete"),
        }
    }

    #[test]
    fn overlapping_joint_enclosures_remain_plural_at_the_declared_precision() {
        let read = release_native_section(&request(100, 100), |prefix, _| {
            Ok(if prefix.is_empty() {
                vec![
                    ExactInterval {
                        lower: rat(2, 5),
                        upper: rat(3, 5),
                    },
                    ExactInterval {
                        lower: rat(2, 5),
                        upper: rat(3, 5),
                    },
                    ExactInterval::point(integer(0)),
                    ExactInterval::point(integer(0)),
                ]
            } else {
                points([integer(1), integer(0), integer(0), integer(0)])
            })
        })
        .unwrap();
        assert!(matches!(
            read.decision,
            NativeSectionDecision::Incomplete {
                reason: IncompleteSection::Plural,
                ..
            }
        ));
    }

    #[test]
    fn every_work_stop_keeps_all_unresolved_nonzero_branches() {
        for (limits, prefix_stop) in [(request(5, 100), true), (request(100, 1), false)] {
            let read =
                release_native_section(&limits, |prefix, _| Ok(conditional(prefix))).unwrap();
            assert_eq!(read.oracle_calls, 1);
            match read.decision {
                NativeSectionDecision::Incomplete {
                    reason,
                    frontier,
                    complete_candidates,
                } => {
                    assert_eq!(frontier.len(), 2);
                    assert!(complete_candidates.is_empty());
                    assert!(if prefix_stop {
                        matches!(reason, IncompleteSection::PrefixBudget)
                    } else {
                        matches!(reason, IncompleteSection::OracleBudget)
                    });
                }
                _ => panic!("a work stop cannot release a prefix"),
            }
        }
    }

    #[test]
    fn native_refusal_keeps_the_refused_prefix_and_its_exact_bound() {
        let read = release_native_section(&request(100, 100), |_, _| {
            Err(HnnError::NonpositiveDeclaration)
        })
        .unwrap();
        assert_eq!(read.oracle_calls, 1);
        match read.decision {
            NativeSectionDecision::Incomplete {
                reason: IncompleteSection::NativeRefusal { prefix, .. },
                frontier,
                ..
            } => {
                assert!(prefix.is_empty());
                assert_eq!(
                    frontier,
                    vec![SectionCandidate {
                        classes: vec![],
                        joint_mass: ExactInterval::point(integer(1))
                    }]
                );
            }
            _ => panic!("the actual refusal must stay incomplete"),
        }
    }

    #[test]
    fn nonnormalized_conditional_faces_are_refused_without_renormalization() {
        assert!(matches!(
            release_native_section(&request(100, 100), |_, _| Ok(points(std::array::from_fn(
                |_| integer(1)
            )))),
            Err(NativeSectionError::InvalidProbabilities)
        ));
        for invalid in [
            ExactInterval {
                lower: rat(-1, 4),
                upper: integer(1),
            },
            ExactInterval {
                lower: integer(0),
                upper: rat(5, 4),
            },
            ExactInterval {
                lower: rat(3, 4),
                upper: rat(1, 4),
            },
        ] {
            assert!(matches!(
                admitted(&vec![invalid; 4]),
                Err(NativeSectionError::InvalidProbabilities)
            ));
        }
    }
}

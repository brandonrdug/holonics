//! **The contact reaction: one law, one resident section** (plan phase 11).
//!
//! [definition] An actual current `h` meets an affine family `F = a + V` returned by the
//! constitutive relation, through the declared unit-admittance metric. With `P` the orthogonal
//! projection onto `V`:
//!
//! ```text
//! h' = P h + (I − P) a      successor (the realized reaction, never a point cast of F)
//! n_in  = (I − P) a         incoming normal (the family's normal face)
//! n_ret = (I − P) h         returned normal (the normal face the current gives back)
//! h' − h = n_in − n_ret     difference
//! ‖h‖² + ‖n_in‖² = ‖h'‖² + ‖n_ret‖²   the exchange is lossless
//! ```
//!
//! (`Holon/AffineContact.lean::contact_difference`, `contact_lossless`, `contact_fixes_family`).
//! An empty family leaves `h` unchanged and reports `OutsideRepresentedRelation`. The resident
//! section is `5c + 2` words `[h | h' | n_in | n_ret | h' − h | den | status]`; the kernels
//! (`record_condition_contact`, `record_prepared_condition_contact`) own it unchanged.
//!
//! [established-bounded; source-inspected] Before phase 11 this section had three wrappers with
//! their own block views and decoders (`ResidentConditionContact`, `ResidentAffineContact`, the
//! wave source contact) and two readings (`AffineContactReading`, `AffineContactReading`). They
//! are now this one reaction and the one [`AffineContactReading`]; the condition current is the
//! successor block of its latest reaction.
use super::*;

/// The one reaction section of a contact, shared by every consumer of that reaction.
#[derive(Clone)]
pub struct ResidentContactReaction<'c> {
    surface: &'c ResidentSurface<'c>,
    section: Rc<ResidentSection<'c>>,
    width: usize,
    metric: ConditionContactMetric,
}

/// The reaction's blocks in its resident section, in order.
pub(crate) mod block {
    pub(crate) const PREDECESSOR: usize = 0;
    pub(crate) const SUCCESSOR: usize = 1;
    pub(crate) const INCOMING_NORMAL: usize = 2;
    pub(crate) const RETURNED_NORMAL: usize = 3;
    pub(crate) const DIFFERENCE: usize = 4;
}

impl<'c> ResidentContactReaction<'c> {
    pub(crate) fn new(
        surface: &'c ResidentSurface<'c>,
        section: Rc<ResidentSection<'c>>,
        width: usize,
        metric: ConditionContactMetric,
    ) -> Self {
        Self {
            surface,
            section,
            width,
            metric,
        }
    }
    /// Real coordinates of the reacting current.
    pub fn width(&self) -> usize {
        self.width
    }
    pub fn metric(&self) -> ConditionContactMetric {
        self.metric
    }
    pub(crate) fn surface(&self) -> &'c ResidentSurface<'c> {
        self.surface
    }
    pub(crate) fn section(&self) -> &Rc<ResidentSection<'c>> {
        &self.section
    }
    pub(crate) fn same_section(&self, section: &Rc<ResidentSection<'c>>) -> bool {
        Rc::ptr_eq(&self.section, section)
    }
    /// One block as an exact current. A guarded block is admitted by a point consumer only when
    /// the contact's status is `Compatible` (checked on device from the status word).
    pub(crate) fn block(&self, block: usize, guarded: bool) -> ResidentConstitutiveCurrent<'_, 'c> {
        debug_assert!(block <= block::DIFFERENCE);
        let c = self.width;
        ResidentConstitutiveCurrent {
            section: &self.section,
            offset: block * c,
            width: c,
            denominator: Some(5 * c),
            disposition: guarded.then_some(5 * c + 1),
        }
    }
    /// The one decoder of the reaction section. `contact` is the standing's contact count when
    /// the reaction was published to a condition current.
    pub fn inspect(
        &self,
        relation_cut: u64,
        contact: Option<u64>,
    ) -> Result<AffineContactReading, ConstitutiveFibreError> {
        let words = self.surface.read_out(&self.section)?;
        let c = self.width;
        if words.len() != 5 * c + 2 || words[5 * c].0 <= 0 || words.iter().any(|(lo, hi)| lo != hi)
        {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let row = |at: usize| {
            words[at..at + c]
                .iter()
                .map(|v| Rat::new(v.0.into(), words[5 * c].0.into()))
                .collect()
        };
        Ok(AffineContactReading {
            contact,
            relation_cut,
            metric: self.metric,
            status: match words[5 * c + 1].0 {
                0 => ConditionContactStatus::Compatible,
                1 => ConditionContactStatus::OutsideRepresentedRelation,
                _ => return Err(ConstitutiveFibreError::Uncertain),
            },
            predecessor: row(0),
            successor: row(c),
            incoming_normal: row(2 * c),
            returned_normal: row(3 * c),
            difference: row(4 * c),
        })
    }
}

/// The one reading of a contact reaction (formerly also `ConditionContactReading`, which added
/// only the standing's contact count). `contact` is omitted from the wire when absent, so both
/// former JSON faces are unchanged.
#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct AffineContactReading {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub contact: Option<u64>,
    pub relation_cut: u64,
    pub metric: ConditionContactMetric,
    pub status: ConditionContactStatus,
    pub predecessor: Vec<Rat>,
    pub successor: Vec<Rat>,
    pub incoming_normal: Vec<Rat>,
    pub returned_normal: Vec<Rat>,
    pub difference: Vec<Rat>,
}

impl AffineContactReading {
    /// `‖h‖² + ‖n_in‖²`, the power the contact receives (`Holon/AffineContact.lean::contact_lossless`).
    pub fn incoming_power(&self) -> Rat {
        square(&self.predecessor) + square(&self.incoming_normal)
    }
    /// `‖h'‖² + ‖n_ret‖²`, the power the contact returns.
    pub fn returned_power(&self) -> Rat {
        square(&self.successor) + square(&self.returned_normal)
    }
    /// The law's two exact faces: `h' − h = n_in − n_ret` and the lossless exchange.
    pub fn is_lossless_exchange(&self) -> bool {
        let difference_holds = (0..self.predecessor.len()).all(|j| {
            self.successor[j].clone() - &self.predecessor[j] == self.difference[j]
                && self.incoming_normal[j].clone() - &self.returned_normal[j] == self.difference[j]
        });
        difference_holds && self.incoming_power() == self.returned_power()
    }
}

fn square(values: &[Rat]) -> Rat {
    values.iter().map(|v| v * v).sum()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The pre-phase-11 condition reading, kept here only to check the wire is unchanged.
    #[derive(Serialize)]
    struct FormerConditionContactReading {
        contact: u64,
        relation_cut: u64,
        metric: ConditionContactMetric,
        status: ConditionContactStatus,
        predecessor: Vec<Rat>,
        successor: Vec<Rat>,
        incoming_normal: Vec<Rat>,
        returned_normal: Vec<Rat>,
        difference: Vec<Rat>,
    }
    /// The pre-phase-11 affine reading.
    #[derive(Serialize)]
    struct FormerAffineContactReading {
        relation_cut: u64,
        metric: ConditionContactMetric,
        status: ConditionContactStatus,
        predecessor: Vec<Rat>,
        successor: Vec<Rat>,
        incoming_normal: Vec<Rat>,
        returned_normal: Vec<Rat>,
        difference: Vec<Rat>,
    }
    fn rats(v: &[i64], d: i64) -> Vec<Rat> {
        v.iter().map(|n| Rat::new((*n).into(), d.into())).collect()
    }

    /// The device witness of `oblique_family_preserves_tangent_and_returns_normal_current`
    /// (h = (7, 4) against the family c₁ + c₂ = 2): both former JSON faces are byte-identical
    /// and the reading satisfies the lossless contact law exactly.
    #[test]
    fn one_contact_reading_keeps_both_former_wires_and_the_lossless_law() {
        let reading = |contact| AffineContactReading {
            contact,
            relation_cut: 6,
            metric: ConditionContactMetric::UnitAdmittanceRealification,
            status: ConditionContactStatus::Compatible,
            predecessor: rats(&[7, 4], 1),
            successor: rats(&[5, -1], 2),
            incoming_normal: rats(&[1, 1], 1),
            returned_normal: rats(&[11, 11], 2),
            difference: rats(&[-9, -9], 2),
        };
        let condition = FormerConditionContactReading {
            contact: 1,
            relation_cut: 6,
            metric: ConditionContactMetric::UnitAdmittanceRealification,
            status: ConditionContactStatus::Compatible,
            predecessor: rats(&[7, 4], 1),
            successor: rats(&[5, -1], 2),
            incoming_normal: rats(&[1, 1], 1),
            returned_normal: rats(&[11, 11], 2),
            difference: rats(&[-9, -9], 2),
        };
        assert_eq!(
            serde_json::to_string(&reading(Some(1))).unwrap(),
            serde_json::to_string(&condition).unwrap()
        );
        let affine = FormerAffineContactReading {
            relation_cut: 6,
            metric: ConditionContactMetric::UnitAdmittanceRealification,
            status: ConditionContactStatus::Compatible,
            predecessor: rats(&[7, 4], 1),
            successor: rats(&[5, -1], 2),
            incoming_normal: rats(&[1, 1], 1),
            returned_normal: rats(&[11, 11], 2),
            difference: rats(&[-9, -9], 2),
        };
        assert_eq!(
            serde_json::to_string(&reading(None)).unwrap(),
            serde_json::to_string(&affine).unwrap()
        );
        let witness = reading(None);
        assert!(witness.is_lossless_exchange());
        assert_eq!(witness.incoming_power(), Rat::from_integer(67.into()));
        let mut broken = reading(None);
        broken.returned_normal = rats(&[5, 5], 1);
        assert!(!broken.is_lossless_exchange());
    }
}

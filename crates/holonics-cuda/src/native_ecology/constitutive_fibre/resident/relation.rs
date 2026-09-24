//! **The constitutive relation as one exact object** (plan phase 11).
//!
//! [definition] The resident constitutive fibre carries one linear relation
//! `R = span{(x_i, y_i)} ⊂ S × T` of the paired currents it received
//! (`Computation/HolonicConstitutiveFibre.lean::pairedCurrentSubmodule`), as positive-pivot
//! echelon rows on the device. Every reading any resident view returns — a point current, a
//! plural family, an outside-domain obstruction, a condition preimage — is **the fibre of that
//! relation over a source**, `R_s = {t | (s, t) ∈ R}`: empty when `s` is outside the source
//! projection, otherwise the translate of the vertical fibre `R_0 = {t | (0, t) ∈ R}` through any
//! member (`Computation/HolonicConstitutiveFibre.lean::vertical_fibre_iff_zero_source_difference`,
//! `sourceSpan_iff_paired_source`). In the core it is the restriction fibre
//! `holonics::restriction::AffineFibre` (`Holon/Restriction.lean::affineFibre_mem`), and a
//! plural reading retains the whole fibre rather than choosing a member.
//!
//! [definition] [`ConstitutiveRelation`] is the exact host reading of the device relation (as
//! `NormalConstitution` is the host reading of `ResidentNormalMaterial`); the device owner is
//! [`ResidentConstitutiveFibre`] and its chart. Its fibre is computed from the annihilator of
//! the rows: `(s, t) ∈ R ⟺ N_T t = −N_S s` for a kernel basis `[N_S | N_T]` of the rows, so
//! `R_s` is the affine preimage of `−N_S s` under `N_T`, whose radical is `R_0`.
use super::*;
use holonics::exact_linear::ExactRatMatrix;
use holonics::restriction::AffineFibre;
use num_traits::{One, Zero};

holonics::fibre_field_names!(pub ParticularDirections = "ConstitutiveFibre", "particular", "directions", deny);

/// The fibre of the constitutive relation over one source: `particular + span(directions)`.
pub type ConstitutiveAffineFibre = AffineFibre<ParticularDirections>;

/// The exact host reading of one resident constitutive relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstitutiveRelation {
    source_width: usize,
    target_width: usize,
    /// Nonzero echelon rows `(s | t)`; their span is the relation.
    rows: Vec<Vec<Rat>>,
}

impl ConstitutiveRelation {
    /// Read a detached relation basis (`ResidentConstitutiveFibre::inspect_relation`).
    pub fn from_rest(
        rest: &ResidentSectionRest,
        source_width: usize,
    ) -> Result<Self, ConstitutiveFibreError> {
        let width = rest.width;
        if source_width == 0
            || source_width >= width
            || rest.rows != width
            || rest.intervals.len() != width * width
            || rest.intervals.iter().any(|(lo, hi)| lo != hi)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let rows = rest
            .intervals
            .chunks_exact(width)
            .filter(|row| row.iter().any(|(v, _)| *v != 0))
            .map(|row| {
                row.iter()
                    .map(|(v, _)| Rat::from_integer((*v).into()))
                    .collect()
            })
            .collect();
        Ok(Self {
            source_width,
            target_width: width - source_width,
            rows,
        })
    }
    pub fn source_width(&self) -> usize {
        self.source_width
    }
    pub fn target_width(&self) -> usize {
        self.target_width
    }
    /// The relation's rank (the number of independent received pairs).
    pub fn rank(&self) -> usize {
        self.rows.len()
    }
    /// `(s, t) ∈ R`.
    pub fn contains(&self, source: &[Rat], target: &[Rat]) -> Result<bool, ConstitutiveFibreError> {
        Ok(self
            .fibre(source)?
            .is_some_and(|fibre| same_span_member(&fibre, target)))
    }
    /// The vertical fibre `R_0 = {t | (0, t) ∈ R}`.
    pub fn vertical(&self) -> Result<Vec<Vec<Rat>>, ConstitutiveFibreError> {
        let zero = vec![Rat::zero(); self.source_width];
        Ok(self.fibre(&zero)?.map(|f| f.radical).unwrap_or_default())
    }
    /// **The fibre over a source**, `R_s`, or `None` when `s` is outside the source projection.
    pub fn fibre(
        &self,
        source: &[Rat],
    ) -> Result<Option<ConstitutiveAffineFibre>, ConstitutiveFibreError> {
        if source.len() != self.source_width {
            return Err(ConstitutiveFibreError::Shape);
        }
        let (s, t) = (self.source_width, self.target_width);
        let annihilator = if self.rows.is_empty() {
            (0..s + t)
                .map(|i| (0..s + t).map(|j| rat_unit(i == j)).collect())
                .collect()
        } else {
            ExactRatMatrix::new(self.rows.clone())
                .and_then(|m| m.kernel_basis())
                .map_err(arithmetic)?
        };
        // One zero constraint keeps the operator nonempty when R is the whole space.
        let mut operator = vec![vec![Rat::zero(); t]];
        let mut target = vec![Rat::zero()];
        for n in &annihilator {
            operator.push(n[s..].to_vec());
            target.push(-n[..s].iter().zip(source).map(|(a, b)| a * b).sum::<Rat>());
        }
        ExactRatMatrix::new(operator)
            .and_then(|m| m.affine_fibre(&target))
            .map_err(arithmetic)
    }
}

fn rat_unit(one: bool) -> Rat {
    if one { Rat::one() } else { Rat::zero() }
}

fn arithmetic(error: impl std::fmt::Display) -> ConstitutiveFibreError {
    ConstitutiveFibreError::Arithmetic(error.to_string())
}

fn span_rank(vectors: &[Vec<Rat>]) -> usize {
    if vectors.is_empty() {
        return 0;
    }
    ExactRatMatrix::new(vectors.to_vec())
        .and_then(|m| m.rank())
        .unwrap_or(usize::MAX)
}

/// `point ∈ particular + span(radical)`.
fn same_span_member(fibre: &ConstitutiveAffineFibre, point: &[Rat]) -> bool {
    if point.len() != fibre.particular.len() {
        return false;
    }
    let offset: Vec<Rat> = point
        .iter()
        .zip(&fibre.particular)
        .map(|(a, b)| a - b)
        .collect();
    if offset.iter().all(Zero::is_zero) {
        return true;
    }
    let mut with = fibre.radical.clone();
    with.push(offset);
    span_rank(&with) == span_rank(&fibre.radical)
}

/// Two retained fibres are the same affine set: equal dimension, and each one's particular and
/// directions lie in the other.
pub fn same_affine_fibre(a: &ConstitutiveAffineFibre, b: &ConstitutiveAffineFibre) -> bool {
    let independent = |f: &ConstitutiveAffineFibre| span_rank(&f.radical) == f.radical.len();
    let directions_in = |x: &ConstitutiveAffineFibre, y: &ConstitutiveAffineFibre| {
        x.radical.iter().all(|d| {
            let mut with = y.radical.clone();
            with.push(d.clone());
            span_rank(&with) == span_rank(&y.radical)
        })
    };
    a.radical.len() == b.radical.len()
        && independent(a)
        && independent(b)
        && directions_in(a, b)
        && directions_in(b, a)
        && same_span_member(b, &a.particular)
}

impl ConstitutiveReading {
    /// The reading as the relation's fibre: `None` outside the source projection.
    pub fn fibre(&self) -> Option<ConstitutiveAffineFibre> {
        match self {
            Self::Unique { current } => Some(AffineFibre::new(current.clone(), Vec::new())),
            Self::Plural {
                particular,
                directions,
            } => Some(AffineFibre::new(particular.clone(), directions.clone())),
            Self::OutsideDomain { .. } => None,
        }
    }
}

impl ConditionPreimageReading {
    /// The condition preimage as the fibre of its derived relation: `None` when no condition
    /// belongs to the represented relation.
    pub fn fibre(&self) -> Option<ConstitutiveAffineFibre> {
        match self {
            Self::Compatible {
                particular,
                directions,
            } => Some(AffineFibre::new(particular.clone(), directions.clone())),
            Self::OutsideRepresentedRelation { .. } => None,
        }
    }
}

impl<'c> ResidentConstitutiveFibre<'c> {
    /// The exact host reading of this relation (one detach of its basis).
    pub fn relation(&self) -> Result<ConstitutiveRelation, ConstitutiveFibreError> {
        if self.source_only {
            return Err(ConstitutiveFibreError::Shape);
        }
        ConstitutiveRelation::from_rest(&self.inspect_relation()?, self.source_width)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::embedding_fiber::ResidentReadout;

    fn r(n: i64) -> Rat {
        Rat::from_integer(n.into())
    }
    fn rows(width: usize, rows: &[&[i64]]) -> ResidentSectionRest {
        let mut values = vec![(0, 0); width * width];
        for (p, row) in rows.iter().enumerate() {
            for (j, v) in row.iter().enumerate() {
                values[p * width + j] = (*v, *v);
            }
        }
        ResidentSectionRest::found(width, width, ResidentGrain(0), 64, values).unwrap()
    }

    /// R = span{(1,0 | 2,0), (0,0 | 0,1)} ⊂ ℚ² × ℚ²: over s = (3,0) the fibre is
    /// (6,0) + span{(0,1)}; over (0,1) it is empty; the vertical fibre is span{(0,1)}.
    #[test]
    fn the_relation_fibre_is_the_translate_of_its_vertical_fibre() {
        let relation =
            ConstitutiveRelation::from_rest(&rows(4, &[&[1, 0, 2, 0], &[], &[], &[0, 0, 0, 1]]), 2)
                .unwrap();
        assert_eq!(relation.rank(), 2);
        let fibre = relation.fibre(&[r(3), r(0)]).unwrap().unwrap();
        let expected = AffineFibre::new(vec![r(6), r(0)], vec![vec![r(0), r(1)]]);
        assert!(same_affine_fibre(&fibre, &expected));
        assert!(relation.contains(&[r(3), r(0)], &[r(6), r(-5)]).unwrap());
        assert!(!relation.contains(&[r(3), r(0)], &[r(5), r(0)]).unwrap());
        assert!(relation.fibre(&[r(0), r(1)]).unwrap().is_none());
        assert!(same_affine_fibre(
            &AffineFibre::new(vec![r(0), r(0)], relation.vertical().unwrap()),
            &AffineFibre::new(vec![r(0), r(0)], vec![vec![r(0), r(2)]])
        ));
        // The readings are that fibre: a plural reading, and its condition-preimage face.
        let plural = ConstitutiveReading::Plural {
            particular: vec![r(6), r(3)],
            directions: vec![vec![r(0), r(-1)]],
        };
        assert!(same_affine_fibre(&plural.fibre().unwrap(), &fibre));
        let preimage = ConditionPreimageReading::Compatible {
            particular: vec![r(6), r(3)],
            directions: vec![vec![r(0), r(-1)]],
        };
        assert_eq!(preimage.fibre(), plural.fibre());
        assert!(
            ConstitutiveReading::OutsideDomain {
                source_remainder: vec![r(0), r(1)]
            }
            .fibre()
            .is_none()
        );
        assert!(!same_affine_fibre(
            &fibre,
            &AffineFibre::new(vec![r(6), r(1)], vec![vec![r(1), r(0)]])
        ));
    }

    fn points<'c>(s: &'c ResidentSurface<'c>, v: &[i64]) -> ResidentSection<'c> {
        s.mount_section_rest(
            &ResidentSectionRest::found(
                1,
                v.len(),
                ResidentGrain(0),
                64,
                v.iter().map(|v| (*v, *v)).collect(),
            )
            .unwrap(),
        )
        .unwrap()
    }
    fn current<'a, 'c>(v: &'a ResidentSection<'c>) -> ResidentConstitutiveCurrent<'a, 'c> {
        ResidentConstitutiveCurrent::integers(v).unwrap()
    }
    fn assert_device_reading_is_the_relation_fibre(
        law: &ResidentConstitutiveFibre<'_>,
        s: &ResidentSurface<'_>,
        sources: &[&[i64]],
    ) -> (usize, usize, usize) {
        let relation = law.relation().unwrap();
        let mut kinds = (0, 0, 0);
        for source in sources {
            let section = points(s, source);
            let reading = law
                .read_resident(current(&section))
                .unwrap()
                .inspect()
                .unwrap()
                .predecessor_reading;
            let host = relation
                .fibre(&source.iter().map(|v| r(*v)).collect::<Vec<_>>())
                .unwrap();
            match (&reading, reading.fibre(), host) {
                (ConstitutiveReading::OutsideDomain { .. }, None, None) => kinds.2 += 1,
                (ConstitutiveReading::Unique { .. }, Some(device), Some(host)) => {
                    // A unique reading is the whole fibre: the host fibre has no direction and
                    // the same point, number for number.
                    assert!(host.radical.is_empty());
                    assert_eq!(device.particular, host.particular);
                    kinds.0 += 1;
                }
                (ConstitutiveReading::Plural { .. }, Some(device), Some(host)) => {
                    assert!(same_affine_fibre(&device, &host), "{device:?} vs {host:?}");
                    kinds.1 += 1;
                }
                (reading, _, host) => {
                    panic!("device {reading:?} is not the relation fibre {host:?}")
                }
            }
        }
        kinds
    }

    /// Host/device parity (resident constitutive-read kernel): every device reading equals the
    /// host core fibre of the detached relation — unique and outside readings for two observed
    /// sources of three (the returns of `(i/2)·z`), and plural readings for a two-target family.
    #[test]
    #[ignore = "requires CUDA; each resident reading is the core fibre of the one relation"]
    fn every_resident_reading_is_the_fibre_of_the_one_relation() {
        let ro = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&ro).unwrap();
        // (i/2)·z on the first two channels, observed at 2e₁ and 2e₂.
        let mut law = ResidentConstitutiveFibre::found(&s, 3, 2).unwrap();
        for (x, y) in [([2, 0, 0], [0, 1]), ([0, 2, 0], [-1, 0])] {
            let (x, y) = (points(&s, &x), points(&s, &y));
            law.advance_resident(current(&x), Some(current(&y)))
                .unwrap();
        }
        let kinds = assert_device_reading_is_the_relation_fibre(
            &law,
            &s,
            &[&[3, 4, 0], &[2, 0, 0], &[0, 0, 1], &[1, 1, 1]],
        );
        assert_eq!(kinds, (2, 0, 2));
        // Two targets for one source: a vertical direction and a plural fibre.
        let mut family = ResidentConstitutiveFibre::found(&s, 2, 4).unwrap();
        let x = points(&s, &[1, 0]);
        for y in [[1, 0, 0, 0], [0, 0, 1, 0]] {
            let y = points(&s, &y);
            family
                .advance_resident(current(&x), Some(current(&y)))
                .unwrap();
        }
        let kinds =
            assert_device_reading_is_the_relation_fibre(&family, &s, &[&[1, 0], &[3, 0], &[0, 1]]);
        assert_eq!(kinds, (0, 2, 1));
        assert_eq!(family.relation().unwrap().vertical().unwrap().len(), 1);
    }
}

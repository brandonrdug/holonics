//! Exact cyclic mode readings of the ring's actual carrier (Refs #73, #62).
//!
//! For P of order N, A_d = (d/N) sum_{j=0}^{N/d-1} P^(jd) projects onto the
//! vectors whose period divides d. For divisors d in increasing order,
//! Q_d = A_d - sum_{e|d,e<d} Q_e isolates the rational cyclotomic subspace of
//! primitive period d. Thus sum_{d|N} Q_d v = v. This uses the existing rotor
//! owner, not a float FFT, inferred feature, learned classifier or separate dynamics.
//!
//! These are transport-mode subspaces, not eigenmodes of the full learned C/K/D
//! constitution. A block retains all phase/quadrature coordinates; collapsing it to
//! one amplitude would discard arrangement. Executable projector, reconstruction,
//! orthogonality and equivariance witnesses follow. Their Lean bridge is owed in #62.

use crate::hnn::{HnnError, Ring};
use crate::ratio::Rat;
use num_bigint::BigInt;
use num_traits::Zero;
use std::sync::{Arc, OnceLock};
pub mod compiled;
pub use compiled::{CompiledProjector, ProjectorStorage};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CyclicMode {
    pub period: u64,
    pub coordinates: Vec<Rat>,
}

/// Faithful rational period decomposition of the supplied, already-produced carrier.
/// Reading a SourceMoment through its contemporary source port and then decomposing
/// cannot recover distinctions that that port or moment already merged.
pub fn decompose(ring: &Ring, carrier: &[Rat]) -> Result<Vec<CyclicMode>, HnnError> {
    if carrier.len() != ring.width() {
        return Err(HnnError::Shape {
            what: "cyclic mode carrier",
            expected: ring.width(),
            found: carrier.len(),
        });
    }
    let n = ring.period();
    let mut modes: Vec<CyclicMode> = Vec::new();
    for d in (1..=n).filter(|d| n.is_multiple_of(*d)) {
        let mut coordinates = vec![Rat::zero(); carrier.len()];
        for j in 0..n / d {
            let transported = ring.rotate(carrier, &BigInt::from(j * d));
            for (out, value) in coordinates.iter_mut().zip(transported) {
                *out += value;
            }
        }
        let count = Rat::from_integer(BigInt::from(n / d));
        for out in &mut coordinates {
            *out /= &count;
        }
        for previous in modes.iter().filter(|m| d.is_multiple_of(m.period)) {
            for (out, value) in coordinates.iter_mut().zip(&previous.coordinates) {
                *out -= value;
            }
        }
        modes.push(CyclicMode {
            period: d,
            coordinates,
        });
    }
    Ok(modes)
}

/// Sum the complete series without dropping its zero or phase components.
pub fn reconstruct(modes: &[CyclicMode]) -> Result<Vec<Rat>, HnnError> {
    let width = modes.first().map_or(0, |m| m.coordinates.len());
    let mut carrier = vec![Rat::zero(); width];
    for mode in modes {
        if mode.coordinates.len() != width {
            return Err(HnnError::Shape {
                what: "cyclic mode reconstruction",
                expected: width,
                found: mode.coordinates.len(),
            });
        }
        for (out, value) in carrier.iter_mut().zip(&mode.coordinates) {
            *out += value;
        }
    }
    Ok(carrier)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::{Field, FieldDeclaration};
    use crate::ratio::{integer, rat};
    fn field() -> Field {
        let mut declared = FieldDeclaration::campaign_one(1 << 20);
        let ring = &mut declared.rings[0];
        ring.period = 28;
        ring.placements = (0..28)
            .map(|i| FieldDeclaration::quarter_turn(i, 28))
            .collect();
        ring.reflector = (0..28).map(|i| ((28 - i) % 28) as usize).collect();
        Field::declare(declared.by_lattice_rule()).unwrap()
    }
    #[test]
    fn exact_series_reconstructs_both_quadratures_and_commutes_with_rotation() {
        let f = field();
        let ring = f.ring(0);
        let v: Vec<_> = (0..ring.width()).map(|i| rat(i as i64 - 13, 7)).collect();
        let modes = decompose(ring, &v).unwrap();
        assert_eq!(
            modes.iter().map(|m| m.period).collect::<Vec<_>>(),
            vec![1, 2, 4, 7, 14, 28]
        );
        assert_eq!(reconstruct(&modes).unwrap(), v);
        let shifted = decompose(ring, &ring.rotate(&v, &BigInt::from(3))).unwrap();
        for (a, b) in modes.iter().zip(shifted) {
            assert_eq!(ring.rotate(&a.coordinates, &BigInt::from(3)), b.coordinates);
            assert_eq!(
                ring.rotate(&a.coordinates, &BigInt::from(a.period)),
                a.coordinates
            );
        }
    }
    #[test]
    fn primitive_blocks_are_exact_projectors_and_mutually_orthogonal() {
        let f = field();
        let ring = f.ring(0);
        let mut v = vec![integer(0); ring.width()];
        v[0] = integer(1);
        v[9] = rat(3, 5);
        let modes = decompose(ring, &v).unwrap();
        for mode in &modes {
            let again = decompose(ring, &mode.coordinates).unwrap();
            for other in again {
                if other.period == mode.period {
                    assert_eq!(other.coordinates, mode.coordinates);
                } else {
                    assert!(other.coordinates.iter().all(Zero::is_zero));
                }
            }
        }
        for (i, a) in modes.iter().enumerate() {
            for b in modes.iter().skip(i + 1) {
                let pairing: Rat = a
                    .coordinates
                    .iter()
                    .zip(&b.coordinates)
                    .map(|(x, y)| x * y)
                    .sum();
                assert!(pairing.is_zero());
            }
        }
    }
    #[test]
    fn constant_and_alternating_carriers_isolate_their_periods() {
        let f = field();
        let ring = f.ring(0);
        let v: Vec<_> = (0..ring.width())
            .map(|i| integer(if (i / 2) % 2 == 0 { 3 } else { 1 }))
            .collect();
        let modes = decompose(ring, &v).unwrap();
        assert!(modes[0].coordinates.iter().all(|v| *v == integer(2)));
        assert!(
            modes
                .iter()
                .skip(2)
                .all(|m| m.coordinates.iter().all(Zero::is_zero))
        );
        assert!(decompose(ring, &v[..v.len() - 1]).is_err());
    }
}

/// A declared receiver-qualified view of fresh source injection. Unlisted sources are whole.
/// The original SourceMoment remains retained; this operator never edits counts or carried motion.
/// Primitive-period projectors are orthogonal and commute with the ring rotor,
/// so the same operator is its exact source adjoint in every transported lift frame.
/// Rotor geometry is bound at construction; reuse on a changed rotor is refused before cache access.
/// Reflection covariance additionally requires the dihedral relation certified by
/// PairedCarrier; an arbitrary field reflector is not enough.
#[derive(Clone, Default)]
pub struct ModeView {
    // (source ring, bound ring period, selected primitive period), canonical source order.
    selected: Vec<(usize, u64, u64)>,
    rotor_bindings: Vec<(usize, Vec<usize>)>,
    compiled: Arc<OnceLock<Vec<(usize, CompiledProjector)>>>,
}
impl std::fmt::Debug for ModeView {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ModeView")
            .field("selected", &self.selected)
            .finish()
    }
}
impl PartialEq for ModeView {
    fn eq(&self, other: &Self) -> bool {
        self.selected == other.selected && self.rotor_bindings == other.rotor_bindings
    }
}
impl Eq for ModeView {}
impl ModeView {
    pub fn whole() -> Self {
        Self::default()
    }
    pub fn is_whole(&self) -> bool {
        self.selected.is_empty()
    }
    pub fn primitive(
        field: &crate::hnn::Field,
        source: usize,
        period: u64,
    ) -> Result<Self, HnnError> {
        Self::from_periods(field, &[(source, period)])
    }
    /// Union of mutually orthogonal primitive-period components on each named source.
    /// Repeated source names select a union; repeated identical (source,period) entries refuse.
    pub fn from_periods(
        field: &crate::hnn::Field,
        selections: &[(usize, u64)],
    ) -> Result<Self, HnnError> {
        let mut selected = Vec::new();
        for &(source, period) in selections {
            if source >= field.rings().len()
                || !field.is_source(source)
                || period == 0
                || !field.ring(source).period().is_multiple_of(period)
                || selected.iter().any(|&(g, _, d)| g == source && d == period)
            {
                return Err(HnnError::Unadmitted {
                    reason: "a mode view selects distinct divisors of declared source periods",
                });
            }
            selected.push((source, field.ring(source).period(), period));
        }
        selected.sort_unstable();
        let rotor_bindings = field
            .sources()
            .iter()
            .filter(|&&g| selected.iter().any(|&(s, _, _)| s == g))
            .map(|&g| {
                (
                    g,
                    field
                        .ring(g)
                        .navigator()
                        .map()
                        .expect("a declared ring rotor")
                        .images()
                        .to_vec(),
                )
            })
            .collect();
        Ok(Self {
            selected,
            rotor_bindings,
            compiled: Arc::new(OnceLock::new()),
        })
    }
    pub fn selections(&self) -> &[(usize, u64, u64)] {
        &self.selected
    }
    pub fn check(&self, field: &crate::hnn::Field) -> Result<(), HnnError> {
        for (source, rotor) in &self.rotor_bindings {
            if field
                .rings()
                .get(*source)
                .and_then(|r| r.navigator().map())
                .map(|m| m.images())
                != Some(rotor.as_slice())
            {
                return Err(HnnError::Unadmitted {
                    reason: "a mode view belongs to its constructor's actual source rotor geometry",
                });
            }
        }
        for &(source, bound, period) in &self.selected {
            if source >= field.rings().len()
                || !field.is_source(source)
                || field.ring(source).period() != bound
                || period == 0
                || !bound.is_multiple_of(period)
            {
                return Err(HnnError::Unadmitted {
                    reason: "a mode view belongs to its declared source geometry",
                });
            }
        }
        Ok(())
    }
    /// Project one ring carrier (also one source-map column or pair output).
    /// The projector commutes with the source phase transport, so projecting these
    /// producing operands before exact expansion equals projecting the completed injection.
    pub fn apply_ring(
        &self,
        field: &crate::hnn::Field,
        source: usize,
        carrier: &[Rat],
    ) -> Result<Vec<Rat>, HnnError> {
        self.check(field)?;
        let ring = field.rings().get(source).ok_or(HnnError::Unadmitted {
            reason: "a mode view ring exists",
        })?;
        if carrier.len() != ring.width() {
            return Err(HnnError::Unadmitted {
                reason: "a mode view ring carrier has its declared width",
            });
        }
        let compiled = self.compiled_projectors(field)?;
        match compiled.iter().find(|(g, _)| *g == source) {
            Some((_, projector)) => projector.apply(ring, carrier),
            None => Ok(carrier.to_vec()),
        }
    }
    /// Compiled once per immutable geometry-bound view and shared by its clones across material
    /// changes. The constructor binds actual source rotor images, checked before cache access.
    pub fn compiled_projectors(
        &self,
        field: &crate::hnn::Field,
    ) -> Result<&[(usize, CompiledProjector)], HnnError> {
        self.check(field)?;
        Ok(self.compiled.get_or_init(|| {
            let mut compiled = Vec::new();
            for &source in field.sources() {
                let periods: Vec<_> = self
                    .selected
                    .iter()
                    .filter(|&&(g, _, _)| g == source)
                    .map(|&(_, _, d)| d)
                    .collect();
                if !periods.is_empty() {
                    compiled.push((
                        source,
                        CompiledProjector::compile(field.ring(source), &periods),
                    ));
                }
            }
            compiled
        }))
    }
    pub fn compiled_storage(
        &self,
        field: &crate::hnn::Field,
    ) -> Result<ProjectorStorage, HnnError> {
        let mut total = ProjectorStorage::default();
        for (_, projector) in self.compiled_projectors(field)? {
            let s = projector.storage();
            total.operators += s.operators;
            total.terms += s.terms;
            total.coefficient_rational_bits += s.coefficient_rational_bits;
            total.gather_entries += s.gather_entries;
            total.gather_length_bytes += s.gather_length_bytes;
            total.gather_capacity_bytes += s.gather_capacity_bytes;
            total.term_descriptor_length_bytes += s.term_descriptor_length_bytes;
            total.term_descriptor_capacity_bytes += s.term_descriptor_capacity_bytes;
        }
        Ok(total)
    }

    /// Apply to a full source-storage vector. This is also the exact transpose.
    pub fn apply(
        &self,
        field: &crate::hnn::Field,
        storage: &[Vec<Rat>],
    ) -> Result<Vec<Vec<Rat>>, HnnError> {
        self.check(field)?;
        if storage.len() != field.rings().len()
            || storage
                .iter()
                .zip(field.rings())
                .any(|(v, r)| v.len() != r.width())
        {
            return Err(HnnError::Unadmitted {
                reason: "a mode view needs the complete shaped source carrier",
            });
        }
        let mut out = storage.to_vec();
        for &source in field.sources() {
            if self.selected.iter().any(|&(g, _, _)| g == source) {
                out[source] = self.apply_ring(field, source, &storage[source])?;
            }
        }
        Ok(out)
    }
    /// The unselected remainder, retained alongside a selected reading; sum equals the input.
    pub fn complement(
        &self,
        field: &crate::hnn::Field,
        storage: &[Vec<Rat>],
    ) -> Result<Vec<Vec<Rat>>, HnnError> {
        let selected = self.apply(field, storage)?;
        Ok(storage
            .iter()
            .zip(selected)
            .map(|(whole, part)| whole.iter().zip(part).map(|(a, b)| a - b).collect())
            .collect())
    }
    /// Logical integer metadata, separate from vector allocation and actual projection work.
    pub fn bits(&self) -> u64 {
        self.selected
            .iter()
            .map(|&(g, n, d)| {
                (usize::BITS - g.leading_zeros()) as u64
                    + (u64::BITS - n.leading_zeros()) as u64
                    + (u64::BITS - d.leading_zeros()) as u64
            })
            .sum()
    }
}

#[cfg(test)]
mod view_tests {
    use super::*;
    use crate::hnn::{Field, FieldDeclaration};
    use crate::ratio::{integer, rat};
    #[test]
    fn mode_view_union_is_exact_half_turn_contrast_with_retained_complement() {
        let mut declaration = FieldDeclaration::campaign_one(1 << 20);
        let source = &mut declaration.rings[0];
        source.period = 28;
        source.placements = (0..28)
            .map(|i| FieldDeclaration::quarter_turn(i, 28))
            .collect();
        source.reflector = (0..28).map(|i| ((28 - i) % 28) as usize).collect();
        declaration.lattice.clear();
        let field = Field::declare(declaration.by_lattice_rule()).unwrap();
        let view = ModeView::from_periods(&field, &[(0, 4), (0, 28)]).unwrap();
        let input: Vec<_> = (0..56).map(|i| rat(i * i + 3 * i - 5, 8)).collect();
        let projected = view.apply_ring(&field, 0, &input).unwrap();
        let opposite = field.ring(0).rotate(&input, &BigInt::from(14));
        let expected: Vec<_> = input
            .iter()
            .zip(opposite)
            .map(|(a, b)| (a - b) / integer(2))
            .collect();
        assert_eq!(projected, expected);
        assert_eq!(view.apply_ring(&field, 0, &projected).unwrap(), projected);
        assert!(
            projected
                .iter()
                .all(|x| x.denom().magnitude().count_ones() == 1),
            "dyadic input stays exactly dyadic"
        );
        let mut full: Vec<_> = field
            .rings()
            .iter()
            .map(|r| vec![Rat::zero(); r.width()])
            .collect();
        full[0] = input;
        let selected = view.apply(&field, &full).unwrap();
        let rest = view.complement(&field, &full).unwrap();
        for ((a, b), c) in full.iter().zip(selected).zip(rest) {
            for ((x, y), z) in a.iter().zip(b).zip(c) {
                assert_eq!(*x, y + z);
            }
        }
        assert!(ModeView::from_periods(&field, &[(0, 4), (0, 4)]).is_err());
    }
}

/// Input-only, budgeted attempts of admitted source views with actual port feedback.
pub mod exploration;

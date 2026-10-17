//! A compiled cyclic polynomial, independent of changing source material.
//! Exact cancellation happens before application. Gathers are powers of the actual
//! rotor; the sparse terms retain the same rational operator and its transpose.
use super::*;
use num_bigint::BigUint;
use num_traits::One;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompiledProjector {
    period: u64,
    rotor: Vec<usize>,
    terms: Vec<(Rat, Vec<usize>)>,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ProjectorStorage {
    pub operators: usize,
    pub terms: usize,
    pub coefficient_rational_bits: u64,
    pub gather_entries: usize,
    pub gather_length_bytes: usize,
    pub gather_capacity_bytes: usize,
    pub term_descriptor_length_bytes: usize,
    pub term_descriptor_capacity_bytes: usize,
}
impl CompiledProjector {
    pub(super) fn compile(ring: &Ring, periods: &[u64]) -> Self {
        let n = ring.period() as usize;
        let mut primitive: Vec<(u64, Vec<Rat>)> = Vec::new();
        for d in (1..=ring.period()).filter(|d| ring.period().is_multiple_of(*d)) {
            let mut polynomial = vec![Rat::zero(); n];
            let coefficient = Rat::new(BigInt::one(), BigInt::from(ring.period() / d));
            for j in 0..ring.period() / d {
                polynomial[(j * d) as usize] = coefficient.clone();
            }
            for (_, old) in primitive.iter().filter(|(e, _)| d.is_multiple_of(*e)) {
                for (a, b) in polynomial.iter_mut().zip(old) {
                    *a -= b;
                }
            }
            primitive.push((d, polynomial));
        }
        let mut polynomial = vec![Rat::zero(); n];
        for (_, component) in primitive.iter().filter(|(d, _)| periods.contains(d)) {
            for (a, b) in polynomial.iter_mut().zip(component) {
                *a += b;
            }
        }
        let map = ring
            .navigator()
            .map()
            .expect("a declared ring has its rotor");
        let terms = polynomial
            .into_iter()
            .enumerate()
            .filter(|(_, c)| !c.is_zero())
            .map(|(shift, c)| (c, map.power(&BigUint::from(shift)).images().to_vec()))
            .collect();
        Self {
            period: ring.period(),
            rotor: map.images().to_vec(),
            terms,
        }
    }
    pub fn terms(&self) -> usize {
        self.terms.len()
    }
    pub fn apply(&self, ring: &Ring, carrier: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        if ring.period() != self.period
            || carrier.len() != ring.width()
            || ring.navigator().map().map(|m| m.images()) != Some(self.rotor.as_slice())
        {
            return Err(HnnError::Unadmitted {
                reason: "a compiled cyclic projector binds the actual rotor and carrier width",
            });
        }
        let mut out = vec![Rat::zero(); carrier.len()];
        for (coefficient, gather) in &self.terms {
            for (node, &target) in gather.iter().enumerate() {
                out[2 * target] += &carrier[2 * node] * coefficient;
                out[2 * target + 1] += &carrier[2 * node + 1] * coefficient;
            }
        }
        Ok(out)
    }
    /// Descriptor/gather bytes and reduced coefficient bits; excludes BigInt allocator limbs.
    pub fn storage(&self) -> ProjectorStorage {
        let entries = self.rotor.len() + self.terms.iter().map(|(_, g)| g.len()).sum::<usize>();
        let capacity =
            self.rotor.capacity() + self.terms.iter().map(|(_, g)| g.capacity()).sum::<usize>();
        ProjectorStorage {
            operators: 1,
            terms: self.terms.len(),
            coefficient_rational_bits: self
                .terms
                .iter()
                .map(|(c, _)| c.numer().bits() + c.denom().bits())
                .sum(),
            gather_entries: entries,
            gather_length_bytes: entries * std::mem::size_of::<usize>(),
            gather_capacity_bytes: capacity * std::mem::size_of::<usize>(),
            term_descriptor_length_bytes: self.terms.len()
                * std::mem::size_of::<(Rat, Vec<usize>)>(),
            term_descriptor_capacity_bytes: self.terms.capacity()
                * std::mem::size_of::<(Rat, Vec<usize>)>(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::{Field, FieldDeclaration};
    use crate::ratio::rat;
    fn field() -> Field {
        let mut d = FieldDeclaration::campaign_one(1 << 20);
        let r = &mut d.rings[0];
        r.period = 28;
        r.placements = (0..28)
            .map(|i| FieldDeclaration::quarter_turn(i, 28))
            .collect();
        r.reflector = (0..28).map(|i| ((28 - i) % 28) as usize).collect();
        d.lattice.clear();
        Field::declare(d.by_lattice_rule()).unwrap()
    }
    fn generic(ring: &Ring, input: &[Rat], periods: &[u64]) -> Vec<Rat> {
        let mut out = vec![Rat::zero(); ring.width()];
        for mode in decompose(ring, input)
            .unwrap()
            .iter()
            .filter(|m| periods.contains(&m.period))
        {
            for (a, b) in out.iter_mut().zip(&mode.coordinates) {
                *a += b;
            }
        }
        out
    }
    #[test]
    fn compiled_mode_projector_matches_generic_rotations_and_transpose() {
        let f = field();
        let ring = f.ring(0);
        let x: Vec<_> = (0..ring.width())
            .map(|i| rat(i as i64 * i as i64 - 9, 8))
            .collect();
        let y: Vec<_> = (0..ring.width())
            .map(|i| rat(3 * i as i64 - 19, 11))
            .collect();
        for periods in [
            vec![1],
            vec![2],
            vec![4],
            vec![7],
            vec![14],
            vec![28],
            vec![4, 28],
            vec![1, 2, 4, 7, 14, 28],
        ] {
            let view =
                ModeView::from_periods(&f, &periods.iter().map(|d| (0, *d)).collect::<Vec<_>>())
                    .unwrap();
            let projected = view.apply_ring(&f, 0, &x).unwrap();
            assert_eq!(projected, generic(ring, &x, &periods));
            let py = view.apply_ring(&f, 0, &y).unwrap();
            assert_eq!(
                x.iter().zip(&py).map(|(a, b)| a * b).sum::<Rat>(),
                projected.iter().zip(&y).map(|(a, b)| a * b).sum::<Rat>()
            );
            assert_eq!(view.apply_ring(&f, 0, &projected).unwrap(), projected);
            let k = BigInt::from(-37);
            assert_eq!(
                view.apply_ring(&f, 0, &ring.rotate(&x, &k)).unwrap(),
                ring.rotate(&projected, &k)
            );
            let cloned = view.clone();
            assert!(std::ptr::eq(
                view.compiled_projectors(&f).unwrap(),
                cloned.compiled_projectors(&f).unwrap()
            ));
            assert_eq!(
                view,
                ModeView::from_periods(&f, &periods.iter().map(|d| (0, *d)).collect::<Vec<_>>())
                    .unwrap()
            );
        }
        let union = ModeView::from_periods(&f, &[(0, 4), (0, 28)]).unwrap();
        assert_eq!(union.compiled_storage(&f).unwrap().terms, 2);
        let q7 = ModeView::primitive(&f, 0, 7).unwrap();
        let mut impulse = vec![Rat::zero(); ring.width()];
        impulse[0] = Rat::one();
        assert!(
            q7.apply_ring(&f, 0, &impulse).unwrap().iter().any(|x| x
                .denom()
                .magnitude()
                .count_ones()
                != 1)
        );
    }
    #[test]
    fn compiled_mode_projector_binding_refuses_foreign_geometry_before_cache_access() {
        let f = field();
        let ring = f.ring(0);
        let x = vec![Rat::one(); ring.width()];
        for warm in [false, true] {
            let mut view = ModeView::primitive(&f, 0, 7).unwrap();
            if warm {
                view.apply_ring(&f, 0, &x).unwrap();
            }
            // Field currently constructs the canonical +1 rotor only. Substitute a foreign
            // binding directly to exercise the same mismatch as a different future rotor field.
            view.rotor_bindings[0].1.reverse();
            assert!(view.check(&f).is_err());
            assert!(view.compiled_projectors(&f).is_err());
            assert!(view.compiled_storage(&f).is_err());
            assert!(view.apply_ring(&f, 0, &x).is_err());
        }
    }
    #[test]
    fn compiled_mode_projector_source_batch_benchmark() {
        let f = field();
        let ring = f.ring(0);
        // Two sources, each 16 E columns plus five pair-output rank-56 row sets.
        let batch: Vec<Vec<Rat>> = (0..592)
            .map(|j| {
                (0..56)
                    .map(|i| rat((i * i + 3 * j * i + 7 * j) as i64, 1024))
                    .collect()
            })
            .collect();
        let start = std::time::Instant::now();
        let view = ModeView::from_periods(&f, &[(0, 4), (0, 28)]).unwrap();
        let storage = view.compiled_storage(&f).unwrap();
        let compilation_ns = start.elapsed().as_nanos();
        let start = std::time::Instant::now();
        let fast: Vec<_> = batch
            .iter()
            .map(|x| view.apply_ring(&f, 0, x).unwrap())
            .collect();
        let compiled_ns = start.elapsed().as_nanos();
        let start = std::time::Instant::now();
        let slow: Vec<_> = batch.iter().map(|x| generic(ring, x, &[4, 28])).collect();
        let generic_ns = start.elapsed().as_nanos();
        assert_eq!(fast, slow);
        println!(
            "compiled_projector_benchmark vectors={} width=56 compilation_ns={compilation_ns} compiled_apply_ns={compiled_ns} generic_apply_ns={generic_ns} storage={storage:?}",
            batch.len()
        );
    }
}

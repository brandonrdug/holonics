//! The marginal read on its integral chart, moved only by changed port/count terms.
//! Derived from contemporary operands; excluded from the moment's retention and equality.
use crate::hnn::HnnError;
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::lcm;
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use std::collections::BTreeMap;
use std::fmt;
use std::sync::{Arc, Mutex, RwLock};

/// Exterior counters only. Every copy shares these totals, never its mutable slot map.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MarginalFaceAudit {
    pub reads: BigUint,
    pub held_matches: BigUint,
    pub count_entries_changed: BigUint,
    pub port_entries_changed: BigUint,
    pub port_entries_on_occupied_columns: BigUint,
    pub integer_multiply_adds: BigUint,
    pub recharts: BigUint,
    pub rebuilds: BigUint,
    pub normalizations: BigUint,
}

#[derive(Clone)]
struct MarginalFace {
    counts: Arc<Vec<u64>>,
    values: Arc<Vec<Rat>>,
    integers: Arc<Vec<BigInt>>,
    denominator: BigInt,
    binned: Vec<Arc<Vec<BigInt>>>,
    period: usize,
    width: usize,
    alphabet: usize,
}

impl MarginalFace {
    fn matches(&self, counts: &[u64], port: &ExactRatMatrix) -> bool {
        self.width == port.rows()
            && self.alphabet == port.columns()
            && self.counts.as_slice() == counts
            && self.values.as_slice() == port.entries()
    }

    fn build(
        counts: &[u64],
        period: usize,
        port: &ExactRatMatrix,
        audit: &mut MarginalFaceAudit,
    ) -> Self {
        let (width, alphabet) = (port.rows(), port.columns());
        let denominator = port
            .entries()
            .iter()
            .fold(BigInt::one(), |d, x| lcm(&d, x.denom()));
        let integers: Vec<_> = port
            .entries()
            .iter()
            .map(|x| x.numer() * (&denominator / x.denom()))
            .collect();
        let mut binned = Vec::with_capacity(period);
        for phase in 0..period {
            let mut row = vec![BigInt::zero(); width];
            for code in 0..alphabet {
                let count = counts[phase * alphabet + code];
                if count == 0 {
                    continue;
                }
                for (r, sum) in row.iter_mut().enumerate() {
                    *sum += BigInt::from(count) * &integers[r * alphabet + code];
                    audit.integer_multiply_adds += BigUint::one();
                }
            }
            binned.push(Arc::new(row));
        }
        audit.rebuilds += BigUint::one();
        Self {
            counts: Arc::new(counts.to_vec()),
            values: Arc::new(port.entries().to_vec()),
            integers: Arc::new(integers),
            denominator,
            binned,
            period,
            width,
            alphabet,
        }
    }

    /// B' = (D'/D)B + M ΔK + ΔM K'. Counts may increase, decrease, or be replaced.
    fn moved(&self, counts: &[u64], port: &ExactRatMatrix, audit: &mut MarginalFaceAudit) -> Self {
        let mut next = self.clone();
        let changed: Vec<_> = port
            .entries()
            .iter()
            .zip(self.values.iter())
            .enumerate()
            .filter_map(|(i, (new, old))| (new != old).then_some(i))
            .collect();
        let denominator = changed.iter().fold(self.denominator.clone(), |d, &i| {
            lcm(&d, port.entries()[i].denom())
        });
        if denominator != self.denominator {
            let scale = &denominator / &self.denominator;
            for value in Arc::make_mut(&mut next.integers) {
                *value *= &scale;
            }
            for row in &mut next.binned {
                for value in Arc::make_mut(row) {
                    *value *= &scale;
                }
            }
            next.denominator = denominator;
            audit.recharts += BigUint::one();
        }
        for &i in &changed {
            let (row, code) = (i / self.alphabet, i % self.alphabet);
            let value = &port.entries()[i];
            let integer = value.numer() * (&next.denominator / value.denom());
            let delta = &integer - &next.integers[i];
            let mut occupied = false;
            for phase in 0..self.period {
                let count = self.counts[phase * self.alphabet + code];
                if count != 0 {
                    Arc::make_mut(&mut next.binned[phase])[row] += BigInt::from(count) * &delta;
                    audit.integer_multiply_adds += BigUint::one();
                    occupied = true;
                }
            }
            audit.port_entries_changed += BigUint::one();
            if occupied {
                audit.port_entries_on_occupied_columns += BigUint::one();
            }
            Arc::make_mut(&mut next.integers)[i] = integer;
        }
        for (slot, (&new, &old)) in counts.iter().zip(self.counts.iter()).enumerate() {
            if new == old {
                continue;
            }
            let (phase, code) = (slot / self.alphabet, slot % self.alphabet);
            let delta = BigInt::from(new) - BigInt::from(old);
            for row in 0..self.width {
                Arc::make_mut(&mut next.binned[phase])[row] +=
                    &delta * &next.integers[row * self.alphabet + code];
                audit.integer_multiply_adds += BigUint::one();
            }
            audit.count_entries_changed += BigUint::one();
        }
        if !changed.is_empty() {
            next.values = Arc::new(port.entries().to_vec());
        }
        if counts != self.counts.as_slice() {
            next.counts = Arc::new(counts.to_vec());
        }
        next
    }

    fn read(&self, audit: &mut MarginalFaceAudit) -> Vec<(usize, Vec<Rat>)> {
        (0..self.period)
            .filter(|&phase| {
                self.counts[phase * self.alphabet..(phase + 1) * self.alphabet]
                    .iter()
                    .any(|&n| n != 0)
            })
            .map(|phase| {
                let row = self.binned[phase]
                    .iter()
                    .map(|n| Rat::new(n.clone(), self.denominator.clone()))
                    .collect();
                audit.normalizations += BigUint::from(self.width);
                (phase, row)
            })
            .collect()
    }
}

#[derive(Default)]
pub(crate) struct ResidentMarginalFaces {
    slots: RwLock<BTreeMap<usize, Arc<MarginalFace>>>,
    audit: Arc<Mutex<BTreeMap<usize, MarginalFaceAudit>>>,
}
impl Clone for ResidentMarginalFaces {
    fn clone(&self) -> Self {
        Self {
            slots: RwLock::new(self.slots.read().map(|s| s.clone()).unwrap_or_default()),
            audit: Arc::clone(&self.audit),
        }
    }
}
impl fmt::Debug for ResidentMarginalFaces {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("ResidentMarginalFaces(derived)")
    }
}
impl PartialEq for ResidentMarginalFaces {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for ResidentMarginalFaces {}

impl ResidentMarginalFaces {
    pub(crate) fn read(
        &self,
        ring: usize,
        counts: &[u64],
        period: usize,
        port: &ExactRatMatrix,
    ) -> Result<Vec<(usize, Vec<Rat>)>, HnnError> {
        if counts.len() != period * port.columns() {
            return Err(HnnError::Shape {
                what: "marginal face counts",
                expected: period * port.columns(),
                found: counts.len(),
            });
        }
        let poison = || HnnError::Unadmitted {
            reason: "marginal face derived lock was poisoned",
        };
        let mut audits = self.audit.lock().map_err(|_| poison())?;
        let audit = audits.entry(ring).or_default();
        audit.reads += BigUint::one();
        {
            let slots = self.slots.read().map_err(|_| poison())?;
            if let Some(face) = slots.get(&ring).filter(|face| face.matches(counts, port)) {
                audit.held_matches += BigUint::one();
                return Ok(face.read(audit));
            }
        }
        let mut slots = self.slots.write().map_err(|_| poison())?;
        let next = match slots.get(&ring) {
            Some(face)
                if face.period == period
                    && face.width == port.rows()
                    && face.alphabet == port.columns() =>
            {
                face.moved(counts, port, audit)
            }
            _ => MarginalFace::build(counts, period, port, audit),
        };
        let reads = next.read(audit);
        slots.insert(ring, Arc::new(next));
        Ok(reads)
    }

    pub(crate) fn audit(&self) -> Vec<(usize, MarginalFaceAudit)> {
        self.audit
            .lock()
            .map(|s| s.iter().map(|(&g, a)| (g, a.clone())).collect())
            .unwrap_or_default()
    }

    pub(crate) fn matches(
        &self,
        ring: usize,
        counts: &[u64],
        port: &ExactRatMatrix,
    ) -> Option<bool> {
        self.slots
            .read()
            .ok()?
            .get(&ring)
            .map(|face| face.matches(counts, port))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::constitution::Constitution;
    use crate::hnn::field::{ConstitutionRead, Current, Field};
    use crate::hnn::moment::SourceMoment;
    use crate::hnn::port::ExecutionPort;
    use crate::hnn::reference::Reference;
    use crate::hnn::tests::learning::{OPEN_BUDGET, chain_declaration, generic_within};
    use crate::hnn::tests::support::encoded;
    use crate::ratio::{integer, rat};

    fn field() -> Field {
        let mut declaration = chain_declaration(1 << 16);
        declaration.alphabet = 2;
        declaration.offsets = vec![1, 2];
        declaration.rings[0].lock = (0..declaration.rings[0].period).collect();
        Field::declare(declaration.by_lattice_rule()).unwrap()
    }
    fn code(n: usize) -> usize {
        (n * n + 3 * n + n / 7) % 2
    }
    fn passage(field: &Field) -> (Current, SourceMoment) {
        let mut current = Current::at_rest(field);
        let mut moment = SourceMoment::open(field, &current);
        for n in 0..400 {
            moment
                .ingest(field, &mut current, &encoded(field, &[code(n)]))
                .unwrap();
        }
        (current, moment)
    }
    fn equal(field: &Field, material: &Constitution, moment: &SourceMoment) {
        for &ring in field.sources() {
            assert_eq!(
                moment.moment_parts(field, material, ring).unwrap(),
                moment
                    .moment_parts_whole_table_oracle(field, material, ring)
                    .unwrap()
            );
        }
    }
    fn text(moment: &SourceMoment) -> String {
        let mut s = String::new();
        moment.write(&mut s);
        s
    }
    fn parsed(field: &Field, moment: &SourceMoment) -> SourceMoment {
        let s = text(moment);
        let mut lines = s.lines();
        SourceMoment::read(field, lines.next().unwrap(), &mut |what| {
            lines.next().ok_or(HnnError::ContinuingState { what })
        })
        .unwrap()
    }
    fn changed_port(material: Constitution, field: &Field, value: Rat) -> Constitution {
        let port = material.source_port(0).unwrap();
        let mut rows: Vec<_> = port
            .entries()
            .chunks(field.alphabet())
            .map(<[Rat]>::to_vec)
            .collect();
        rows[0][0] = value;
        material
            .with_ports(0, None, Some(ExactRatMatrix::new(rows).unwrap()), None)
            .unwrap()
    }

    #[test]
    fn marginal_face_reads_the_whole_table() {
        let field = field();
        let reference = Reference::new(4, OPEN_BUDGET);
        let mut resident = reference
            .mount_with(
                &field,
                &Current::at_rest(&field),
                generic_within(&field, 301, OPEN_BUDGET),
            )
            .unwrap();
        // Take the first two actual deposits, before the period-four chain's
        // recorded carrier edge at cell two (2026-10-05 record, section 2).
        // The marginal identity concerns these admitted port values and counts;
        // alternating them exercises both signs without widening the carrier.
        let mut held = None;
        let mut deposited = Vec::new();
        for n in 0..2 {
            let (id, _) = reference
                .ingest(&mut resident, held.as_ref(), &encoded(&field, &[code(n)]))
                .unwrap();
            let phases = resident.admitted()[0].clone();
            let (pending, _) = reference.refine(&mut resident, &id, &phases).unwrap();
            let targets: Vec<_> = (1..=field.receivers()[0].aperture)
                .map(|offset| code(n + offset))
                .collect();
            let (staged, _) = reference
                .compare(&mut resident, pending, &encoded(&field, &targets))
                .unwrap();
            reference.deposit(&mut resident, staged).unwrap();
            deposited.push(resident.constitution().clone());
            held = Some(id);
        }
        let mut current = Current::at_rest(&field);
        let mut moment = SourceMoment::open(&field, &current);
        for n in 0..400 {
            moment
                .ingest(&field, &mut current, &encoded(&field, &[code(n)]))
                .unwrap();
            let before = &deposited[n % 2];
            let after = &deposited[(n + 1) % 2];
            let before_port = before.source_port(0).unwrap();
            let after_port = after.source_port(0).unwrap();
            assert_eq!(before_port.rows(), after_port.rows());
            assert_eq!(before_port.columns(), field.alphabet());
            assert_eq!(after_port.columns(), field.alphabet());
            assert_ne!(before_port, after_port, "E must differ on every cell");
            assert!(
                before_port
                    .entries()
                    .iter()
                    .zip(after_port.entries())
                    .enumerate()
                    .any(|(i, (old, new))| old != new
                        && (0..moment.rings[0].period)
                            .any(|phase| moment.phase_counts(0, phase).unwrap()
                                [i % field.alphabet()]
                                != 0)),
                "the changed port entry must meet a counted phase on every cell"
            );
            equal(&field, before, &moment);
            equal(&field, after, &moment);
        }
        println!(
            "marginal_oracle cells=400 actual_deposited_constitutions=2 alternating_port_changes=400"
        );
    }

    #[test]
    fn marginal_face_follows_any_count_change() {
        let field = field();
        let material = generic_within(&field, 301, OPEN_BUDGET);
        let (current, mut moment) = passage(&field);
        equal(&field, &material, &moment);
        let cells: Vec<_> = (0..400).map(|n| (n % 11 != 0).then(|| code(n))).collect();
        equal(
            &field,
            &material,
            &moment.continued(&field, &current, 0, &cells).unwrap(),
        );
        equal(
            &field,
            &material,
            &SourceMoment::open(&field, &current)
                .station_section(&field, &current, 0, &cells)
                .unwrap(),
        );
        equal(&field, &material, &parsed(&field, &moment));
        moment.rings[0].first[0] += 13;
        equal(&field, &material, &moment);
        moment.rings[0].first[0] -= 7;
        equal(&field, &material, &moment);
        let mut declaration = chain_declaration(1 << 16);
        declaration.alphabet = 2;
        declaration.offsets.clear();
        declaration.rings[0].lock = (0..declaration.rings[0].period).collect();
        let plain = Field::declare(declaration.by_lattice_rule()).unwrap();
        let (current, moment) = passage(&plain);
        let material = generic_within(&plain, 301, OPEN_BUDGET);
        equal(&plain, &material, &moment);
        equal(
            &plain,
            &material,
            &moment
                .dyad(&plain, &current, 0, &[Some(1), Some(0)], 0)
                .unwrap(),
        );
        let founding =
            Field::declare(crate::hnn::field::founding_tests::listener(2, 1 << 16)).unwrap();
        let (mut current, mut moment) = passage(&founding);
        equal(
            &founding,
            &generic_within(&founding, 301, OPEN_BUDGET),
            &moment,
        );
        let expanded = founding
            .found(crate::hnn::FoundedRing { period: 2, key: 1 })
            .unwrap();
        moment.found_ring(&expanded, 3).unwrap();
        current.found_ring(1);
        let material = generic_within(&expanded, 301, OPEN_BUDGET);
        equal(&expanded, &material, &moment);
        for n in 0..400 {
            moment
                .ingest(&expanded, &mut current, &encoded(&expanded, &[code(n)]))
                .unwrap();
            equal(&expanded, &material, &moment);
        }
    }

    #[test]
    fn marginal_face_recharts() {
        let field = field();
        let material = generic_within(&field, 301, OPEN_BUDGET);
        let (_, moment) = passage(&field);
        equal(&field, &material, &moment);
        let old = moment.marginal_face_audit()[0].1.recharts.clone();
        let material = changed_port(material, &field, rat(1, 3));
        equal(&field, &material, &moment);
        assert_eq!(
            moment.marginal_face_audit()[0].1.recharts,
            &old + BigUint::one()
        );
        let material = changed_port(material, &field, integer(1));
        equal(&field, &material, &moment);
        assert_eq!(
            moment.marginal_face_audit()[0].1.recharts,
            old + BigUint::one()
        );
    }

    #[test]
    fn marginal_face_applies_only_the_change() {
        let field = field();
        let material = generic_within(&field, 301, OPEN_BUDGET);
        let (_, mut moment) = passage(&field);
        equal(&field, &material, &moment);
        let before = moment.marginal_face_audit()[0].1.clone();
        let phases = moment.rings[0]
            .first
            .chunks(field.alphabet())
            .filter(|row| row[0] != 0)
            .count();
        let value = material.source_port(0).unwrap().get(0, 0).unwrap() + rat(1, 2);
        let material = changed_port(material, &field, value);
        moment.rings[0].first[0] += 1;
        equal(&field, &material, &moment);
        let after = moment.marginal_face_audit()[0].1.clone();
        assert_eq!(
            after.count_entries_changed - before.count_entries_changed,
            BigUint::one()
        );
        assert_eq!(
            after.port_entries_changed - before.port_entries_changed,
            BigUint::one()
        );
        assert_eq!(
            after.integer_multiply_adds - before.integer_multiply_adds,
            BigUint::from(field.ring(0).width() + phases)
        );
        assert_eq!(after.recharts, before.recharts);
    }

    #[test]
    fn marginal_face_clones_are_independent() {
        let field = field();
        let material = generic_within(&field, 301, OPEN_BUDGET);
        let (current, moment) = passage(&field);
        equal(&field, &material, &moment);
        let original = text(&moment);
        let original_read = moment.moment_parts(&field, &material, 0).unwrap();
        let (mut fork, mut current) = (moment.clone(), current);
        fork.ingest(&field, &mut current, &encoded(&field, &[1]))
            .unwrap();
        equal(&field, &material, &fork);
        equal(&field, &material, &moment);
        assert_eq!(text(&moment), original);
        assert_eq!(
            moment.moment_parts(&field, &material, 0).unwrap(),
            original_read
        );
        assert_ne!(fork, moment);
    }

    #[test]
    fn marginal_face_is_not_retained() {
        let field = field();
        let material = generic_within(&field, 301, OPEN_BUDGET);
        let (_, moment) = passage(&field);
        let before = text(&moment);
        let bits = moment.dense_bits();
        let cold = parsed(&field, &moment);
        equal(&field, &material, &moment);
        assert_eq!(text(&moment), before);
        assert_eq!(moment.dense_bits(), bits);
        assert_eq!(moment, cold);
        assert!(cold.marginal_face_audit().is_empty());
        equal(&field, &material, &cold);
    }
}

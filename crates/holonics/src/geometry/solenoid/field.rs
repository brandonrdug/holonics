//! The finite solenoidal face of an actual HNN field (J1; Refs #62 #73).
//!
//! [definition; agent-inferred from the field's declared carry law] In carry order, let the
//! Lock rings have periods `d_g`, weights `w_g = product_(h<g) d_h`, and digits `tau_g` read
//! through their own navigator clocks. Then `V = sum tau_g*w_g` lies in `Z/N`, with the
//! **factored product** `N = product d_g`. It is not the LCM of independent unit ticks.
//! Each native class translates this face by `A(x) = sum a_g(x)*w_g`: the actual lock fit,
//! or the located occurrence's declared digits. Own rings remain independent leaf coordinates.
//!
//! [`FieldSolenoid::step`] consumes [`Current::step`], then checks
//! `face(step(lambda,x)) = face(lambda)+A(x)` and equal carry-out using the existing
//! [`Odometer`]. It publishes the current only after the square holds. This module owns no
//! stepping law. [`FieldSolenoid::phase_path`] is an offline reading of already native class
//! lists and actual keys; it calls the existing field class-step owner, not an exterior codec.
//! These returned readings are observations, never additional retained HNN state or a replay tape.
//!
//! The lift `V + N*floor(lambda_top/d_top)` reads the last Lock ring's actual winding.
//! Lower ring windings are not added again: they have already carried into higher coordinates.
//! Finite restriction discards the added top digits; it cannot reconstruct the lower ring's
//! retained lift when added rings also receive their own fitted advances. The caller keeps the
//! actual [`Current`]. An exact character is returned as rational turns `k V/N (mod 1)`.
//!
//! The helical pair interaction touches the helix, faces, and finite tower restrictions here;
//! contacts, cell holonomy, and the tube remain owned by the field and its consumers. The
//! lessons' failed detached consumer is avoided by checking the equation on the actual step;
//! bounded controls are not a learned-output claim. A general Lean proof joining the field's
//! selective-step law to this odometer face and its append restrictions remains owed in #62.

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use thiserror::Error;

use crate::geometry::winding::{Odometer, WindingError};
use crate::hnn::HnnError;
use crate::hnn::encoding::Encoded;
use crate::hnn::field::{Current, Field, RingAdvance, SelectiveStep};
use crate::ratio::Rat;
use crate::ratio::surprisal::{SurprisalError, factor_biguint};

/// Refusal of an actual field/phase operand or of the consuming square.
#[derive(Debug, Error)]
pub enum FieldPhaseError {
    #[error("the supplied field has a different class or ring advance declaration")]
    DifferentField,
    #[error("the finer field must append rings above the unchanged declared chain")]
    NotATopExtension,
    #[error("the supplied Lock phase is not a reading of this factored modulus")]
    InvalidPhase,
    #[error("the field's actual step disagrees with its {square} solenoidal square")]
    StepSquare { square: &'static str },
    #[error(transparent)]
    Hnn(Box<HnnError>),
    #[error(transparent)]
    Winding(#[from] WindingError),
    #[error(transparent)]
    Factorization(#[from] SurprisalError),
}

impl From<HnnError> for FieldPhaseError {
    fn from(error: HnnError) -> Self {
        Self::Hnn(Box::new(error))
    }
}

/// Product of the declared Lock periods, with their exact prime factorizations retained.
/// Each inner factorization belongs to the corresponding radix; the existing factorizer owns
/// trial division. This representation never replaces a carried cascade by independent circles.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FactoredModulus {
    radices: Vec<BigUint>,
    prime_factors: Vec<Vec<(u64, u32)>>,
    value: BigUint,
}

impl FactoredModulus {
    pub fn radices(&self) -> &[BigUint] {
        &self.radices
    }

    pub fn prime_factors(&self) -> &[Vec<(u64, u32)>] {
        &self.prime_factors
    }

    pub fn value(&self) -> &BigUint {
        &self.value
    }
}

/// The finite Lock face and the distinct lift read from the actual top Lock clock.
/// Public operands allow an offline reader to validate and report exact comparisons.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LockPhase {
    pub digits: Vec<BigUint>,
    pub value: BigUint,
    pub lift: BigInt,
    pub winding: BigInt,
}

/// An Own ring is a leaf, with its actual ring index, digit and retained lift.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OwnPhase {
    pub ring: usize,
    pub period: u64,
    pub digit: u64,
    pub lift: BigInt,
    pub winding: BigInt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldPhase {
    pub lock: LockPhase,
    pub own: Vec<OwnPhase>,
}

/// A checked observation of one actual field step, including its exact aeon-boundary carry.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldPhaseStep {
    pub before: FieldPhase,
    pub after: FieldPhase,
    pub increment: BigUint,
    pub carry_out: BigUint,
    pub selective: SelectiveStep,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RingLaw {
    period: u64,
    advance: RingAdvance,
    notches: Vec<u64>,
}

/// A read-only chart derived from the field's actual declaration. No current or source passage
/// is retained here. Ring order, class count, lock fits and Own/Lock distinctions are checked
/// at every call that consumes a field.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldSolenoid {
    alphabet: usize,
    rings: Vec<RingLaw>,
    lock_rings: Vec<usize>,
    modulus: FactoredModulus,
}

impl FieldSolenoid {
    pub fn from_field(field: &Field) -> Result<Self, FieldPhaseError> {
        let rings: Vec<_> = field
            .rings()
            .iter()
            .map(|ring| RingLaw {
                period: ring.period(),
                advance: ring.advance(),
                notches: ring.notches(),
            })
            .collect();
        let lock_rings: Vec<_> = rings
            .iter()
            .enumerate()
            .filter_map(|(ring, law)| (law.advance == RingAdvance::Lock).then_some(ring))
            .collect();
        let radices: Vec<_> = lock_rings
            .iter()
            .map(|&ring| BigUint::from(rings[ring].period))
            .collect();
        let prime_factors = radices
            .iter()
            .map(factor_biguint)
            .collect::<Result<_, _>>()?;
        let value = radices.iter().fold(BigUint::one(), |n, d| n * d);
        Ok(Self {
            alphabet: field.alphabet(),
            rings,
            lock_rings,
            modulus: FactoredModulus {
                radices,
                prime_factors,
                value,
            },
        })
    }

    pub fn modulus(&self) -> &FactoredModulus {
        &self.modulus
    }

    pub fn lock_radices(&self) -> &[BigUint] {
        self.modulus.radices()
    }

    pub fn lock_rings(&self) -> &[usize] {
        &self.lock_rings
    }

    fn check_field(&self, field: &Field) -> Result<(), FieldPhaseError> {
        if self.alphabet != field.alphabet()
            || self.rings.len() != field.rings().len()
            || self.rings.iter().zip(field.rings()).any(|(law, ring)| {
                law.period != ring.period()
                    || law.advance != ring.advance()
                    || law.notches != ring.notches()
            })
        {
            return Err(FieldPhaseError::DifferentField);
        }
        Ok(())
    }

    /// Read each phase and winding through the actual ring's navigator clock. A current of the
    /// wrong shape, including a stale pre-founding key, is refused before any indexing.
    pub fn phase(&self, field: &Field, current: &Current) -> Result<FieldPhase, FieldPhaseError> {
        self.check_field(field)?;
        if current.lift().len() != self.rings.len() {
            return Err(HnnError::Shape {
                what: "solenoidal field key",
                expected: self.rings.len(),
                found: current.lift().len(),
            }
            .into());
        }
        let digits = self
            .lock_rings
            .iter()
            .map(|&ring| current.phase(field, ring).map(BigUint::from))
            .collect::<Result<Vec<_>, _>>()?;
        let value = Odometer::with_digits(self.lock_radices().to_vec(), digits.clone())?.value();
        let winding = match self.lock_rings.last() {
            Some(&top) => current.winding(field, top)?,
            None => BigInt::zero(),
        };
        let lift =
            BigInt::from(value.clone()) + BigInt::from(self.modulus.value.clone()) * &winding;
        let own = self
            .rings
            .iter()
            .enumerate()
            .filter(|(_, law)| law.advance == RingAdvance::Own)
            .map(|(ring, law)| {
                Ok(OwnPhase {
                    ring,
                    period: law.period,
                    digit: current.phase(field, ring)?,
                    lift: current.lift()[ring].clone(),
                    winding: current.winding(field, ring)?,
                })
            })
            .collect::<Result<_, HnnError>>()?;
        Ok(FieldPhase {
            lock: LockPhase {
                digits,
                value,
                lift,
                winding,
            },
            own,
        })
    }

    /// A key is an actual nonnegative lift coordinate for every field ring, not a lag divided by
    /// a period. It may include arbitrarily many already completed windings.
    pub fn key_phase(&self, field: &Field, key: &[BigInt]) -> Result<FieldPhase, FieldPhaseError> {
        self.phase(field, &Current::at(field, key.to_vec())?)
    }

    /// Native class advance before carry, using the existing field owner for each Lock ring.
    pub fn class_increment(&self, field: &Field, class: usize) -> Result<BigUint, FieldPhaseError> {
        self.check_field(field)?;
        if class >= field.alphabet() {
            return Err(HnnError::CellOutside {
                code: class,
                alphabet: field.alphabet(),
            }
            .into());
        }
        self.weighted_increment(|ring| field.class_advance(ring, class))
    }

    /// Actual occurrence advance: a located encoding's digits take precedence over lock fits.
    /// This reads the encoded native source and its admission, never an exterior code modulo d.
    pub fn occurrence_increment(
        &self,
        field: &Field,
        encoded: &Encoded,
        at: usize,
    ) -> Result<BigUint, FieldPhaseError> {
        self.check_field(field)?;
        field.admit(encoded)?;
        let cell = encoded.cells().get(at).ok_or(HnnError::Shape {
            what: "an occurrence of the encoded passage",
            expected: encoded.len(),
            found: at,
        })?;
        if cell.class() >= field.alphabet() {
            return Err(HnnError::CellOutside {
                code: cell.class(),
                alphabet: field.alphabet(),
            }
            .into());
        }
        if let Some(digits) = encoded.advance(at) {
            if digits.len() != self.rings.len() {
                return Err(HnnError::Shape {
                    what: "solenoidal occurrence advances",
                    expected: self.rings.len(),
                    found: digits.len(),
                }
                .into());
            }
            for &ring in &self.lock_rings {
                if digits[ring] >= self.rings[ring].period {
                    return Err(FieldPhaseError::InvalidPhase);
                }
            }
        }
        self.weighted_increment(|ring| {
            Ok(field.advance_of(ring, cell.class(), encoded.advance(at)))
        })
    }

    fn weighted_increment(
        &self,
        mut advance: impl FnMut(usize) -> Result<u64, HnnError>,
    ) -> Result<BigUint, FieldPhaseError> {
        let mut weight = BigUint::one();
        let mut total = BigUint::zero();
        for (&ring, radix) in self.lock_rings.iter().zip(self.lock_radices()) {
            total += BigUint::from(advance(ring)?) * &weight;
            weight *= radix;
        }
        Ok(total)
    }

    /// Consume the actual admitted source step atomically and check its finite face, retained
    /// lift, Own leaves and carry. Odometer supplies the addition; Current supplies the motion.
    pub fn step(
        &self,
        field: &Field,
        current: &mut Current,
        encoded: &Encoded,
        at: usize,
    ) -> Result<FieldPhaseStep, FieldPhaseError> {
        let before = self.phase(field, current)?;
        let increment = self.occurrence_increment(field, encoded, at)?;
        let mut staged = current.clone();
        let selective = staged.step(field, encoded, at)?;
        let after = self.phase(field, &staged)?;
        let reading = self.check_step(before, after, increment, selective)?;
        *current = staged;
        Ok(reading)
    }

    fn check_step(
        &self,
        before: FieldPhase,
        after: FieldPhase,
        increment: BigUint,
        selective: SelectiveStep,
    ) -> Result<FieldPhaseStep, FieldPhaseError> {
        let mut expected =
            Odometer::with_digits(self.lock_radices().to_vec(), before.lock.digits.clone())?;
        expected.advance(&increment);
        let carry_out = expected.overflow_winding().clone();
        if expected.digits() != after.lock.digits
            || after.lock.lift != &before.lock.lift + BigInt::from(increment.clone())
        {
            return Err(FieldPhaseError::StepSquare {
                square: "Lock phase and retained lift",
            });
        }
        if carry_out != BigUint::from(u8::from(selective.carry_out))
            || after.lock.winding != &before.lock.winding + BigInt::from(carry_out.clone())
        {
            return Err(FieldPhaseError::StepSquare {
                square: "carry-out",
            });
        }
        if before.own.len() != after.own.len()
            || before.own.iter().zip(&after.own).any(|(left, right)| {
                left.ring != right.ring
                    || left.period != right.period
                    || right.lift != &left.lift + BigInt::one()
            })
        {
            return Err(FieldPhaseError::StepSquare { square: "Own leaf" });
        }
        Ok(FieldPhaseStep {
            before,
            after,
            increment,
            carry_out,
            selective,
        })
    }

    /// Offline phase annotations for already native class lists and an actual key. The result
    /// includes the entry phase of every cell and the final endpoint (`classes.len()+1`).
    /// Ordinary fitted advances apply; for located source laws use [`Self::encoded_phase_path`].
    pub fn phase_path(
        &self,
        field: &Field,
        key: &[BigInt],
        classes: &[usize],
    ) -> Result<Vec<FieldPhase>, FieldPhaseError> {
        let mut current = Current::at(field, key.to_vec())?;
        let mut path = vec![self.phase(field, &current)?];
        for &class in classes {
            let increment = self.class_increment(field, class)?;
            let before = path.last().expect("the entry phase exists").clone();
            let mut lift = current.lift().to_vec();
            let selective = field.step_class(&mut lift, class, None)?;
            current = Current::at(field, lift)?;
            let after = self.phase(field, &current)?;
            let reading = self.check_step(before, after, increment, selective)?;
            path.push(reading.after);
        }
        Ok(path)
    }

    /// The same offline annotation for an admitted encoding, preserving its actual source law.
    pub fn encoded_phase_path(
        &self,
        field: &Field,
        key: &[BigInt],
        encoded: &Encoded,
    ) -> Result<Vec<FieldPhase>, FieldPhaseError> {
        let mut current = Current::at(field, key.to_vec())?;
        let mut path = vec![self.phase(field, &current)?];
        field.admit(encoded)?;
        for at in 0..encoded.len() {
            path.push(self.step(field, &mut current, encoded, at)?.after);
        }
        Ok(path)
    }

    fn check_phase(&self, phase: &LockPhase) -> Result<(), FieldPhaseError> {
        let reading = Odometer::with_digits(self.lock_radices().to_vec(), phase.digits.clone())?;
        if reading.value() != phase.value
            || phase.value >= self.modulus.value
            || phase.lift
                != BigInt::from(phase.value.clone())
                    + BigInt::from(self.modulus.value.clone()) * &phase.winding
        {
            return Err(FieldPhaseError::InvalidPhase);
        }
        Ok(())
    }

    /// Finite restriction after appending rings at the top. Returns a normalized odometer
    /// (`overflow_winding = 0`), explicitly a finite observation. It does not claim that the
    /// lower retained lift is recoverable from the finer joint lift. Reordering, removing, or
    /// changing a lower ring's advance/lock declaration is refused.
    pub fn restrict_face(
        &self,
        finer: &Self,
        phase: &LockPhase,
    ) -> Result<Odometer, FieldPhaseError> {
        if self.alphabet != finer.alphabet || !finer.rings.starts_with(&self.rings) {
            return Err(FieldPhaseError::NotATopExtension);
        }
        finer.check_phase(phase)?;
        Ok(Odometer::from_value(
            self.lock_radices().to_vec(),
            &(&phase.value % &self.modulus.value),
        )?)
    }

    /// Exact phase of the character `exp(2*pi*i*k*V/N)`, represented in turns in `[0,1)`.
    /// No trigonometric approximation, imaginary floating constant, or Cayley parameter is used.
    pub fn character_phase(&self, phase: &LockPhase, k: &BigInt) -> Result<Rat, FieldPhaseError> {
        self.check_phase(phase)?;
        let numerator = super::signed_residue(
            &(k * BigInt::from(phase.value.clone())),
            &self.modulus.value,
        );
        Ok(Rat::new(
            BigInt::from(numerator),
            BigInt::from(self.modulus.value.clone()),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::field::{ContactDeclaration, FieldDeclaration, FoundedRing, RingDeclaration};
    use crate::holarchy::terrain::KnownTruth;
    use crate::ratio::{integer, rat};

    fn declaration(periods: &[u64], locks: &[Vec<u64>]) -> FieldDeclaration {
        let mut declared = FieldDeclaration::campaign_one(1 << 17);
        let axis = declared.rings[0].screw.clone();
        declared.rings = periods
            .iter()
            .zip(locks)
            .map(|(&period, lock)| RingDeclaration {
                period,
                screw: axis.clone(),
                placements: (0..period)
                    .map(|n| FieldDeclaration::quarter_turn(n, period))
                    .collect(),
                lock: lock.clone(),
                reflector: (0..period)
                    .map(|n| ((period - n) % period) as usize)
                    .collect(),
                admittance: integer(2),
                initial: 0,
            })
            .collect();
        declared.contacts = (1..periods.len())
            .map(|to| ContactDeclaration {
                from: to - 1,
                to,
                channel: vec![(0, 0)],
                admittance: integer(2),
                exponent: integer(2),
            })
            .collect();
        declared.loops.clear();
        declared.sources = vec![0];
        declared.alphabet = 2;
        declared.receivers[0].ring = periods.len() - 1;
        declared.receivers[0].aperture = 1;
        declared.receivers[0].depth = 1;
        declared.founding = true;
        declared.by_lattice_rule()
    }

    fn field() -> Field {
        Field::declare(declaration(&[2, 4, 3], &[vec![0], vec![1], vec![0]])).unwrap()
    }

    fn encoded(field: &Field, classes: &[usize]) -> Encoded {
        Encoded::identity(&KnownTruth::declared(2, vec![classes.to_vec()]), field)
            .unwrap()
            .remove(0)
    }

    #[test]
    fn field_face_uses_fitted_steps_and_product_even_for_non_coprime_periods() {
        let field = field();
        let chart = FieldSolenoid::from_field(&field).unwrap();
        assert_eq!(chart.lock_radices(), &[2u32, 4, 3].map(BigUint::from));
        assert_eq!(chart.modulus().value(), &BigUint::from(24u32));
        assert_eq!(
            chart.modulus().prime_factors(),
            &[vec![(2, 1)], vec![(2, 2)], vec![(3, 1)]]
        );
        assert_eq!(
            chart.class_increment(&field, 0).unwrap(),
            BigUint::from(9u32)
        );
        assert_eq!(
            chart.class_increment(&field, 1).unwrap(),
            BigUint::from(2u32)
        );
        let classes = [0, 1, 0, 0, 1, 1, 0];
        let source = encoded(&field, &classes);
        // All finite keys, two distinct retained top windings, every source occurrence.
        for winding in 0..2 {
            for a in 0..2 {
                for b in 0..4 {
                    for c in 0..3 {
                        let key = vec![a.into(), b.into(), (c + 3 * winding).into()];
                        let mut actual = Current::at(&field, key.clone()).unwrap();
                        let mut observed = actual.clone();
                        let path = chart.phase_path(&field, &key, &classes).unwrap();
                        assert_eq!(
                            path,
                            chart.encoded_phase_path(&field, &key, &source).unwrap()
                        );
                        for at in 0..classes.len() {
                            let step = actual.step(&field, &source, at).unwrap();
                            let read = chart.step(&field, &mut observed, &source, at).unwrap();
                            assert_eq!(actual, observed);
                            assert_eq!(read.selective, step);
                            assert_eq!(read.before, path[at]);
                            assert_eq!(read.after, path[at + 1]);
                            let total = &read.before.lock.value + &read.increment;
                            assert_eq!(read.after.lock.value, &total % chart.modulus().value());
                            assert_eq!(read.carry_out, total / chart.modulus().value());
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn mixed_source_own_ring_keeps_its_leaf_and_leaves_lock_carry_out_unchanged() {
        let base = field();
        let mixed = base.found(FoundedRing { period: 2, key: 1 }).unwrap();
        assert_eq!(mixed.ring(3).advance(), RingAdvance::Own);
        assert!(mixed.is_source(0) && mixed.is_source(3));
        let chart = FieldSolenoid::from_field(&mixed).unwrap();
        assert_eq!(chart.modulus().value(), &BigUint::from(24u32));
        assert_eq!(chart.lock_rings(), &[0, 1, 2]);
        let source = encoded(&mixed, &[0, 1, 0, 1, 1, 0]);
        let mut current =
            Current::at(&mixed, vec![1.into(), 3.into(), 2.into(), 7.into()]).unwrap();
        let mut plain = Current::at(&base, current.lift()[..3].to_vec()).unwrap();
        let plain_source = encoded(&base, &[0, 1, 0, 1, 1, 0]);
        for at in 0..source.len() {
            let read = chart.step(&mixed, &mut current, &source, at).unwrap();
            let old = plain.step(&base, &plain_source, at).unwrap();
            assert_eq!(read.selective.carry_out, old.carry_out);
            assert_eq!(&current.lift()[..3], plain.lift());
            assert_eq!(read.after.own[0].ring, 3);
            assert_eq!(read.after.own[0].lift, BigInt::from(8 + at));
        }
    }

    #[test]
    fn top_append_restricts_finite_face_and_characters_but_does_not_invent_a_lower_lift() {
        let coarse_field = Field::declare(declaration(&[2, 4], &[vec![0], vec![1]])).unwrap();
        let fine_field = field();
        let coarse = FieldSolenoid::from_field(&coarse_field).unwrap();
        let fine = FieldSolenoid::from_field(&fine_field).unwrap();
        let classes = [0, 0, 1, 0, 1, 1, 0];
        let low = coarse
            .phase_path(&coarse_field, &[1.into(), 7.into()], &classes)
            .unwrap();
        let high = fine
            .phase_path(&fine_field, &[1.into(), 7.into(), 11.into()], &classes)
            .unwrap();
        for (low, high) in low.iter().zip(&high) {
            let restriction = coarse.restrict_face(&fine, &high.lock).unwrap();
            assert_eq!(restriction.digits(), low.lock.digits);
            assert_eq!(restriction.value(), low.lock.value);
            assert!(restriction.overflow_winding().is_zero());
            assert_eq!(
                coarse.character_phase(&low.lock, &BigInt::one()).unwrap(),
                fine.character_phase(&high.lock, &BigInt::from(3)).unwrap()
            );
        }
        let mut changed = declaration(&[2, 4, 3], &[vec![1], vec![1], vec![0]]);
        changed.rings[0].initial = 1;
        let changed = FieldSolenoid::from_field(&Field::declare(changed).unwrap()).unwrap();
        assert!(matches!(
            coarse.restrict_face(&changed, &high[0].lock),
            Err(FieldPhaseError::NotATopExtension)
        ));
        assert!(fine.restrict_face(&coarse, &low[0].lock).is_err());
    }

    #[test]
    fn finite_equal_faces_keep_distinct_actual_lifts_and_signed_exact_characters() {
        let field = field();
        let chart = FieldSolenoid::from_field(&field).unwrap();
        let left = chart
            .key_phase(&field, &[1.into(), 2.into(), 1.into()])
            .unwrap();
        let right = chart
            .key_phase(&field, &[1.into(), 2.into(), 7.into()])
            .unwrap();
        assert_eq!(left.lock.value, BigUint::from(13u32));
        assert_eq!(left.lock.value, right.lock.value);
        assert_eq!(right.lock.lift - left.lock.lift.clone(), BigInt::from(48));
        assert_eq!(
            chart
                .character_phase(&left.lock, &BigInt::from(-1))
                .unwrap(),
            rat(11, 24)
        );
        assert_eq!(
            chart
                .character_phase(&left.lock, &BigInt::from(24))
                .unwrap(),
            Rat::zero()
        );
    }

    #[test]
    fn invalid_classes_keys_stale_fields_and_occurrences_are_typed_and_atomic() {
        let field = field();
        let chart = FieldSolenoid::from_field(&field).unwrap();
        assert!(chart.key_phase(&field, &[0.into()]).is_err());
        assert!(
            chart
                .key_phase(&field, &[0.into(), (-1).into(), 0.into()])
                .is_err()
        );
        assert!(
            chart
                .phase_path(&field, &[0.into(), 0.into(), 0.into()], &[2])
                .is_err()
        );
        assert!(chart.class_increment(&field, 2).is_err());
        let mixed = field.found(FoundedRing { period: 2, key: 0 }).unwrap();
        assert!(matches!(
            chart.phase(&mixed, &Current::at_rest(&mixed)),
            Err(FieldPhaseError::DifferentField)
        ));
        let mut current = Current::at_rest(&field);
        let before = current.clone();
        assert!(
            chart
                .step(&field, &mut current, &encoded(&field, &[0]), 1)
                .is_err()
        );
        assert_eq!(current, before);
        let mut invalid = chart.phase(&field, &current).unwrap().lock;
        invalid.value += BigUint::one();
        assert!(chart.character_phase(&invalid, &BigInt::one()).is_err());
    }
}

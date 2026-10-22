//! Per-node half-turn cover readings of the actual pumped ring (J3; Refs #62 #73).
//!
//! [definition; agent-inferred] At base phase `tau < d`, a node whose actual displacement
//! has sheet `s` reads `tau + d*s` in the two-element fibre over `tau` modulo `d`.
//! [`crate::hnn::ring::sheets`] is the sole owner of the half-turn threshold. Every node's
//! bit is retained in this observation. Zero in-phase projection (including a pure quadrature
//! displacement) keeps both fibre digits, alongside the owner's deterministic bit at zero.
//! A uniform resolved projection permits a single instantaneous sheet reading; no majority,
//! attracting-domain certificate, or period theorem is inferred from it.
//!
//! This reads the actual declared material and the field's actual base clock. The half-turn
//! digit is observed, never advanced or passed as carry. `None` and strength-zero pumps expose
//! only the base phase. Scheduled operands are a typed refusal until an actual schedule-axis
//! witness is supplied: the material's reference axis need not be the executed schedule's axis.
//!
//! [scope] The reconstructed step-1a locking pump is standing, with a saturated period-one
//! fixed sheet. It does not establish a subharmonic orbit of period `2d`. This finite fibre
//! reading supplies the local cover observation; a compatible actual phase evolution and any
//! subharmonic period/attractor proof remain owed in #62. The controls consume executed
//! [`ResonatorOperands::step`] states, including this period-one counterexample. No new
//! dynamics, event archive, or learned-output capability is introduced.

use num_bigint::BigUint;
use num_traits::Zero;
use thiserror::Error;

use crate::hnn::HnnError;
use crate::hnn::field::{Current, Field};
use crate::hnn::ring::{ResonatorOperands, sheets};
use crate::holon::parametron::Carrier;
use crate::ratio::Rat;

/// A refused read, with the missing operand or incompatible shape named.
#[derive(Debug, Error)]
pub enum PumpCoverError {
    #[error(transparent)]
    Hnn(Box<HnnError>),
    #[error("ring {ring} is outside the field's {rings} rings")]
    RingOutside { ring: usize, rings: usize },
    #[error("{what}: expected {expected} coordinates, found {found}")]
    Shape {
        what: &'static str,
        expected: usize,
        found: usize,
    },
    #[error("the actual pump axis or strength is invalid")]
    InvalidPump,
    #[error("an exact displacement or pump coordinate has a zero denominator")]
    InvalidRational,
    #[error("scheduled pump operands need an actual schedule-axis witness")]
    ScheduledAxisWitnessOwed,
}

impl From<HnnError> for PumpCoverError {
    fn from(error: HnnError) -> Self {
        Self::Hnn(Box::new(error))
    }
}

/// Both digits are retained when an actual projection does not resolve the half-turn sheet.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SheetFibre {
    Resolved { digit: BigUint },
    Unresolved { digits: [BigUint; 2] },
}

/// A node's actual sheet bit and its exact projection in the declared pump-axis frame.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NodeCover {
    pub node: usize,
    pub owner_sheet: bool,
    pub in_phase: Rat,
    pub quadrature: Rat,
    pub fibre: SheetFibre,
}

/// A finite two-element fibre at every node. `modulus = 2*base_period` describes the cover
/// labels, not an observed dynamical recurrence period. The factors remain explicit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PumpCover {
    pub base_period: u64,
    pub degree: u64,
    pub modulus: BigUint,
    pub axis: Carrier,
    pub nodes: Vec<NodeCover>,
}

impl PumpCover {
    /// A single sheet only when every actual node projection is nonzero and agrees. This is an
    /// instantaneous projection witness; it claims neither a lock ball nor future persistence.
    pub fn uniform_resolved_sheet(&self) -> Option<bool> {
        let first = self.nodes.first()?;
        self.nodes
            .iter()
            .all(|node| !node.in_phase.is_zero() && node.owner_sheet == first.owner_sheet)
            .then_some(first.owner_sheet)
    }

    pub fn owner_sheets(&self) -> Vec<bool> {
        self.nodes.iter().map(|node| node.owner_sheet).collect()
    }
}

/// A read of the base clock plus the optional per-node cover fibre. The base clock is always
/// retained and is unchanged by mounting/removing a pump or by an unresolved sheet.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PumpCoverReading {
    pub ring: usize,
    pub base_period: u64,
    pub base_phase: u64,
    pub cover: Option<PumpCover>,
}

impl PumpCoverReading {
    /// Read the actual ring and material of the executed operands. No separate requested axis,
    /// guessed sheet, nominal pump flag, or arbitrary base period can override these operands.
    pub fn read(
        field: &Field,
        current: &Current,
        operands: &ResonatorOperands,
        displacement: &[Rat],
    ) -> Result<Self, PumpCoverError> {
        let ring = operands.ring();
        let declared = field.rings().get(ring).ok_or(PumpCoverError::RingOutside {
            ring,
            rings: field.rings().len(),
        })?;
        if current.lift().len() != field.rings().len() {
            return Err(PumpCoverError::Shape {
                what: "the actual field current",
                expected: field.rings().len(),
                found: current.lift().len(),
            });
        }
        let width = declared.width();
        for (what, found) in [
            ("the actual resonator material", operands.width()),
            ("the actual displacement", displacement.len()),
        ] {
            if found != width {
                return Err(PumpCoverError::Shape {
                    what,
                    expected: width,
                    found,
                });
            }
        }
        if displacement.iter().any(|x| x.denom().is_zero()) {
            return Err(PumpCoverError::InvalidRational);
        }
        let base_period = declared.period();
        let base_phase = current.phase(field, ring)?;
        // Current::phase delegates the period/range check to the ring's navigator clock.
        let mut reading = Self {
            ring,
            base_period,
            base_phase,
            cover: None,
        };
        if operands.schedule().is_some() {
            return Err(PumpCoverError::ScheduledAxisWitnessOwed);
        }
        let Some(pump) = operands.material().pump() else {
            return Ok(reading);
        };
        let axis = pump.axis();
        if [pump.strength(), axis.cos(), axis.sin()]
            .iter()
            .any(|x| x.denom().is_zero())
        {
            return Err(PumpCoverError::InvalidRational);
        }
        if pump.strength() < &Rat::zero()
            || Carrier::new(axis.cos().clone(), axis.sin().clone()).is_err()
        {
            return Err(PumpCoverError::InvalidPump);
        }
        if pump.strength().is_zero() {
            return Ok(reading);
        }
        let bits = sheets(displacement, axis);
        let base = BigUint::from(base_phase);
        let far = &base + BigUint::from(base_period);
        let nodes = displacement
            .chunks_exact(2)
            .zip(bits)
            .enumerate()
            .map(|(node, (xy, owner_sheet))| {
                let in_phase = &xy[0] * axis.cos() + &xy[1] * axis.sin();
                let quadrature = &xy[1] * axis.cos() - &xy[0] * axis.sin();
                let fibre = if in_phase.is_zero() {
                    SheetFibre::Unresolved {
                        digits: [base.clone(), far.clone()],
                    }
                } else {
                    SheetFibre::Resolved {
                        digit: if owner_sheet {
                            far.clone()
                        } else {
                            base.clone()
                        },
                    }
                };
                NodeCover {
                    node,
                    owner_sheet,
                    in_phase,
                    quadrature,
                    fibre,
                }
            })
            .collect();
        reading.cover = Some(PumpCover {
            base_period,
            degree: 2,
            modulus: BigUint::from(2u8) * BigUint::from(base_period),
            axis: axis.clone(),
            nodes,
        });
        Ok(reading)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::field::{FieldDeclaration, RingDeclaration};
    use crate::hnn::ring::{
        PumpDeclaration, PumpSchedule, PumpStep, ResonatorMaterial, ResonatorRemainders,
    };
    use crate::ratio::linear::ExactRatMatrix;
    use crate::ratio::{integer, rat};
    use num_bigint::BigInt;
    use num_traits::One;

    fn field() -> Field {
        let mut declaration = FieldDeclaration::campaign_one(1 << 17);
        let old = declaration.rings[0].clone();
        declaration.rings = vec![RingDeclaration {
            period: 2,
            screw: old.screw,
            placements: (0..2)
                .map(|node| FieldDeclaration::quarter_turn(node, 2))
                .collect(),
            lock: vec![0],
            reflector: vec![0, 1],
            admittance: integer(2),
            initial: 0,
        }];
        declaration.contacts.clear();
        declaration.loops.clear();
        declaration.alphabet = 2;
        declaration.receivers[0].ring = 0;
        declaration.receivers[0].aperture = 1;
        declaration.receivers[0].depth = 1;
        Field::declare(declaration.by_lattice_rule()).unwrap()
    }

    fn pump(strength: Rat, axis: Carrier, step: PumpStep) -> PumpDeclaration {
        PumpDeclaration::new(strength, axis, step).unwrap()
    }

    fn material(pump: Option<PumpDeclaration>) -> ResonatorMaterial {
        ResonatorMaterial::new(
            ExactRatMatrix::identity(4).unwrap(),
            ExactRatMatrix::identity(4).unwrap(),
            ExactRatMatrix::zero(4, 4).unwrap(),
            pump,
        )
        .unwrap()
    }

    fn operands(material: &ResonatorMaterial) -> ResonatorOperands {
        ResonatorOperands::at_cut(0, material, &integer(2), &Rat::one(), None).unwrap()
    }

    fn check_nodes(reading: &PumpCoverReading, displacement: &[Rat], axis: &Carrier) {
        let cover = reading.cover.as_ref().unwrap();
        assert_eq!(cover.owner_sheets(), sheets(displacement, axis));
        assert_eq!(cover.nodes.len(), reading.base_period as usize);
        for node in &cover.nodes {
            let digits = match &node.fibre {
                SheetFibre::Resolved { digit } => vec![digit.clone()],
                SheetFibre::Unresolved { digits } => digits.to_vec(),
            };
            for digit in digits {
                assert_eq!(
                    &digit % BigUint::from(reading.base_period),
                    BigUint::from(reading.base_phase)
                );
                assert!(digit < cover.modulus);
            }
        }
    }

    #[test]
    fn actual_executed_states_read_every_node_at_every_declared_pump_phase() {
        let field = field();
        let axis = Carrier::at(&rat(1, 2));
        let owner = operands(&material(Some(pump(
            rat(1, 8),
            axis.clone(),
            PumpStep::Quarter,
        ))));
        let mut current = Current::at(&field, vec![BigInt::one()]).unwrap();
        let mut state = [
            vec![integer(1), integer(2), integer(-2), integer(1)],
            vec![Rat::zero(); 4],
        ];
        let mut remainder = ResonatorRemainders::default();
        for tick in 0..owner.phases() {
            let reading = PumpCoverReading::read(&field, &current, &owner, &state[0]).unwrap();
            check_nodes(&reading, &state[0], &axis);
            let step = owner
                .step(
                    tick,
                    &vec![Rat::zero(); 4],
                    [&state[0], &state[1]],
                    &remainder,
                    None,
                )
                .unwrap();
            assert!(step.closes());
            assert_eq!(step.phase, owner.phase_at(tick));
            remainder = step.remainders().clone();
            state = step.state;
            // The base clock remains the actual field owner, never a sheet carry.
            let mut lift = current.lift().to_vec();
            field.step_class(&mut lift, 0, None).unwrap();
            current = Current::at(&field, lift).unwrap();
            check_nodes(
                &PumpCoverReading::read(&field, &current, &owner, &state[0]).unwrap(),
                &state[0],
                &axis,
            );
        }
    }

    #[test]
    fn standing_saturated_fixed_sheets_are_period_one_without_invented_period_doubling() {
        let field = field();
        let axis = Carrier::sheet(false);
        // K_eff along the in-phase axis is 1-2p=-1, and beta=1 fixes amplitudes +/-1.
        let material = material(Some(pump(Rat::one(), axis.clone(), PumpStep::Stand)))
            .with_symmetric_saturation(Rat::one())
            .unwrap();
        let owner = operands(&material);
        assert_eq!(owner.phases(), 1);
        let current = Current::at_rest(&field);
        let state = [
            vec![Rat::one(), Rat::zero(), -Rat::one(), Rat::zero()],
            vec![Rat::zero(); 4],
        ];
        let step = owner
            .step(
                0,
                &vec![Rat::zero(); 4],
                [&state[0], &state[1]],
                &ResonatorRemainders::default(),
                None,
            )
            .unwrap();
        assert!(step.closes());
        assert_eq!(
            step.state, state,
            "the actual state closes after the one-tick standing period"
        );
        let before = PumpCoverReading::read(&field, &current, &owner, &state[0]).unwrap();
        let after = PumpCoverReading::read(&field, &current, &owner, &step.state[0]).unwrap();
        assert_eq!(before, after);
        assert_eq!(
            before.cover.as_ref().unwrap().owner_sheets(),
            vec![false, true]
        );
        assert_eq!(
            before.cover.as_ref().unwrap().uniform_resolved_sheet(),
            None
        );
        check_nodes(&after, &step.state[0], &axis);
    }

    #[test]
    fn zero_and_quadrature_keep_both_fibre_digits_and_the_actual_threshold_bit() {
        let field = field();
        let axis = Carrier::at(&rat(1, 2));
        let owner = operands(&material(Some(pump(
            rat(1, 8),
            axis.clone(),
            PumpStep::Stand,
        ))));
        let current = Current::at(&field, vec![BigInt::from(3)]).unwrap();
        let displacement = vec![
            Rat::zero(),
            Rat::zero(),
            -axis.sin().clone(),
            axis.cos().clone(),
        ];
        let reading = PumpCoverReading::read(&field, &current, &owner, &displacement).unwrap();
        let cover = reading.cover.as_ref().unwrap();
        assert_eq!(cover.owner_sheets(), sheets(&displacement, &axis));
        assert_eq!(cover.uniform_resolved_sheet(), None);
        for node in &cover.nodes {
            assert!(node.in_phase.is_zero());
            assert_eq!(
                node.fibre,
                SheetFibre::Unresolved {
                    digits: [BigUint::from(1u8), BigUint::from(3u8)]
                }
            );
        }
        assert_eq!(cover.nodes[1].quadrature, Rat::one());
        let uniform = (0..2)
            .flat_map(|_| [axis.cos().clone(), axis.sin().clone()])
            .collect::<Vec<_>>();
        let reading = PumpCoverReading::read(&field, &current, &owner, &uniform).unwrap();
        assert_eq!(reading.cover.unwrap().uniform_resolved_sheet(), Some(false));
    }

    #[test]
    fn removed_or_zero_strength_pump_has_only_the_unchanged_base_phase() {
        let field = field();
        let current = Current::at(&field, vec![BigInt::from(7)]).unwrap();
        let displacement = vec![Rat::one(), Rat::zero(), -Rat::one(), Rat::zero()];
        for pump in [
            None,
            Some(pump(Rat::zero(), Carrier::sheet(true), PumpStep::Stand)),
        ] {
            let owner = operands(&material(pump));
            let reading = PumpCoverReading::read(&field, &current, &owner, &displacement).unwrap();
            assert_eq!(reading.base_phase, 1);
            assert_eq!(reading.base_period, 2);
            assert!(reading.cover.is_none());
            let quiet = vec![Rat::zero(); 4];
            let step = owner
                .step(
                    0,
                    &quiet,
                    [&displacement, &quiet],
                    &ResonatorRemainders::default(),
                    None,
                )
                .unwrap();
            assert!(step.closes());
            let after = PumpCoverReading::read(&field, &current, &owner, &step.state[0]).unwrap();
            assert_eq!(after.base_phase, reading.base_phase);
            assert!(after.cover.is_none());
        }
    }

    #[test]
    fn incompatible_current_displacement_material_and_scheduled_axis_are_refused() {
        let field = field();
        let current = Current::at_rest(&field);
        let base = material(Some(pump(
            rat(1, 8),
            Carrier::sheet(false),
            PumpStep::Quarter,
        )));
        let owner = operands(&base);
        assert!(PumpCoverReading::read(&field, &current, &owner, &vec![Rat::zero(); 3]).is_err());
        let invalid = vec![Rat::new_raw(BigInt::one(), BigInt::zero()); 4];
        assert!(matches!(
            PumpCoverReading::read(&field, &current, &owner, &invalid),
            Err(PumpCoverError::InvalidRational)
        ));
        let mut stale = current.clone();
        stale.found_ring(0);
        assert!(PumpCoverReading::read(&field, &stale, &owner, &vec![Rat::zero(); 4]).is_err());
        let wrong = ResonatorOperands::at_cut(1, &base, &integer(2), &Rat::one(), None).unwrap();
        assert!(matches!(
            PumpCoverReading::read(&field, &current, &wrong, &vec![Rat::zero(); 4]),
            Err(PumpCoverError::RingOutside { .. })
        ));
        let wrong_width = ResonatorMaterial::new(
            ExactRatMatrix::identity(2).unwrap(),
            ExactRatMatrix::identity(2).unwrap(),
            ExactRatMatrix::zero(2, 2).unwrap(),
            None,
        )
        .unwrap();
        assert!(matches!(
            PumpCoverReading::read(
                &field,
                &current,
                &operands(&wrong_width),
                &vec![Rat::zero(); 4]
            ),
            Err(PumpCoverError::Shape {
                what: "the actual resonator material",
                ..
            })
        ));
        let schedule = PumpSchedule::declared(base.pump().unwrap());
        let unpumped = material(None);
        let scheduled =
            ResonatorOperands::scheduled(0, &unpumped, &schedule, &integer(2), &Rat::one(), None)
                .unwrap();
        assert!(matches!(
            PumpCoverReading::read(&field, &current, &scheduled, &vec![Rat::zero(); 4]),
            Err(PumpCoverError::ScheduledAxisWitnessOwed)
        ));
    }
}

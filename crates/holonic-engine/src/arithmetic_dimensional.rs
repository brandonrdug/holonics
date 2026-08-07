//! Growing exact dimensional receiver source for the counting ecology.
//!
//! [`ArithmeticFiberStanding`] already owns multiplication-founded primes,
//! squarefree incidence, valuation multiplicity, recognition fibers, and the
//! formal prime-power current.  This module does not rebuild or label that
//! arithmetic.  It gives the standing an exact coordinate mouth suitable for
//! [`crate::DimensionalReceiverAtlas`].
//!
//! Each integer occurrence carries four affine receiver coordinates and one
//! exact unit-conic phase for every factor axis admitted by its contemporary
//! square-root horizon.  The phase population therefore grows at actual
//! prime-square walls.  A point before a wall genuinely lacks the later
//! coordinate; it is not padded with zero.  Products of these conics are the
//! finite-place toroidal body whose two-dimensional receiver sections can be
//! inspected without promoting their projection to arithmetic incidence.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    ArithmeticFiberError, ArithmeticFiberStanding, CoordinateCarrierId, CoordinateCarrierKind,
    CoordinateGermId, DimensionalAxis, DimensionalAxisId, DimensionalReceiverError,
    DimensionalWaveCarrierDoctrine, DimensionalWaveError, DimensionalWaveImpulse,
    DimensionalWaveMode, DimensionalWaveModeId, EventId, ExactComplexAxisPair,
    ExactComplexWaveCurrent, ExactCoordinateCarrier, ExactCoordinateGerm, ExactDimensionalSource,
    ExactDimensionalWaveLaw, ExactSliceCovector, PrimePowerCurrentEvent, PrimeRecognitionClosure,
    PrimeValuation,
};

pub const ARITHMETIC_COUNT_AXIS: DimensionalAxisId = DimensionalAxisId(1);
pub const ARITHMETIC_RECOGNITION_DEPTH_AXIS: DimensionalAxisId = DimensionalAxisId(2);
pub const ARITHMETIC_VALUATION_MASS_AXIS: DimensionalAxisId = DimensionalAxisId(3);
pub const ARITHMETIC_SUPPORT_GRADE_AXIS: DimensionalAxisId = DimensionalAxisId(4);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArithmeticPhaseAxes {
    pub prime: u64,
    pub real: DimensionalAxisId,
    pub imaginary: DimensionalAxisId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArithmeticDimensionalOccurrence {
    pub value: u64,
    pub germ: CoordinateGermId,
    pub valuation: Vec<PrimeValuation>,
    pub squarefree_support: Vec<u64>,
    pub recognition_depth: u64,
    pub factor_horizon: Vec<u64>,
    pub irreducible: bool,
    pub prime_power: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArithmeticAxisCurrent {
    pub axis: DimensionalAxisId,
    pub before: Option<Rat>,
    pub after: Option<Rat>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ArithmeticDimensionalFrontKind {
    /// A prime axis becomes capable of receiving the candidate at its first
    /// square-root horizon. The prime identity existed earlier; this is the
    /// caused rank admission, not a second prime founding.
    RankAdmission {
        prime: u64,
        real: DimensionalAxisId,
        imaginary: DimensionalAxisId,
    },
    OccurrenceEmission,
    ChronologyCarry {
        carrier: CoordinateCarrierId,
    },
    ProbeLeader {
        prime: u64,
        quotient: u64,
        carrier: CoordinateCarrierId,
    },
    ProbeReturn {
        prime: u64,
        quotient: u64,
        remainder: u64,
        carrier: CoordinateCarrierId,
    },
    RecognitionClosure {
        closure: PrimeRecognitionClosure,
    },
    PrimeFounding {
        prime: u64,
        cell: crate::CausalCellId,
    },
    BoundaryIncidence {
        carrier: CoordinateCarrierId,
    },
    PhaseReturn {
        prime: u64,
        carrier: CoordinateCarrierId,
    },
    PrimePowerCurrent {
        event: PrimePowerCurrentEvent,
    },
    Rest,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArithmeticDimensionalFront {
    pub ordinal: u64,
    pub event: EventId,
    pub value: u64,
    pub kind: ArithmeticDimensionalFrontKind,
    pub active_germs: BTreeSet<CoordinateGermId>,
    pub active_carriers: BTreeSet<CoordinateCarrierId>,
    /// Exact coordinate departure carried by the occurrence. Missing-before
    /// coordinates remain explicit rank births rather than zero values.
    pub coordinate_current: Vec<ArithmeticAxisCurrent>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArithmeticDimensionalWave {
    pub event: EventId,
    pub value: u64,
    pub causal_horizon_after: BTreeSet<EventId>,
    pub fronts: Vec<ArithmeticDimensionalFront>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArithmeticDimensionalHistory {
    pub schema: String,
    pub through: u64,
    pub waves: Vec<ArithmeticDimensionalWave>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArithmeticDimensionalMount {
    pub schema: String,
    pub through: u64,
    pub source: ExactDimensionalSource,
    pub phase_axes: BTreeMap<u64, ArithmeticPhaseAxes>,
    pub occurrences: BTreeMap<u64, ArithmeticDimensionalOccurrence>,
    pub chronology_carriers: BTreeSet<CoordinateCarrierId>,
    pub boundary_carriers: BTreeSet<CoordinateCarrierId>,
    pub phase_return_carriers: BTreeSet<CoordinateCarrierId>,
    pub probe_carriers: BTreeMap<(u64, u64), CoordinateCarrierId>,
    pub chronology_by_value: BTreeMap<u64, CoordinateCarrierId>,
    pub boundary_by_event: BTreeMap<EventId, Vec<CoordinateCarrierId>>,
    pub phase_returns_by_value: BTreeMap<u64, Vec<(u64, CoordinateCarrierId)>>,
    pub history: ArithmeticDimensionalHistory,
}

impl ArithmeticDimensionalMount {
    pub fn mount(standing: &ArithmeticFiberStanding) -> Result<Self, ArithmeticDimensionalError> {
        standing.validate()?;
        if standing.value < 2 {
            return Err(ArithmeticDimensionalError::EmptyCountingEcology);
        }
        let first_event = standing.occurrences()[&2].event;
        let mut axes = vec![
            DimensionalAxis::new(
                ARITHMETIC_COUNT_AXIS,
                "count chronology",
                BTreeSet::from([first_event]),
            )?,
            DimensionalAxis::new(
                ARITHMETIC_RECOGNITION_DEPTH_AXIS,
                "prime recognition closure depth",
                BTreeSet::from([first_event]),
            )?,
            DimensionalAxis::new(
                ARITHMETIC_VALUATION_MASS_AXIS,
                "valuation multiplicity mass",
                BTreeSet::from([first_event]),
            )?,
            DimensionalAxis::new(
                ARITHMETIC_SUPPORT_GRADE_AXIS,
                "squarefree support grade",
                BTreeSet::from([first_event]),
            )?,
        ];
        let factor_axes = standing
            .recognitions()
            .values()
            .flat_map(|trace| trace.initial_fiber.unreturned_factor_axes.iter().copied())
            .collect::<BTreeSet<_>>();
        let mut phase_axes = BTreeMap::new();
        let mut complex_pairs = Vec::new();
        for prime in factor_axes {
            let pair = phase_axis_ids(prime)?;
            let source_event = standing
                .occurrences()
                .get(&prime)
                .ok_or(ArithmeticDimensionalError::MissingPrimeAxisOccurrence(
                    prime,
                ))?
                .event;
            axes.push(DimensionalAxis::new(
                pair.real,
                format!("residue phase {prime} real"),
                BTreeSet::from([source_event]),
            )?);
            axes.push(DimensionalAxis::new(
                pair.imaginary,
                format!("residue phase {prime} imaginary"),
                BTreeSet::from([source_event]),
            )?);
            complex_pairs.push(ExactComplexAxisPair {
                real: pair.real,
                imaginary: pair.imaginary,
                unit_conic: true,
            });
            phase_axes.insert(prime, pair);
        }

        let mut occurrences = BTreeMap::new();
        let mut germs = Vec::with_capacity(standing.occurrences().len());
        for (value, occurrence) in standing.occurrences() {
            let recognition = &standing.recognitions()[value];
            let factor_horizon = recognition.initial_fiber.unreturned_factor_axes.clone();
            let valuation_mass = occurrence
                .valuation
                .iter()
                .try_fold(0_u64, |sum, factor| {
                    sum.checked_add(u64::from(factor.exponent))
                })
                .ok_or(ArithmeticDimensionalError::CarrierOverflow)?;
            let support_grade = occurrence
                .squarefree_support
                .len()
                .checked_sub(1)
                .ok_or(ArithmeticDimensionalError::CarrierOverflow)?;
            let mut coordinates = BTreeMap::from([
                (ARITHMETIC_COUNT_AXIS, integer_rat(*value)),
                (
                    ARITHMETIC_RECOGNITION_DEPTH_AXIS,
                    integer_rat(recognition.bounds.certificate_probe_upper_bound),
                ),
                (ARITHMETIC_VALUATION_MASS_AXIS, integer_rat(valuation_mass)),
                (
                    ARITHMETIC_SUPPORT_GRADE_AXIS,
                    integer_rat(
                        u64::try_from(support_grade)
                            .map_err(|_| ArithmeticDimensionalError::CarrierOverflow)?,
                    ),
                ),
            ]);
            for prime in &factor_horizon {
                let pair = phase_axes
                    .get(prime)
                    .ok_or(ArithmeticDimensionalError::MissingPrimePhaseAxes(*prime))?;
                let (real, imaginary) = exact_residue_conic_phase(*value % *prime, *prime)?;
                coordinates.insert(pair.real, real);
                coordinates.insert(pair.imaginary, imaginary);
            }
            let germ = CoordinateGermId(*value);
            germs.push(ExactCoordinateGerm {
                id: germ,
                name: format!("integer occurrence {value}"),
                source_cell: occurrence.support_cell,
                source_events: BTreeSet::from([occurrence.event]),
                coordinates,
            });
            occurrences.insert(
                *value,
                ArithmeticDimensionalOccurrence {
                    value: *value,
                    germ,
                    valuation: occurrence.valuation.clone(),
                    squarefree_support: occurrence.squarefree_support.clone(),
                    recognition_depth: recognition.bounds.certificate_probe_upper_bound,
                    factor_horizon,
                    irreducible: matches!(
                        recognition.closure,
                        PrimeRecognitionClosure::Irreducible { .. }
                    ),
                    prime_power: occurrence.valuation.len() == 1,
                },
            );
        }

        let event_germs = standing
            .occurrences()
            .values()
            .map(|occurrence| (occurrence.event, CoordinateGermId(occurrence.value)))
            .collect::<BTreeMap<_, _>>();
        let mut carriers = Vec::new();
        let mut chronology_carriers = BTreeSet::new();
        let mut boundary_carriers = BTreeSet::new();
        let mut phase_return_carriers = BTreeSet::new();
        let mut probe_carriers = BTreeMap::new();
        let mut chronology_by_value = BTreeMap::new();
        let mut boundary_by_event = BTreeMap::<EventId, Vec<CoordinateCarrierId>>::new();
        let mut phase_returns_by_value = BTreeMap::<u64, Vec<(u64, CoordinateCarrierId)>>::new();
        let mut next_carrier = 1_u64;
        let mut mint_carrier =
            |name: String, from: CoordinateGermId, to: CoordinateGermId, source_events, kind| {
                let id = CoordinateCarrierId(next_carrier);
                next_carrier = next_carrier
                    .checked_add(1)
                    .ok_or(ArithmeticDimensionalError::CarrierOverflow)?;
                carriers.push(ExactCoordinateCarrier {
                    id,
                    name,
                    from,
                    to,
                    source_events,
                    kind,
                });
                Ok::<CoordinateCarrierId, ArithmeticDimensionalError>(id)
            };

        for value in 3..=standing.value {
            let before = CoordinateGermId(value - 1);
            let after = CoordinateGermId(value);
            let source_events = BTreeSet::from([
                standing.occurrences()[&(value - 1)].event,
                standing.occurrences()[&value].event,
            ]);
            let chronology = mint_carrier(
                format!("count chronology {} -> {}", value - 1, value),
                before,
                after,
                source_events.clone(),
                CoordinateCarrierKind::Chronology,
            )?;
            chronology_carriers.insert(chronology);
            chronology_by_value.insert(value, chronology);
            for prime in &occurrences[&value].factor_horizon {
                if value.is_multiple_of(*prime)
                    && occurrences[&(value - 1)].factor_horizon.contains(prime)
                {
                    let carrier = mint_carrier(
                        format!("residue phase {prime} return at {value}"),
                        before,
                        after,
                        source_events.clone(),
                        CoordinateCarrierKind::PhaseReturn {
                            axis: phase_axes[prime].real,
                        },
                    )?;
                    phase_return_carriers.insert(carrier);
                    phase_returns_by_value
                        .entry(value)
                        .or_default()
                        .push((*prime, carrier));
                }
            }
        }

        for (value, recognition) in standing.recognitions() {
            let candidate = CoordinateGermId(*value);
            let candidate_event = standing.occurrences()[value].event;
            for step in &recognition.steps {
                let prime = step.probe.prime_axis;
                let prime_germ = CoordinateGermId(prime);
                let prime_event = standing.occurrences()[&prime].event;
                let carrier = mint_carrier(
                    format!("candidate {value} probes factor axis {prime}"),
                    candidate,
                    prime_germ,
                    BTreeSet::from([prime_event, candidate_event]),
                    CoordinateCarrierKind::Interaction {
                        doctrine: "ordered multiplication receiver probe".to_owned(),
                    },
                )?;
                if probe_carriers.insert((*value, prime), carrier).is_some() {
                    return Err(ArithmeticDimensionalError::MalformedMount);
                }
            }
        }

        for higher in standing.incidence().cells().values() {
            let higher_event = *higher
                .source_events
                .iter()
                .next()
                .ok_or(ArithmeticDimensionalError::MissingCellOccurrence(higher.id))?;
            let higher_germ = *event_germs
                .get(&higher_event)
                .ok_or(ArithmeticDimensionalError::MissingCellOccurrence(higher.id))?;
            for (lower, coefficient) in higher.boundary.coefficients() {
                let lower_body = standing.incidence().cell(*lower)?;
                let lower_event = *lower_body
                    .source_events
                    .iter()
                    .next()
                    .ok_or(ArithmeticDimensionalError::MissingCellOccurrence(*lower))?;
                let lower_germ = *event_germs
                    .get(&lower_event)
                    .ok_or(ArithmeticDimensionalError::MissingCellOccurrence(*lower))?;
                let carrier = mint_carrier(
                    format!("oriented boundary {:?} -> {:?}", higher.id, lower),
                    higher_germ,
                    lower_germ,
                    higher.source_events.clone(),
                    CoordinateCarrierKind::Boundary {
                        higher: higher.id,
                        lower: *lower,
                        coefficient: coefficient.clone(),
                    },
                )?;
                boundary_carriers.insert(carrier);
                boundary_by_event
                    .entry(higher_event)
                    .or_default()
                    .push(carrier);
            }
        }

        let source = ExactDimensionalSource::new(
            standing.incidence().clone(),
            axes,
            complex_pairs,
            germs,
            carriers,
        )?;
        let mut result = Self {
            schema: "holonic-engine.arithmetic-dimensional-mount.v2".to_owned(),
            through: standing.value,
            source,
            phase_axes,
            occurrences,
            chronology_carriers,
            boundary_carriers,
            phase_return_carriers,
            probe_carriers,
            chronology_by_value,
            boundary_by_event,
            phase_returns_by_value,
            history: ArithmeticDimensionalHistory {
                schema: "holonic-engine.arithmetic-dimensional-history.v1".to_owned(),
                through: standing.value,
                waves: Vec::new(),
            },
        };
        result.history = ArithmeticDimensionalHistory::derive(&result, standing)?;
        result.validate()?;
        Ok(result)
    }

    pub fn phase_product_covectors(
        &self,
        first_prime: u64,
        second_prime: u64,
    ) -> Result<(ExactSliceCovector, ExactSliceCovector), ArithmeticDimensionalError> {
        if first_prime == second_prime {
            return Err(ArithmeticDimensionalError::RepeatedProjectionPrime(
                first_prime,
            ));
        }
        let first = self.phase_axes.get(&first_prime).ok_or(
            ArithmeticDimensionalError::MissingPrimePhaseAxes(first_prime),
        )?;
        let second = self.phase_axes.get(&second_prime).ok_or(
            ArithmeticDimensionalError::MissingPrimePhaseAxes(second_prime),
        )?;
        let third = Rat::new(BigInt::one(), BigInt::from(3));
        Ok((
            ExactSliceCovector::new(BTreeMap::from([
                (first.real, Rat::one()),
                (second.real, third.clone()),
            ]))?,
            ExactSliceCovector::new(BTreeMap::from([
                (first.imaginary, Rat::one()),
                (second.imaginary, third),
            ]))?,
        ))
    }

    /// Realize every currently transport-capable finite-place phase as one
    /// simultaneous exact lossless wave mode.
    ///
    /// The application declares one common carrier delay so receiver charts
    /// can compare apparent displacement without silently changing source
    /// cadence. Boundary admittance is its exact incidence multiplicity;
    /// every other admitted carrier has the unit current of its declaration.
    pub fn exact_phase_wave_law(
        &self,
        carrier_delay: u32,
    ) -> Result<ExactDimensionalWaveLaw, ArithmeticDimensionalError> {
        self.exact_phase_wave_law_through(carrier_delay, self.through)
    }

    /// Restrict the physical wave ecology to an exact caused counting
    /// horizon while leaving the complete dimensional source available to
    /// other receivers. The horizon is an application section, not a locus
    /// ceiling: a later remount may lawfully admit more caused carriers.
    pub fn exact_phase_wave_law_through(
        &self,
        carrier_delay: u32,
        through: u64,
    ) -> Result<ExactDimensionalWaveLaw, ArithmeticDimensionalError> {
        if carrier_delay == 0 {
            return Err(ArithmeticDimensionalError::ZeroWaveDelay);
        }
        if !(4..=self.through).contains(&through) {
            return Err(ArithmeticDimensionalError::InvalidWaveHorizon {
                supplied: through,
                source_through: self.through,
            });
        }
        let admitted_carriers = self
            .source
            .carriers()
            .values()
            .filter(|carrier| carrier.from.0 <= through && carrier.to.0 <= through)
            .collect::<Vec<_>>();
        let modes = self
            .phase_axes
            .values()
            .filter(|pair| {
                admitted_carriers.iter().any(|carrier| {
                    let from = &self.source.germs()[&carrier.from].coordinates;
                    let to = &self.source.germs()[&carrier.to].coordinates;
                    from.contains_key(&pair.real)
                        && from.contains_key(&pair.imaginary)
                        && to.contains_key(&pair.real)
                        && to.contains_key(&pair.imaginary)
                })
            })
            .map(|pair| DimensionalWaveMode {
                id: DimensionalWaveModeId(pair.prime),
                name: format!("finite-place phase {}", pair.prime),
                real_axis: pair.real,
                imaginary_axis: pair.imaginary,
            })
            .collect::<Vec<_>>();
        let doctrines = admitted_carriers
            .into_iter()
            .map(|carrier| {
                let admittance = match &carrier.kind {
                    CoordinateCarrierKind::Boundary { coefficient, .. } => {
                        Rat::from_integer(coefficient.difference().abs())
                    }
                    CoordinateCarrierKind::Chronology
                    | CoordinateCarrierKind::PhaseReturn { .. }
                    | CoordinateCarrierKind::Interaction { .. } => Rat::one(),
                };
                DimensionalWaveCarrierDoctrine {
                    carrier: carrier.id,
                    delay: carrier_delay,
                    admitted_modes: BTreeSet::new(),
                    admittance,
                    modal_admittance: BTreeMap::new(),
                    phase_transport: BTreeMap::new(),
                }
            })
            .collect();
        ExactDimensionalWaveLaw::new(self.source.clone(), modes, doctrines).map_err(Into::into)
    }

    /// Emit the exact prime-power population at one counting occurrence into
    /// its already-admitted finite-place mode.
    ///
    /// The formal logarithmic coefficient remains the retained arithmetic
    /// lineage. This deed emits one exact occurrence population for this
    /// `p^k`; no transcendental approximation to `log(p)` is introduced.
    pub fn phase_wave_impulses(
        &self,
        law: &ExactDimensionalWaveLaw,
        value: u64,
    ) -> Result<Vec<DimensionalWaveImpulse>, ArithmeticDimensionalError> {
        if law.source() != &self.source {
            return Err(ArithmeticDimensionalError::WaveSourceMismatch);
        }
        let occurrence = self
            .occurrences
            .get(&value)
            .ok_or(ArithmeticDimensionalError::MissingWaveOccurrence(value))?;
        if occurrence.valuation.len() != 1 {
            return Ok(Vec::new());
        }
        let prime = occurrence.valuation[0].prime;
        let mode = DimensionalWaveModeId(prime);
        if !law.has_junction(mode, occurrence.germ) {
            return Ok(Vec::new());
        }
        let pair = self
            .phase_axes
            .get(&prime)
            .ok_or(ArithmeticDimensionalError::MissingPrimePhaseAxes(prime))?;
        let germ = &self.source.germs()[&occurrence.germ];
        let Some((real, imaginary)) = germ
            .coordinates
            .get(&pair.real)
            .zip(germ.coordinates.get(&pair.imaginary))
        else {
            return Ok(Vec::new());
        };
        let source_event = *germ
            .source_events
            .iter()
            .next()
            .ok_or(ArithmeticDimensionalError::MalformedMount)?;
        Ok(vec![DimensionalWaveImpulse {
            source_event,
            mode,
            germ: occurrence.germ,
            departure: ExactComplexWaveCurrent::new(real.clone(), imaginary.clone()),
        }])
    }

    pub fn validate(&self) -> Result<(), ArithmeticDimensionalError> {
        if self.schema != "holonic-engine.arithmetic-dimensional-mount.v2"
            || self.through < 2
            || self.occurrences.keys().copied().collect::<Vec<_>>()
                != (2..=self.through).collect::<Vec<_>>()
        {
            return Err(ArithmeticDimensionalError::MalformedMount);
        }
        self.source.validate()?;
        for (prime, pair) in &self.phase_axes {
            if pair.prime != *prime
                || !self.source.axes().contains_key(&pair.real)
                || !self.source.axes().contains_key(&pair.imaginary)
            {
                return Err(ArithmeticDimensionalError::MalformedMount);
            }
        }
        for occurrence in self.occurrences.values() {
            let germ = self
                .source
                .germs()
                .get(&occurrence.germ)
                .ok_or(ArithmeticDimensionalError::MalformedMount)?;
            if occurrence.value != occurrence.germ.0
                || germ.source_events.len() != 1
                || occurrence
                    .factor_horizon
                    .iter()
                    .any(|prime| !self.phase_axes.contains_key(prime))
            {
                return Err(ArithmeticDimensionalError::MalformedMount);
            }
        }
        let classified = self
            .chronology_carriers
            .union(&self.boundary_carriers)
            .copied()
            .collect::<BTreeSet<_>>()
            .union(&self.phase_return_carriers)
            .copied()
            .collect::<BTreeSet<_>>()
            .union(
                &self
                    .probe_carriers
                    .values()
                    .copied()
                    .collect::<BTreeSet<_>>(),
            )
            .copied()
            .collect::<BTreeSet<_>>();
        if classified.len() != self.source.carriers().len()
            || classified
                != self
                    .source
                    .carriers()
                    .keys()
                    .copied()
                    .collect::<BTreeSet<_>>()
        {
            return Err(ArithmeticDimensionalError::MalformedMount);
        }
        self.history.validate(self)?;
        Ok(())
    }
}

impl ArithmeticDimensionalHistory {
    fn derive(
        mount: &ArithmeticDimensionalMount,
        standing: &ArithmeticFiberStanding,
    ) -> Result<Self, ArithmeticDimensionalError> {
        if mount.through != standing.value {
            return Err(ArithmeticDimensionalError::MalformedHistory);
        }
        let mut waves = Vec::with_capacity(
            usize::try_from(mount.through.saturating_sub(1))
                .map_err(|_| ArithmeticDimensionalError::CarrierOverflow)?,
        );
        let mut causal_horizon = BTreeSet::new();
        let mut next_front = 1_u64;
        let mut log_coefficients = BTreeMap::<u64, u32>::new();
        let mut chebyshev_product = BigUint::one();

        for value in 2..=mount.through {
            let occurrence = &mount.occurrences[&value];
            let standing_occurrence = &standing.occurrences()[&value];
            let recognition = &standing.recognitions()[&value];
            causal_horizon.insert(standing_occurrence.event);
            let coordinate_current = coordinate_current(mount, value);
            let mut fronts = Vec::new();
            let prior_horizon = value
                .checked_sub(1)
                .and_then(|prior| mount.occurrences.get(&prior))
                .map(|prior| prior.factor_horizon.as_slice())
                .unwrap_or(&[]);
            {
                let mut front_emitter = ArithmeticFrontEmitter {
                    fronts: &mut fronts,
                    next_front: &mut next_front,
                    event: standing_occurrence.event,
                    value,
                };

                for prime in occurrence
                    .factor_horizon
                    .iter()
                    .filter(|prime| !prior_horizon.contains(prime))
                {
                    let pair = mount.phase_axes[prime];
                    let rank_current = coordinate_current
                        .iter()
                        .filter(|current| {
                            current.axis == pair.real || current.axis == pair.imaginary
                        })
                        .cloned()
                        .collect();
                    front_emitter.push(
                        ArithmeticDimensionalFrontKind::RankAdmission {
                            prime: *prime,
                            real: pair.real,
                            imaginary: pair.imaginary,
                        },
                        BTreeSet::from([occurrence.germ]),
                        BTreeSet::new(),
                        rank_current,
                    )?;
                }

                front_emitter.push(
                    ArithmeticDimensionalFrontKind::OccurrenceEmission,
                    BTreeSet::from([occurrence.germ]),
                    BTreeSet::new(),
                    coordinate_current,
                )?;

                if let Some(carrier) = mount.chronology_by_value.get(&value) {
                    front_emitter.push(
                        ArithmeticDimensionalFrontKind::ChronologyCarry { carrier: *carrier },
                        BTreeSet::from([CoordinateGermId(value - 1), occurrence.germ]),
                        BTreeSet::from([*carrier]),
                        Vec::new(),
                    )?;
                }

                for step in &recognition.steps {
                    let prime = step.probe.prime_axis;
                    let carrier = mount.probe_carriers[&(value, prime)];
                    let active_germs = BTreeSet::from([occurrence.germ, CoordinateGermId(prime)]);
                    front_emitter.push(
                        ArithmeticDimensionalFrontKind::ProbeLeader {
                            prime,
                            quotient: step.probe.quotient,
                            carrier,
                        },
                        active_germs.clone(),
                        BTreeSet::from([carrier]),
                        Vec::new(),
                    )?;
                    front_emitter.push(
                        ArithmeticDimensionalFrontKind::ProbeReturn {
                            prime,
                            quotient: step.probe.quotient,
                            remainder: step.probe.remainder,
                            carrier,
                        },
                        active_germs,
                        BTreeSet::from([carrier]),
                        Vec::new(),
                    )?;
                }

                front_emitter.push(
                    ArithmeticDimensionalFrontKind::RecognitionClosure {
                        closure: recognition.closure.clone(),
                    },
                    BTreeSet::from([occurrence.germ]),
                    BTreeSet::new(),
                    Vec::new(),
                )?;

                if occurrence.irreducible {
                    let cell = standing.prime_cells()[&value];
                    front_emitter.push(
                        ArithmeticDimensionalFrontKind::PrimeFounding { prime: value, cell },
                        BTreeSet::from([occurrence.germ]),
                        BTreeSet::new(),
                        Vec::new(),
                    )?;
                }

                for carrier in mount
                    .boundary_by_event
                    .get(&standing_occurrence.event)
                    .into_iter()
                    .flatten()
                {
                    let body = &mount.source.carriers()[carrier];
                    front_emitter.push(
                        ArithmeticDimensionalFrontKind::BoundaryIncidence { carrier: *carrier },
                        BTreeSet::from([body.from, body.to]),
                        BTreeSet::from([*carrier]),
                        Vec::new(),
                    )?;
                }

                for (prime, carrier) in mount
                    .phase_returns_by_value
                    .get(&value)
                    .into_iter()
                    .flatten()
                {
                    front_emitter.push(
                        ArithmeticDimensionalFrontKind::PhaseReturn {
                            prime: *prime,
                            carrier: *carrier,
                        },
                        BTreeSet::from([CoordinateGermId(value - 1), occurrence.germ]),
                        BTreeSet::from([*carrier]),
                        Vec::new(),
                    )?;
                }

                if occurrence.valuation.len() == 1 {
                    let valuation = &occurrence.valuation[0];
                    let coefficient = log_coefficients.entry(valuation.prime).or_default();
                    *coefficient = coefficient
                        .checked_add(1)
                        .ok_or(ArithmeticDimensionalError::CarrierOverflow)?;
                    chebyshev_product *= BigUint::from(valuation.prime);
                    front_emitter.push(
                        ArithmeticDimensionalFrontKind::PrimePowerCurrent {
                            event: PrimePowerCurrentEvent {
                                value,
                                prime: valuation.prime,
                                exponent: valuation.exponent,
                                log_coefficient_after: *coefficient,
                                chebyshev_product_after: chebyshev_product.clone(),
                            },
                        },
                        BTreeSet::from([occurrence.germ]),
                        BTreeSet::new(),
                        Vec::new(),
                    )?;
                }

                front_emitter.push(
                    ArithmeticDimensionalFrontKind::Rest,
                    BTreeSet::from([occurrence.germ]),
                    BTreeSet::new(),
                    Vec::new(),
                )?;
            }
            waves.push(ArithmeticDimensionalWave {
                event: standing_occurrence.event,
                value,
                causal_horizon_after: causal_horizon.clone(),
                fronts,
            });
        }

        if log_coefficients != standing.prime_power_current().log_coefficients
            || chebyshev_product != standing.prime_power_current().chebyshev_product
        {
            return Err(ArithmeticDimensionalError::MalformedHistory);
        }
        Ok(Self {
            schema: "holonic-engine.arithmetic-dimensional-history.v1".to_owned(),
            through: mount.through,
            waves,
        })
    }

    pub fn validate(
        &self,
        mount: &ArithmeticDimensionalMount,
    ) -> Result<(), ArithmeticDimensionalError> {
        if self.schema != "holonic-engine.arithmetic-dimensional-history.v1"
            || self.through != mount.through
            || self.waves.len()
                != usize::try_from(self.through.saturating_sub(1))
                    .map_err(|_| ArithmeticDimensionalError::CarrierOverflow)?
        {
            return Err(ArithmeticDimensionalError::MalformedHistory);
        }
        let mut prior_horizon = BTreeSet::new();
        let mut expected_front = 1_u64;
        for (offset, wave) in self.waves.iter().enumerate() {
            let value = u64::try_from(offset)
                .map_err(|_| ArithmeticDimensionalError::CarrierOverflow)?
                .checked_add(2)
                .ok_or(ArithmeticDimensionalError::CarrierOverflow)?;
            let occurrence = &mount.occurrences[&value];
            let event = *mount.source.germs()[&occurrence.germ]
                .source_events
                .iter()
                .next()
                .ok_or(ArithmeticDimensionalError::MalformedHistory)?;
            let mut expected_horizon = prior_horizon.clone();
            expected_horizon.insert(event);
            if wave.value != value
                || wave.event != event
                || wave.causal_horizon_after != expected_horizon
                || wave.fronts.is_empty()
                || !matches!(
                    wave.fronts.last().map(|front| &front.kind),
                    Some(ArithmeticDimensionalFrontKind::Rest)
                )
            {
                return Err(ArithmeticDimensionalError::MalformedHistory);
            }
            for front in &wave.fronts {
                if front.ordinal != expected_front
                    || front.event != event
                    || front.value != value
                    || front
                        .active_germs
                        .iter()
                        .any(|germ| !mount.source.germs().contains_key(germ))
                    || front
                        .active_carriers
                        .iter()
                        .any(|carrier| !mount.source.carriers().contains_key(carrier))
                    || front.coordinate_current.iter().any(|current| {
                        !mount.source.axes().contains_key(&current.axis)
                            || current.before == current.after
                    })
                {
                    return Err(ArithmeticDimensionalError::MalformedHistory);
                }
                expected_front = expected_front
                    .checked_add(1)
                    .ok_or(ArithmeticDimensionalError::CarrierOverflow)?;
            }
            prior_horizon = expected_horizon;
        }
        if prior_horizon != *mount.source.source_events() {
            return Err(ArithmeticDimensionalError::MalformedHistory);
        }
        Ok(())
    }
}

fn coordinate_current(
    mount: &ArithmeticDimensionalMount,
    value: u64,
) -> Vec<ArithmeticAxisCurrent> {
    let after = &mount.source.germs()[&CoordinateGermId(value)].coordinates;
    let before = value
        .checked_sub(1)
        .and_then(|prior| mount.source.germs().get(&CoordinateGermId(prior)))
        .map(|germ| &germ.coordinates);
    let axes = after
        .keys()
        .copied()
        .chain(
            before
                .into_iter()
                .flat_map(|coordinates| coordinates.keys().copied()),
        )
        .collect::<BTreeSet<_>>();
    axes.into_iter()
        .filter_map(|axis| {
            let before = before
                .and_then(|coordinates| coordinates.get(&axis))
                .cloned();
            let after = after.get(&axis).cloned();
            (before != after).then_some(ArithmeticAxisCurrent {
                axis,
                before,
                after,
            })
        })
        .collect()
}

struct ArithmeticFrontEmitter<'a> {
    fronts: &'a mut Vec<ArithmeticDimensionalFront>,
    next_front: &'a mut u64,
    event: EventId,
    value: u64,
}

impl ArithmeticFrontEmitter<'_> {
    fn push(
        &mut self,
        kind: ArithmeticDimensionalFrontKind,
        active_germs: BTreeSet<CoordinateGermId>,
        active_carriers: BTreeSet<CoordinateCarrierId>,
        coordinate_current: Vec<ArithmeticAxisCurrent>,
    ) -> Result<(), ArithmeticDimensionalError> {
        self.fronts.push(ArithmeticDimensionalFront {
            ordinal: *self.next_front,
            event: self.event,
            value: self.value,
            kind,
            active_germs,
            active_carriers,
            coordinate_current,
        });
        *self.next_front = self
            .next_front
            .checked_add(1)
            .ok_or(ArithmeticDimensionalError::CarrierOverflow)?;
        Ok(())
    }
}

fn phase_axis_ids(prime: u64) -> Result<ArithmeticPhaseAxes, ArithmeticDimensionalError> {
    let real = prime
        .checked_mul(2)
        .and_then(|value| value.checked_add(1_000))
        .ok_or(ArithmeticDimensionalError::CarrierOverflow)?;
    let imaginary = real
        .checked_add(1)
        .ok_or(ArithmeticDimensionalError::CarrierOverflow)?;
    Ok(ArithmeticPhaseAxes {
        prime,
        real: DimensionalAxisId(real),
        imaginary: DimensionalAxisId(imaginary),
    })
}

fn integer_rat(value: u64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

/// Exact rational point on a unit conic for one finite cyclic residue phase.
///
/// Four rational Cayley charts cover four oriented quadrants.  The embedding
/// is a receiver chart for the discrete cyclic order; it is not a claim that
/// chord length is an intrinsic metric on `Z/pZ`.
pub fn exact_residue_conic_phase(
    residue: u64,
    modulus: u64,
) -> Result<(Rat, Rat), ArithmeticDimensionalError> {
    if modulus < 2 || residue >= modulus {
        return Err(ArithmeticDimensionalError::InvalidResiduePhase { residue, modulus });
    }
    let four_residue = residue
        .checked_mul(4)
        .ok_or(ArithmeticDimensionalError::CarrierOverflow)?;
    let quadrant = four_residue / modulus;
    let local = four_residue % modulus;
    let parameter = Rat::new(BigInt::from(local), BigInt::from(modulus));
    let denominator = Rat::one() + &parameter * &parameter;
    let first = (Rat::one() - &parameter * &parameter) / &denominator;
    let second = (Rat::from_integer(BigInt::from(2)) * parameter) / denominator;
    let point = match quadrant {
        0 => (first, second),
        1 => (-second, first),
        2 => (-first, -second),
        3 => (second, -first),
        _ => {
            return Err(ArithmeticDimensionalError::InvalidResiduePhase { residue, modulus });
        }
    };
    debug_assert_eq!(&point.0 * &point.0 + &point.1 * &point.1, Rat::one());
    Ok(point)
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ArithmeticDimensionalError {
    #[error(transparent)]
    Arithmetic(#[from] ArithmeticFiberError),
    #[error(transparent)]
    Receiver(#[from] DimensionalReceiverError),
    #[error(transparent)]
    Causal(#[from] crate::CausalAlgebraicError),
    #[error(transparent)]
    Wave(#[from] DimensionalWaveError),
    #[error("the counting ecology has no occurrence to mount")]
    EmptyCountingEcology,
    #[error("the dimensional wave carrier delay must be positive")]
    ZeroWaveDelay,
    #[error("wave horizon {supplied} is outside caused source horizon 4..={source_through}")]
    InvalidWaveHorizon { supplied: u64, source_through: u64 },
    #[error("the dimensional wave law was built from another source ecology")]
    WaveSourceMismatch,
    #[error("counting occurrence {0} is absent from the dimensional wave source")]
    MissingWaveOccurrence(u64),
    #[error("prime axis {0} has no founding occurrence")]
    MissingPrimeAxisOccurrence(u64),
    #[error("prime axis {0} has no dimensional phase pair")]
    MissingPrimePhaseAxes(u64),
    #[error("causal cell {0:?} has no occurrence germ")]
    MissingCellOccurrence(crate::CausalCellId),
    #[error("a phase product cannot repeat prime {0}")]
    RepeatedProjectionPrime(u64),
    #[error("residue {residue} is invalid for modulus {modulus}")]
    InvalidResiduePhase { residue: u64, modulus: u64 },
    #[error("the arithmetic dimensional mount is malformed")]
    MalformedMount,
    #[error("the arithmetic dimensional causal history is malformed")]
    MalformedHistory,
    #[error("an arithmetic dimensional carrier overflowed")]
    CarrierOverflow,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ArithmeticFiberEvent, ArithmeticFiberLaw, CausalWorld, EventId};
    use num_traits::Zero;

    fn ecology(limit: u64) -> ArithmeticFiberStanding {
        let mut world = CausalWorld::new(ArithmeticFiberLaw, ArithmeticFiberStanding::default());
        for value in 2..=limit {
            world
                .receive(&ArithmeticFiberEvent {
                    event: EventId(value - 1),
                    value,
                })
                .unwrap();
        }
        world.standing().clone()
    }

    #[test]
    fn residue_charts_are_exact_unit_conic_sections() {
        for modulus in [2_u64, 3, 5, 7, 11, 13] {
            for residue in 0..modulus {
                let (real, imaginary) = exact_residue_conic_phase(residue, modulus).unwrap();
                assert_eq!(&real * &real + &imaginary * &imaginary, Rat::one());
            }
        }
    }

    #[test]
    fn prime_square_wall_grows_local_dimension_without_zero_padding_history() {
        let mount = ArithmeticDimensionalMount::mount(&ecology(64)).unwrap();
        let before = mount
            .source
            .germ_local_dimension(CoordinateGermId(48))
            .unwrap();
        let after = mount
            .source
            .germ_local_dimension(CoordinateGermId(49))
            .unwrap();
        assert_eq!(after, before + 1);
        let seven = mount.phase_axes[&7];
        assert!(
            !mount.source.germs()[&CoordinateGermId(48)]
                .coordinates
                .contains_key(&seven.real)
        );
        assert!(
            mount.source.germs()[&CoordinateGermId(49)]
                .coordinates
                .contains_key(&seven.real)
        );
    }

    #[test]
    fn arithmetic_incidence_chronology_and_phase_returns_remain_distinct() {
        let mount = ArithmeticDimensionalMount::mount(&ecology(64)).unwrap();
        assert_eq!(mount.chronology_carriers.len(), 62);
        assert!(!mount.boundary_carriers.is_empty());
        assert!(!mount.phase_return_carriers.is_empty());
        assert_eq!(
            mount.chronology_carriers.len()
                + mount.boundary_carriers.len()
                + mount.phase_return_carriers.len()
                + mount.probe_carriers.len(),
            mount.source.carriers().len()
        );
        assert_eq!(mount.history.waves.len(), 63);
        assert!(mount.history.waves.iter().all(|wave| {
            matches!(
                wave.fronts.last().map(|front| &front.kind),
                Some(ArithmeticDimensionalFrontKind::Rest)
            )
        }));
    }

    #[test]
    fn history_carries_actual_probe_returns_and_prime_square_rank_births() {
        let mount = ArithmeticDimensionalMount::mount(&ecology(64)).unwrap();
        let thirty_five = &mount.history.waves[usize::try_from(35 - 2).unwrap()];
        let returned_primes = thirty_five
            .fronts
            .iter()
            .filter_map(|front| match front.kind {
                ArithmeticDimensionalFrontKind::ProbeReturn { prime, .. } => Some(prime),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(returned_primes, vec![2, 3, 5]);
        assert!(matches!(
            thirty_five.fronts.last().unwrap().kind,
            ArithmeticDimensionalFrontKind::Rest
        ));

        let forty_nine = &mount.history.waves[usize::try_from(49 - 2).unwrap()];
        let rank = forty_nine
            .fronts
            .iter()
            .find(|front| {
                matches!(
                    front.kind,
                    ArithmeticDimensionalFrontKind::RankAdmission { prime: 7, .. }
                )
            })
            .unwrap();
        let seven = mount.phase_axes[&7];
        assert_eq!(
            rank.coordinate_current,
            vec![
                ArithmeticAxisCurrent {
                    axis: seven.real,
                    before: None,
                    after: Some(
                        mount.source.germs()[&CoordinateGermId(49)].coordinates[&seven.real]
                            .clone()
                    ),
                },
                ArithmeticAxisCurrent {
                    axis: seven.imaginary,
                    before: None,
                    after: Some(
                        mount.source.germs()[&CoordinateGermId(49)].coordinates[&seven.imaginary]
                            .clone()
                    ),
                },
            ]
        );
        assert_eq!(forty_nine.causal_horizon_after.len(), 48);
    }

    #[test]
    fn prime_power_occurrences_drive_simultaneous_lossless_phase_modes() {
        let mount = ArithmeticDimensionalMount::mount(&ecology(24)).unwrap();
        let law = mount.exact_phase_wave_law(3).unwrap();
        assert_eq!(
            law.modes().iter().map(|mode| mode.id).collect::<Vec<_>>(),
            vec![DimensionalWaveModeId(2), DimensionalWaveModeId(3)]
        );
        let mut world = CausalWorld::new(law.clone(), law.initial_standing());
        let mut emitted_values = Vec::new();
        for value in 2..=24 {
            let impulses = mount.phase_wave_impulses(world.law(), value).unwrap();
            if !impulses.is_empty() {
                emitted_values.push(value);
            }
            let receipt = world
                .receive(&crate::DimensionalWaveEvent {
                    event: EventId(10_000 + value),
                    impulses,
                })
                .unwrap();
            assert!(receipt.radiation[0].exact_energy_residual.is_zero());
        }
        assert_eq!(emitted_values, vec![4, 8, 9, 16]);
        let retained_energy = world.standing().energy.clone();
        assert!(retained_energy > Rat::zero());

        for offset in 0..8 {
            let receipt = world
                .receive(&crate::DimensionalWaveEvent {
                    event: EventId(20_000 + offset),
                    impulses: Vec::new(),
                })
                .unwrap();
            assert!(receipt.radiation[0].source_work.is_zero());
            assert!(receipt.radiation[0].exact_energy_residual.is_zero());
            assert_eq!(receipt.radiation[0].energy_after, retained_energy);
        }
        law.validate_standing(world.standing()).unwrap();
    }
}

//! Actual station response of the continuing contact differential (Refs #73 #62).
//!
//! [agent-inferred] This reads A=d(receiving logits)/d(raw contact factors) at ONE
//! producing material, observer and full current. Incoming held columns and every
//! native material forcing term are retained. It is not a uniform finite-ray bound.
//! Norms use identity in the explicitly enumerated raw parameter/realified logit
//! charts; they are coordinate readings, not physical storage energies. The loaded
//! span's kappa instead maps contact RHS streams, so it cannot be compared to A
//! without its actual feature/forcing map. No observed gain authorizes a step.

use super::*;
use crate::hnn::field::FieldMaterial;
use crate::hnn::propagation::participation;
use crate::hnn::ratio::RatioCovector;
use crate::hnn::receiving::{ReceivingCarrier, ReceivingPhases};
use crate::holon::deposition::{schur_norms, spectral_norm};

/// The transient matrix's predeclared extent and exact-bit budget. Native CPU/wall
/// and all temporary workspace remain the sole queue's independently measured budget.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StationResponseBudget {
    pub ratios: usize,
    pub bits: u64,
}

/// Full station response at the same producing Word; never installed in the Resident.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContactStationResponse {
    pub producing_commit: u64,
    pub current: Current,
    pub opened_at: usize,
    pub receiver: usize,
    pub grain: u64,
    pub station_ticks: Vec<usize>,
    pub coordinates: Vec<ContactCoordinate>,
    /// Rows: all actual stations, then all realified receiving coordinates.
    pub matrix: ExactRatMatrix,
    pub matrix_bits: u64,
    rows_per_station: usize,
}

/// Exact sufficient enclosure of the squared norm in the declared coordinate metrics.
/// Both ends are ratios. This has no finite admission authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StationResponseReading {
    pub station_ticks: Vec<usize>,
    pub coordinates: Vec<ContactCoordinate>,
    pub matrix: ExactRatMatrix,
    pub lower_squared: Rat,
    pub upper_squared: Rat,
    pub schur_squared: Rat,
    pub frobenius_squared: Rat,
    pub spectral_squared: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StationDirectionReading {
    pub parameter_squared: Rat,
    pub receiving_squared: Rat,
    pub gain_squared: Rat,
    pub response: Vec<Rat>,
}

fn squared_values(values: &[Rat]) -> Rat {
    values.iter().map(|x| x * x).sum()
}

impl StationResponseReading {
    /// Exact gain on the SUPPLIED coordinate direction, not a favorable finite trial.
    pub fn directional(&self, direction: &[Rat]) -> Result<StationDirectionReading, HnnError> {
        let response = self.matrix.apply(direction)?;
        let parameter_squared = squared_values(direction);
        if parameter_squared.is_zero() {
            return refuse("a zero parameter direction has no defined gain ratio");
        }
        let receiving_squared = squared_values(&response);
        let gain_squared = &receiving_squared / &parameter_squared;
        if gain_squared > self.upper_squared {
            return refuse(
                "the actual directional response stays within its certified point-operator norm",
            );
        }
        Ok(StationDirectionReading {
            parameter_squared,
            receiving_squared,
            gain_squared,
            response,
        })
    }
}

impl ContactStationResponse {
    /// Restrict only the observer's actual compared station partition.
    pub fn select(&self, compared: &[bool]) -> Result<StationResponseReading, HnnError> {
        if compared.len() != self.station_ticks.len() {
            return refuse("a realized response reads its complete producing station partition");
        }
        let mut rows = Vec::new();
        let mut station_ticks = Vec::new();
        for (station, selected) in compared.iter().enumerate() {
            if !selected {
                continue;
            }
            station_ticks.push(self.station_ticks[station]);
            for coordinate in 0..self.rows_per_station {
                let row = station * self.rows_per_station + coordinate;
                rows.push(
                    (0..self.matrix.columns())
                        .map(|j| self.matrix.get(row, j).cloned())
                        .collect::<Result<Vec<_>, _>>()?,
                );
            }
        }
        let matrix = ExactRatMatrix::shaped(rows.len(), self.coordinates.len(), rows)?;
        let (column, row) = schur_norms(&matrix);
        let schur_squared = column * row;
        let frobenius_squared = squared_values(matrix.entries());
        let spectral = spectral_norm(matrix.rows(), matrix.columns(), matrix.entries());
        let spectral_squared = &spectral * &spectral;
        let upper_squared = schur_squared
            .clone()
            .min(frobenius_squared.clone())
            .min(spectral_squared.clone());
        // Each basis vector is unit in the declared raw coordinate chart.
        let mut lower_squared = Rat::zero();
        for j in 0..matrix.columns() {
            let values = (0..matrix.rows())
                .map(|i| matrix.get(i, j).cloned())
                .collect::<Result<Vec<_>, _>>()?;
            lower_squared = lower_squared.max(squared_values(&values));
        }
        if lower_squared > upper_squared {
            return refuse("the realized station operator's exact norm enclosure is consistent");
        }
        Ok(StationResponseReading {
            station_ticks,
            coordinates: self.coordinates.clone(),
            matrix,
            lower_squared,
            upper_squared,
            schur_squared,
            frobenius_squared,
            spectral_squared,
        })
    }

    /// The same receiving covector returns through ALL raw material columns.
    /// A consuming comparison checks this against its independent current+delayed adjoint.
    pub fn pullback(&self, covector: &RatioCovector) -> Result<Vec<Rat>, HnnError> {
        if covector.logits().len() != self.station_ticks.len()
            || covector
                .logits()
                .iter()
                .any(|x| x.len() != self.rows_per_station)
        {
            return refuse("the realized response and ratio use the same complete receiving chart");
        }
        Ok(self
            .matrix
            .transpose()?
            .apply(&covector.logits().concat())?)
    }

    /// Independent forward-tangent/adjoint consuming square, checked exactly.
    pub fn check_pullback(&self, covector: &RatioCovector, total: &[Rat]) -> Result<(), HnnError> {
        if self.pullback(covector)? != total {
            return refuse(
                "the actual station response transposes to the same current-plus-delayed material covector",
            );
        }
        Ok(())
    }
}

impl HeldContactVariation {
    /// Keep the existing declared limits; no diagnostic cap is raised after a run.
    pub(crate) fn station_response_budget(&self) -> StationResponseBudget {
        StationResponseBudget {
            ratios: self.budget.ratios,
            bits: self.budget.bits,
        }
    }

    /// Fused existing column advancement and station observation. One native producing
    /// Word and exactly the original admitted column-ticks, with a declared transient matrix.
    /// Current source/preparation and observer coefficients are held fixed; differentiating
    /// action selection, observation, R updates or incoming remainders needs their own join.
    pub(crate) fn advanced_with_station_response(
        &self,
        word: &Word<'_>,
        opened: &[EndChange],
        phases: &ReceivingPhases,
        budget: StationResponseBudget,
    ) -> Result<(Self, ContactStationResponse), HnnError> {
        if opened != self.opened(word)?.as_slice()
            || word.ticks() < phases.junction_steps()
            || phases.ring() >= word.field.rings().len()
            || word.field.first_epoch(phases.ring()) != Some(phases.first_epoch())
            || !phases.is_declared_restriction(word.field)?
        {
            return refuse(
                "a station response consumes the actual full opening differential and native crossings",
            );
        }
        let (theta, current, _, _) = word.native_source.as_ref().ok_or(HnnError::Unadmitted {
            reason: "a station response keeps its actual native producing material/current",
        })?;
        if FieldMaterial::receiving_carrier(theta, phases.ring()) != ReceivingCarrier::Anchor {
            return refuse(
                "a variable/non-anchor observer supplies its own coefficient differential",
            );
        }
        let map = FieldMaterial::receiving_map(theta, phases.ring()).ok_or(
            HnnError::MissingReceivingMap {
                ring: phases.ring(),
            },
        )?;
        if map.columns() != word.field.ring(phases.ring()).width()
            || map.rows()
                != word
                    .field
                    .alphabet()
                    .checked_mul(2)
                    .ok_or(HnnError::CountOverflow)?
        {
            return refuse("the realized station response keeps its producing receiving map shape");
        }
        let rows_per_station = map.rows();
        let rows = phases
            .aperture()
            .checked_mul(rows_per_station)
            .ok_or(HnnError::CountOverflow)?;
        let extent = rows
            .checked_mul(self.coordinates.len())
            .ok_or(HnnError::CountOverflow)?;
        if extent > budget.ratios {
            return refuse("the realized response exceeds its predeclared transient matrix extent");
        }
        let mut entries = vec![vec![Rat::zero(); self.coordinates.len()]; rows];
        let next = self.advance_contact_columns(word, opened, |t, columns| {
            if t >= phases.first_epoch() && t <= phases.last_epoch() {
                let row_offset = (t - phases.first_epoch()) * rows_per_station;
                for (j, chi) in columns.iter().enumerate() {
                    let ring = phases.ring();
                    let incoming: Vec<_> = word
                        .operands
                        .incident(ring)
                        .iter()
                        .map(|&a| chi.arrivals[a][word.operands.end_slot(a, ring)].as_slice())
                        .collect();
                    let anchor =
                        participation(word.operands.weights(ring), &chi.storage[ring], &incoming)?;
                    let read =
                        map.apply(&word.field.ring(ring).rotate(&anchor, &current.lift()[ring]))?;
                    for (i, value) in read.into_iter().enumerate() {
                        entries[row_offset + i][j] = value;
                    }
                }
            }
            Ok(())
        })?;
        let matrix = ExactRatMatrix::shaped(rows, self.coordinates.len(), entries)?;
        let mut matrix_bits = 0u64;
        for x in matrix.entries() {
            matrix_bits = matrix_bits
                .checked_add(x.numer().bits())
                .and_then(|n| n.checked_add(x.denom().bits()))
                .ok_or(HnnError::CountOverflow)?;
        }
        if matrix_bits > budget.bits {
            return refuse("the realized response exceeds its predeclared exact matrix bit budget");
        }
        let station_ticks = phases
            .epochs()
            .map(|t| {
                word.opened_at()
                    .checked_add(t)
                    .ok_or(HnnError::CountOverflow)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let response = ContactStationResponse {
            producing_commit: theta.commit(),
            current: current.clone(),
            opened_at: word.opened_at(),
            receiver: phases.ring(),
            grain: phases.grain(),
            station_ticks,
            coordinates: self.coordinates.clone(),
            matrix,
            matrix_bits,
            rows_per_station,
        };
        Ok((next, response))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compression::landmark::context::{BaseMeasure, StopPrior};
    use crate::geometry::{RatVec3, screw::ScrewGenerator};
    use crate::hnn::constitution::CAMPAIGN_ONE_BUDGET;
    use crate::hnn::field::{
        ContactDeclaration, CribDeclaration, FieldDeclaration, ReceiverDeclaration, RingDeclaration,
    };
    use crate::hnn::ratio::{Faces, TargetPhases};
    use crate::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial};
    use crate::holon::parametron::Carrier;
    use crate::ratio::{integer, rat};
    use num_bigint::BigInt;
    use num_traits::{One, Zero};
    use std::sync::Arc;

    /// A physical-law fixture, not an acquired task solution or a proposed admission policy.
    /// Its single complex contact has exactly twelve raw C/K/D factor coordinates.
    fn fixture() -> (Field, Constitution, Current) {
        let ring = |source| RingDeclaration {
            period: 2,
            screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
            placements: (0..2)
                .map(|node| FieldDeclaration::quarter_turn(node, 2))
                .collect(),
            lock: if source { vec![0, 1] } else { Vec::new() },
            reflector: vec![0, 1],
            admittance: integer(2),
            initial: 0,
        };
        let field = Field::declare(
            FieldDeclaration {
                rings: vec![ring(true), ring(false)],
                contacts: vec![ContactDeclaration {
                    from: 0,
                    to: 1,
                    channel: vec![(0, 0)],
                    admittance: integer(2),
                    exponent: integer(0),
                }],
                loops: Vec::new(),
                sources: vec![0],
                offsets: Vec::new(),
                alphabet: 2,
                step: integer(1),
                exponent_grain: 1,
                receivers: vec![ReceiverDeclaration {
                    ring: 1,
                    aperture: 2,
                    tolerance: rat(1, 16),
                    depth: 2,
                    prior: StopPrior::half(),
                    mass: 1,
                    base: BaseMeasure::Even,
                    receiving_prior: 0,
                }],
                crib: CribDeclaration {
                    window: 16,
                    offset: 1,
                },
                population: 1 << 16,
                lattice: Default::default(),
            }
            .by_lattice_rule(),
        )
        .unwrap();
        let factor = ExactRatMatrix::identity(2).unwrap();
        let mut theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET)
            .unwrap()
            .with_channel(0, factor.clone(), factor.clone(), factor)
            .unwrap()
            .with_ports(1, None, None, Some(ExactRatMatrix::identity(4).unwrap()))
            .unwrap();
        for g in 0..2 {
            theta = theta
                .with_ring_resonator(
                    &field,
                    g,
                    ResonatorMaterial::new(
                        ExactRatMatrix::identity(4).unwrap(),
                        ExactRatMatrix::identity(4).unwrap().scaled(&rat(1, 8)),
                        ExactRatMatrix::identity(4).unwrap().scaled(&rat(1, 16)),
                        Some(
                            PumpDeclaration::new(
                                rat(1, 16),
                                Carrier::at(&rat(1, 2)),
                                PumpStep::Half,
                            )
                            .unwrap(),
                        ),
                    )
                    .unwrap(),
                )
                .unwrap();
        }
        let current = Current::at(&field, vec![BigInt::from(0), BigInt::from(1)]).unwrap();
        (field, theta, current)
    }

    #[test]
    fn forward_station_rows_match_the_full_current_and_delayed_adjoint() {
        let (field, theta, current) = fixture();
        let phases =
            ReceivingPhases::declare(&field, &theta, &current, &field.receivers()[0]).unwrap();
        let source = Arc::new(
            SourceMoment::open(&field, &current)
                .continued(&field, &current, 0, &[Some(0)])
                .unwrap(),
        );
        let ops = Operands::exact_at_cut(&field, &theta, &current).unwrap();
        let parameters = (0..field.contacts().len())
            .map(|a| {
                factors(&theta, a)
                    .iter()
                    .map(|f| f.rows() * f.columns())
                    .sum::<usize>()
            })
            .sum::<usize>();
        assert_eq!(parameters, 12);
        let budget = VariationBudget {
            ratios: parameters * values(&EndChange::rest(&field, &ops)).count(),
            bits: CAMPAIGN_ONE_BUDGET,
            column_ticks: parameters * phases.junction_steps() * 2,
        };
        let held = HeldContactVariation::begin(&field, &theta, &current, None, budget).unwrap();
        let mut first = Word::open_source_exact_received(
            &field,
            &theta,
            &current,
            source.clone(),
            &WordOpening::Rest,
        )
        .unwrap()
        .0;
        let opening = held.opened(&first).unwrap();
        first.run(phases.junction_steps()).unwrap();
        let (held, _) = held
            .advanced_with_station_response(
                &first,
                &opening,
                &phases,
                held.station_response_budget(),
            )
            .unwrap();
        assert!(first.field_balances().iter().all(|b| b.closes()));
        let carry = first.reception_end().unwrap();
        drop(first);

        let mut second = Word::open_source_exact_received(
            &field,
            &theta,
            &current,
            source,
            &WordOpening::Received {
                carry,
                absorption: Absorption::Nothing,
            },
        )
        .unwrap()
        .0;
        let opening = held.opened(&second).unwrap();
        let actual_opening = second.change().unwrap();
        let actual_operands = second.operands.clone();
        let actual_clock = second.opened_at();
        assert!(opening.iter().flat_map(values).any(|x| !x.is_zero()));
        assert!(
            opening
                .iter()
                .flat_map(|c| c.resonators.iter().flatten().flatten().flatten())
                .any(|x| !x.is_zero())
        );
        second.run(phases.junction_steps()).unwrap();
        assert!(second.field_balances().iter().all(|b| b.closes()));
        let (next, response) = held
            .advanced_with_station_response(
                &second,
                &opening,
                &phases,
                held.station_response_budget(),
            )
            .unwrap();
        assert_eq!(next.reading().column_ticks, budget.column_ticks);
        assert_eq!(
            response.station_ticks,
            phases
                .epochs()
                .map(|t| second.opened_at() + t)
                .collect::<Vec<_>>()
        );

        // Actual receiving reads form the covector. The targets are only a declared
        // algebraic test comparison; this fixture claims no actual-world observation.
        let reads = phases
            .epochs()
            .map(|t| {
                phases
                    .read(
                        &field,
                        &theta,
                        &current,
                        second.anchor(t, phases.ring()).unwrap(),
                    )
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let compared = [false, true];
        let ratio = HolonRatio::compare_partition(
            Faces::of_reads(&reads, phases.grain()).unwrap(),
            &[0, 1],
            &TargetPhases {
                branch: BigInt::from(0),
                phases: vec![Rat::zero(), rat(1, 2)],
            },
            &compared,
        )
        .unwrap();
        let covector = ratio.covector().unwrap();
        let support = second.native_source.as_ref().unwrap().3.clone();
        let diamond = Diamond::opened(&field, &phases, &support);
        // Check EVERY station row through independent native reverse-law controls.
        // These eight extra three-tick fixture passages are explicitly costed tests,
        // not copies installed as runtime state or purported World trial branches.
        for (station, epoch) in phases.epochs().enumerate() {
            for component in 0..response.rows_per_station {
                let map = FieldMaterial::receiving_map(&theta, phases.ring()).unwrap();
                let row = (0..map.columns())
                    .map(|j| map.get(component, j).unwrap().clone())
                    .collect::<Vec<_>>();
                let mut anchors = vec![None; phases.junction_steps()];
                anchors[epoch] = Some(
                    field
                        .ring(phases.ring())
                        .rotate(&row, &(-current.lift()[phases.ring()].clone())),
                );
                let mut control = Word::on_change(
                    &field,
                    actual_operands.clone(),
                    actual_opening.clone(),
                    actual_clock,
                )
                .unwrap();
                control.run(phases.junction_steps()).unwrap();
                let (back, dual) = control
                    .pull_back_continuing(anchors, phases.ring(), None)
                    .unwrap();
                let (_, pull) = crate::hnn::reference::compose_contact(
                    &field,
                    &theta,
                    &back,
                    &diamond,
                    &|locus| diamond.retains(&field, locus),
                    current.lift(),
                    field.step(),
                    0,
                )
                .unwrap();
                let matrix_row = station * response.rows_per_station + component;
                for (j, coordinate) in response.coordinates.iter().enumerate() {
                    let factor =
                        [&pull.storage, &pull.stiffness, &pull.dissipation][coordinate.family];
                    let returned = factor.get(coordinate.row, coordinate.column).unwrap()
                        + dual.pairing(&opening[j]);
                    assert_eq!(response.matrix.get(matrix_row, j).unwrap(), &returned);
                }
            }
        }
        // Independent reverse-law owner: it reads the actual native primal Word;
        // it neither transposes the new matrix nor repeats its forward column loop.
        let (back, dual) = second
            .pull_back_full(
                &covector,
                FieldMaterial::receiving_map(&theta, phases.ring()).unwrap(),
                &current.lift()[phases.ring()],
                &phases,
            )
            .unwrap();
        let (_, pull) = crate::hnn::reference::compose_contact(
            &field,
            &theta,
            &back,
            &diamond,
            &|locus| diamond.retains(&field, locus),
            current.lift(),
            field.step(),
            0,
        )
        .unwrap();
        let carried = opening
            .iter()
            .map(|chi| dual.pairing(chi))
            .collect::<Vec<_>>();
        assert!(carried.iter().any(|x| !x.is_zero()));
        let total = response
            .coordinates
            .iter()
            .zip(&carried)
            .map(|(coordinate, past)| {
                let factor = [&pull.storage, &pull.stiffness, &pull.dissipation][coordinate.family];
                factor.get(coordinate.row, coordinate.column).unwrap() + past
            })
            .collect::<Vec<Rat>>();
        response.check_pullback(&covector, &total).unwrap();

        let selected = response.select(&compared).unwrap();
        assert_eq!(selected.station_ticks.len(), 1);
        assert_eq!(selected.matrix.rows(), 4);
        assert_eq!(selected.matrix.columns(), parameters);
        assert!(selected.lower_squared > Rat::zero());
        let directional = selected.directional(&vec![Rat::one(); parameters]).unwrap();
        assert_eq!(directional.parameter_squared, integer(12));
        assert!(directional.gain_squared <= selected.upper_squared);
        assert!(
            selected
                .directional(&vec![Rat::zero(); parameters])
                .is_err()
        );
        assert!(response.select(&[true]).is_err());
    }
}

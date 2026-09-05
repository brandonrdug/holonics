//! Exterior rest of the complete native session. This codec never runs inside a recurrence.
//! The coefficient base is an explicit separate dependency; this state is not source-independent.

use super::{
    full_operation::ContemporaryCarrier, operative_passage_return::PassageCultivation,
    operative_return::OverlayAtom, operative_reuse::NativeForwardReuse,
    operative_terminal::TiledCarrier, NativeCarrierOrdinal, NativeCycleInterruption,
    NativeCycleProgress, NativeForwardReuseCensus, NativeFullOperationError,
    NativeFullOperatorEcology, NativeFullOperatorSession, NativeNumericalOrigin,
    NativeOperatorResidence, NativeOverlayRest, NativePassageReturn, NativeReturnAperture,
    NativeSuccessorProjection, NativeTensorOrdinal,
};
use crate::resident_section::{
    ResidentGrain, ResidentRefusal, ResidentSectionRest, ResidentSurface,
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use thiserror::Error;

pub const NATIVE_SESSION_REST_SCHEMA: &str = "holonic-engine.native-full-session-rest.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeSessionRestHeader {
    pub schema: String,
    /// Operator/incidence chart only. Equality of this header does not identify base codewords.
    pub ecology: NativeFullOperatorEcology,
    pub operation_at: usize,
    pub generation: u64,
    pub chronology: Vec<u64>,
    pub grain: u32,
    pub row_population: Option<usize>,
    pub cycle_complete: bool,
    pub previous_context: Option<Vec<u32>>,
    pub aperture: Option<NativeReturnAperture>,
    pub terminal_seal: bool,
    pub progress: Option<NativeCycleProgress>,
    pub interruption: Option<NativeCycleInterruption>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct NativeTiledRest {
    pub carrier: NativeCarrierOrdinal,
    pub rows: usize,
    pub width: usize,
    pub grain: u32,
    pub sections: Vec<ResidentSectionRest>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct NativePassageRest {
    pub aperture: NativeReturnAperture,
    pub pending: BTreeMap<NativeTensorOrdinal, Vec<NativeOverlayRest>>,
    pub returns: Vec<NativePassageReturn>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeNumericalRest {
    pub admitted: u32,
    pub projection: NativeSuccessorProjection,
    pub origin: NativeNumericalOrigin,
}

#[derive(Debug, PartialEq, Eq)]
pub struct NativeForwardReuseRest {
    pub census: NativeForwardReuseCensus,
    pub numerical: BTreeMap<NativeCarrierOrdinal, NativeNumericalRest>,
    pub standing: BTreeMap<NativeCarrierOrdinal, ResidentSectionRest>,
}

/// A serialized chart, not a cloned live owner. Remount requires the exact declared base and
/// its admitted restrictions; the public artifact layer is responsible for pinning those bytes.
#[derive(Debug, PartialEq, Eq)]
pub struct NativeFullSessionRest {
    pub header: NativeSessionRestHeader,
    pub carriers: BTreeMap<NativeCarrierOrdinal, ResidentSectionRest>,
    pub checkpoints: BTreeMap<NativeCarrierOrdinal, ResidentSectionRest>,
    pub terminal_carrier: Option<NativeTiledRest>,
    pub terminal_reacted: Option<NativeTiledRest>,
    pub terminal_contracted: Option<Vec<(i64, i64)>>,
    pub terminal_presented: Option<ResidentSectionRest>,
    pub overlay: BTreeMap<NativeTensorOrdinal, Vec<NativeOverlayRest>>,
    pub passage: Option<NativePassageRest>,
    pub reuse: Option<NativeForwardReuseRest>,
}

#[derive(Debug, Error)]
pub enum NativeSessionRestError {
    #[error("native session rest: {0}")]
    Malformed(String),
    #[error("this session rest boundary is not supported: {0}")]
    Unsupported(&'static str),
    #[error("resident rest: {0}")]
    Resident(#[from] ResidentRefusal),
    #[error("native operation: {0}")]
    Operation(#[from] NativeFullOperationError),
    #[error("rest I/O: {0}")]
    Io(#[from] std::io::Error),
    #[error("rest header: {0}")]
    Json(#[from] serde_json::Error),
}

pub(super) fn detach_carriers(
    surface: &ResidentSurface<'_>,
    carriers: &BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'_>>,
) -> Result<BTreeMap<NativeCarrierOrdinal, ResidentSectionRest>, NativeSessionRestError> {
    carriers
        .iter()
        .map(|(ordinal, carrier)| {
            Ok((
                *ordinal,
                surface.detach_section(&carrier.section, carrier.bound_octaves)?,
            ))
        })
        .collect()
}

pub(super) fn mount_carriers<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    rest: &BTreeMap<NativeCarrierOrdinal, ResidentSectionRest>,
) -> Result<BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'chart>>, NativeSessionRestError> {
    rest.iter()
        .map(|(ordinal, section)| {
            Ok((
                *ordinal,
                ContemporaryCarrier {
                    section: surface.mount_section_rest(section)?,
                    bound_octaves: section.bound_octaves,
                },
            ))
        })
        .collect()
}

pub(super) fn detach_overlays(
    surface: &ResidentSurface<'_>,
    overlays: &BTreeMap<NativeTensorOrdinal, Vec<OverlayAtom<'_>>>,
) -> Result<BTreeMap<NativeTensorOrdinal, Vec<NativeOverlayRest>>, NativeSessionRestError> {
    overlays
        .iter()
        .map(|(population, atoms)| {
            Ok((
                *population,
                atoms
                    .iter()
                    .map(|atom| atom.detach(surface))
                    .collect::<Result<_, _>>()?,
            ))
        })
        .collect()
}

pub(super) fn mount_overlays<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    rest: &BTreeMap<NativeTensorOrdinal, Vec<NativeOverlayRest>>,
) -> Result<BTreeMap<NativeTensorOrdinal, Vec<OverlayAtom<'chart>>>, NativeSessionRestError> {
    rest.iter()
        .map(|(population, atoms)| {
            Ok((
                *population,
                atoms
                    .iter()
                    .map(|atom| OverlayAtom::remount(surface, atom))
                    .collect::<Result<_, _>>()?,
            ))
        })
        .collect()
}

fn detach_tiled(
    surface: &ResidentSurface<'_>,
    tiled: &TiledCarrier<'_>,
) -> Result<NativeTiledRest, NativeSessionRestError> {
    if tiled.sections.len() != tiled.bounds.len() {
        return Err(NativeSessionRestError::Malformed("tiled bounds".into()));
    }
    Ok(NativeTiledRest {
        carrier: tiled.carrier,
        rows: tiled.rows,
        width: tiled.width,
        grain: tiled.grain.0,
        sections: tiled
            .sections
            .iter()
            .zip(&tiled.bounds)
            .map(|(section, bound)| surface.detach_section(section, *bound))
            .collect::<Result<_, _>>()?,
    })
}

fn mount_tiled<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    rest: &NativeTiledRest,
) -> Result<TiledCarrier<'chart>, NativeSessionRestError> {
    Ok(TiledCarrier {
        carrier: rest.carrier,
        rows: rest.rows,
        width: rest.width,
        grain: ResidentGrain(rest.grain),
        bounds: rest.sections.iter().map(|s| s.bound_octaves).collect(),
        sections: rest
            .sections
            .iter()
            .map(|s| surface.mount_section_rest(s))
            .collect::<Result<_, _>>()?,
    })
}

impl<'residence, 'chart> NativeFullOperatorSession<'residence, 'chart> {
    /// Detach state at an explicit checkpoint boundary while retaining the unique live owner.
    /// A failed writer need not consume this owner. Dissection/held external withdrawals refuse
    /// rather than silently omitting their independently owned material.
    pub fn detach_rest(&self) -> Result<NativeFullSessionRest, NativeSessionRestError> {
        if self.dissection.is_some() {
            return Err(NativeSessionRestError::Unsupported("dissection apparatus"));
        }
        if let Some(passage) = &self.passage_cultivation {
            passage.check_rest_ownership()?;
        }
        let surface = self.residence.surface();
        let rest = NativeFullSessionRest {
            header: NativeSessionRestHeader {
                schema: NATIVE_SESSION_REST_SCHEMA.into(),
                ecology: self.ecology.clone(),
                operation_at: self.operation_at,
                generation: self.generation,
                chronology: self.chronology.clone(),
                grain: self.grain.0,
                row_population: self.row_population,
                cycle_complete: self.cycle_complete,
                previous_context: self.previous_context.clone(),
                aperture: self.aperture,
                terminal_seal: self.terminal_seal,
                progress: self.progress.clone(),
                interruption: self.interruption.clone(),
            },
            carriers: detach_carriers(surface, &self.carriers)?,
            checkpoints: detach_carriers(surface, &self.checkpoints)?,
            terminal_carrier: self
                .terminal_carrier
                .as_ref()
                .map(|t| detach_tiled(surface, t))
                .transpose()?,
            terminal_reacted: self
                .terminal_reacted
                .as_ref()
                .map(|t| detach_tiled(surface, t))
                .transpose()?,
            terminal_contracted: self.terminal_contracted.clone(),
            terminal_presented: self
                .terminal_presented
                .as_ref()
                .map(|c| surface.detach_section(&c.section, c.bound_octaves))
                .transpose()?,
            overlay: detach_overlays(surface, &self.overlay)?,
            passage: self
                .passage_cultivation
                .as_ref()
                .map(|p| p.detach_rest(surface))
                .transpose()?,
            reuse: self
                .forward_reuse
                .as_ref()
                .map(|r| r.detach_rest(surface))
                .transpose()?,
        };
        rest.validate()?;
        Ok(rest)
    }

    /// Remount this chart on its declared coefficient base. This checks the complete operator
    /// chart, not coefficient content; callers must bind the actual base bytes, not only a path.
    pub fn remount_rest(
        ecology: &'residence NativeFullOperatorEcology,
        residence: &'residence mut NativeOperatorResidence<'chart>,
        rest: &NativeFullSessionRest,
    ) -> Result<Self, NativeSessionRestError> {
        rest.validate()?;
        if ecology != &rest.header.ecology {
            return Err(NativeSessionRestError::Malformed(
                "operator base chart differs".into(),
            ));
        }
        let mut session = match rest.header.aperture {
            Some(aperture) => Self::found_with_return(ecology, residence, aperture)?,
            None => Self::found(ecology, residence)?,
        };
        if session.grain.0 != rest.header.grain {
            return Err(NativeSessionRestError::Malformed(
                "base grain differs".into(),
            ));
        }
        let surface = session.residence.surface();
        session.carriers = mount_carriers(surface, &rest.carriers)?;
        session.checkpoints = mount_carriers(surface, &rest.checkpoints)?;
        session.terminal_carrier = rest
            .terminal_carrier
            .as_ref()
            .map(|t| mount_tiled(surface, t))
            .transpose()?;
        session.terminal_reacted = rest
            .terminal_reacted
            .as_ref()
            .map(|t| mount_tiled(surface, t))
            .transpose()?;
        session.terminal_contracted = rest.terminal_contracted.clone();
        session.terminal_presented = rest
            .terminal_presented
            .as_ref()
            .map(|s| {
                Ok::<_, NativeSessionRestError>(ContemporaryCarrier {
                    section: surface.mount_section_rest(s)?,
                    bound_octaves: s.bound_octaves,
                })
            })
            .transpose()?;
        session.overlay = mount_overlays(surface, &rest.overlay)?;
        session.passage_cultivation = rest
            .passage
            .as_ref()
            .map(|p| PassageCultivation::remount_rest(ecology, surface, p))
            .transpose()?;
        session.forward_reuse = rest
            .reuse
            .as_ref()
            .map(|r| NativeForwardReuse::remount_rest(ecology, surface, r))
            .transpose()?;
        if let Some(rows) = rest.header.row_population {
            session.ensure_row_population(rows)?;
        }
        session.operation_at = rest.header.operation_at;
        session.generation = rest.header.generation;
        session.chronology = rest.header.chronology.clone();
        session.cycle_complete = rest.header.cycle_complete;
        session.previous_context = rest.header.previous_context.clone();
        session.terminal_seal = rest.header.terminal_seal;
        session.progress = rest.header.progress.clone();
        session.interruption = rest.header.interruption.clone();
        Ok(session)
    }
}

impl NativeFullSessionRest {
    pub fn validate(&self) -> Result<(), NativeSessionRestError> {
        self.header
            .ecology
            .validate()
            .map_err(NativeFullOperationError::from)?;
        if self.header.schema != NATIVE_SESSION_REST_SCHEMA
            || self.header.generation != self.header.chronology.len() as u64
            || self
                .header
                .chronology
                .iter()
                .enumerate()
                .any(|(at, generation)| *generation != at as u64)
            || self.header.operation_at > self.header.ecology.operations.len()
            || (self.header.cycle_complete && self.header.operation_at != 0)
            || self.header.row_population == Some(0)
            || self
                .header
                .interruption
                .as_ref()
                .is_some_and(|i| self.header.progress.as_ref() != Some(&i.progress))
            || (self.header.aperture.is_some() && self.passage.is_some())
            || (self.reuse.is_some() && self.passage.is_none())
        {
            return Err(NativeSessionRestError::Malformed(
                "session header or profile".into(),
            ));
        }
        let section = |s: &ResidentSectionRest| -> Result<(), NativeSessionRestError> {
            s.validate().map_err(NativeSessionRestError::Malformed)?;
            if s.bound_octaves > 64
                || s.intervals.iter().any(|(lo, hi)| {
                    64 - lo.unsigned_abs().leading_zeros() > s.bound_octaves
                        || 64 - hi.unsigned_abs().leading_zeros() > s.bound_octaves
                })
            {
                return Err(NativeSessionRestError::Malformed(
                    "section octave declaration".into(),
                ));
            }
            Ok(())
        };
        for map in [&self.carriers, &self.checkpoints] {
            for (ordinal, held) in map {
                if ordinal.0 as usize >= self.header.ecology.carriers.len() {
                    return Err(NativeSessionRestError::Malformed("carrier address".into()));
                }
                section(held)?;
            }
        }
        for tiled in [&self.terminal_carrier, &self.terminal_reacted]
            .into_iter()
            .flatten()
        {
            let width = tiled
                .sections
                .iter()
                .try_fold(0usize, |sum, s| sum.checked_add(s.width));
            if tiled.sections.is_empty()
                || width != Some(tiled.width)
                || tiled.carrier.0 as usize >= self.header.ecology.carriers.len()
                || tiled
                    .sections
                    .iter()
                    .any(|s| s.rows != tiled.rows || s.grain.0 != tiled.grain)
            {
                return Err(NativeSessionRestError::Malformed("tiled terminal".into()));
            }
            for held in &tiled.sections {
                section(held)?;
            }
        }
        if let Some(held) = &self.terminal_presented {
            section(held)?;
        }
        let overlays = |map: &BTreeMap<NativeTensorOrdinal, Vec<NativeOverlayRest>>| -> Result<(), NativeSessionRestError> {
            for (population, atoms) in map {
                let shape = self.header.ecology.coefficient_populations.get(population.0 as usize)
                    .ok_or_else(|| NativeSessionRestError::Malformed("overlay population".into()))?;
                for atom in atoms {
                    atom.validate()?;
                    if shape.shape.as_slice() != [atom.rows, atom.width] { return Err(NativeSessionRestError::Malformed("overlay shape differs from its base".into())); }
                }
            }
            Ok(())
        };
        overlays(&self.overlay)?;
        if let Some(passage) = &self.passage {
            overlays(&passage.pending)?;
        }
        if let Some(reuse) = &self.reuse {
            for (ordinal, held) in &reuse.standing {
                section(held)?;
                if !reuse.numerical.contains_key(ordinal) {
                    return Err(NativeSessionRestError::Malformed(
                        "retained numerical source absent".into(),
                    ));
                }
            }
            for (ordinal, numerical) in &reuse.numerical {
                let operation = self
                    .header
                    .ecology
                    .operations
                    .get(numerical.origin.operation as usize)
                    .ok_or_else(|| {
                        NativeSessionRestError::Malformed("numerical origin operation".into())
                    })?;
                if operation.output != *ordinal
                    || numerical.origin.occurrence > self.header.generation
                {
                    return Err(NativeSessionRestError::Malformed(
                        "numerical origin boundary".into(),
                    ));
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod native_tests {
    use super::super::{
        mount_operator_surface, NativeAttentionTopology, NativeCarrierAxis, NativeCarrierChart,
        NativeCoefficientIntake, NativeCoefficientPopulation, NativeKvStanding,
        NativeLayerTopology, NativeOperationPrimitive as P, NativeOperatorNode,
        NativeOperatorResidenceError, NativeScaleConstraint as S,
        NATIVE_FULL_OPERATOR_ECOLOGY_SCHEMA,
    };
    use super::*;
    use crate::embedding_fiber::ResidentReadout;

    fn interrupted_chart() -> NativeFullOperatorEcology {
        let node = |at: u32, primitive, inputs: &[u32], coefficients: &[u32]| NativeOperatorNode {
            ordinal: at,
            layer: (at < 5).then_some(0),
            primitive,
            inputs: inputs.iter().copied().map(NativeCarrierOrdinal).collect(),
            output: NativeCarrierOrdinal(at),
            coefficients: coefficients
                .iter()
                .copied()
                .map(NativeTensorOrdinal)
                .collect(),
        };
        NativeFullOperatorEcology {
            schema: NATIVE_FULL_OPERATOR_ECOLOGY_SCHEMA.into(),
            shared_carrier_extent: 2,
            coefficient_populations: [vec![3, 2], vec![3, 2], vec![2, 3], vec![4, 1]]
                .into_iter()
                .enumerate()
                .map(|(at, shape)| NativeCoefficientPopulation {
                    ordinal: NativeTensorOrdinal(at as u32),
                    coefficient_population: shape.iter().product::<usize>() as u64,
                    shape,
                })
                .collect(),
            carriers: [2, 3, 2, 2, 1, 4, 4, 4, 4, 4]
                .into_iter()
                .enumerate()
                .map(|(at, width)| NativeCarrierChart {
                    ordinal: NativeCarrierOrdinal(at as u32),
                    axes: vec![
                        NativeCarrierAxis::Occurrence,
                        NativeCarrierAxis::Fixed(width),
                    ],
                })
                .collect(),
            operations: vec![
                node(
                    0,
                    P::Lookup {
                        scale: S::Bfloat16NearestSquareRootOf(1),
                    },
                    &[],
                    &[0],
                ),
                node(1, P::Contract, &[0], &[1]),
                node(2, P::Contract, &[1], &[2]),
                node(3, P::Add, &[0, 2], &[]),
                node(4, P::Select { axis: 1, at: 0 }, &[3], &[]),
                node(5, P::Contract, &[4], &[3]),
                // An explicit pole in the declared terminal chart. Earlier native current and
                // the local return really execute; the terminal law must then refuse.
                node(
                    6,
                    P::Scale {
                        by: S::Rational {
                            numerator: 1,
                            denominator: 0,
                        },
                    },
                    &[5],
                    &[],
                ),
                node(7, P::Tanh, &[6], &[]),
                node(
                    8,
                    P::Scale {
                        by: S::Rational {
                            numerator: 1,
                            denominator: 1,
                        },
                    },
                    &[7],
                    &[],
                ),
                node(9, P::Emit, &[8], &[]),
            ],
            layers: vec![NativeLayerTopology {
                ordinal: 0,
                attention: NativeAttentionTopology::Local,
                kv_standing: NativeKvStanding::Own,
                first_operation: 0,
                operation_population: 5,
            }],
            coefficient_obstructions: vec![],
        }
    }

    struct Intake(Vec<usize>);
    impl NativeCoefficientIntake for Intake {
        fn populations(&self) -> usize {
            self.0.len()
        }
        fn population_octets(&self, ordinal: usize) -> Result<u64, NativeOperatorResidenceError> {
            Ok(self.0[ordinal] as u64 * 2)
        }
        fn deliver(
            &mut self,
            ordinal: usize,
            sink: &mut dyn FnMut(usize, &[u8]) -> Result<(), NativeOperatorResidenceError>,
        ) -> Result<(), NativeOperatorResidenceError> {
            let bytes: Vec<u8> = (0..self.0[ordinal])
                .flat_map(|_| 0x3f80u16.to_le_bytes())
                .collect();
            sink(0, &bytes)
        }
    }

    #[test]
    #[ignore = "requires CUDA; actual partial native return survives an obstruction and remount"]
    fn an_interrupted_native_owner_preserves_pending_morphology_and_refuses_silent_replay() {
        let ecology = interrupted_chart();
        let mut intake = Intake(
            ecology
                .coefficient_populations
                .iter()
                .map(|p| p.coefficient_population as usize)
                .collect(),
        );
        let readout = ResidentReadout::new().expect("CUDA");
        let surface = mount_operator_surface(&readout).unwrap();
        let mut residence =
            NativeOperatorResidence::mount_from_intake(&surface, &ecology, &mut intake).unwrap();
        let mut session = NativeFullOperatorSession::found_with_passage_return(
            &ecology,
            &mut residence,
            NativeReturnAperture {
                learning_shift: 16,
                series_terms: 14,
            },
        )
        .unwrap();
        assert!(session.advance_cycle_retained(&[0]).is_err());
        let interruption = session.interruption().expect("explicit held interruption");
        assert_eq!(interruption.progress.installed_through, Some(4));
        assert!(interruption.progress.at_terminal);
        let state = session.detach_rest().unwrap();
        assert!(!state.carriers.is_empty() || !state.checkpoints.is_empty());
        assert!(!state.passage.as_ref().unwrap().pending.is_empty());
        assert!(
            state.overlay.is_empty(),
            "an unclosed return is not published morphology"
        );
        assert!(matches!(
            session.advance_cycle_retained(&[0]),
            Err(NativeFullOperationError::Interrupted)
        ));
        assert!(
            session.detach_rest().unwrap() == state,
            "refusal cannot silently retry or mutate the held state"
        );
        let mut bytes = Vec::new();
        state.write_to(&mut bytes).unwrap();
        let decoded =
            NativeFullSessionRest::read_from(&mut &bytes[..], bytes.len() as u64).unwrap();
        assert_eq!(decoded, state);
        drop(session);
        let mut resumed =
            NativeFullOperatorSession::remount_rest(&ecology, &mut residence, &decoded).unwrap();
        assert!(resumed.detach_rest().unwrap() == decoded);
        assert!(matches!(
            resumed.advance_cycle_retained(&[0]),
            Err(NativeFullOperationError::Interrupted)
        ));
    }
}

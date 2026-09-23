//! **The one rest of the extracted operator.** An exterior chart of a session's state, never a
//! cloned live owner; this codec never runs inside a recurrence. Both executors rest here: the
//! graph session (`ExtractedOperatorSession`) and the branch session (`ExtractedBranchSession`,
//! whose morphology is the six-node instance of the same constitution chart). The coefficient
//! base is an explicit separate dependency; this state is not source-independent.
//!
//! [definition] Retention law (`CLAUDE.md`, `Foundation/Standing.lean`): a rest carries the
//! quotient the admitted future needs — the operation position and chronology, the contemporary
//! carriers of an unfinished word with their within-cycle checkpoints, the receiver's emitted face,
//! the deposited overlay (the constitution's change), a pending passage return and the numerical
//! reuse standing. It never carries a previous cycle's terminal cut: the continuing return reads
//! the contemporary constitution at `previous_context`. Older wires that still carry the reacted
//! and presented terminal carriers or the dissection's tied row decode; those fields are read and
//! released, never remounted.

use super::{
    full_operation::ContemporaryCarrier, operative_passage_return::PassageCultivation,
    operative_return::OverlayAtom, operative_reuse::NativeForwardReuse,
    operative_terminal::TiledCarrier, ExtractedOperatorRefusal, ExtractedOperatorSession,
    NativeCarrierOrdinal, NativeCycleInterruption, NativeCycleProgress, NativeForwardReuseCensus,
    NativeFullOperatorEcology, NativeNumericalOrigin, NativeOperatorResidence,
    NativePassageReturn, NativeReturnAperture, NativeSuccessorProjection, NativeTensorOrdinal,
};
use crate::resident_section::{
    ResidentGrain, ResidentRefusal, ResidentSectionRest, ResidentSurface,
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

pub const NATIVE_SESSION_REST_SCHEMA: &str = "holonic-engine.native-full-session-rest.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExtractedOperatorRestHeader {
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

/// The rest of one deposited overlay atom `u · v` — the constitution's change on one coefficient
/// population, not another running ecology. The two arrays are the actual sealed integer factors,
/// with their distinct dyadic exponents.
#[derive(Debug, PartialEq, Eq)]
pub struct NativeOverlayRest {
    pub rows: usize,
    pub width: usize,
    pub rank: usize,
    pub u: Vec<i64>,
    pub v: Vec<i64>,
    pub u_exponent: i32,
    pub v_exponent: i32,
    pub u_octaves: u32,
    pub v_octaves: u32,
}

impl NativeOverlayRest {
    pub fn validate(&self) -> Result<(), ResidentRefusal> {
        let bound = |words: &[i64], octaves: u32| octaves <= 64 && words.iter().all(|word|
            64 - word.unsigned_abs().leading_zeros() <= octaves);
        if self.rows == 0 || self.width == 0 || self.rank == 0
            || self.rows.checked_mul(self.rank) != Some(self.u.len())
            || self.rank.checked_mul(self.width) != Some(self.v.len())
            || !bound(&self.u, self.u_octaves) || !bound(&self.v, self.v_octaves) {
            return Err(ResidentRefusal::Declaration { operation: "native-overlay-rest",
                what: "factor shapes or declared octave bounds do not reconstruct the held atom".into() });
        }
        Ok(())
    }
}

/// **The one rest.** A serialized chart, not a cloned live owner. Remount requires the exact
/// declared base and its admitted restrictions; the public artifact layer is responsible for
/// pinning those bytes.
#[derive(Debug, PartialEq, Eq)]
pub struct ExtractedOperatorRest {
    pub header: ExtractedOperatorRestHeader,
    /// The contemporary carriers of the unfinished word (the branch: its current carrier and,
    /// inside the word, the retained re-entry carrier at `c0`).
    pub carriers: BTreeMap<NativeCarrierOrdinal, ResidentSectionRest>,
    /// Cross-layer checkpoints of the unfinished cycle; empty at a cycle boundary.
    pub checkpoints: BTreeMap<NativeCarrierOrdinal, ResidentSectionRest>,
    /// The emitted face held for its receiver.
    pub terminal_carrier: Option<NativeTiledRest>,
    pub overlay: BTreeMap<NativeTensorOrdinal, Vec<NativeOverlayRest>>,
    pub passage: Option<NativePassageRest>,
    pub reuse: Option<NativeForwardReuseRest>,
}

pub(super) fn detach_carriers(
    surface: &ResidentSurface<'_>,
    carriers: &BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'_>>,
) -> Result<BTreeMap<NativeCarrierOrdinal, ResidentSectionRest>, ExtractedOperatorRefusal> {
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
) -> Result<BTreeMap<NativeCarrierOrdinal, ContemporaryCarrier<'chart>>, ExtractedOperatorRefusal> {
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
) -> Result<BTreeMap<NativeTensorOrdinal, Vec<NativeOverlayRest>>, ExtractedOperatorRefusal> {
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
) -> Result<BTreeMap<NativeTensorOrdinal, Vec<OverlayAtom<'chart>>>, ExtractedOperatorRefusal> {
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
) -> Result<NativeTiledRest, ExtractedOperatorRefusal> {
    if tiled.sections.len() != tiled.bounds.len() {
        return Err(ExtractedOperatorRefusal::Rest("tiled bounds".into()));
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
) -> Result<TiledCarrier<'chart>, ExtractedOperatorRefusal> {
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

impl<'residence, 'chart> ExtractedOperatorSession<'residence, 'chart> {
    /// Detach state at an explicit checkpoint boundary while retaining the unique live owner.
    /// A failed writer need not consume this owner. Dissection/held external withdrawals refuse
    /// rather than silently omitting their independently owned material.
    pub fn detach_rest(&self) -> Result<ExtractedOperatorRest, ExtractedOperatorRefusal> {
        if self.dissection.is_some() {
            return Err(ExtractedOperatorRefusal::Unsupported("dissection apparatus"));
        }
        if let Some(passage) = &self.passage_cultivation {
            passage.check_rest_ownership()?;
        }
        let surface = self.residence.surface();
        let rest = ExtractedOperatorRest {
            header: ExtractedOperatorRestHeader {
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
        rest: &ExtractedOperatorRest,
    ) -> Result<Self, ExtractedOperatorRefusal> {
        rest.validate()?;
        if ecology != &rest.header.ecology {
            return Err(ExtractedOperatorRefusal::Rest(
                "operator base chart differs".into(),
            ));
        }
        let mut session = match rest.header.aperture {
            Some(aperture) => Self::found_with_return(ecology, residence, aperture)?,
            None => Self::found(ecology, residence)?,
        };
        if session.grain.0 != rest.header.grain {
            return Err(ExtractedOperatorRefusal::Rest(
                "base grain differs".into(),
            ));
        }
        let surface = session.residence.surface();
        session.carriers = mount_carriers(surface, &rest.carriers)?;
        // A cycle boundary holds no checkpoints; an older wire's previous-cycle checkpoints are
        // released here rather than remounted as an archive of the last cycle.
        if !rest.header.cycle_complete || rest.header.interruption.is_some() {
            session.checkpoints = mount_carriers(surface, &rest.checkpoints)?;
        }
        session.terminal_carrier = rest
            .terminal_carrier
            .as_ref()
            .map(|t| mount_tiled(surface, t))
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

impl ExtractedOperatorRest {
    pub fn validate(&self) -> Result<(), ExtractedOperatorRefusal> {
        self.header
            .ecology
            .validate()
            .map_err(ExtractedOperatorRefusal::from)?;
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
            return Err(ExtractedOperatorRefusal::Rest(
                "session header or profile".into(),
            ));
        }
        let section = |s: &ResidentSectionRest| -> Result<(), ExtractedOperatorRefusal> {
            s.validate().map_err(ExtractedOperatorRefusal::Rest)?;
            if s.bound_octaves > 64
                || s.intervals.iter().any(|(lo, hi)| {
                    64 - lo.unsigned_abs().leading_zeros() > s.bound_octaves
                        || 64 - hi.unsigned_abs().leading_zeros() > s.bound_octaves
                })
            {
                return Err(ExtractedOperatorRefusal::Rest(
                    "section octave declaration".into(),
                ));
            }
            Ok(())
        };
        for map in [&self.carriers, &self.checkpoints] {
            for (ordinal, held) in map {
                if ordinal.0 as usize >= self.header.ecology.carriers.len() {
                    return Err(ExtractedOperatorRefusal::Rest("carrier address".into()));
                }
                section(held)?;
            }
        }
        if let Some(tiled) = &self.terminal_carrier {
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
                return Err(ExtractedOperatorRefusal::Rest("tiled terminal".into()));
            }
            for held in &tiled.sections {
                section(held)?;
            }
        }
        let overlays = |map: &BTreeMap<NativeTensorOrdinal, Vec<NativeOverlayRest>>| -> Result<(), ExtractedOperatorRefusal> {
            for (population, atoms) in map {
                let shape = self.header.ecology.coefficient_populations.get(population.0 as usize)
                    .ok_or_else(|| ExtractedOperatorRefusal::Rest("overlay population".into()))?;
                for atom in atoms {
                    atom.validate()?;
                    if shape.shape.as_slice() != [atom.rows, atom.width] { return Err(ExtractedOperatorRefusal::Rest("overlay shape differs from its base".into())); }
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
                    return Err(ExtractedOperatorRefusal::Rest(
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
                        ExtractedOperatorRefusal::Rest("numerical origin operation".into())
                    })?;
                if operation.output != *ordinal
                    || numerical.origin.occurrence > self.header.generation
                {
                    return Err(ExtractedOperatorRefusal::Rest(
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
        let mut session = ExtractedOperatorSession::found_with_passage_return(
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
            Err(ExtractedOperatorRefusal::Interrupted)
        ));
        assert!(
            session.detach_rest().unwrap() == state,
            "refusal cannot silently retry or mutate the held state"
        );
        let mut bytes = Vec::new();
        state.write_to(&mut bytes).unwrap();
        let decoded =
            ExtractedOperatorRest::read_from(&mut &bytes[..], bytes.len() as u64).unwrap();
        assert_eq!(decoded, state);
        drop(session);
        let mut resumed =
            ExtractedOperatorSession::remount_rest(&ecology, &mut residence, &decoded).unwrap();
        assert!(resumed.detach_rest().unwrap() == decoded);
        assert!(matches!(
            resumed.advance_cycle_retained(&[0]),
            Err(ExtractedOperatorRefusal::Interrupted)
        ));
    }

    #[test]
    #[ignore = "requires CUDA; live row acquisition and staged refusal"]
    fn live_input_rows_stage_before_publish_and_preserve_held_native_state() {
        use super::super::NativeInputRowExtension;
        struct Input;
        impl NativeCoefficientIntake for Input {
            fn populations(&self)->usize {4}
            fn population_octets(&self,at:usize)->Result<u64,NativeOperatorResidenceError> {Ok([12,12,12,8][at])}
            fn retained_rows(&self,at:usize)->Result<Option<Vec<u32>>,NativeOperatorResidenceError> {Ok((at==0).then_some(vec![0]))}
            fn deliver_retained(&mut self,at:usize,sink:&mut dyn FnMut(usize,&[u8])->Result<(),NativeOperatorResidenceError>) -> Result<(),NativeOperatorResidenceError> {
                let count=[2,6,6,4][at];
                let bytes:Vec<_>=(0..count).flat_map(|_|0x3e80u16.to_le_bytes()).collect();
                sink(0,&bytes)
            }
            fn deliver(&mut self,at:usize,sink:&mut dyn FnMut(usize,&[u8])->Result<(),NativeOperatorResidenceError>) -> Result<(),NativeOperatorResidenceError> {
                if at==0 {sink(0,&[0x80,0x3e,0x80,0x3e,0,0,0,0,0,0,0,0])} else {self.deliver_retained(at,sink)}
            }
        }
        let mut graph=interrupted_chart();
        graph.operations[6].primitive=P::Scale {by:S::Rational {numerator:1,denominator:1}};
        let readout=ResidentReadout::new().unwrap();
        let surface=mount_operator_surface(&readout).unwrap();
        let mut residence=NativeOperatorResidence::mount_from_intake(&surface,&graph,&mut Input).unwrap();
        let mut session=ExtractedOperatorSession::found(&graph,&mut residence).unwrap();
        let old=session.advance_cycle_retained(&[0]).unwrap().final_emission.intervals;
        let held=session.detach_rest().unwrap();
        let finer=NativeInputRowExtension {population:0,rows:3,dim:2,addresses:vec![1],words:vec![1,1]};
        assert!(matches!(session.extend_input_rows(&[finer]),Err(ExtractedOperatorRefusal::Grain)));
        assert_eq!(session.missing_input_rows(&[1])[&0],vec![1]);
        assert_eq!(session.detach_rest().unwrap(),held);
        let added=NativeInputRowExtension {population:0,rows:3,dim:2,addresses:vec![1],words:vec![0x3f00,0x3f00]};
        session.extend_input_rows(std::slice::from_ref(&added)).unwrap();
        assert!(session.missing_input_rows(&[0,1]).is_empty());
        assert_eq!(session.detach_rest().unwrap(),held);
        assert!(session.extend_input_rows(&[added]).is_err());
        assert_eq!(session.detach_rest().unwrap(),held);
        assert_eq!(session.advance_cycle_retained(&[0]).unwrap().final_emission.intervals,old);
        assert_ne!(session.advance_cycle_retained(&[1]).unwrap().final_emission.intervals,old);
    }
}

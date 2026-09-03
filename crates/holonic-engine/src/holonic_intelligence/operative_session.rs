//! Resident recurrence over one source-neutral operator morphology.
//!
//! Every mathematical operation is one step. Its resident carrier is moved into the next step;
//! no exterior verdict, candidate, commit, or reconstructed predecessor sits between them.

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    embedding_fiber::{MountedReadout, ResidentReadout},
    resident_section::{
        Dyadic, ResidentGrain, ResidentRefusal, ResidentSection, ResidentSectionRest,
        ResidentSurface, SeriesAperture, TransferCensus,
    },
};

use super::{NativeOperatorKind, NativeOperatorMorphology, NativeOperatorMorphologyError};

pub const NATIVE_OPERATOR_STEP_SCHEMA: &str = "holonic-engine.native-operator-step.v1";
pub const NATIVE_OPERATOR_SESSION_REST_SCHEMA: &str =
    "holonic-engine.native-operator-session-rest.v1";

/// Source-neutral coefficient populations mounted once for every later operation.
pub struct ResidentOperatorMorphology<'morphology, 'chart> {
    morphology: &'morphology NativeOperatorMorphology,
    surface: &'chart ResidentSurface<'chart>,
    input: MountedReadout<'chart>,
    output: MountedReadout<'chart>,
    gain: MountedReadout<'chart>,
    gelu_c1: Dyadic,
    gelu_c2: Dyadic,
    epsilon: Dyadic,
    series: SeriesAperture,
}

impl<'morphology, 'chart> ResidentOperatorMorphology<'morphology, 'chart> {
    pub fn mount(
        surface: &'chart ResidentSurface<'chart>,
        morphology: &'morphology NativeOperatorMorphology,
    ) -> Result<Self, NativeOperatorExecutionError> {
        morphology.validate()?;
        let readout = surface.readout();
        let input = readout.mount_bfloat16(
            &morphology.matrices[0].bfloat16_words()?,
            morphology.carrier_extent,
        )?;
        let output = readout.mount_bfloat16(
            &morphology.matrices[1].bfloat16_words()?,
            morphology.interaction_extent,
        )?;
        let gain_words = morphology
            .norm_gain
            .iter()
            .copied()
            .map(|value| value.bfloat16_word())
            .collect::<Result<Vec<_>, _>>()?;
        let gain = readout.mount_bfloat16(&gain_words, morphology.carrier_extent)?;
        Ok(Self {
            morphology,
            surface,
            input,
            output,
            gain,
            gelu_c1: Dyadic::of_binary64_bits(0x3fe9884533d43651)?,
            gelu_c2: Dyadic::of_binary64_bits(0x3fa6e4e26d4801f7)?,
            epsilon: Dyadic::of_binary64_bits(0x3eb0c6f7a0b5ed8d)?,
            series: SeriesAperture(14),
        })
    }

    pub fn device_name(&self) -> &str {
        self.surface.device_name()
    }

    pub fn resident_coefficient_octets(&self) -> usize {
        self.input.resident_octets() + self.output.resident_octets() + self.gain.resident_octets()
    }

    /// The finest initial carrier grain admitted by the material and the card.
    pub fn finest_initial_grain(
        &self,
        carrier_words: &[u16],
    ) -> Result<ResidentGrain, NativeOperatorExecutionError> {
        if carrier_words.len() != self.morphology.carrier_extent {
            return Err(NativeOperatorExecutionError::CarrierExtent);
        }
        let section_word_octaves = i64::BITS - 1;
        (0..=ResidentSurface::carrier_octaves().min(section_word_octaves))
            .rev()
            .find_map(|grain| {
                let grain = ResidentGrain(grain);
                let entered = self
                    .surface
                    .shape_enter(
                        1,
                        self.morphology.carrier_extent,
                        Dyadic::ONE,
                        grain,
                        carrier_words,
                    )
                    .ok()?;
                let projected = self
                    .surface
                    .shape_contract(
                        1,
                        self.morphology.carrier_extent,
                        entered.needed,
                        &self.input,
                    )
                    .ok()?;
                self.surface
                    .shape_gelu_tanh(
                        1,
                        self.morphology.interaction_extent,
                        projected.needed,
                        grain,
                        self.gelu_c1,
                        self.gelu_c2,
                        self.series,
                    )
                    .ok()
                    .map(|_| grain)
            })
            .ok_or(NativeOperatorExecutionError::NoAdmittedGrain)
    }

    pub fn mount_initial<'resident>(
        &'resident self,
        carrier_words: &[u16],
        grain: ResidentGrain,
    ) -> Result<NativeOperatorSession<'resident, 'morphology, 'chart>, NativeOperatorExecutionError>
    {
        if carrier_words.len() != self.morphology.carrier_extent {
            return Err(NativeOperatorExecutionError::CarrierExtent);
        }
        let shape = self.surface.shape_enter(
            1,
            self.morphology.carrier_extent,
            Dyadic::ONE,
            grain,
            carrier_words,
        )?;
        let staged = self
            .surface
            .stage_words(carrier_words, 1, self.morphology.carrier_extent)?;
        let carrier = self
            .surface
            .fresh_section(1, self.morphology.carrier_extent, grain)?;
        let mut builder = self.surface.begin_passage(&[vec![]])?;
        let lane = builder.open(0, &[])?;
        self.surface
            .record_enter(&lane, &staged, Dyadic::ONE, &carrier)?;
        builder.close(0, &carrier, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound = exact_bound(&reading).map_err(|flags| {
            NativeOperatorExecutionError::ResidentObstruction {
                operation: "enter".to_owned(),
                flags,
            }
        })?;
        Ok(NativeOperatorSession {
            resident: self,
            carrier,
            carrier_bound: bound,
            retained_reentry: None,
            operation_at: 0,
            generation: 0,
            chronology: Vec::new(),
        })
    }

    pub fn remount_session<'resident>(
        &'resident self,
        rest: &NativeOperatorSessionRest,
    ) -> Result<NativeOperatorSession<'resident, 'morphology, 'chart>, NativeOperatorExecutionError>
    {
        rest.validate(self.morphology.operations.len())?;
        let carrier_rest = ResidentSectionRest::read(&rest.carrier_wire)
            .map_err(NativeOperatorExecutionError::Rest)?;
        let carrier = self.surface.mount_section_rest(&carrier_rest)?;
        let retained_reentry = rest
            .retained_reentry_wire
            .as_deref()
            .map(ResidentSectionRest::read)
            .transpose()
            .map_err(NativeOperatorExecutionError::Rest)?
            .as_ref()
            .map(|retained| self.surface.mount_section_rest(retained))
            .transpose()?
            .zip(rest.retained_reentry_bound);
        Ok(NativeOperatorSession {
            resident: self,
            carrier,
            carrier_bound: rest.carrier_bound,
            retained_reentry,
            operation_at: rest.operation_at,
            generation: rest.generation,
            chronology: rest.chronology.clone(),
        })
    }
}

/// One ordinary occurrence. Only Hadamard contact consumes an additional carrier population.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeOperatorOccurrence {
    pub ordinal: u64,
    pub interaction_words: Vec<u16>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeOperatorEmission {
    pub generation: u64,
    pub operation: NativeOperatorKind,
    pub rows: usize,
    pub width: usize,
    pub grain: u32,
    pub intervals: Vec<(i64, i64)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeOperatorTrace {
    pub schema: String,
    pub predecessor_generation: u64,
    pub successor_generation: u64,
    pub occurrence: u64,
    pub chronology: Vec<u64>,
    pub operation: NativeOperatorKind,
    pub predecessor_width: usize,
    pub successor_width: usize,
    pub resident_coefficient_octets: usize,
    pub passage_slot_population: usize,
    pub refusal_population: usize,
    pub successor_bound_octaves: u32,
    pub census_before: TransferCensus,
    pub census_after: TransferCensus,
}

/// The move-owned contemporary ecology. Coefficients remain resident; the carrier itself advances.
pub struct NativeOperatorSession<'resident, 'morphology, 'chart> {
    resident: &'resident ResidentOperatorMorphology<'morphology, 'chart>,
    carrier: ResidentSection<'chart>,
    carrier_bound: u32,
    retained_reentry: Option<(ResidentSection<'chart>, u32)>,
    operation_at: usize,
    generation: u64,
    chronology: Vec<u64>,
}

pub struct NativeOperatorStep<'resident, 'morphology, 'chart> {
    pub emission: NativeOperatorEmission,
    pub trace: NativeOperatorTrace,
    pub successor: NativeOperatorSession<'resident, 'morphology, 'chart>,
}

pub struct NativeOperatorBranch<'resident, 'morphology, 'chart> {
    pub emissions: Vec<NativeOperatorEmission>,
    pub traces: Vec<NativeOperatorTrace>,
    pub successor: NativeOperatorSession<'resident, 'morphology, 'chart>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOperatorSessionRest {
    pub schema: String,
    pub carrier_wire: Vec<u8>,
    pub retained_reentry_wire: Option<Vec<u8>>,
    pub retained_reentry_bound: Option<u32>,
    pub carrier_bound: u32,
    pub operation_at: usize,
    pub generation: u64,
    pub chronology: Vec<u64>,
}

impl NativeOperatorSessionRest {
    pub fn validate(
        &self,
        operation_population: usize,
    ) -> Result<(), NativeOperatorExecutionError> {
        let carrier = ResidentSectionRest::read(&self.carrier_wire)
            .map_err(NativeOperatorExecutionError::Rest)?;
        if self.schema != NATIVE_OPERATOR_SESSION_REST_SCHEMA
            || operation_population == 0
            || self.operation_at >= operation_population
            || self.chronology.len() as u64 != self.generation
            || self.operation_at != self.generation as usize % operation_population
            || carrier.bound_octaves != self.carrier_bound
            || self.retained_reentry_wire.is_some() != self.retained_reentry_bound.is_some()
        {
            return Err(NativeOperatorExecutionError::Rest(
                "the recurrent session rest is malformed".to_owned(),
            ));
        }
        if let Some(wire) = &self.retained_reentry_wire {
            ResidentSectionRest::read(wire).map_err(NativeOperatorExecutionError::Rest)?;
        }
        Ok(())
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, NativeOperatorExecutionError> {
        self.validate(6)?;
        serde_json::to_vec(self)
            .map_err(|error| NativeOperatorExecutionError::Rest(error.to_string()))
    }

    pub fn read(bytes: &[u8]) -> Result<Self, NativeOperatorExecutionError> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| NativeOperatorExecutionError::Rest(error.to_string()))?;
        rest.validate(6)?;
        Ok(rest)
    }
}

impl<'resident, 'morphology, 'chart> NativeOperatorSession<'resident, 'morphology, 'chart> {
    pub fn generation(&self) -> u64 {
        self.generation
    }

    pub fn chronology(&self) -> &[u64] {
        &self.chronology
    }

    pub fn operation_at(&self) -> usize {
        self.operation_at
    }

    pub fn rest(&self) -> Result<NativeOperatorSessionRest, NativeOperatorExecutionError> {
        let carrier_wire = self
            .resident
            .surface
            .detach_section(&self.carrier, self.carrier_bound)?
            .canonical_bytes()
            .map_err(NativeOperatorExecutionError::Rest)?;
        let retained_reentry_wire = self
            .retained_reentry
            .as_ref()
            .map(|(section, bound)| {
                self.resident
                    .surface
                    .detach_section(section, *bound)?
                    .canonical_bytes()
                    .map_err(|error| ResidentRefusal::Declaration {
                        operation: "operator-rest",
                        what: error,
                    })
            })
            .transpose()?;
        let rest = NativeOperatorSessionRest {
            schema: NATIVE_OPERATOR_SESSION_REST_SCHEMA.to_owned(),
            carrier_wire,
            retained_reentry_wire,
            retained_reentry_bound: self.retained_reentry.as_ref().map(|(_, bound)| *bound),
            carrier_bound: self.carrier_bound,
            operation_at: self.operation_at,
            generation: self.generation,
            chronology: self.chronology.clone(),
        };
        rest.validate(self.resident.morphology.operations.len())?;
        Ok(rest)
    }

    /// Complete the morphology's own operation word. The word, not the caller, decides its extent
    /// and which operation receives the additional interaction carrier.
    pub fn advance_branch(
        mut self,
        interaction_words: &[u16],
    ) -> Result<NativeOperatorBranch<'resident, 'morphology, 'chart>, NativeOperatorExecutionError>
    {
        let extent = self.resident.morphology.operations.len();
        let mut emissions = Vec::with_capacity(extent);
        let mut traces = Vec::with_capacity(extent);
        for _ in 0..extent {
            let occurrence = NativeOperatorOccurrence {
                ordinal: self.generation,
                interaction_words: if matches!(
                    self.resident.morphology.operations[self.operation_at],
                    NativeOperatorKind::HadamardOccurrence
                ) {
                    interaction_words.to_vec()
                } else {
                    Vec::new()
                },
            };
            let step = self.advance(occurrence)?;
            emissions.push(step.emission);
            traces.push(step.trace);
            self = step.successor;
        }
        Ok(NativeOperatorBranch {
            emissions,
            traces,
            successor: self,
        })
    }

    pub fn advance(
        self,
        occurrence: NativeOperatorOccurrence,
    ) -> Result<NativeOperatorStep<'resident, 'morphology, 'chart>, NativeOperatorExecutionError>
    {
        if occurrence.ordinal != self.generation {
            return Err(NativeOperatorExecutionError::Occurrence);
        }
        let morphology = self.resident.morphology;
        let operation = morphology
            .operations
            .get(self.operation_at)
            .cloned()
            .ok_or(NativeOperatorExecutionError::Operation)?;
        let surface = self.resident.surface;
        let predecessor_width = self.carrier.width();
        let grain = self.carrier.grain();

        let (successor_carrier, reading, retained_reentry) = match &operation {
            NativeOperatorKind::Contract { matrix } if matrix == "operator/input-cross-section" => {
                require_empty(&occurrence)?;
                let shape = surface.shape_contract(
                    1,
                    predecessor_width,
                    self.carrier_bound,
                    &self.resident.input,
                )?;
                let out = surface.fresh_section(1, morphology.interaction_extent, grain)?;
                let mut builder = surface.begin_passage(&[vec![]])?;
                let lane = builder.open(0, &[])?;
                surface.record_contract(&lane, &self.carrier, &self.resident.input, &out)?;
                builder.close(0, &out, shape.needed)?;
                let reading = builder.finish()?.launch()?;
                (out, reading, Some((self.carrier, self.carrier_bound)))
            }
            NativeOperatorKind::GeluTanh => {
                require_empty(&occurrence)?;
                let shape = surface.shape_gelu_tanh(
                    1,
                    predecessor_width,
                    self.carrier_bound,
                    grain,
                    self.resident.gelu_c1,
                    self.resident.gelu_c2,
                    self.resident.series,
                )?;
                let out = surface.fresh_section(1, predecessor_width, grain)?;
                let mut builder = surface.begin_passage(&[vec![]])?;
                let lane = builder.open(0, &[])?;
                surface.record_gelu_tanh(
                    &lane,
                    &self.carrier,
                    self.resident.gelu_c1,
                    self.resident.gelu_c2,
                    self.resident.series,
                    &out,
                )?;
                builder.close(0, &out, shape.needed)?;
                let reading = builder.finish()?.launch()?;
                (out, reading, self.retained_reentry)
            }
            NativeOperatorKind::HadamardOccurrence => {
                if occurrence.interaction_words.len() != predecessor_width {
                    return Err(NativeOperatorExecutionError::InteractionExtent);
                }
                let interaction_shape = surface.shape_enter(
                    1,
                    predecessor_width,
                    Dyadic::ONE,
                    grain,
                    &occurrence.interaction_words,
                )?;
                let interaction_staged =
                    surface.stage_words(&occurrence.interaction_words, 1, predecessor_width)?;
                let interaction = surface.fresh_section(1, predecessor_width, grain)?;
                let product_shape = surface.shape_hadamard(
                    1,
                    predecessor_width,
                    self.carrier_bound,
                    interaction_shape.needed,
                )?;
                let out = surface.fresh_section(1, predecessor_width, grain)?;
                let mut builder = surface.begin_passage(&[vec![], vec![0]])?;
                let lane = builder.open(0, &[])?;
                surface.record_enter(&lane, &interaction_staged, Dyadic::ONE, &interaction)?;
                builder.close(0, &interaction, interaction_shape.needed)?;
                let lane = builder.open(1, &[0])?;
                surface.record_hadamard(&lane, &self.carrier, &interaction, &out)?;
                builder.close(1, &out, product_shape.needed)?;
                let reading = builder.finish()?.launch()?;
                (out, reading, self.retained_reentry)
            }
            NativeOperatorKind::Contract { matrix }
                if matrix == "operator/output-cross-section" =>
            {
                require_empty(&occurrence)?;
                let shape = surface.shape_contract(
                    1,
                    predecessor_width,
                    self.carrier_bound,
                    &self.resident.output,
                )?;
                let out = surface.fresh_section(1, morphology.carrier_extent, grain)?;
                let mut builder = surface.begin_passage(&[vec![]])?;
                let lane = builder.open(0, &[])?;
                surface.record_contract(&lane, &self.carrier, &self.resident.output, &out)?;
                builder.close(0, &out, shape.needed)?;
                let reading = builder.finish()?.launch()?;
                (out, reading, self.retained_reentry)
            }
            NativeOperatorKind::RmsNorm {
                gain_population, ..
            } => {
                require_empty(&occurrence)?;
                if *gain_population != predecessor_width {
                    return Err(NativeOperatorExecutionError::Operation);
                }
                let shape = surface.shape_rms_rebase(
                    1,
                    predecessor_width,
                    predecessor_width,
                    self.carrier_bound,
                    Some(&self.resident.gain),
                )?;
                let out = surface.fresh_section(1, predecessor_width, grain)?;
                let mut builder = surface.begin_passage(&[vec![]])?;
                let lane = builder.open(0, &[])?;
                surface.record_rms_rebase(
                    &lane,
                    &self.carrier,
                    predecessor_width,
                    Some(&self.resident.gain),
                    self.resident.epsilon,
                    &shape,
                    &out,
                )?;
                builder.close(0, &out, shape.needed)?;
                let reading = builder.finish()?.launch()?;
                (out, reading, self.retained_reentry)
            }
            NativeOperatorKind::Reentry => {
                require_empty(&occurrence)?;
                let (retained, retained_bound) = self
                    .retained_reentry
                    .ok_or(NativeOperatorExecutionError::MissingReentry)?;
                let shape = surface.shape_re_entry(
                    1,
                    predecessor_width,
                    retained_bound,
                    self.carrier_bound,
                )?;
                let out = surface.fresh_section(1, predecessor_width, grain)?;
                let mut builder = surface.begin_passage(&[vec![]])?;
                let lane = builder.open(0, &[])?;
                surface.record_re_entry(&lane, &retained, &self.carrier, &out)?;
                builder.close(0, &out, shape.needed)?;
                let reading = builder.finish()?.launch()?;
                (out, reading, None)
            }
            _ => return Err(NativeOperatorExecutionError::Operation),
        };
        let successor_bound = exact_bound(&reading).map_err(|flags| {
            NativeOperatorExecutionError::ResidentObstruction {
                operation: format!("{operation:?}"),
                flags,
            }
        })?;
        let intervals = surface.read_out(&successor_carrier)?;
        let successor_generation = self
            .generation
            .checked_add(1)
            .ok_or(NativeOperatorExecutionError::Generation)?;
        let mut chronology = self.chronology;
        chronology.push(occurrence.ordinal);
        let next_operation = (self.operation_at + 1) % morphology.operations.len();
        let successor_width = successor_carrier.width();
        Ok(NativeOperatorStep {
            emission: NativeOperatorEmission {
                generation: successor_generation,
                operation: operation.clone(),
                rows: successor_carrier.rows(),
                width: successor_width,
                grain: grain.0,
                intervals,
            },
            trace: NativeOperatorTrace {
                schema: NATIVE_OPERATOR_STEP_SCHEMA.to_owned(),
                predecessor_generation: self.generation,
                successor_generation,
                occurrence: occurrence.ordinal,
                chronology: chronology.clone(),
                operation,
                predecessor_width,
                successor_width,
                resident_coefficient_octets: self.resident.resident_coefficient_octets(),
                passage_slot_population: reading.slots.len(),
                refusal_population: reading.obstruction.refusals.len(),
                successor_bound_octaves: successor_bound,
                census_before: reading.census_before,
                census_after: reading.census_after,
            },
            successor: NativeOperatorSession {
                resident: self.resident,
                carrier: successor_carrier,
                carrier_bound: successor_bound,
                retained_reentry,
                operation_at: next_operation,
                generation: successor_generation,
                chronology,
            },
        })
    }
}

fn require_empty(
    occurrence: &NativeOperatorOccurrence,
) -> Result<(), NativeOperatorExecutionError> {
    if occurrence.interaction_words.is_empty() {
        Ok(())
    } else {
        Err(NativeOperatorExecutionError::InteractionExtent)
    }
}

fn exact_bound(reading: &crate::resident_section::PassageReading) -> Result<u32, u32> {
    if !reading.obstruction.is_empty() {
        return Err(reading.obstruction.joined_flags());
    }
    Ok(reading
        .slots
        .last()
        .map(|slot| slot.max_octave.max(1))
        .unwrap_or(1))
}

#[derive(Debug, Error)]
pub enum NativeOperatorExecutionError {
    #[error(transparent)]
    Morphology(#[from] NativeOperatorMorphologyError),
    #[error(transparent)]
    Resident(#[from] ResidentRefusal),
    #[error("the carrier occurrence has the wrong extent")]
    CarrierExtent,
    #[error("the interaction occurrence has the wrong extent for this operation")]
    InteractionExtent,
    #[error("the operation occurrence does not join the current ecology")]
    Occurrence,
    #[error("the resident operation word and the morphology disagree")]
    Operation,
    #[error("the resident operation {operation} returned obstruction flags {flags:#x}")]
    ResidentObstruction { operation: String, flags: u32 },
    #[error("the residual re-entry standing is absent")]
    MissingReentry,
    #[error("the ecology generation overflowed")]
    Generation,
    #[error("no exact resident grain admits the initial carrier")]
    NoAdmittedGrain,
    #[error("recurrent session rest: {0}")]
    Rest(String),
}

impl From<crate::embedding_fiber::FiberError> for NativeOperatorExecutionError {
    fn from(error: crate::embedding_fiber::FiberError) -> Self {
        Self::Resident(ResidentRefusal::Declaration {
            operation: "operator-mount",
            what: error.to_string(),
        })
    }
}

pub fn mount_operator_surface(
    readout: &ResidentReadout,
) -> Result<ResidentSurface<'_>, NativeOperatorExecutionError> {
    Ok(ResidentSurface::on(readout)?)
}

//! The branch session: the extracted per-layer interaction branch, advanced one operation at a
//! time on its host-entered carriers ([`super::extracted_operator`]).
//!
//! Every mathematical operation is one step. Its resident carrier is moved into the next step;
//! no exterior verdict, candidate, commit, or reconstructed predecessor sits between them. The
//! branch rests in the one rest ([`ExtractedOperatorRest`]) on its constitution chart
//! (`NativeOperatorMorphology::constitution_chart`); its legacy JSON wire still decodes.

use std::collections::BTreeMap;

use serde::Deserialize;

use crate::{
    embedding_fiber::{MountedReadout, ResidentReadout},
    resident_section::{
        Dyadic, ResidentGrain, ResidentSection, ResidentSectionRest, ResidentSurface,
        SeriesAperture,
    },
};

use super::{
    BranchTraceChart, ExtractedOperatorAdvance, ExtractedOperatorBranch, ExtractedOperatorEmission,
    ExtractedOperatorOccurrence, ExtractedOperatorRefusal, ExtractedOperatorRest,
    ExtractedOperatorRestHeader, ExtractedOperatorStep, ExtractedOperatorTrace,
    NATIVE_SESSION_REST_SCHEMA, NativeCarrierOrdinal, NativeOperatorKind, NativeOperatorMorphology,
};

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
    ) -> Result<Self, ExtractedOperatorRefusal> {
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
    ) -> Result<ResidentGrain, ExtractedOperatorRefusal> {
        if carrier_words.len() != self.morphology.carrier_extent {
            return Err(ExtractedOperatorRefusal::CarrierExtent);
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
            .ok_or(ExtractedOperatorRefusal::NoAdmittedGrain)
    }

    pub fn mount_initial<'resident>(
        &'resident self,
        carrier_words: &[u16],
        grain: ResidentGrain,
    ) -> Result<ExtractedBranchSession<'resident, 'morphology, 'chart>, ExtractedOperatorRefusal>
    {
        if carrier_words.len() != self.morphology.carrier_extent {
            return Err(ExtractedOperatorRefusal::CarrierExtent);
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
            ExtractedOperatorRefusal::ResidentObstruction {
                operation: u32::MAX,
                flags,
            }
        })?;
        Ok(ExtractedBranchSession {
            resident: self,
            carrier,
            carrier_bound: bound,
            retained_reentry: None,
            operation_at: 0,
            generation: 0,
            chronology: Vec::new(),
        })
    }
}

/// The legacy JSON wire of a branch session rest (`holonic-engine.native-operator-session-rest.v1`).
/// It is decoded into the one rest, [`ExtractedOperatorRest`], and never written.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct BranchRestWire {
    schema: String,
    carrier_wire: Vec<u8>,
    retained_reentry_wire: Option<Vec<u8>>,
    retained_reentry_bound: Option<u32>,
    carrier_bound: u32,
    operation_at: usize,
    generation: u64,
    chronology: Vec<u64>,
}

/// The branch session: the per-layer interaction branch advanced one operation at a time on its
/// host-entered carriers. Coefficients remain resident; the carrier itself advances.
pub struct ExtractedBranchSession<'resident, 'morphology, 'chart> {
    resident: &'resident ResidentOperatorMorphology<'morphology, 'chart>,
    carrier: ResidentSection<'chart>,
    carrier_bound: u32,
    retained_reentry: Option<(ResidentSection<'chart>, u32)>,
    operation_at: usize,
    generation: u64,
    chronology: Vec<u64>,
}

/// The branch's two entered carriers precede the outputs of its operations in the chart:
/// `c0` the entered (and re-entering) carrier, `c1` the occurrence-entered interaction.
const BRANCH_ENTERED: u32 = 2;

fn branch_output(operation: usize) -> NativeCarrierOrdinal {
    NativeCarrierOrdinal(BRANCH_ENTERED + operation as u32)
}

/// Where the branch's current carrier sits in the constitution chart: the entered carrier before
/// any operation, else the output of the last enacted operation.
fn branch_current(operation_at: usize, generation: u64, operations: usize) -> NativeCarrierOrdinal {
    if generation == 0 {
        NativeCarrierOrdinal(0)
    } else {
        branch_output((operation_at + operations - 1) % operations)
    }
}

impl<'morphology, 'chart> ResidentOperatorMorphology<'morphology, 'chart> {
    /// Remount a branch session from the one rest. The rest's constitution chart must be this
    /// morphology's own chart; the branch holds no overlay, terminal face or apparatus.
    pub fn remount_session<'resident>(
        &'resident self,
        rest: &ExtractedOperatorRest,
    ) -> Result<ExtractedBranchSession<'resident, 'morphology, 'chart>, ExtractedOperatorRefusal>
    {
        rest.validate()?;
        let operations = self.morphology.operations.len();
        let header = &rest.header;
        let current = branch_current(header.operation_at, header.generation, operations);
        let malformed =
            || ExtractedOperatorRefusal::Rest("the branch session rest is malformed".into());
        if header.ecology != self.morphology.constitution_chart()?
            || header.operation_at >= operations
            || header.operation_at != header.generation as usize % operations
            || header.row_population.is_some()
            || header.previous_context.is_some()
            || header.aperture.is_some()
            || header.progress.is_some()
            || !rest.checkpoints.is_empty()
            || rest.terminal_carrier.is_some()
            || !rest.overlay.is_empty()
            || rest.passage.is_some()
            || rest.reuse.is_some()
            || rest.carriers.keys().any(|at| *at != current && at.0 != 0)
        {
            return Err(malformed());
        }
        let held = rest.carriers.get(&current).ok_or_else(malformed)?;
        if held.grain.0 != header.grain {
            return Err(malformed());
        }
        let carrier = self.surface.mount_section_rest(held)?;
        let retained_reentry = match rest.carriers.get(&NativeCarrierOrdinal(0)) {
            Some(retained) if current.0 != 0 => Some((
                self.surface.mount_section_rest(retained)?,
                retained.bound_octaves,
            )),
            _ => None,
        };
        Ok(ExtractedBranchSession {
            resident: self,
            carrier,
            carrier_bound: held.bound_octaves,
            retained_reentry,
            operation_at: header.operation_at,
            generation: header.generation,
            chronology: header.chronology.clone(),
        })
    }

    /// Decode the legacy JSON wire of a branch session rest into the one rest, on this
    /// morphology's constitution chart. The wire's own checks are kept.
    pub fn read_legacy_rest(
        &self,
        bytes: &[u8],
    ) -> Result<ExtractedOperatorRest, ExtractedOperatorRefusal> {
        let wire: BranchRestWire = serde_json::from_slice(bytes)
            .map_err(|error| ExtractedOperatorRefusal::Rest(error.to_string()))?;
        let operations = self.morphology.operations.len();
        let carrier = ResidentSectionRest::read(&wire.carrier_wire)
            .map_err(ExtractedOperatorRefusal::Rest)?;
        let retained = wire
            .retained_reentry_wire
            .as_deref()
            .map(ResidentSectionRest::read)
            .transpose()
            .map_err(ExtractedOperatorRefusal::Rest)?;
        if wire.schema != NATIVE_OPERATOR_SESSION_REST_SCHEMA
            || operations == 0
            || wire.operation_at >= operations
            || wire.chronology.len() as u64 != wire.generation
            || wire.operation_at != wire.generation as usize % operations
            || carrier.bound_octaves != wire.carrier_bound
            || retained.is_some() != wire.retained_reentry_bound.is_some()
            || retained
                .as_ref()
                .zip(wire.retained_reentry_bound)
                .is_some_and(|(section, bound)| section.bound_octaves != bound)
        {
            return Err(ExtractedOperatorRefusal::Rest(
                "the recurrent session rest is malformed".to_owned(),
            ));
        }
        let current = branch_current(wire.operation_at, wire.generation, operations);
        let grain = carrier.grain.0;
        let mut carriers = BTreeMap::from([(current, carrier)]);
        if let Some(retained) = retained {
            if current.0 == 0 {
                return Err(ExtractedOperatorRefusal::Rest(
                    "the entered carrier cannot also be retained".to_owned(),
                ));
            }
            carriers.insert(NativeCarrierOrdinal(0), retained);
        }
        let rest = branch_rest(
            self.morphology.constitution_chart()?,
            wire.operation_at,
            wire.generation,
            wire.chronology,
            grain,
            carriers,
        );
        rest.validate()?;
        Ok(rest)
    }
}

fn branch_rest(
    ecology: super::NativeFullOperatorEcology,
    operation_at: usize,
    generation: u64,
    chronology: Vec<u64>,
    grain: u32,
    carriers: BTreeMap<NativeCarrierOrdinal, ResidentSectionRest>,
) -> ExtractedOperatorRest {
    ExtractedOperatorRest {
        header: ExtractedOperatorRestHeader {
            schema: NATIVE_SESSION_REST_SCHEMA.into(),
            ecology,
            operation_at,
            generation,
            chronology,
            grain,
            row_population: None,
            cycle_complete: generation > 0 && operation_at == 0,
            previous_context: None,
            aperture: None,
            terminal_seal: true,
            progress: None,
            interruption: None,
        },
        carriers,
        checkpoints: BTreeMap::new(),
        terminal_carrier: None,
        overlay: BTreeMap::new(),
        passage: None,
        reuse: None,
    }
}

impl<'resident, 'morphology, 'chart> ExtractedBranchSession<'resident, 'morphology, 'chart> {
    pub fn generation(&self) -> u64 {
        self.generation
    }

    pub fn chronology(&self) -> &[u64] {
        &self.chronology
    }

    pub fn operation_at(&self) -> usize {
        self.operation_at
    }

    /// The one rest: the current carrier at its place in the constitution chart and, inside the
    /// word, the retained re-entry carrier at the entered carrier's place.
    pub fn rest(&self) -> Result<ExtractedOperatorRest, ExtractedOperatorRefusal> {
        let surface = self.resident.surface;
        let operations = self.resident.morphology.operations.len();
        let current = branch_current(self.operation_at, self.generation, operations);
        let mut carriers = BTreeMap::from([(
            current,
            surface.detach_section(&self.carrier, self.carrier_bound)?,
        )]);
        if let Some((section, bound)) = &self.retained_reentry {
            carriers.insert(
                NativeCarrierOrdinal(0),
                surface.detach_section(section, *bound)?,
            );
        }
        let rest = branch_rest(
            self.resident.morphology.constitution_chart()?,
            self.operation_at,
            self.generation,
            self.chronology.clone(),
            self.carrier.grain().0,
            carriers,
        );
        rest.validate()?;
        Ok(rest)
    }

    /// Complete the morphology's own operation word. The word, not the caller, decides its extent
    /// and which operation receives the additional interaction carrier.
    pub fn advance_branch(
        mut self,
        interaction_words: &[u16],
    ) -> Result<ExtractedOperatorBranch<Self>, ExtractedOperatorRefusal> {
        let extent = self.resident.morphology.operations.len();
        let mut emissions = Vec::with_capacity(extent);
        let mut traces = Vec::with_capacity(extent);
        for _ in 0..extent {
            let occurrence = if matches!(
                self.resident.morphology.operations[self.operation_at],
                NativeOperatorKind::HadamardOccurrence
            ) {
                ExtractedOperatorOccurrence::entered(self.generation, interaction_words.to_vec())
            } else {
                ExtractedOperatorOccurrence::internal(self.generation)
            };
            let step = self.advance(occurrence)?;
            emissions.push(step.emission);
            traces.push(step.trace);
            self = step.successor;
        }
        Ok(ExtractedOperatorBranch {
            emissions,
            traces,
            successor: self,
        })
    }

    pub fn advance(
        self,
        occurrence: ExtractedOperatorOccurrence,
    ) -> Result<ExtractedOperatorStep<Self>, ExtractedOperatorRefusal> {
        if occurrence.ordinal != self.generation || !occurrence.row_addresses.is_empty() {
            return Err(ExtractedOperatorRefusal::Occurrence);
        }
        let morphology = self.resident.morphology;
        let operation_at = self.operation_at;
        let operation = morphology
            .operations
            .get(self.operation_at)
            .cloned()
            .ok_or(ExtractedOperatorRefusal::Operation)?;
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
                    return Err(ExtractedOperatorRefusal::InteractionExtent);
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
                    return Err(ExtractedOperatorRefusal::Operation);
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
                    .ok_or(ExtractedOperatorRefusal::MissingReentry)?;
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
            _ => return Err(ExtractedOperatorRefusal::Operation),
        };
        let successor_bound = exact_bound(&reading).map_err(|flags| {
            ExtractedOperatorRefusal::ResidentObstruction {
                operation: operation_at as u32,
                flags,
            }
        })?;
        let intervals = surface.read_out(&successor_carrier)?;
        let successor_generation = self
            .generation
            .checked_add(1)
            .ok_or(ExtractedOperatorRefusal::Generation)?;
        let mut chronology = self.chronology;
        chronology.push(occurrence.ordinal);
        let next_operation = (self.operation_at + 1) % morphology.operations.len();
        let successor_width = successor_carrier.width();
        Ok(ExtractedOperatorStep {
            emission: ExtractedOperatorEmission {
                generation: successor_generation,
                operation: operation.clone(),
                carrier: branch_output(operation_at),
                rows: successor_carrier.rows(),
                width: successor_width,
                grain: grain.0,
                intervals,
                projection: None,
            },
            trace: ExtractedOperatorTrace {
                schema: NATIVE_OPERATOR_STEP_SCHEMA.to_owned(),
                predecessor_generation: self.generation,
                successor_generation,
                occurrence: occurrence.ordinal,
                successor_bound_octaves: successor_bound,
                resident_coefficient_octets: self.resident.resident_coefficient_octets() as u64,
                census_before: reading.census_before,
                census_after: reading.census_after,
                chart: BranchTraceChart {
                    chronology: chronology.clone(),
                    operation,
                    predecessor_width,
                    successor_width,
                    passage_slot_population: reading.slots.len(),
                    refusal_population: reading.obstruction.refusals.len(),
                },
            },
            successor: ExtractedBranchSession {
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

impl ExtractedOperatorAdvance for ExtractedBranchSession<'_, '_, '_> {
    type Operation = NativeOperatorKind;
    type TraceChart = BranchTraceChart;

    fn generation(&self) -> u64 {
        self.generation
    }

    fn operation_at(&self) -> usize {
        self.operation_at
    }

    fn chronology(&self) -> &[u64] {
        &self.chronology
    }

    fn advance_occurrence(
        self,
        occurrence: ExtractedOperatorOccurrence,
    ) -> Result<ExtractedOperatorStep<Self>, ExtractedOperatorRefusal> {
        self.advance(occurrence)
    }
}

fn require_empty(occurrence: &ExtractedOperatorOccurrence) -> Result<(), ExtractedOperatorRefusal> {
    if occurrence.interaction_words.is_empty() {
        Ok(())
    } else {
        Err(ExtractedOperatorRefusal::InteractionExtent)
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

pub fn mount_operator_surface(
    readout: &ResidentReadout,
) -> Result<ResidentSurface<'_>, ExtractedOperatorRefusal> {
    Ok(ResidentSurface::on(readout)?)
}

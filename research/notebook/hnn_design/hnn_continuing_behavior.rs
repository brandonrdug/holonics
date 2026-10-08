//! One continuing native receiver through observation, delayed contact credit and publication.
//! Refs #73 #62 #148. The run is `hnn_prediction executed continuing-behavior <out> <pin>`.
//!
//! [agent-inferred] The acceptance keeps the original seven-passage gate: two externally
//! admitted actual Receiving comparisons locate R from its zero opening; a contact future then
//! carries a blind passage, three later comparisons, at least two actual C/K/D factor movements,
//! and a blind consequence. Before that contact future, two native preparations must additionally
//! execute actual coupled encounters, update R from the actual observed faces, and change a later
//! physical preparation through R alone at matched present source/carry/Current/operators. The
//! contact future's declared budget is unchanged. This interposition changes the integrated
//! trajectory, and does not establish that the saved original factor failure was repaired.
//! Every original blind boundary is flushed before its observation is read. The native encounter
//! constructs its own observation; the exterior supplies neither effort nor target.
//! One PhysicalReceiver retains the same Resident, its actual momentum, pump phase and material.
//! The native owner alone stages, certifies, deposits and rebases the reached total covector.
//!
//! This is the existing correlated KnownTruth alternation orbit through Encoded::identity.
//! Its generator belongs to the terrain, never the HNN. No expected string, answer routine,
//! authored readout, source reinjection at deposition, independent learner or retained Word is
//! added. The sparse boundary's actual Held decision is output; point leaders are not release.
//! The decoder is that Encoded chart's D and fibre. A foreign byte passage would require the
//! existing located encoding squares, not this known-truth identity chart.
//!
//! The computational object is the helical pair interaction: the source/receiver phase faces,
//! pair contact and loaded parametron on a continuing tube. Helix, pair, faces and placement,
//! and tube are touched; declared cell holonomy and tower restrictions remain attached.
//! Lessons 3/6/7/9 are consumers here: unrepaired owner refusal ends the whole run, deposition
//! must be the native certified return, actual output decides behavior, and no budget is raised.

use std::fs::File;
use std::io::{BufWriter, Write};
use std::time::Instant;

use holonics::compression::landmark::context::{BaseMeasure, StopPrior};
use holonics::geometry::RatVec3;
use holonics::geometry::screw::ScrewGenerator;
use holonics::hnn::constitution::{CAMPAIGN_ONE_BUDGET, Constitution};
use holonics::hnn::encoding::Encoded;
use holonics::hnn::field::{
    ConstitutionRead, ContactDeclaration, CribDeclaration, Current, Field, FieldDeclaration,
    ReceiverDeclaration, RingDeclaration,
};
use holonics::hnn::physical::action::{ActionCommunication, BoundJointWorld, NativeEncounter};
use holonics::hnn::physical::communication::PhysicalBoundary;
use holonics::hnn::physical::contact::ContactObservation;
use holonics::hnn::physical::{PhysicalLearning, PhysicalObservation, PhysicalReceiver};
use holonics::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial};
use holonics::hnn::word::action::{ControlFibre, PortPreparation, ProspectiveControl};
use holonics::hnn::word::variation::{ContactVariationAction, VariationBudget};
use holonics::hnn::word::{Absorption, WordOpening};
use holonics::holarchy::terrain::{CyclicLaw, KnownTruth};
use holonics::holon::law::{ReferenceHolon, Scheme};
use holonics::holon::parametron::Carrier;
use holonics::holon::{Holon, HolonError, HolonState, PortHolon};
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::linear::inertia::SymmetricForm;
use holonics::ratio::{Rat, integer, rat};
use holonics::receiver::receipt::{Receipt, ReceiptLaw, RegionChart};
use holonics::receiver::reception::{JointLaw, JointStep, ReceiverFace};
use num_traits::Zero;

use super::exterior;

const CLASSES: usize = 2;
const PREFIX: usize = 2;
const APERTURE: usize = PREFIX + 1;
const RECEIVING_OBSERVATIONS: usize = CLASSES;
const CONTACT_OBSERVATIONS: usize = 3;
const CONTACT_WORDS: usize = 1 + CONTACT_OBSERVATIONS + 1;
const WHOLE_PASSAGES: usize = RECEIVING_OBSERVATIONS + CONTACT_WORDS;
// One actual encounter and a later preparation are the minimal chronology of an acquired
// relation. These two requests are not an expanded contact future or a training sweep.
const NATIVE_ENCOUNTERS: usize = 2;
const SOURCE_SEED: u64 = 20_261_008_001;
const CONSEQUENCE_SEED: u64 = 20_261_008_011;
// Fixed exact admission of this prospective future, inherited from the existing variation
// owner control's bit domain. This is a resource bound, not precision or a machinery literal.
const VARIATION_BITS: u64 = 1 << 20;

fn publish(output: &mut impl Write, line: impl AsRef<str>) {
    let line = line.as_ref();
    output
        .write_all(line.as_bytes())
        .expect("the whole actual receipt is writable");
    output
        .flush()
        .expect("publish before obtaining a later observation");
    print!("{line}");
    std::io::stdout()
        .flush()
        .expect("the actual boundary reaches stdout");
}

fn ratios(values: &[Rat]) -> Vec<String> {
    values.iter().map(exterior::ratio).collect()
}

fn opening_tick(opening: &WordOpening) -> usize {
    match opening {
        WordOpening::Rest => 0,
        WordOpening::Received { carry, .. } => carry.ticks,
    }
}

fn continued(opening: &WordOpening) -> bool {
    matches!(
        opening,
        WordOpening::Received {
            absorption: Absorption::Nothing,
            ..
        }
    )
}

fn ring(period: u64, lock: Vec<u64>) -> RingDeclaration {
    RingDeclaration {
        period,
        screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
        placements: (0..period)
            .map(|node| FieldDeclaration::quarter_turn(node, period))
            .collect(),
        lock,
        reflector: (0..period)
            .map(|port| ((period - port) % period) as usize)
            .collect(),
        admittance: integer(2),
        initial: 0,
    }
}

fn declare() -> Result<(Field, ReceiverDeclaration), holonics::hnn::HnnError> {
    let receiver = ReceiverDeclaration {
        ring: 0,
        aperture: APERTURE,
        tolerance: rat(1, 16),
        depth: 1,
        prior: StopPrior::half(),
        mass: 1,
        base: BaseMeasure::Even,
        receiving_prior: 0,
    };
    // Source period four holds both classes at distinct phase addresses and exceeds aperture
    // three. The legal period-two interior has width four and keeps the actual Half pump clock.
    let field = Field::declare(
        FieldDeclaration {
            rings: vec![ring(4, (0..4).collect()), ring(2, Vec::new())],
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
            alphabet: CLASSES,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![receiver.clone()],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 16,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )?;
    Ok((field, receiver))
}

fn material(field: &Field) -> Result<Constitution, holonics::hnn::HnnError> {
    let theta = Constitution::initial(field, CAMPAIGN_ONE_BUDGET)?;
    let width = field.ring(1).width();
    let factor = ExactRatMatrix::identity(width)?;
    let pump = PumpDeclaration::new(
        rat(1, 16),
        Carrier::new(integer(1), integer(0))?,
        PumpStep::Half,
    )?;
    // Existing loaded storage/pump law, declared independently of every observed class.
    theta.with_ring_resonator(
        field,
        1,
        ResonatorMaterial::new(factor.clone(), factor.clone(), factor, Some(pump))?,
    )
}

/// [agent-inferred] A participating quadratic Holon pair, independent of every requested or
/// observed receiving face. J is the native gyrator join, Q the declared unit storage, and the
/// external ports span the whole pair. The source-wave/effort conversion is the core's native
/// Robin owner; this declaration supplies no effort, guessed observation, or control policy.
#[derive(Clone)]
struct WorldDeclaration {
    law: JointLaw,
    state: HolonState,
    face: ReceiverFace,
    receipt: ReceiptLaw,
    admittance: Vec<Rat>,
}

fn world_declaration(field: &Field, _native_origin: usize) -> Result<WorldDeclaration, HolonError> {
    // The world state is declared in the common receiving log-amplitude/phase-lift chart:
    // real coordinates are base-two log-amplitudes; imaginary coordinates are twice lifted
    // turns. This is the exact convention consumed by ReceivingRead::of_logits.
    // These are not Cartesian wave quadratures reinterpreted as a measured phase. Each
    // participant carries the full chart, with its actual fixed identity receiver face.
    let participant = 2 * field.alphabet();
    let extent = 2 * participant;
    let ring = field.sources()[0];
    if participant == 0 || extent != field.ring(ring).width() {
        return Err(HolonError::Shape {
            what: "the world pair's external wave ports match the declared source ring",
            expected: field.ring(ring).width(),
            found: extent,
        });
    }
    let structure = ExactRatMatrix::shaped(
        extent,
        extent,
        (0..extent)
            .map(|i| {
                (0..extent)
                    .map(|j| {
                        if i < participant && j == participant + i {
                            -integer(1)
                        } else if i >= participant && j == i - participant {
                            integer(1)
                        } else {
                            Rat::zero()
                        }
                    })
                    .collect()
            })
            .collect(),
    )?;
    let holon = Holon::new(PortHolon::medium(
        &structure,
        &ExactRatMatrix::zero(extent, extent)?,
        SymmetricForm::from_rows(
            (0..extent)
                .map(|i| {
                    (0..extent)
                        .map(|j| if i == j { integer(1) } else { Rat::zero() })
                        .collect()
                })
                .collect(),
        )?,
        &ExactRatMatrix::identity(extent)?,
        false,
    )?)?;
    let law = JointLaw::new(
        ReferenceHolon::new(holon, field.step().clone(), Scheme::Midpoint)?,
        participant,
    )?;
    let mut initial = vec![Rat::zero(); extent];
    // Unit stored motion at one declared source coordinate; the receiver begins at rest.
    // It is an initial physical configuration, never a class target or an authored response.
    initial[0] = integer(1);
    // Its actual initial World clock is zero. BoundJointWorld declares the affine join to
    // the native origin; it does not manufacture unexecuted World commits to equal that origin.
    let state = HolonState::at(initial, 0);
    let face = ReceiverFace::receiver_state(participant, participant)?;
    let readers = (0..extent)
        .map(|i| {
            (0..extent)
                .map(|j| if i == j { integer(1) } else { Rat::zero() })
                .collect()
        })
        .collect();
    let chart = RegionChart::new(integer(1), field.step().clone(), 0)?;
    let receipt = ReceiptLaw::new(extent, readers, vec![chart; extent])?;
    Ok(WorldDeclaration {
        law,
        state,
        face,
        receipt,
        admittance: vec![field.ring(ring).admittance().clone(); extent],
    })
}

/// Read the solved native encounter without executing another step or fabricating a target.
/// The caller supplies the actual pre-state and native returned step/receipt, obtained from the
/// opaque core encounter. Every participant and face coordinate reaches the exterior receipt.
fn joint_world_receipt(
    output: &mut impl Write,
    role: &str,
    world: &WorldDeclaration,
    before: &HolonState,
    step: &JointStep,
    receipt: &Receipt,
) -> Result<bool, HolonError> {
    let source = world.law.source_extent();
    let next = step.next_state();
    let extent = source + world.law.receiver_extent();
    for state in [before, &next] {
        if state.configuration.len() != extent {
            return Err(HolonError::Shape {
                what: "the encounter receipt's complete joint state",
                expected: extent,
                found: state.configuration.len(),
            });
        }
    }
    let face_before = world.face.read(
        &before.configuration[..source],
        &before.configuration[source..],
    )?;
    let motion = step.face_motion();
    let face_closes = face_before.len() == step.face().len()
        && [
            motion.source.len(),
            motion.receiver.len(),
            motion.chart.len(),
        ]
        .into_iter()
        .all(|len| len == step.face().len())
        && face_before.iter().enumerate().all(|(i, value)| {
            value + &motion.source[i] + &motion.receiver[i] + &motion.chart[i] == step.face()[i]
        });
    let stored_closes =
        step.stored_after().joint() - step.stored_before().joint() == step.balance().stored_change;
    let power_closes = world.law.law().step() * step.boundary().power() == step.balance().port;
    let state_closes = next.commit == step.commit()
        && &next.configuration[..source] == step.next_source()
        && &next.configuration[source..] == step.next_receiver();
    let clock_closes = before.commit.checked_add(1) == Some(next.commit);
    let closes = step.balance().is_exact()
        && face_closes
        && stored_closes
        && power_closes
        && state_closes
        && clock_closes;
    publish(
        output,
        format!(
            "ACTUAL NATIVE WORLD RECEIPT; role={role}; pre_state={before:?}; next_source={:?}; next_receiver={:?}; reached_state={next:?}; face_before={face_before:?}; observed_face={:?}; face_motion={motion:?}; unresolved={:?}; stored_before={:?}; stored_after={:?}; external_flow={:?}; external_effort={:?}; full_balance={:?}; regions={receipt:?}; step={:?}; face_closes={face_closes}; stored_closes={stored_closes}; power_closes={power_closes}; state_closes={state_closes}; clock_closes={clock_closes}; closes={closes}\n",
            step.next_source(),
            step.next_receiver(),
            step.face(),
            step.unresolved(),
            step.stored_before(),
            step.stored_after(),
            step.boundary().flow(),
            step.boundary().effort(),
            step.balance(),
            world.law.law().step(),
        ),
    );
    Ok(closes)
}

/// Check the actual core-produced wave termination against its solved power-conjugate bond.
/// a and b are inputs from that opaque native receipt; this consumer never solves for an effort
/// or supplies a world observation. Model preparation work is printed by its separate owner.
fn world_wave_receipt(
    output: &mut impl Write,
    role: &str,
    world: &WorldDeclaration,
    step: &JointStep,
    incident: &[Rat],
    reflected: &[Rat],
) -> Result<bool, HolonError> {
    let effort = step.boundary().effort();
    let flow = step.boundary().flow();
    let ports = world.admittance.len();
    for values in [incident, reflected, effort, flow] {
        if values.len() != ports {
            return Err(HolonError::Shape {
                what: "the encounter's matched external wave ports",
                expected: ports,
                found: values.len(),
            });
        }
    }
    let chart_closes = (0..ports).all(|i| {
        incident[i] == &effort[i] + &flow[i] / &world.admittance[i]
            && reflected[i] == &effort[i] - &flow[i] / &world.admittance[i]
    });
    let wave_work: Rat = world.law.law().step()
        * incident
            .iter()
            .zip(reflected)
            .zip(&world.admittance)
            .map(|((a, b), y)| y * (a * a - b * b))
            .sum::<Rat>()
        / integer(4);
    let work_closes = wave_work == step.balance().port;
    let closes = chart_closes && work_closes && step.balance().is_exact();
    publish(
        output,
        format!(
            "ACTUAL WORLD WAVE INTERFACE; role={role}; incident={incident:?}; reflected={reflected:?}; admittance={:?}; actual_effort={effort:?}; actual_flow={flow:?}; actual_wave_work={wave_work:?}; actual_joint_port_work={:?}; chart_closes={chart_closes}; work_closes={work_closes}; closes={closes}; model_preparation_work_is_a_separate_reading=true\n",
            world.admittance,
            step.balance().port,
        ),
    );
    Ok(closes)
}

/// Read the whole exact joint control relation before an action is attempted. A fibre origin
/// is printed as a coordinate of the relation, never selected from a positive-dimensional fibre.
fn prospective_receipt(
    output: &mut impl Write,
    role: &str,
    prospective: &ProspectiveControl,
) -> Result<bool, holonics::hnn::HnnError> {
    publish(
        output,
        format!(
            "ACTUAL NATIVE INFERENCE PASSAGE; role={role}; whole_word={:?}; every_tick={:?}; baseline_is_model_inference_not_an_executed_world_action=true; no_world_state_was_reset=true\n",
            prospective.prediction_word(),
            prospective.prediction_balances(),
        ),
    );
    let response = prospective.response();
    let residual = prospective.residual();
    let closes = match prospective.fibre() {
        ControlFibre::Affine { particular, kernel } => {
            response.apply(particular)? == residual
                && kernel.iter().all(|direction| {
                    response
                        .apply(direction)
                        .is_ok_and(|image| image.iter().all(Rat::is_zero))
                })
        }
        ControlFibre::Obstructed { covector, pairing } => {
            response
                .transpose()?
                .apply(covector)?
                .iter()
                .all(Rat::is_zero)
                && covector.len() == residual.len()
                && covector
                    .iter()
                    .zip(residual)
                    .map(|(q, r)| q * r)
                    .sum::<Rat>()
                    == *pairing
                && !pairing.is_zero()
        }
    };
    publish(
        output,
        format!(
            "NATIVE PROSPECTIVE RELATION; role={role}; producing_material_commit={}; source_Current={:?}; opened_at={}; source_wave_preparation={:?}; receiving_phases={:?}; requested_native_carriers={:?}; compared_partition={:?}; actual_baseline={:?}; complete_response={response:?}; residual={residual:?}; full_control_fibre={:?}; unique_control={:?}; joint_relation_closes={closes}; actual_world_observation_is_not_the_request=true\n",
            prospective.producing_commit(),
            prospective.current(),
            prospective.opened_at(),
            prospective.preparation(),
            prospective.phases(),
            prospective.requested(),
            prospective.compared(),
            prospective.baseline(),
            prospective.fibre(),
            prospective.unique_control(),
        ),
    );
    // The preparation declaration admits its entire exact rational control space. Read its
    // zero and unit directions as alternatives before imposing the requested consequence.
    // These native response readings are not executed probes, selected controls, a catalogue
    // of source answers or evidence that any unobserved alternative is the true source.
    let controls = prospective.preparation().controls();
    let selected_baseline: Vec<Rat> = prospective
        .baseline()
        .iter()
        .zip(prospective.compared())
        .filter(|(_, compared)| **compared)
        .flat_map(|(carrier, _)| carrier.iter().cloned())
        .collect();
    if selected_baseline.len() != response.rows() || controls != response.columns() {
        return Err(holonics::hnn::HnnError::Realization {
            what: "the complete joint action relation has its declared control and receiving shape",
        });
    }
    for alternative in 0..=controls {
        let mut control = vec![Rat::zero(); controls];
        if alternative > 0 {
            control[alternative - 1] = integer(1);
        }
        let prediction: Vec<Rat> = selected_baseline
            .iter()
            .zip(response.apply(&control)?)
            .map(|(baseline, response)| baseline + response)
            .collect();
        publish(
            output,
            format!(
                "DECLARED NATIVE CONTROL ALTERNATIVE; role={role}; admitted_control={control:?}; joint_predicted_selected_carrier={prediction:?}; compatible_with_declared_preparation_domain=true; compatibility_with_requested_consequence_is_not_presumed=true; is_an_actual_encounter=false\n",
            ),
        );
    }
    Ok(closes)
}

/// Compare only the receiving relation at identical present source, carry, operators and request.
/// An actual earlier opaque material snapshot supplies R_old; no old receiver/world is replayed.
fn matched_receiving_receipt(
    output: &mut impl Write,
    frozen: &ProspectiveControl,
    contemporary: &ProspectiveControl,
) -> Result<(bool, bool), holonics::hnn::HnnError> {
    let matched = frozen.current() == contemporary.current()
        && frozen.opened_at() == contemporary.opened_at()
        && frozen.preparation() == contemporary.preparation()
        && frozen.phases() == contemporary.phases()
        && frozen.requested() == contemporary.requested()
        && frozen.compared() == contemporary.compared();
    let relation_changed = frozen.baseline() != contemporary.baseline()
        || frozen.response() != contemporary.response()
        || frozen.fibre() != contemporary.fibre();
    let unique_choice_changed = matches!(
        (frozen.unique_control(), contemporary.unique_control()),
        (Some(old), Some(new)) if old != new
    );
    let frozen_injection = frozen
        .unique_control()
        .map(|u| frozen.preparation().map().apply(u))
        .transpose()?;
    let contemporary_injection = contemporary
        .unique_control()
        .map(|u| contemporary.preparation().map().apply(u))
        .transpose()?;
    let physical_preparation_changed = matches!(
        (&frozen_injection, &contemporary_injection),
        (Some(old), Some(new)) if old != new
    );
    let closes = prospective_receipt(
        output,
        "earlier R at present identical source/carry",
        frozen,
    )? && prospective_receipt(
        output,
        "actual successor R at present identical source/carry",
        contemporary,
    )? && matched;
    publish(
        output,
        format!(
            "MATCHED RECEIVING MATERIAL ATTRIBUTION; same_present_source_carry_current_operators_native_owner=true; same_public_bindings={matched}; complete_relation_changed={relation_changed}; unique_native_choice_changed={unique_choice_changed}; frozen_source_wave_injection={frozen_injection:?}; contemporary_source_wave_injection={contemporary_injection:?}; physical_preparation_changed={physical_preparation_changed}; closes={closes}; frozen_material_commit={}; contemporary_material_commit={}; full_fibres_retained=true; no_policy_derivative_claim=true\n",
            frozen.producing_commit(),
            contemporary.producing_commit(),
        ),
    );
    Ok((
        closes,
        unique_choice_changed && physical_preparation_changed,
    ))
}

/// Consume all actual coupled steps and the native observed faces, then join both clocks to
/// the retained world state. No representative, effort solve or observed target is constructed.
fn encounter_receipt(
    output: &mut impl Write,
    role: &str,
    declaration: &WorldDeclaration,
    before: &HolonState,
    encounter: &NativeEncounter,
    world: &BoundJointWorld,
) -> Result<bool, holonics::hnn::HnnError> {
    let mut previous = before.clone();
    let mut closes = encounter.before_world_tick == before.commit
        && encounter
            .after_native_tick
            .checked_sub(encounter.before_native_tick)
            == Some(encounter.steps().len())
        && encounter
            .after_world_tick
            .checked_sub(encounter.before_world_tick)
            == u64::try_from(encounter.steps().len()).ok()
        && encounter.chart() == world.common_chart();
    for (index, step) in encounter.steps().iter().enumerate() {
        let step_role = format!("{role}, native world crossing {}", index + 1);
        closes &= joint_world_receipt(
            output,
            &step_role,
            declaration,
            &previous,
            &step.joint,
            &step.receipt,
        )?;
        closes &= world_wave_receipt(
            output,
            &step_role,
            declaration,
            &step.joint,
            &step.incident,
            &step.reflected,
        )?;
        closes &= step.closes(&declaration.admittance, declaration.law.law().step())
            && encounter.before_native_tick.checked_add(index + 1) == Some(step.native_tick);
        previous = step.joint.next_state();
    }
    closes &= &previous == world.state()
        && encounter.after_world_tick == world.state().commit
        && encounter.after_native_tick == world.native_tick()?;
    publish(
        output,
        format!(
            "ACTUAL COUPLED ENCOUNTER; role={role}; before_native_tick={}; after_native_tick={}; before_world_tick={}; after_world_tick={}; producing_common_chart={:?}; observed_native_receiving_faces={:?}; retained_world_state={:?}; all_actual_steps_and_clocks_close={closes}; observation_origin=actual_opaque_native_encounter; actual_face_change_alone_does_not_isolate_preparation_from_autonomous_motion=true\n",
            encounter.before_native_tick,
            encounter.after_native_tick,
            encounter.before_world_tick,
            encounter.after_world_tick,
            encounter.chart(),
            encounter.observed(),
            world.state(),
        ),
    );
    Ok(closes)
}

#[derive(Debug, Default)]
struct EncounterWitness {
    received: usize,
    receiving_movements: usize,
    matched_choice_changes: usize,
    nonzero_preparations: usize,
    closed: bool,
}

impl EncounterWitness {
    fn accepted(&self) -> bool {
        self.closed
            && self.received == NATIVE_ENCOUNTERS
            && self.receiving_movements > 0
            && self.matched_choice_changes > 0
            && self.nonzero_preparations > 0
    }
}

/// The same native receiver meets a continuing participating Holon. The actual source E
/// declares B before any world observation. A quiet receiving consequence is an independent
/// requested constraint, never the later observed target. Native core owns all execution,
/// comparison, publication and refusal; this function consumes the returned evidence.
fn native_encounters(
    output: &mut impl Write,
    field: &Field,
    receiver: &mut PhysicalReceiver<'_>,
    declared: &ReceiverDeclaration,
    source: &Encoded,
    pin: &exterior::Pin,
) -> Result<EncounterWitness, holonics::hnn::HnnError> {
    let source_ring = field.sources()[0];
    let source_port = receiver
        .constitution()
        .source_port(source_ring)
        .ok_or(holonics::hnn::HnnError::Unadmitted {
            reason: "the preparation family is the actual declared source E port",
        })?
        .clone();
    let preparation = PortPreparation::new(field, source_ring, source_port)?;
    let requested = vec![vec![Rat::zero(); 2 * field.alphabet()]; declared.aperture];
    let compared: Vec<bool> = (0..declared.aperture)
        .map(|station| station == source.len())
        .collect();
    let common_chart = source.part(0..0)?;
    let native_origin = opening_tick(&receiver.opening());
    let declaration = world_declaration(field, native_origin)?;
    let world = BoundJointWorld::new(
        declaration.law.clone(),
        declaration.state.clone(),
        declaration.face.clone(),
        declaration.receipt.clone(),
        declaration.admittance.clone(),
        common_chart,
        native_origin,
    )?;
    receiver.bind_world(world)?;
    let earlier_receiving = receiver.receiving_snapshot(declared)?;
    let world = receiver
        .participating_world()
        .ok_or(holonics::hnn::HnnError::Unadmitted {
            reason: "the actual World remains owned by the continuing Resident",
        })?;
    publish(
        output,
        format!(
            "NATIVE ACTION/WORLD DECLARATION; retained_receiver_material={}; source={source:?}; source_E_preparation={preparation:?}; requested_quiet_native_carriers={requested:?}; compared_joint_partition={compared:?}; initial_actual_world_state={:?}; native_origin={native_origin}; world_initial_commit={}; whole_receiving_chart_real_units=base2_log_amplitude; whole_receiving_chart_imaginary_units=twice_lifted_turns; full_common_chart={:?}; world_coefficients_are_unavailable_to_native_action_inference=true; no_contact_future_is_reset_or_expanded=true\n",
            receiver.constitution().commit(),
            world.state(),
            world.state().commit,
            world.common_chart(),
        ),
    );
    let mut witness = EncounterWitness {
        closed: true,
        ..EncounterWitness::default()
    };
    let mut expected_next_control: Option<Vec<Rat>> = None;
    for action in 0..NATIVE_ENCOUNTERS {
        let role = format!("native prepared encounter {action}");
        let start = Instant::now();
        let before_world = receiver
            .participating_world()
            .ok_or(holonics::hnn::HnnError::Unadmitted {
                reason: "the next actual encounter consumes the retained World",
            })?
            .state()
            .clone();
        let before_world_tick = receiver.participating_world().unwrap().native_tick()?;
        let before_world_chart = receiver
            .participating_world()
            .unwrap()
            .common_chart()
            .clone();
        let before_opening = receiver.opening();
        let before_current = receiver.current().clone();
        let before_commit = receiver.constitution().commit();
        let before_receiving = receiver
            .constitution()
            .receiving_map(declared.ring)
            .cloned();
        let prepared =
            receiver.prepare_action(source, declared, &preparation, &requested, &compared)?;
        let planned_control = prepared.prospective().unique_control().map(<[Rat]>::to_vec);
        if action > 0 {
            let continuation_closes = planned_control == expected_next_control;
            witness.closed &= continuation_closes;
            publish(
                output,
                format!(
                    "ACTUAL LATER PREPARATION CONSUMES PRECEDING RELATION; role={role}; preceding_contemporary_control={expected_next_control:?}; actual_next_native_control={planned_control:?}; identical_present_binding_continues={continuation_closes}; material_version={}\n",
                    prepared.producing_commit()
                ),
            );
        }
        if !prospective_receipt(output, &role, prepared.prospective())? {
            return Err(holonics::hnn::HnnError::Realization {
                what: "the native preparation preserves the whole joint relation before execution",
            });
        }
        publish(
            output,
            format!(
                "BOUND ACTUAL SOURCE/ACTION/OBSERVER; role={role}; producing_material={}; source_chart={:?}; source_Current={:?}; native_opened_at={}; native_receiving_phases={:?}; actual_world_pre_state={before_world:?}; actual_world_native_tick={}; observer_chart={:?}; request_is_bound_before_execution=true\n",
                prepared.producing_commit(),
                prepared.source_chart(),
                prepared.current(),
                prepared.opened_at(),
                prepared.receiving_phases(),
                before_world_tick,
                before_world_chart,
            ),
        );
        match prepared.encounter()? {
            ActionCommunication::Interrupted(received) => {
                let world =
                    receiver
                        .participating_world()
                        .ok_or(holonics::hnn::HnnError::Unadmitted {
                            reason: "a failed actual encounter preserves its retained World",
                        })?;
                witness.closed = false;
                boundary(output, &role, &received.boundary);
                publish(
                    output,
                    format!(
                        "INCOMPLETE ACTUAL NATIVE ENCOUNTER; role={role}; full_partial_receipt={received:?}; actual_native_carry={:?}; actual_world_state={:?}; failed_physical_consequences_preserved=true; no_material_return_committed=true\n",
                        receiver.opening(),
                        world.state(),
                    ),
                );
                break;
            }
            ActionCommunication::Held { prospective } => {
                let world =
                    receiver
                        .participating_world()
                        .ok_or(holonics::hnn::HnnError::Unadmitted {
                            reason: "withholding action does not remove the retained World",
                        })?;
                witness.closed &=
                    prospective_receipt(output, "native encounter held full fibre", &prospective)?
                        && world.state() == &before_world
                        && receiver.opening() == before_opening
                        && receiver.current() == &before_current
                        && receiver.constitution().commit() == before_commit;
                publish(
                    output,
                    format!(
                        "HELD NATIVE ENCOUNTER; role={role}; witness={witness:?}; no_control_selected=true; actual_world_and_retained_receiver_unchanged={}; full_relation={prospective:?}\n",
                        witness.closed
                    ),
                );
                // A refusal does not become an executed action or license another family/cap.
                break;
            }
            ActionCommunication::Received(received) => {
                let world =
                    receiver
                        .participating_world()
                        .ok_or(holonics::hnn::HnnError::Unadmitted {
                            reason: "the returned World remains in the same Resident",
                        })?;
                boundary(output, &role, &received.boundary);
                witness.closed &= encounter_receipt(
                    output,
                    &role,
                    &declaration,
                    &before_world,
                    &received.encounter,
                    &world,
                )?;
                witness.closed &= received.closes()
                    && received.comparison.is_ok()
                    && planned_control.as_deref() == Some(received.applied.control())
                    && received.carry.ticks == opening_tick(&receiver.opening())
                    && received.carry.ticks == world.native_tick()?
                    && continued(&receiver.opening());
                let return_sum: Rat = received.source_returns.iter().map(|r| &r.work).sum();
                let return_closes = received.source_returns.len()
                    == received.encounter.steps().len()
                    && received
                        .source_returns
                        .iter()
                        .zip(received.encounter.steps())
                        .enumerate()
                        .all(|(i, (r, s))| {
                            r.ring == source_ring
                                && r.tick == i + 1
                                && r.incident == s.incident
                                && r.reflected == s.reflected
                                && r.work == -&s.port_work
                                && received
                                    .balances
                                    .get(i)
                                    .is_some_and(|b| b.boundary == r.work && b.closes())
                        })
                    && return_sum == received.word.boundary
                    && received.source_returns.last().is_some_and(|r| {
                        received.carry.change.storage.get(source_ring) == Some(&r.reflected)
                    });
                witness.closed &= return_closes;
                publish(
                    output,
                    format!(
                        "ACTUAL CO-CLOCK WORLD RETURN INTO NATIVE CURRENT; role={role}; complete_source_returns={:?}; native_boundary_work={:?}; world_port_work={:?}; retained_native_carry={:?}; retained_world_state={:?}; per_tick_waves_work_and_final_source_storage_close={return_closes}; actual_World_is_owned_by_Resident=true; requested_model_consequence_is_not_injected_as_observation=true; conditional_R_return_holds_actual_boundary_trajectory_fixed=true; World_material_jet_is_not_claimed=true\n",
                        received.source_returns,
                        received.word.boundary,
                        received
                            .encounter
                            .steps()
                            .iter()
                            .map(|s| &s.port_work)
                            .sum::<Rat>(),
                        received.carry,
                        world.state(),
                    ),
                );
                witness.nonzero_preparations +=
                    usize::from(received.applied.injection().iter().any(|q| !q.is_zero()));
                witness.receiving_movements += usize::from(
                    before_receiving
                        != receiver
                            .constitution()
                            .receiving_map(declared.ring)
                            .cloned(),
                );
                witness.received += 1;
                publish(
                    output,
                    format!(
                        "ACTUAL NATIVE ACTION RETURN; role={role}; full_return={received:?}; contemporary_material_commit={}; actual_native_carry={:?}; actual_world_state={:?}; actual_receipt_precedes_its_learning_in_native_owner=true; snapshot_remains_an_exterior_matched_comparison_not_retention=true\n",
                        receiver.constitution().commit(),
                        receiver.opening(),
                        world.state(),
                    ),
                );
            }
        }
        // Both plans use the PRESENT actual source, carry, Current and physical operators.
        // Only R is substituted from the opaque actual earlier snapshot. This does not execute
        // another encounter, alter the world or bind an old material to the retained learner.
        let matched_world = receiver.participating_world().unwrap().state().clone();
        let matched_opening = receiver.opening();
        let matched_current = receiver.current().clone();
        let matched_commit = receiver.constitution().commit();
        let frozen = receiver.plan_action_with_receiving(
            &earlier_receiving,
            source,
            declared,
            &preparation,
            &requested,
            &compared,
        )?;
        let contemporary =
            receiver.plan_action(source, declared, &preparation, &requested, &compared)?;
        let (matched, changed) = matched_receiving_receipt(output, &frozen, &contemporary)?;
        witness.closed &= matched
            && receiver.participating_world().unwrap().state() == &matched_world
            && receiver.opening() == matched_opening
            && receiver.current() == &matched_current
            && receiver.constitution().commit() == matched_commit;
        witness.matched_choice_changes += usize::from(changed);
        expected_next_control = contemporary.unique_control().map(<[Rat]>::to_vec);
        point(output, &role, receiver);
        if !elapsed(output, &role, start, pin) {
            witness.closed = false;
            break;
        }
    }
    publish(
        output,
        format!(
            "NATIVE ENCOUNTER WITNESS; actual_received={}/{NATIVE_ENCOUNTERS}; actual_receiving_movements={}; matched_receiving_only_choice_changes={}; nonzero_source_wave_preparations={}; full_receipts_close={}; native_encounter_operation_acceptance={}; preparation_effect_on_world_requires_native_matched_pre_state_comparison=true; no_usefulness_or_true_source_selection_claim=true\n",
            witness.received,
            witness.receiving_movements,
            witness.matched_choice_changes,
            witness.nonzero_preparations,
            witness.closed,
            witness.accepted(),
        ),
    );
    Ok(witness)
}

fn boundary(output: &mut impl Write, role: &str, blind: &PhysicalBoundary) {
    publish(
        output,
        format!(
            "BLIND OUTPUT BEGIN; role={role}; first_station={}; grain={}\n",
            blind.first_station(),
            blind.grain()
        ),
    );
    publish(
        output,
        format!(
            "producing decoder D={:?}; encoding fibre={:?}; classes={}; sources={:?}; located={:?}\n",
            blind.chart().decoder(),
            blind.chart().fibre(),
            blind.chart().classes(),
            blind.chart().sources(),
            blind.chart().located()
        ),
    );
    for (index, read) in blind.readings().iter().enumerate() {
        publish(
            output,
            format!(
                "station={}; crossing={}; absolute_tick={}; complete_complex_logits={:?}; phase_turns={:?}; grain_cells={:?}; point_leaders={:?}; actual_decision={:?}; actual_domain={:?}\n",
                read.station,
                read.crossing,
                read.tick,
                ratios(&read.read.logits),
                ratios(&read.read.phases),
                read.read.cells,
                read.leaders(),
                blind.decisions()[index],
                blind.domains()[index]
            ),
        );
    }
    publish(
        output,
        format!(
            "BLIND OUTPUT END; role={role}; no observation has entered this forward constructor\n"
        ),
    );
}

fn point(output: &mut impl Write, role: &str, receiver: &PhysicalReceiver<'_>) {
    let opening = receiver.opening();
    publish(
        output,
        format!(
            "retained point; role={role}; material_commit={}; source_Current={:?}; absolute_next_tick={}; continued_without_absorption={}; actual_opening={opening:?}\n",
            receiver.constitution().commit(),
            receiver.current(),
            opening_tick(&opening),
            continued(&opening)
        ),
    );
    publish(
        output,
        format!(
            "actual retained future; role={role}; state_bits={}; sensitivity={:?}\n",
            receiver.resident().state_bits(),
            receiver
                .resident()
                .held_contact_variation()
                .map(|h| h.reading())
        ),
    );
    publish(
        output,
        format!(
            "actual action/current clock binding; role={role}; action={:?}; clock_matches={:?}\n",
            receiver
                .resident()
                .held_contact_variation()
                .map(|h| h.action()),
            receiver
                .resident()
                .held_contact_variation()
                .zip(receiver.resident().carried())
                .map(|(h, carry)| h.reading().next_tick == carry.ticks)
        ),
    );
}

fn elapsed(output: &mut impl Write, role: &str, start: Instant, pin: &exterior::Pin) -> bool {
    let ns = start.elapsed().as_nanos();
    let valid = pin
        .unit_bound_ms()
        .is_none_or(|bound| ns <= bound * 1_000_000);
    publish(
        output,
        format!(
            "passage complete; role={role}; elapsed_ns={ns}; elapsed_ms={}; measured_unit_bound_ms={:?}; within_declared_unit={valid}; resident_bytes={:?}\n",
            ns / 1_000_000,
            pin.unit_bound_ms(),
            exterior::resident_set()
        ),
    );
    if !valid {
        publish(
            output,
            "INCOMPLETE: this whole passage exceeded the fixed measured unit projection; no later passage or larger limit\n",
        );
    }
    valid
}

/// No program-selected answer gates the output. Acceptance requires the actual continuing
/// native operations, actual material movement and complete declared observations to occur.
pub(super) fn run(out: &str, pin: &exterior::Pin) {
    run_domain(out, pin, false);
}

pub(super) fn run_world_history(out: &str, pin: &exterior::Pin) {
    run_domain(out, pin, true);
}

fn run_domain(out: &str, pin: &exterior::Pin, world_domain: bool) {
    std::fs::create_dir_all(out).expect("the output receipt directory");
    let mut output =
        BufWriter::new(File::create(format!("{out}/ACTUAL_OUTPUT.txt")).expect("actual output"));
    let all = Instant::now();
    let before_work = holonics::hnn::word::work::read();
    let accepted = exercise(&mut output, pin, world_domain);
    publish(
        &mut output,
        format!(
            "WHOLE RUN RECEIPT; integrated_operation_acceptance={accepted}; measured_wall_ns={}; owner_calls={:?}; resident_bytes={:?}; declared_wall_guard_ms={}; measured_unit_bound_ms={:?}; threads={}; no limit changed\n",
            all.elapsed().as_nanos(),
            holonics::hnn::word::work::read().since(before_work),
            exterior::resident_set(),
            pin.deadline_ms(),
            pin.unit_bound_ms(),
            pin.threads()
        ),
    );
    if !accepted {
        // The complete receipt was flushed; a refused native operation is not process success.
        std::process::exit(2);
    }
}

fn exercise(mut output: &mut impl Write, pin: &exterior::Pin, world_domain: bool) -> bool {
    let all = Instant::now();
    let before_work = holonics::hnn::word::work::read();
    publish(
        &mut output,
        format!(
            "continuing-behavior-v2; correlated native terrain; source_seed={SOURCE_SEED}; consequence_seed={CONSEQUENCE_SEED}; classes={CLASSES}; prefix={PREFIX}; aperture={APERTURE}; receiving_observations={RECEIVING_OBSERVATIONS}; native_encounters={NATIVE_ENCOUNTERS}; blind_contact=1; observed_contact={CONTACT_OBSERVATIONS}; blind_consequence=1; original_passages={WHOLE_PASSAGES}; pin_wall_guard_ms={}; threads={}\n",
            pin.deadline_ms(),
            pin.threads()
        ),
    );
    publish(&mut output, if world_domain {
        "fixed scoped World-operation acceptance: two existing actual receiving observations precede two acquired-R actual coupled encounters; actual World faces and R movement, later matched R-only preparation change, both participant states and conjugate wave work/clock close. This is not the full prior-World-history choice proof; that bounded mechanical control is separate. The original seven-passage C/K/D movement gate remains failed and recorded; combined World/contact material transport remains unadmitted. No holdout, acquisition, repair or useful-product claim.\n"
    } else {
        "unchanged closed-field foundation acceptance: seven native passages, at least two actual C/K/D factor movements, nonzero delayed comparison, full held differential/clock, and all source/work/momentum balances close. No actual World is bound or discarded in this domain. The coupled World/contact foundation gate remains open. No holdout, acquisition, repair or useful-product claim.\n"
    });
    let (field, declared) = match declare() {
        Ok(v) => v,
        Err(error) => {
            publish(
                &mut output,
                format!("INCOMPLETE: declared native field refused {error:?}\n"),
            );
            return false;
        }
    };
    let theta = match material(&field) {
        Ok(v) => v,
        Err(error) => {
            publish(
                &mut output,
                format!("INCOMPLETE: native material/mount refused {error:?}\n"),
            );
            return false;
        }
    };
    let current = Current::at_rest(&field);
    let truth =
        KnownTruth::cyclic_class_orbit(CyclicLaw::Alternation, CLASSES, SOURCE_SEED, APERTURE)
            .expect("the existing correlated terrain declaration");
    let encoded = Encoded::identity(&truth, &field).expect("actual known-truth identity admission");
    let consequence =
        KnownTruth::cyclic_class_orbit(CyclicLaw::Alternation, CLASSES, CONSEQUENCE_SEED, APERTURE)
            .expect("the blind source terrain");
    let consequence = Encoded::identity(&consequence, &field).expect("the same admitted chart");
    let mut receiver = match PhysicalReceiver::new(&field, theta, current, WordOpening::Rest) {
        Ok(v) => v,
        Err(error) => {
            publish(
                &mut output,
                format!("INCOMPLETE: common native Resident mount refused {error:?}\n"),
            );
            return false;
        }
    };
    publish(
        &mut output,
        format!("declared Field={field:?}; receiving section={declared:?}\n"),
    );
    point(&mut output, "initial", &receiver);
    let compared: Vec<bool> = (0..APERTURE).map(|station| station >= PREFIX).collect();
    let mut completed = 0;
    let mut receiving_changed = 0;
    for observed in &encoded {
        let role = format!("receiving observation {completed}");
        let start = Instant::now();
        let work = holonics::hnn::word::work::read();
        let before_tick = opening_tick(&receiver.opening());
        let before = receiver.constitution().clone();
        let source = observed.part(0..PREFIX).expect("actual source prefix only");
        publish(
            &mut output,
            format!(
                "source admission; role={role}; encoded_prefix={:?}; prior_next_tick={before_tick}; source is supplied once to this native section query\n",
                source.cells()
            ),
        );
        let receipt = match receiver.communicate(&source, &declared, |blind| {
            boundary(&mut output, &role, blind);
            // Reading/printing the later observation happens only here, after the entire blind
            // receipt has reached both outputs. It supplies the existing declared comparison.
            publish(
                &mut output,
                format!(
                    "LATER OBSERVATION; role={role}; actual_section={:?}; compared={compared:?}\n",
                    observed.cells()
                ),
            );
            Some(PhysicalObservation {
                observed: observed.clone(),
                compared: compared.clone(),
                learning: PhysicalLearning::Receiving,
            })
        }) {
            Ok(v) => v,
            Err(error) => {
                publish(
                    &mut output,
                    format!("INCOMPLETE: {role} native forward refused {error:?}\n"),
                );
                point(&mut output, "after receiving refusal", &receiver);
                return false;
            }
        };
        publish(
            &mut output,
            format!(
                "source/physical work; role={role}; closes={}; opening={:?}; Word={:?}; per_tick={:?}; owner_calls={:?}\n",
                receipt.closes(),
                receipt.opening,
                receipt.word,
                receipt.balances,
                holonics::hnn::word::work::read().since(work)
            ),
        );
        let closed = receipt.closes();
        match receipt.comparison {
            Ok(Some(publication)) => {
                let changed = before.receiving_map(declared.ring)
                    != receiver.constitution().receiving_map(declared.ring);
                receiving_changed += usize::from(changed);
                publish(
                    &mut output,
                    format!(
                        "actual Receiving publication; role={role}; map_changed={changed}; ratio={:?}; publication={:?}\n",
                        publication.ratio, publication.publication
                    ),
                );
            }
            other => {
                publish(
                    &mut output,
                    format!("INCOMPLETE: {role} comparison/publication is {other:?}\n"),
                );
                point(&mut output, "after receiving comparison refusal", &receiver);
                return false;
            }
        }
        point(&mut output, &role, &receiver);
        if !closed
            || opening_tick(&receiver.opening()) <= before_tick
            || !continued(&receiver.opening())
        {
            publish(
                &mut output,
                "INCOMPLETE: the actual source/work/continuing-clock receipt did not close\n",
            );
            return false;
        }
        completed += 1;
        if !elapsed(&mut output, &role, start, pin) {
            return false;
        }
    }
    if receiving_changed == 0 {
        publish(
            &mut output,
            "INCOMPLETE: actual Receiving comparisons acquired no readout movement; no authored map substitutes\n",
        );
        return false;
    }
    // [agent-inferred] The combined World/contact-material jet is not an admitted owner.
    // A scoped World consumer ends before the closed-field held future. No actual World
    // or held future is removed to enable the other, and no contact budget is raised.
    if world_domain {
        let action_source = encoded[0]
            .part(0..PREFIX)
            .expect("the existing actual source chart");
        let encounters = match native_encounters(
            &mut output,
            &field,
            &mut receiver,
            &declared,
            &action_source,
            pin,
        ) {
            Ok(witness) => witness,
            Err(error) => {
                publish(
                    &mut output,
                    format!(
                        "INCOMPLETE: actual native preparation/encounter/receiving return refused {error:?}; no guessed control or target replaces it\n"
                    ),
                );
                point(&mut output, "after native encounter refusal", &receiver);
                return false;
            }
        };
        point(&mut output, "final scoped coupled receiver", &receiver);
        publish(
            &mut output,
            format!(
                "WHOLE SCOPED ACTUAL WORLD OPERATION; actual_initial_receiving_passages={completed}; actual_native_encounters={encounters:?}; scoped_operation_acceptance={}; retained_World_state={:?}; retained_World_native_tick={:?}; native_next_tick={}; exact_owner_calls={:?}; wall_ns={}; resident_bytes={:?}; original_v111_factor_movement_gate_remains_failed_and_recorded=true; combined_World_contact_jet_is_unadmitted=true; no_full_architecture_or_useful_output_claim=true\n",
                encounters.accepted(),
                receiver.participating_world().map(|w| w.state()),
                receiver.participating_world().map(|w| w.native_tick()),
                opening_tick(&receiver.opening()),
                holonics::hnn::word::work::read().since(before_work),
                all.elapsed().as_nanos(),
                exterior::resident_set(),
            ),
        );
        return encounters.accepted();
    }
    // Derive the fixed numerical domain from the actual full-state shape and factor coordinates.
    // This native cut is charged by the work owner; it neither executes a second passage nor
    // changes the common material/carry. Its loaded slots are part of the retained differential.
    let ops = match holonics::hnn::propagation::Operands::exact_at_cut(
        &field,
        receiver.constitution(),
        receiver.current(),
    ) {
        Ok(v) => v,
        Err(error) => {
            publish(
                &mut output,
                format!("INCOMPLETE: prospective native operand admission refused {error:?}\n"),
            );
            return false;
        }
    };
    let shape = holonics::hnn::word::EndChange::rest(&field, &ops);
    let state_coordinates = shape
        .storage
        .iter()
        .chain(shape.arrivals.iter().flatten())
        .chain(shape.states.iter().flatten())
        .chain(shape.resonators.iter().flatten().flatten())
        .map(Vec::len)
        .sum::<usize>();
    let parameters = (0..field.contacts().len())
        .map(|a| {
            [
                receiver.constitution().contact_storage(a),
                receiver.constitution().contact_stiffness(a),
                receiver.constitution().contact_dissipation(a),
            ]
            .iter()
            .map(|f| f.rows() * f.columns())
            .sum::<usize>()
        })
        .sum::<usize>();
    let budget = VariationBudget {
        ratios: parameters * state_coordinates,
        bits: VARIATION_BITS,
        column_ticks: parameters * APERTURE * CONTACT_WORDS,
    };
    drop(shape);
    drop(ops);
    let admission = match receiver.begin_continuing_contact_variation(budget) {
        Ok(v) => v,
        Err(error) => {
            publish(
                &mut output,
                format!(
                    "INCOMPLETE: current held-material future refused {error:?}; no derivative reset or bypass\n"
                ),
            );
            point(&mut output, "after prospective future refusal", &receiver);
            return false;
        }
    };
    publish(
        &mut output,
        format!(
            "actual prospective held future; budget={budget:?}; admitted={admission:?}; earlier readout-acquisition derivatives are not claimed\n"
        ),
    );
    publish(
        &mut output,
        "Declared continuing action: RealizedFactorTranslation, applied native factor increments held as controls, explicit P=I. The learner/rounding/observation-selection policy is not differentiated. The native current-Word ray/joint/storage checks admit the supplied reached direction; they do not certify historical-response score decrease. Source station entrance remains tau_g+1+j at its fixed Current lift; the independent carried hop/pump clock advances.\n",
    );
    let mut moved_publications = 0;
    let mut delayed_comparisons = 0;
    for passage in 0..CONTACT_WORDS {
        let observes = (1..=CONTACT_OBSERVATIONS).contains(&passage);
        let role = if passage == 0 {
            "blind contact".to_string()
        } else if observes {
            format!("contact observation {passage}")
        } else {
            "blind consequence".to_string()
        };
        let observed = if passage == CONTACT_WORDS - 1 {
            &consequence[0]
        } else {
            &encoded[passage % encoded.len()]
        };
        let source = observed
            .part(0..PREFIX)
            .expect("actual source only, never future target");
        let start = Instant::now();
        let work = holonics::hnn::word::work::read();
        let before_tick = opening_tick(&receiver.opening());
        let before_commit = receiver.constitution().commit();
        publish(
            &mut output,
            format!(
                "source admission; role={role}; encoded_prefix={:?}; prior_next_tick={before_tick}; producing_commit={before_commit}\n",
                source.cells()
            ),
        );
        let receipt = match receiver.communicate_contact(&source, &declared, |blind| {
            boundary(&mut output, &role, blind);
            observes.then(|| {
                publish(&mut output, format!("LATER OBSERVATION; role={role}; actual_section={:?}; compared={compared:?}\n", observed.cells()));
                ContactObservation { observed: observed.clone(), compared: compared.clone() }
            })
        }) {
            Ok(v) => v,
            Err(error) => { publish(&mut output, format!("INCOMPLETE: {role} native forward/held future refused {error:?}; no reset/skip/restart\n")); point(&mut output, "after contact forward refusal", &receiver);
                return false; }
        };
        let closed = receipt.closes();
        publish(
            &mut output,
            format!(
                "source/physical work; role={role}; closes={closed}; opening={:?}; Word={:?}; per_tick={:?}; owner_calls={:?}\n",
                receipt.opening,
                receipt.word,
                receipt.balances,
                holonics::hnn::word::work::read().since(work)
            ),
        );
        match receipt.held_comparison {
            Ok(Some(credit)) if observes => {
                let has_delayed = credit.carried.iter().any(|x| !x.is_zero());
                delayed_comparisons += usize::from(has_delayed);
                let sum_closes = credit
                    .total
                    .iter()
                    .zip(&credit.within_word)
                    .zip(&credit.carried)
                    .all(|((total, direct), carried)| total == &(direct + carried));
                publish(
                    &mut output,
                    format!(
                        "actual full contact credit; role={role}; producing_commit={}; coordinates={:?}; within_word={:?}; carried={:?}; total={:?}; sum_closes={sum_closes}; delayed_nonzero={has_delayed}; opening_costate={:?}; reached_metric={:?}; retained_reading={:?}\n",
                        credit.producing_commit,
                        credit.coordinates,
                        ratios(&credit.within_word),
                        ratios(&credit.carried),
                        ratios(&credit.total),
                        credit.opening,
                        credit.metric,
                        credit.reading
                    ),
                );
                if !sum_closes || credit.producing_commit != before_commit {
                    publish(
                        &mut output,
                        "INCOMPLETE: the actual delayed covector/material pairing did not close\n",
                    );
                    return false;
                }
            }
            Ok(None) if !observes => {}
            other => {
                publish(
                    &mut output,
                    format!("INCOMPLETE: {role} held comparison is {other:?}\n"),
                );
                point(&mut output, "after held comparison refusal", &receiver);
                return false;
            }
        }
        if !matches!(receipt.comparison.as_ref(), Ok(None)) {
            publish(
                &mut output,
                format!(
                    "INCOMPLETE: continuing contact unexpectedly used an ordinary local publication {:?}\n",
                    receipt.comparison
                ),
            );
            return false;
        }
        match receipt.held_publication {
            Ok(Some(publication)) if observes => {
                let moved = publication
                    .continuation
                    .material
                    .iter()
                    .any(|m| m.factor.entries().iter().any(|x| !x.is_zero()));
                moved_publications += usize::from(moved);
                let parameters = receiver
                    .resident()
                    .held_contact_variation()
                    .map_or(0, |h| h.reading().parameters);
                let identity = ExactRatMatrix::identity(parameters)
                    .expect("the declared finite parameter identity");
                let actual_rebase = receiver
                    .resident()
                    .held_contact_variation()
                    .map(|h| h.reading());
                let rebase_closes = publication.parameter_transport == identity
                    && Some(&publication.rebase) == actual_rebase
                    && publication.rebase.next_tick == receipt.carry.ticks;
                publish(
                    &mut output,
                    format!(
                        "actual native contact publication; role={role}; factor_moved={moved}; actual_material_commit={}; admitted_publication={:?}; canonical_held_continuation={:?}; declared_parameter_transport={:?}; successor_sensitivity={:?}; rebase_closes={rebase_closes}\n",
                        receiver.constitution().commit(),
                        publication.publication,
                        publication.continuation,
                        publication.parameter_transport,
                        publication.rebase
                    ),
                );
                if !rebase_closes {
                    publish(
                        &mut output,
                        "INCOMPLETE: the actual canonical sensitivity rebase did not match the declared action/material/clock\n",
                    );
                    return false;
                }
            }
            Ok(None) if !observes => {
                if receiver.constitution().commit() != before_commit {
                    publish(
                        &mut output,
                        "INCOMPLETE: a blind passage unexpectedly published material\n",
                    );
                    return false;
                }
            }
            other => {
                publish(
                    &mut output,
                    format!(
                        "INCOMPLETE: {role} native material publication/rebase is {other:?}; the held gradient is not a finite Deposit by itself\n"
                    ),
                );
                point(&mut output, "after material/rebase refusal", &receiver);
                return false;
            }
        }
        point(&mut output, &role, &receiver);
        if !closed
            || receipt.carry
                != match receiver.opening() {
                    WordOpening::Received { carry, .. } => carry,
                    WordOpening::Rest => receipt.blind_carry.clone(),
                }
            || opening_tick(&receiver.opening()) <= before_tick
            || !continued(&receiver.opening())
        {
            publish(
                &mut output,
                "INCOMPLETE: actual source/work/canonical carry/continuing clock did not close\n",
            );
            return false;
        }
        completed += 1;
        if !elapsed(&mut output, &role, start, pin) {
            return false;
        }
    }
    // Move the same Resident out only at the end. Reconstructing the receiver merely to inspect
    // it between inputs would throw away its declaring-face cache and obscure real whole costs.
    let resident = receiver.into_resident();
    let held = resident.held_contact_variation();
    let held_complete = held.is_some_and(|h| {
        h.action() == ContactVariationAction::RealizedFactorTranslation
            && h.reading().words == CONTACT_WORDS
            && h.reading().next_tick == resident.carried().map_or(0, |c| c.ticks)
    });
    let accepted = completed == WHOLE_PASSAGES
        && moved_publications >= 2
        && delayed_comparisons > 0
        && held_complete;
    publish(
        &mut output,
        format!(
            "whole actual closed-field interaction; complete_passages={completed}/{WHOLE_PASSAGES}; actual_receiving_movements={receiving_changed}; actual_contact_factor_publications={moved_publications}; nonzero_delayed_comparisons={delayed_comparisons}; held_future_matches_actual_clock={held_complete}; retained_state_bits={}; final_held_reading={:?}; final_material_commit={}; source_Current={:?}; owner_calls={:?}; wall_ns={}; resident_bytes={:?}; integrated_operation_acceptance={accepted}\n",
            resident.state_bits(),
            held.map(|h| h.reading()),
            resident.constitution().commit(),
            resident.current(),
            holonics::hnn::word::work::read().since(before_work),
            all.elapsed().as_nanos(),
            exterior::resident_set()
        ),
    );
    if !accepted {
        publish(
            &mut output,
            "INCOMPLETE: the whole continuing-operation acceptance did not pass; actual output above remains the receipt\n",
        );
    }
    publish(
        &mut output,
        "Response attribution: the native encounter stage separately prints current and earlier-R planning at identical present source/carry/Current/operators, preserving full fibres. Source, carried state and material all change across the other passages; their separate finite effects remain unisolated. Actual publication and retained state are distinct from usefulness or adaptation.\n",
    );
    publish(
        &mut output,
        "Scope: section-source clock and absolute carried pump clock are separately printed. This run adds no unsupported ingest, save/cold/device continuation, policy derivative, foreign codec or completion-domain release. No useful-language/product conclusion follows from the operation acceptance.\n",
    );
    accepted
}

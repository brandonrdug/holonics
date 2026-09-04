use std::io::Write;
use std::path::PathBuf;

use body::incidence::IncidenceHand;
use body::manifold::FeltDeed;
use body::num::Cog;
use life::current_world::{
    present_native_event_with, present_native_event_with_regional, NativeEventCurrent,
    NativeEventRelation, NativePathChart, NativeRegionalArc, NativeRegionalRelation,
    NativeRelationOrgan, NativeRelationOrganImage,
};
use life::form_mouth::deposit_form_or_message;
use serde::Serialize;
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryRadiation, CpuLiveCurrentExecutor, CurrentBoundaryPort, InterfaceCapability,
    LiveBoundaryTransition, LiveConstituent, LiveCurrentMachine, LiveCurrentRestImage,
    SparseStandingSurface,
};

/// This driver's name at the plate mouth: `.local/artifacts/eros_exact_growing_calculator/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_exact_growing_calculator";
/// The `ERST` half of the calculator checkpoint. This one has a mouth today.
const CHECKPOINT_MACHINE_FORM: &str = "checkpoint-machine";
/// The four relation-organ wires of the same checkpoint. Real codecs; no held plate schema.
const GCD_STATE_FORM: &str = "checkpoint-gcd-state";
const RATIO_STATE_FORM: &str = "checkpoint-ratio-state";
const CONTEXT_FORM: &str = "checkpoint-context";
const ARRIVAL_FORM: &str = "checkpoint-arrival";

const TRAINING_INPUTS: [Pair; 2] = [Pair::new(84, 30), Pair::new(1_071, 462)];
const HELD_OUT_INPUT: Pair = Pair::new(391, 299);
const DIVISION_STAGES: u32 = 3;

const OBJECTIVE_GCD: i64 = 10_001;
const OBJECTIVE_REDUCE: i64 = 10_002;
const STAGE_BASE: i64 = 20_000;
const CAPABILITY_DIVMOD: i64 = 30_001;
const CAPABILITY_RETURN: i64 = 30_002;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct Pair {
    a: u64,
    b: u64,
}

impl Pair {
    const fn new(a: u64, b: u64) -> Self {
        Self { a, b }
    }

    fn divide(self) -> Result<(u64, u64, Self), String> {
        if self.b == 0 {
            return Err("DIVMOD cannot receive a zero divisor".to_owned());
        }
        let quotient = self.a / self.b;
        let remainder = self.a % self.b;
        Ok((quotient, remainder, Self::new(self.b, remainder)))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct ExactRatio {
    numerator: i128,
    denominator: u128,
}

impl ExactRatio {
    fn new(numerator: i128, denominator: u128) -> Result<Self, String> {
        if denominator == 0 {
            return Err("an exact ratio needs a nonzero denominator".to_owned());
        }
        if numerator == 0 {
            return Ok(Self {
                numerator: 0,
                denominator: 1,
            });
        }
        let common = gcd_u128(numerator.unsigned_abs(), denominator);
        Ok(Self {
            numerator: numerator / common as i128,
            denominator: denominator / common,
        })
    }

    fn subtract(self, other: Self) -> Result<Self, String> {
        let left = self
            .numerator
            .checked_mul(other.denominator as i128)
            .ok_or_else(|| "ratio subtraction overflowed the fixed observation".to_owned())?;
        let right = other
            .numerator
            .checked_mul(self.denominator as i128)
            .ok_or_else(|| "ratio subtraction overflowed the fixed observation".to_owned())?;
        let denominator = self
            .denominator
            .checked_mul(other.denominator)
            .ok_or_else(|| "ratio denominator overflowed the fixed observation".to_owned())?;
        Self::new(left - right, denominator)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct EuclideanDivision {
    stage: u32,
    before: Pair,
    quotient: u64,
    remainder: u64,
    after: Pair,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct RegionalRead {
    grain: u32,
    axes: u32,
    cells: usize,
    incidences: usize,
    pins: usize,
    boundaries: usize,
    paths: usize,
    folded_paths: usize,
    transport_terms: usize,
    exposed_pins: usize,
    open_boundaries: usize,
    ride_boundaries: usize,
    found_boundaries: usize,
    native_sha256: String,
    acquired_path_conducted: bool,
}

#[derive(Clone, Debug, Serialize)]
struct TrainingStageRead {
    stage: u32,
    capability: &'static str,
    inputs: [Pair; 2],
    divisions: Vec<EuclideanDivision>,
    taught_region: RegionalRead,
    ordinary_current_radiation_exact: bool,
    directed_radiation_exact: bool,
}

#[derive(Clone, Debug, Serialize)]
struct TrainingRead {
    examples: [Pair; 2],
    stages: Vec<TrainingStageRead>,
    returned_gcd: u64,
    returned_ratio: ExactRatio,
    taught_checkpoint_sha256: String,
    no_region_checkpoint_sha256: String,
    rest_remount_exact: bool,
}

#[derive(Clone, Debug, Serialize)]
struct ExecutionStageRead {
    stage: u32,
    capability: &'static str,
    input: Pair,
    region: RegionalRead,
    division: Option<EuclideanDivision>,
}

#[derive(Clone, Debug, Serialize)]
struct ExecutionRead {
    source: &'static str,
    input: Pair,
    stages: Vec<ExecutionStageRead>,
    completed: bool,
    gcd: Option<u64>,
    reduced_ratio: Option<ExactRatio>,
    result_returned_as_later_current: bool,
    before_sha256: String,
    after_sha256: String,
    stop_reason: String,
}

#[derive(Clone, Debug, Serialize)]
struct HandFoilRead {
    input: Pair,
    region: RegionalRead,
    same_hand_as_training: bool,
    acquired_path_conducted: bool,
}

#[derive(Clone, Debug, Serialize)]
struct NumericFaceRead {
    binary32_word: String,
    binary32_exact_dyadic: ExactRatio,
    bounded_candidate: ExactRatio,
    bounded_candidate_denominator_limit: u64,
    candidate_rounds_to_binary32_word: bool,
    stored_minus_candidate: ExactRatio,
    continued_fraction_quotients: Vec<u128>,
    bfloat16_word: String,
    bfloat16_exact_dyadic: ExactRatio,
}

#[derive(Clone, Debug, Serialize)]
struct AcceptanceRead {
    no_region_sibling_refused_material_conduct: bool,
    trained_body_conducted_every_held_out_stage: bool,
    exact_rest_remount_preserved_conduct: bool,
    held_out_magnitudes_absent_from_training: bool,
    euclidean_path_served_gcd_and_ratio_reduction: bool,
    reverse_hand_did_not_conduct_the_acquired_path: bool,
    exact_result_returned_later: bool,
    no_private_executor_testimony_read: bool,
}

#[derive(Clone, Debug, Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    event_grain: &'static str,
    action_boundary: &'static str,
    numerical_faces: NumericFaceRead,
    training: TrainingRead,
    held_out: ExecutionRead,
    no_region_control: ExecutionRead,
    reversed_hand: HandFoilRead,
    acceptance: AcceptanceRead,
}

#[derive(Clone)]
struct CalculatorCheckpoint {
    machine: LiveCurrentRestImage,
    gcd_state: NativeRelationOrganImage,
    ratio_state: NativeRelationOrganImage,
    context: NativeRelationOrganImage,
    arrival: NativeRelationOrganImage,
}

struct CalculatorWorld {
    machine: LiveCurrentMachine,
    gcd_state: NativeRelationOrgan,
    ratio_state: NativeRelationOrgan,
    context: NativeRelationOrgan,
    arrival: NativeRelationOrgan,
}

impl CalculatorWorld {
    fn new() -> Result<Self, String> {
        Ok(Self {
            machine: LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?),
            gcd_state: NativeRelationOrgan::new(),
            ratio_state: NativeRelationOrgan::new(),
            context: NativeRelationOrgan::new(),
            arrival: NativeRelationOrgan::new(),
        })
    }

    fn from_checkpoint(checkpoint: &CalculatorCheckpoint) -> Result<Self, String> {
        let machine =
            LiveCurrentMachine::from_rest_image(checkpoint.machine.clone()).map_err(debug)?;
        Ok(Self {
            gcd_state: NativeRelationOrgan::recover(checkpoint.gcd_state, &machine)
                .map_err(debug)?,
            ratio_state: NativeRelationOrgan::recover(checkpoint.ratio_state, &machine)
                .map_err(debug)?,
            context: NativeRelationOrgan::recover(checkpoint.context, &machine).map_err(debug)?,
            arrival: NativeRelationOrgan::recover(checkpoint.arrival, &machine).map_err(debug)?,
            machine,
        })
    }

    fn checkpoint(&self) -> Result<CalculatorCheckpoint, String> {
        Ok(CalculatorCheckpoint {
            machine: self.machine.rest_image().map_err(debug)?,
            gcd_state: self.gcd_state.checkpoint(),
            ratio_state: self.ratio_state.checkpoint(),
            context: self.context.checkpoint(),
            arrival: self.arrival.checkpoint(),
        })
    }

    fn present_capability(
        &mut self,
        states: [Pair; 2],
        stage: u32,
        hand: IncidenceHand,
        regional: bool,
    ) -> Result<ContemporaryRadiation, String> {
        let capability = if stage < DIVISION_STAGES {
            CAPABILITY_DIVMOD
        } else {
            CAPABILITY_RETURN
        };
        let gcd_atoms = state_atoms(OBJECTIVE_GCD, states[0], 1)?;
        let ratio_atoms = state_atoms(OBJECTIVE_REDUCE, states[1], 2)?;
        let context_atoms = [atom(STAGE_BASE + stage as i64)?, atom(capability)?];
        let arrival_atoms = [atom(STAGE_BASE + stage as i64 + 1)?];
        let gcd_chart = NativePathChart::new(&gcd_atoms).map_err(debug)?;
        let ratio_chart = NativePathChart::new(&ratio_atoms).map_err(debug)?;
        let context_chart = NativePathChart::new(&context_atoms).map_err(debug)?;
        let arcs = [NativeRegionalArc::new(
            2,
            CurrentBoundaryPort::Exposed(0),
            3,
            CurrentBoundaryPort::Cell,
            // Stage is chronology, not interface identity. The same context-to-arrival seam is
            // available at every calculator step.
            InterfaceCapability::new(0x4341_4c43, 0),
            0,
            0,
            hand,
        )];
        let regions = [NativeRegionalRelation::new(3, &arcs)];
        let relations = [
            NativeEventRelation::new(0, 3),
            NativeEventRelation::new(1, 3),
        ];
        let mut currents = [
            NativeEventCurrent::continuing_complex(
                &mut self.gcd_state,
                gcd_chart.complex(),
                action(),
            ),
            NativeEventCurrent::continuing_complex(
                &mut self.ratio_state,
                ratio_chart.complex(),
                action(),
            ),
            NativeEventCurrent::continuing_complex(
                &mut self.context,
                context_chart.complex(),
                action(),
            ),
            NativeEventCurrent::continuing(&mut self.arrival, &arrival_atoms, action()),
        ];
        let mut cpu = CpuLiveCurrentExecutor;
        present_native_event_with_regional(
            &mut self.machine,
            &mut cpu,
            &mut currents,
            &relations,
            if regional { &regions } else { &[] },
        )
        .map_err(debug)
    }

    fn present_result(
        &mut self,
        gcd: u64,
        reduced: ExactRatio,
    ) -> Result<ContemporaryRadiation, String> {
        let gcd_atoms = [atom(OBJECTIVE_GCD)?, encoded_atom(gcd, 5)?];
        let numerator = u64::try_from(reduced.numerator)
            .map_err(|_| "the fixed reduced numerator must be positive u64".to_owned())?;
        let denominator = u64::try_from(reduced.denominator)
            .map_err(|_| "the fixed reduced denominator must fit u64".to_owned())?;
        let ratio_atoms = [
            atom(OBJECTIVE_REDUCE)?,
            encoded_atom(numerator, 6)?,
            encoded_atom(denominator, 7)?,
        ];
        let gcd_chart = NativePathChart::new(&gcd_atoms).map_err(debug)?;
        let ratio_chart = NativePathChart::new(&ratio_atoms).map_err(debug)?;
        let mut currents = [
            NativeEventCurrent::continuing_complex(
                &mut self.gcd_state,
                gcd_chart.complex(),
                action(),
            ),
            NativeEventCurrent::continuing_complex(
                &mut self.ratio_state,
                ratio_chart.complex(),
                action(),
            ),
        ];
        let mut cpu = CpuLiveCurrentExecutor;
        present_native_event_with(&mut self.machine, &mut cpu, &mut currents, &[]).map_err(debug)
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros exact growing calculator: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let output = PathBuf::from(
        arguments
            .next()
            .ok_or_else(|| "usage: eros_exact_growing_calculator <new-report.json>".to_owned())?,
    );
    if arguments.next().is_some() {
        return Err("usage: eros_exact_growing_calculator <new-report.json>".to_owned());
    }

    let numerical_faces = numerical_faces()?;
    let (training, trained_checkpoint, no_region_checkpoint) = train()?;

    let mut remounted = CalculatorWorld::from_checkpoint(&trained_checkpoint)?;
    let remounted_checkpoint = remounted.checkpoint()?;
    let rest_remount_exact =
        checkpoint_bytes(&remounted_checkpoint)? == checkpoint_bytes(&trained_checkpoint)?;
    let held_out = execute(
        "trained-rest-remount",
        &mut remounted,
        HELD_OUT_INPUT,
        IncidenceHand::Against,
    )?;

    let mut control = CalculatorWorld::from_checkpoint(&no_region_checkpoint)?;
    let no_region_control = execute(
        "same-history-without-regional-training",
        &mut control,
        HELD_OUT_INPUT,
        IncidenceHand::Against,
    )?;

    let mut hand_foil = CalculatorWorld::from_checkpoint(&trained_checkpoint)?;
    let foil_radiation = hand_foil.present_capability(
        [HELD_OUT_INPUT, HELD_OUT_INPUT],
        0,
        IncidenceHand::With,
        true,
    )?;
    let foil_region = radiation_region(&foil_radiation)?;
    let reversed_hand = HandFoilRead {
        input: HELD_OUT_INPUT,
        acquired_path_conducted: foil_region.acquired_path_conducted,
        region: foil_region,
        same_hand_as_training: false,
    };

    let acceptance = AcceptanceRead {
        no_region_sibling_refused_material_conduct: !no_region_control.completed
            && no_region_control.stages.first().is_some_and(|stage| {
                !stage.region.acquired_path_conducted && stage.division.is_none()
            }),
        trained_body_conducted_every_held_out_stage: held_out.completed
            && held_out
                .stages
                .iter()
                .all(|stage| stage.region.acquired_path_conducted),
        exact_rest_remount_preserved_conduct: rest_remount_exact && held_out.completed,
        held_out_magnitudes_absent_from_training: TRAINING_INPUTS
            .iter()
            .all(|pair| *pair != HELD_OUT_INPUT),
        euclidean_path_served_gcd_and_ratio_reduction: held_out.gcd == Some(23)
            && held_out.reduced_ratio == Some(ExactRatio::new(17, 13)?),
        reverse_hand_did_not_conduct_the_acquired_path: !reversed_hand.acquired_path_conducted,
        exact_result_returned_later: held_out.result_returned_as_later_current,
        no_private_executor_testimony_read: true,
    };
    let accepted = acceptance.no_region_sibling_refused_material_conduct
        && acceptance.trained_body_conducted_every_held_out_stage
        && acceptance.exact_rest_remount_preserved_conduct
        && acceptance.held_out_magnitudes_absent_from_training
        && acceptance.euclidean_path_served_gcd_and_ratio_reduction
        && acceptance.reverse_hand_did_not_conduct_the_acquired_path
        && acceptance.exact_result_returned_later
        && acceptance.no_private_executor_testimony_read;

    let mut training = training;
    training.rest_remount_exact = rest_remount_exact;
    let report = Report {
        schema: "eros.exact-growing-calculator.observer.v1",
        status: if accepted {
            "accepted"
        } else {
            "observed-missing-relation"
        },
        event_grain: "two co-present exact numerical state paths meet one addressed capability edge; one stage completion is one regional event",
        action_boundary: "the world enacts a primitive only when public regional radiation carries a cross-event folded path; no executor touched-set is read",
        numerical_faces,
        training,
        held_out,
        no_region_control,
        reversed_hand,
        acceptance,
    };
    let mut bytes = serde_json::to_vec_pretty(&report)
        .map_err(|error| format!("report does not encode: {error}"))?;
    bytes.push(b'\n');
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&output)
        .map_err(|error| format!("{} opens as a new report: {error}", output.display()))?;
    file.write_all(&bytes)
        .map_err(|error| format!("{} writes completely: {error}", output.display()))?;
    file.sync_all()
        .map_err(|error| format!("{} syncs completely: {error}", output.display()))?;
    eprintln!(
        "eros exact growing calculator: {} · {} bytes · {}",
        report.status,
        bytes.len(),
        output.display()
    );
    Ok(())
}

fn train() -> Result<(TrainingRead, CalculatorCheckpoint, CalculatorCheckpoint), String> {
    let mut taught = CalculatorWorld::new()?;
    let mut no_region = CalculatorWorld::new()?;
    let mut states = TRAINING_INPUTS;
    let mut stages = Vec::new();
    for stage in 0..=DIVISION_STAGES {
        let inputs = states;
        let taught_radiation =
            taught.present_capability(states, stage, IncidenceHand::Against, true)?;
        let control_radiation =
            no_region.present_capability(states, stage, IncidenceHand::Against, false)?;
        let mut divisions = Vec::new();
        if stage < DIVISION_STAGES {
            for state in &mut states {
                let before = *state;
                let (quotient, remainder, after) = before.divide()?;
                divisions.push(EuclideanDivision {
                    stage,
                    before,
                    quotient,
                    remainder,
                    after,
                });
                *state = after;
            }
        } else if states.iter().any(|state| state.b != 0) {
            return Err(
                "both fixed demonstrations must terminate at the declared stage".to_owned(),
            );
        }
        stages.push(TrainingStageRead {
            stage,
            capability: capability_name(stage),
            inputs,
            divisions,
            taught_region: radiation_region(&taught_radiation)?,
            ordinary_current_radiation_exact: taught_radiation.currents()
                == control_radiation.currents(),
            directed_radiation_exact: taught_radiation.relations() == control_radiation.relations(),
        });
    }
    let returned_gcd = states[0].a;
    let returned_ratio = ExactRatio::new(
        (TRAINING_INPUTS[1].a / states[1].a) as i128,
        (TRAINING_INPUTS[1].b / states[1].a) as u128,
    )?;
    taught.present_result(returned_gcd, returned_ratio)?;
    no_region.present_result(returned_gcd, returned_ratio)?;
    let taught_checkpoint = taught.checkpoint()?;
    let no_region_checkpoint = no_region.checkpoint()?;
    let training = TrainingRead {
        examples: TRAINING_INPUTS,
        stages,
        returned_gcd,
        returned_ratio,
        taught_checkpoint_sha256: checkpoint_sha256(&taught_checkpoint)?,
        no_region_checkpoint_sha256: checkpoint_sha256(&no_region_checkpoint)?,
        rest_remount_exact: false,
    };
    Ok((training, taught_checkpoint, no_region_checkpoint))
}

fn execute(
    source: &'static str,
    world: &mut CalculatorWorld,
    input: Pair,
    hand: IncidenceHand,
) -> Result<ExecutionRead, String> {
    let before_sha256 = checkpoint_sha256(&world.checkpoint()?)?;
    let mut state = input;
    let mut stages = Vec::new();
    let mut completed = false;
    let mut gcd = None;
    let mut reduced_ratio = None;
    let mut returned = false;
    let mut stop_reason = String::new();
    for stage in 0..=DIVISION_STAGES {
        let radiation = world.present_capability([state, state], stage, hand, true)?;
        let region = radiation_region(&radiation)?;
        if !region.acquired_path_conducted {
            stop_reason = format!(
                "stage {stage} emitted no cross-event folded path; no world primitive was enacted"
            );
            stages.push(ExecutionStageRead {
                stage,
                capability: capability_name(stage),
                input: state,
                region,
                division: None,
            });
            break;
        }
        if stage < DIVISION_STAGES {
            let before = state;
            let (quotient, remainder, after) = before.divide()?;
            let division = EuclideanDivision {
                stage,
                before,
                quotient,
                remainder,
                after,
            };
            state = after;
            stages.push(ExecutionStageRead {
                stage,
                capability: capability_name(stage),
                input: before,
                region,
                division: Some(division),
            });
            continue;
        }
        if state.b != 0 {
            stop_reason =
                "RETURN was afforded before the exact Euclidean boundary closed".to_owned();
            stages.push(ExecutionStageRead {
                stage,
                capability: capability_name(stage),
                input: state,
                region,
                division: None,
            });
            break;
        }
        let found_gcd = state.a;
        let reduced =
            ExactRatio::new((input.a / found_gcd) as i128, (input.b / found_gcd) as u128)?;
        world.present_result(found_gcd, reduced)?;
        completed = true;
        gcd = Some(found_gcd);
        reduced_ratio = Some(reduced);
        returned = true;
        stop_reason = "the exact result returned as a genuinely later world current".to_owned();
        stages.push(ExecutionStageRead {
            stage,
            capability: capability_name(stage),
            input: state,
            region,
            division: None,
        });
        break;
    }
    let after_sha256 = checkpoint_sha256(&world.checkpoint()?)?;
    Ok(ExecutionRead {
        source,
        input,
        stages,
        completed,
        gcd,
        reduced_ratio,
        result_returned_as_later_current: returned,
        before_sha256,
        after_sha256,
        stop_reason,
    })
}

fn radiation_region(radiation: &ContemporaryRadiation) -> Result<RegionalRead, String> {
    let region = radiation.regional().first().ok_or_else(|| {
        "the declared capability event returned no regional constituent".to_owned()
    })?;
    regional_read(region.constituent())
}

fn regional_read(constituent: &LiveConstituent) -> Result<RegionalRead, String> {
    let mut paths = 0usize;
    let mut folded_paths = 0usize;
    let mut transport_terms = 0usize;
    let mut open_boundaries = 0usize;
    let mut ride_boundaries = 0usize;
    let mut found_boundaries = 0usize;
    for (at, boundary) in constituent.boundaries().iter().enumerate() {
        match constituent.boundary_transition(at) {
            Some(LiveBoundaryTransition::Open) => open_boundaries += 1,
            Some(LiveBoundaryTransition::Ride) => ride_boundaries += 1,
            Some(LiveBoundaryTransition::Found) => found_boundaries += 1,
            None => {}
        }
        paths += boundary.paths().len();
        for path in boundary.paths() {
            folded_paths += usize::from(path.interior_folded());
            transport_terms += path.transport().terms().len();
        }
    }
    let words = constituent.native_words().map_err(debug)?;
    Ok(RegionalRead {
        grain: constituent.grain(),
        axes: constituent.axis_count(),
        cells: constituent.cells().len(),
        incidences: constituent.incidences().len(),
        pins: constituent.pins().len(),
        boundaries: constituent.boundaries().len(),
        paths,
        folded_paths,
        transport_terms,
        exposed_pins: constituent.exposed().len(),
        open_boundaries,
        ride_boundaries,
        found_boundaries,
        native_sha256: words_sha256(&words),
        acquired_path_conducted: folded_paths != 0,
    })
}

fn numerical_faces() -> Result<NumericFaceRead, String> {
    let binary32_word = 0x3dcc_cccdu32;
    let exact = decode_binary32(binary32_word)?;
    let candidate = limit_denominator(exact, 10)?;
    let stored_minus_candidate = exact.subtract(candidate)?;
    let (continued_fraction_quotients, _) = continued_fraction(exact)?;
    let bfloat16_word = 0x3dcdu16;
    Ok(NumericFaceRead {
        binary32_word: format!("0x{binary32_word:08x}"),
        binary32_exact_dyadic: exact,
        bounded_candidate: candidate,
        bounded_candidate_denominator_limit: 10,
        candidate_rounds_to_binary32_word: round_ratio_to_binary32(candidate)? == binary32_word,
        stored_minus_candidate,
        continued_fraction_quotients,
        bfloat16_word: format!("0x{bfloat16_word:04x}"),
        bfloat16_exact_dyadic: decode_bfloat16(bfloat16_word)?,
    })
}

fn decode_binary32(word: u32) -> Result<ExactRatio, String> {
    let sign = word >> 31;
    let exponent = (word >> 23) & 0xff;
    let fraction = word & 0x7f_ffff;
    if exponent == 0xff {
        return Err("infinity and NaN are not exact ratio species".to_owned());
    }
    let (coefficient, power) = if exponent == 0 {
        (fraction as u128, -149)
    } else {
        (((1u32 << 23) | fraction) as u128, exponent as i32 - 150)
    };
    signed_power_two_ratio(sign != 0, coefficient, power)
}

fn decode_bfloat16(word: u16) -> Result<ExactRatio, String> {
    let sign = word >> 15;
    let exponent = (word >> 7) & 0xff;
    let fraction = word & 0x7f;
    if exponent == 0xff {
        return Err("infinity and NaN are not exact ratio species".to_owned());
    }
    let (coefficient, power) = if exponent == 0 {
        (fraction as u128, -133)
    } else {
        (((1u16 << 7) | fraction) as u128, exponent as i32 - 134)
    };
    signed_power_two_ratio(sign != 0, coefficient, power)
}

fn signed_power_two_ratio(
    negative: bool,
    coefficient: u128,
    power: i32,
) -> Result<ExactRatio, String> {
    if coefficient == 0 {
        return ExactRatio::new(0, 1);
    }
    let (numerator, denominator) = if power >= 0 {
        (
            coefficient
                .checked_shl(power as u32)
                .ok_or_else(|| "dyadic numerator exceeded u128".to_owned())?,
            1,
        )
    } else {
        (
            coefficient,
            1u128
                .checked_shl((-power) as u32)
                .ok_or_else(|| "dyadic denominator exceeded u128".to_owned())?,
        )
    };
    let signed = if negative {
        -(numerator as i128)
    } else {
        numerator as i128
    };
    ExactRatio::new(signed, denominator)
}

fn continued_fraction(value: ExactRatio) -> Result<(Vec<u128>, ExactRatio), String> {
    if value.numerator <= 0 {
        return Err("the bounded continued-fraction control expects a positive ratio".to_owned());
    }
    let mut numerator = value.numerator as u128;
    let mut denominator = value.denominator;
    let mut quotients = Vec::new();
    while denominator != 0 {
        let quotient = numerator / denominator;
        quotients.push(quotient);
        let remainder = numerator % denominator;
        numerator = denominator;
        denominator = remainder;
    }
    Ok((quotients, value))
}

fn limit_denominator(value: ExactRatio, maximum: u64) -> Result<ExactRatio, String> {
    if value.numerator <= 0 || maximum == 0 {
        return Err("bounded rational reconstruction expects positive input and bound".to_owned());
    }
    let original_numerator = value.numerator as u128;
    let original_denominator = value.denominator;
    let mut numerator = original_numerator;
    let mut denominator = original_denominator;
    let (mut p0, mut q0, mut p1, mut q1) = (0u128, 1u128, 1u128, 0u128);
    loop {
        let quotient = numerator / denominator;
        let q2 = q0
            .checked_add(
                quotient
                    .checked_mul(q1)
                    .ok_or_else(|| "continued-fraction denominator overflowed".to_owned())?,
            )
            .ok_or_else(|| "continued-fraction denominator overflowed".to_owned())?;
        if q2 > maximum as u128 {
            break;
        }
        let p2 = p0
            .checked_add(
                quotient
                    .checked_mul(p1)
                    .ok_or_else(|| "continued-fraction numerator overflowed".to_owned())?,
            )
            .ok_or_else(|| "continued-fraction numerator overflowed".to_owned())?;
        (p0, q0, p1, q1) = (p1, q1, p2, q2);
        let remainder = numerator - quotient * denominator;
        if remainder == 0 {
            return ExactRatio::new(p1 as i128, q1);
        }
        numerator = denominator;
        denominator = remainder;
    }
    let k = (maximum as u128 - q0) / q1;
    let bound_one = ExactRatio::new((p0 + k * p1) as i128, q0 + k * q1)?;
    let bound_two = ExactRatio::new(p1 as i128, q1)?;
    if rational_distance_le(
        bound_two,
        bound_one,
        original_numerator,
        original_denominator,
    )? {
        Ok(bound_two)
    } else {
        Ok(bound_one)
    }
}

fn rational_distance_le(
    left: ExactRatio,
    right: ExactRatio,
    target_numerator: u128,
    target_denominator: u128,
) -> Result<bool, String> {
    let distance = |candidate: ExactRatio| -> Result<(u128, u128), String> {
        let candidate_numerator = candidate.numerator as u128;
        let left = candidate_numerator
            .checked_mul(target_denominator)
            .ok_or_else(|| "distance numerator overflowed".to_owned())?;
        let right = target_numerator
            .checked_mul(candidate.denominator)
            .ok_or_else(|| "distance numerator overflowed".to_owned())?;
        let numerator = left.abs_diff(right);
        let denominator = candidate
            .denominator
            .checked_mul(target_denominator)
            .ok_or_else(|| "distance denominator overflowed".to_owned())?;
        Ok((numerator, denominator))
    };
    let (left_numerator, left_denominator) = distance(left)?;
    let (right_numerator, right_denominator) = distance(right)?;
    Ok(left_numerator
        .checked_mul(right_denominator)
        .ok_or_else(|| "distance comparison overflowed".to_owned())?
        <= right_numerator
            .checked_mul(left_denominator)
            .ok_or_else(|| "distance comparison overflowed".to_owned())?)
}

fn round_ratio_to_binary32(value: ExactRatio) -> Result<u32, String> {
    if value.numerator <= 0 {
        return Err("the fixed binary32 rounding control expects a positive ratio".to_owned());
    }
    let numerator = value.numerator as u128;
    let denominator = value.denominator;
    let mut power = numerator.bit_length() as i32 - denominator.bit_length() as i32;
    if compare_ratio_to_power_two(numerator, denominator, power) < 0 {
        power -= 1;
    }
    while compare_ratio_to_power_two(numerator, denominator, power + 1) >= 0 {
        power += 1;
    }
    if power < -126 {
        let fraction = round_scaled_ratio(numerator, denominator, 149)?;
        if fraction >= 1 << 23 {
            return Ok(1 << 23);
        }
        return Ok(fraction as u32);
    }
    let mut significand = round_scaled_ratio(numerator, denominator, 23 - power)?;
    let mut normalized_power = power;
    if significand == 1 << 24 {
        significand >>= 1;
        normalized_power += 1;
    }
    let exponent = normalized_power + 127;
    if exponent >= 255 {
        return Ok(0x7f80_0000);
    }
    Ok(((exponent as u32) << 23) | (significand as u32 - (1 << 23)))
}

fn compare_ratio_to_power_two(numerator: u128, denominator: u128, power: i32) -> i8 {
    let (left, right) = if power >= 0 {
        (numerator, denominator.checked_shl(power as u32))
    } else {
        (
            numerator.checked_shl((-power) as u32).unwrap_or(u128::MAX),
            Some(denominator),
        )
    };
    match right {
        Some(right) => (left > right) as i8 - (left < right) as i8,
        None => -1,
    }
}

fn round_scaled_ratio(
    numerator: u128,
    denominator: u128,
    binary_shift: i32,
) -> Result<u128, String> {
    let (scaled_numerator, scaled_denominator) = if binary_shift >= 0 {
        (
            numerator
                .checked_shl(binary_shift as u32)
                .ok_or_else(|| "rounding numerator exceeded u128".to_owned())?,
            denominator,
        )
    } else {
        (
            numerator,
            denominator
                .checked_shl((-binary_shift) as u32)
                .ok_or_else(|| "rounding denominator exceeded u128".to_owned())?,
        )
    };
    let (mut quotient, remainder) = div_rem_u128(scaled_numerator, scaled_denominator);
    let doubled = remainder
        .checked_mul(2)
        .ok_or_else(|| "rounding remainder exceeded u128".to_owned())?;
    if doubled > scaled_denominator || (doubled == scaled_denominator && quotient & 1 != 0) {
        quotient += 1;
    }
    Ok(quotient)
}

fn state_atoms(objective: i64, state: Pair, lane: u64) -> Result<[RelationAtom; 3], String> {
    Ok([
        atom(objective)?,
        encoded_atom(state.a, lane * 2 + 1)?,
        encoded_atom(state.b, lane * 2 + 2)?,
    ])
}

fn encoded_atom(value: u64, lane: u64) -> Result<RelationAtom, String> {
    let encoded = value
        .checked_mul(16)
        .and_then(|value| value.checked_add(lane))
        .and_then(|value| i64::try_from(value).ok())
        .ok_or_else(|| "the fixed source atom exceeded i64".to_owned())?;
    atom(encoded)
}

fn atom(value: i64) -> Result<RelationAtom, String> {
    RelationAtom::new(Cog::lit(value)).ok_or_else(|| "a source atom cannot be zero".to_owned())
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving calculator action")
}

fn capability_name(stage: u32) -> &'static str {
    if stage < DIVISION_STAGES {
        "DIVMOD_REBASE"
    } else {
        "RETURN"
    }
}

fn checkpoint_bytes(checkpoint: &CalculatorCheckpoint) -> Result<Vec<u8>, String> {
    let machine = checkpoint.machine.encode_native_bytes().map_err(debug)?;
    // THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*. The checkpoint hash below is
    // untouched. The machine half is a canonical `ERST` form and reaches the plate's mouth here;
    // the four organ wires are deposited beside it under their own names rather than only inside a
    // concatenation, because a form no reader holds is still a form and the falsifier reports it.
    let deposited = deposit_form_or_message(FORM_DRIVER, CHECKPOINT_MACHINE_FORM, &machine)?;
    eprintln!("form deposited: {}", deposited.path.display());
    let mut bytes = Vec::with_capacity(machine.len() + 4 * 20);
    bytes.extend_from_slice(&machine);
    for (name, organ) in [
        (GCD_STATE_FORM, checkpoint.gcd_state),
        (RATIO_STATE_FORM, checkpoint.ratio_state),
        (CONTEXT_FORM, checkpoint.context),
        (ARRIVAL_FORM, checkpoint.arrival),
    ] {
        let organ_octets = organ.encode_native_bytes();
        let deposited = deposit_form_or_message(FORM_DRIVER, name, &organ_octets)?;
        eprintln!("form deposited: {}", deposited.path.display());
        bytes.extend_from_slice(&organ_octets);
    }
    Ok(bytes)
}

fn checkpoint_sha256(checkpoint: &CalculatorCheckpoint) -> Result<String, String> {
    Ok(sha256(&checkpoint_bytes(checkpoint)?))
}

fn words_sha256(words: &[u32]) -> String {
    let mut hash = Sha256::new();
    for word in words {
        hash.update(word.to_le_bytes());
    }
    encode_digest(hash.finalize())
}

fn sha256(bytes: &[u8]) -> String {
    encode_digest(Sha256::digest(bytes))
}

fn encode_digest(digest: impl IntoIterator<Item = u8>) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(64);
    for byte in digest {
        encoded.push(HEX[(byte >> 4) as usize] as char);
        encoded.push(HEX[(byte & 0x0f) as usize] as char);
    }
    encoded
}

fn gcd_u128(mut left: u128, mut right: u128) -> u128 {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left
}

fn div_rem_u128(left: u128, right: u128) -> (u128, u128) {
    (left / right, left % right)
}

trait BitLength {
    fn bit_length(self) -> u32;
}

impl BitLength for u128 {
    fn bit_length(self) -> u32 {
        u128::BITS - self.leading_zeros()
    }
}

fn deed_name(deed: FeltDeed) -> &'static str {
    match deed {
        FeltDeed::Ride => "RIDE",
        FeltDeed::FoundThis => "FOUND_THIS",
        FeltDeed::FoundThat => "FOUND_THAT",
        FeltDeed::Dark => "DARK",
    }
}

fn debug(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}

#[allow(dead_code)]
fn _retain_deed_vocabulary(deed: FeltDeed) -> &'static str {
    deed_name(deed)
}

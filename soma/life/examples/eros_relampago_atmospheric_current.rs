//! Recurrent RELAMPAGO generation through the typed exact/live-current organ over native GLM,
//! ABI, and IGRA data.
//!
//! The first ten minutes condition the production GLM relation.  The next ten
//! minutes enter as five successive two-minute occurrence ecologies.  Before
//! each native GLM group return, the generated optical relation is coupled to
//! five native ABI infrared/water-vapor sections and one independently
//! received vertical atmospheric profile.  The complete later return first
//! grades both generated relations, then changes the intermediate morphology
//! which conducts the following interval.  The run therefore measures
//! generation, structured obstruction, return, and recurrent conditioning on
//! one real storm chronology rather than one monolithic held-out batch.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs::{self, File};
use std::io::{BufRead, BufReader, BufWriter, Read, Write};
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use holonic_engine::{
    exact_rational_from_f32_bits, AtmosphericInverseEvent, AtmosphericInverseLaw,
    AtmosphericInverseResolution, AtmosphericInverseStanding, AtmosphericObstructionKind,
    AtmosphericProfile, AtmosphericProfileId, AtmosphericProfileLevel,
    AtmosphericVerticalCoordinate, AtmosphericVerticalFiber, CausalBodyDeed, CausalBodyEvent,
    CausalBodyRadiation, CausalBodyStanding, CausalCellId, CausalCellReference, CausalOpeningState,
    CausalWorld, ComparativeMultiplicity, CoupledInformantEvent, CoupledInformantGrade,
    CoupledInformantLaw, CoupledInformantPrediction, CoupledInformantRelationState,
    CoupledInformantStanding, CoupledInformantWork, CoupledPhaseBranch, CoupledRelationOrigin,
    CpuExecutionError, CpuExecutionReceipt, CpuExecutor, EventBoundaryTerm, EventCellId, EventId,
    ExactCausalBodyLaw, ExactCoordinateInterval, ExactInterval, ObservationEcologyEvent,
    ObservationEcologyLaw, ObservationEcologyStanding, ObservationEcologyWork,
    OpaqueThermalChordDoctrine, ReceiverAffineChart, ReceiverBatch, ReceiverChartId,
    ReceiverCoordinateFamily, ReceiverCoordinateFamilyId, ReceiverGradeId, ReceiverLineageId,
    ReceiverRelationGrade, ReceiverRelationPrediction, ReceiverRelationState, ReceiverTestimony,
    ReceiverTestimonyId, ReturnedAlgorithmId, ReturnedCellCoverage, ReturnedCellId,
    ReturnedReceiverCell, ReturnedReceiverPartition, SpectralAddressStatus, SpectralBandId,
    SpectralContactTemporality, SpectralReceiverContact, SpectralReceiverOccurrence,
    SpectralScanId, TransitionReceipt, VerticalFiberSupport,
};
use life::coupled_informant_current::CoupledInformantCurrentAdapter;
use life::exact_world::ExactWorldOrgan;
use life::form_mouth::deposit_form;
use life::live_current_cuda::CudaLiveCurrentExecutor;
use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};
use relational_geometry::{Rat, ReceiverId};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use soma_membrane::{
    ContemporaryRadiation, HostLiveCurrentExecutor, LiveCurrentExecutor, LiveCurrentMachine,
    LiveCurrentRestImage, SparseStandingSurface,
};

/// This driver's name at the plate mouth: `output/eros_relampago_atmospheric_current/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_relampago_atmospheric_current";
/// The live-current rest this driver seals. `ERST` is the schema `holon-plate` holds for it. This
/// driver already wrote these octets to a caller-supplied directory as `coupled-live-current.bin`;
/// that write stays, and this one puts the same octets at the declared mouth path where a plate
/// deposit finds them without being told where the driver's run directory was.
const COUPLED_LIVE_CURRENT_FORM: &str = "coupled-live-current";

const GLM_FAMILY: ReceiverCoordinateFamilyId = ReceiverCoordinateFamilyId(0x0047_4c4d);
const GLM_GROUP_ALGORITHM: ReturnedAlgorithmId = ReturnedAlgorithmId(0x0047_4c4d_4752_4f55);
const GLM_RECEIVER: ReceiverId = ReceiverId(16);
const ABI_RECEIVER: ReceiverId = ReceiverId(19);
const IGRA_RECEIVER: ReceiverId = ReceiverId(20);

const DEFAULT_MANIFEST: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../../data/relampago-lightning/manifests/glm_relampago_full_window.keys"
);
const DEFAULT_GLM_RAW: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../../data/relampago-lightning/raw/glm"
);
const DEFAULT_ABI_RAW: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../../data/relampago-lightning/raw/abi"
);
const DEFAULT_IGRA: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../../data/relampago-lightning/raw/igra/ARM00087344-data.txt.zip"
);
const DEFAULT_OUTPUT: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../../output/relampago-lightning/coupled-informant-generation"
);
const IGRA_PROFILE_SOURCE: &str =
    "NOAA NCEI IGRA v2 station ARM00087344 native profile 2018-12-14 00Z";
const HELD_OUT_EPISODES: usize = 5;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Split {
    Training,
    HeldOut,
    Outside,
}

#[derive(Clone, Debug)]
struct ProductTime {
    year: u32,
    day: u32,
    hour: u32,
    minute: u32,
    second: u32,
    tenth: u32,
}

impl ProductTime {
    fn split(&self) -> Split {
        match (self.year, self.day, self.hour, self.minute) {
            (2018, 347, 22, 50..=59) => Split::Training,
            (2018, 347, 23, 0..=9) => Split::HeldOut,
            _ => Split::Outside,
        }
    }

    fn seconds_from_training_day(&self) -> Rat {
        let day = i64::from(self.day) - 347;
        let whole = day * 86_400
            + i64::from(self.hour) * 3_600
            + i64::from(self.minute) * 60
            + i64::from(self.second);
        Rat::new(
            BigInt::from(whole * 10 + i64::from(self.tenth)),
            BigInt::from(10),
        )
    }

    fn held_out_episode(&self) -> Option<usize> {
        match (self.year, self.day, self.hour, self.minute) {
            (2018, 347, 23, 0..=9) => Some(usize::try_from(self.minute / 2).ok()?),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
struct ProductRequest {
    key: String,
    time: ProductTime,
    chart: ReceiverChartId,
    path: PathBuf,
}

#[derive(Clone, Debug)]
struct LoadedProduct {
    split: Split,
    held_out_episode: Option<usize>,
    chart: ReceiverAffineChart,
    occurrences: Vec<ReceiverTestimony>,
    cells: BTreeMap<ReturnedCellId, BTreeSet<ReceiverTestimonyId>>,
    total_events: usize,
}

#[derive(Clone, Debug)]
struct ReceivedOccurrence {
    testimony: ReceiverTestimony,
    latitude: Rat,
    longitude: Rat,
    clock: Rat,
    energy: Rat,
}

#[derive(Clone, Debug, Default)]
struct EpisodeSource {
    occurrences: Vec<ReceivedOccurrence>,
    cells: BTreeMap<ReturnedCellId, BTreeSet<ReceiverTestimonyId>>,
}

#[derive(Clone)]
struct EpisodeResult {
    ordinal: usize,
    occurrences: Vec<ReceivedOccurrence>,
    optical_prediction: std::sync::Arc<ReceiverRelationPrediction>,
    optical_grade: std::sync::Arc<ReceiverRelationGrade>,
    atmospheric_resolution: std::sync::Arc<AtmosphericInverseResolution>,
    coupled_prediction: std::sync::Arc<CoupledInformantPrediction>,
    unconditioned_control_prediction: std::sync::Arc<CoupledInformantPrediction>,
    coupled_grade: std::sync::Arc<CoupledInformantGrade>,
    optical_prediction_work: ObservationEcologyWork,
    optical_grade_work: ObservationEcologyWork,
    coupled_generation_work: CoupledInformantWork,
    prediction_ms: u128,
    inverse_ms: u128,
    coupled_ms: u128,
    generation_current: LiveCrossingReceipt,
    grade_current: LiveCrossingReceipt,
    admission_current: LiveCrossingReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct CausalBodyRelationCell {
    relation_ordinal: usize,
    branch_ordinal: usize,
    state: CoupledInformantRelationState,
    cell: CausalCellId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct CausalBodyEpisodeReceipt {
    episode: usize,
    source_event: EventId,
    chronology: u64,
    fiber_cells: Vec<CausalCellId>,
    relation_cells: Vec<CausalBodyRelationCell>,
    transition: TransitionReceipt<CausalBodyRadiation>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct RelampagoCausalRelationSection {
    members: [ReceiverTestimonyId; 2],
    origin: CoupledRelationOrigin,
    base_state: ReceiverRelationState,
    branch: CoupledPhaseBranch,
    generated_state: CoupledInformantRelationState,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct RelampagoCausalBodyResearch {
    standing: CausalBodyStanding,
    next_ordinal: u64,
    episodes: Vec<CausalBodyEpisodeReceipt>,
    vertical_sections: BTreeMap<CausalCellId, AtmosphericVerticalFiber>,
    relation_sections: BTreeMap<CausalCellId, RelampagoCausalRelationSection>,
}

#[derive(Clone, Copy)]
struct LiveCrossingReceipt {
    before_rank: u64,
    after_rank: u64,
    before_cells: usize,
    after_cells: usize,
    currents: usize,
    directed_relations: usize,
}

impl From<&ContemporaryRadiation> for LiveCrossingReceipt {
    fn from(radiation: &ContemporaryRadiation) -> Self {
        Self {
            before_rank: radiation.before_rank(),
            after_rank: radiation.after_rank(),
            before_cells: radiation.before_cells(),
            after_cells: radiation.after_cells(),
            currents: radiation.currents().len(),
            directed_relations: radiation.relations().len(),
        }
    }
}

#[derive(Clone, Debug)]
struct PackedAxis {
    raw: Vec<i64>,
    offset: Rat,
    scale: Rat,
}

#[derive(Clone, Debug)]
struct NativeGlmDump {
    latitude: PackedAxis,
    longitude: PackedAxis,
    time: PackedAxis,
    energy: PackedAxis,
    event_ids: Vec<u64>,
    parent_groups: Vec<u64>,
}

fn main() -> Result<(), Box<dyn Error>> {
    let arguments = std::env::args().skip(1).collect::<Vec<_>>();
    let manifest = PathBuf::from(
        arguments
            .first()
            .map(String::as_str)
            .unwrap_or(DEFAULT_MANIFEST),
    );
    let glm_raw = PathBuf::from(
        arguments
            .get(1)
            .map(String::as_str)
            .unwrap_or(DEFAULT_GLM_RAW),
    );
    let abi_raw = PathBuf::from(
        arguments
            .get(2)
            .map(String::as_str)
            .unwrap_or(DEFAULT_ABI_RAW),
    );
    let igra = PathBuf::from(arguments.get(3).map(String::as_str).unwrap_or(DEFAULT_IGRA));
    let output = PathBuf::from(
        arguments
            .get(4)
            .map(String::as_str)
            .unwrap_or(DEFAULT_OUTPUT),
    );
    fs::create_dir_all(&output)?;

    let workers = std::thread::available_parallelism()
        .unwrap_or_else(|_| NonZeroUsize::new(1).expect("one is nonzero"));
    let aperture = relampago_aperture();
    let family = ReceiverCoordinateFamily::new(
        GLM_FAMILY,
        vec![
            "reported latitude".to_owned(),
            "reported longitude".to_owned(),
            "receiver clock".to_owned(),
            "reported radiant energy".to_owned(),
            "receiver product aperture".to_owned(),
        ],
        vec![0, 1, 2, 3],
        vec![4],
    )?;
    let mut observation_world = CausalWorld::new(
        ObservationEcologyLaw::multicore_cuda(workers),
        ObservationEcologyStanding::default(),
    );
    let mut observation_event = 1_u64;
    observation_world.receive(&ObservationEcologyEvent::DeclareFamily {
        event: take_event(&mut observation_event),
        family,
    })?;

    let acquisition_started = Instant::now();
    let requests = read_manifest(&manifest)?
        .into_iter()
        .enumerate()
        .filter_map(|(ordinal, key)| {
            let time = parse_product_time(&key).ok()?;
            (time.split() != Split::Outside).then_some((ordinal, key, time))
        })
        .map(|(ordinal, key, time)| {
            let chart = ReceiverChartId(
                u64::try_from(ordinal)?
                    .checked_add(1)
                    .ok_or("chart carrier overflow")?,
            );
            let filename = Path::new(&key)
                .file_name()
                .ok_or("manifest key has no filename")?
                .to_owned();
            Ok(ProductRequest {
                key,
                time,
                chart,
                path: glm_raw.join(filename),
            })
        })
        .collect::<Result<Vec<_>, Box<dyn Error>>>()?;
    let loader = CpuExecutor::multicore(workers);
    let (loaded, loader_receipt) = loader
        .execute_indexed(&requests, |_index, request| {
            load_glm_product(
                &request.key,
                &request.path,
                request.chart,
                &request.time,
                &aperture,
            )
            .map_err(|error| error.to_string())
        })
        .map_err(|error| match error {
            CpuExecutionError::Operation(error) => error,
            CpuExecutionError::WorkerPanicked => "one GLM import worker panicked".to_owned(),
        })?;

    let mut next_testimony = 1_u64;
    let mut training_occurrences = Vec::new();
    let mut training_cells = BTreeMap::new();
    let mut episode_sources = vec![EpisodeSource::default(); HELD_OUT_EPISODES];
    let mut total_native_events = 0_usize;
    for mut product in loaded {
        rebase_product(&mut product, &mut next_testimony)?;
        let chart = product.chart.clone();
        observation_world.receive(&ObservationEcologyEvent::DeclareChart {
            event: take_event(&mut observation_event),
            chart: chart.clone(),
        })?;
        total_native_events = total_native_events
            .checked_add(product.total_events)
            .ok_or("native event count overflow")?;
        let mut received = product
            .occurrences
            .iter()
            .map(|testimony| {
                let coordinates = chart.receive(&testimony.raw)?;
                Ok(ReceivedOccurrence {
                    testimony: testimony.clone(),
                    latitude: coordinates[0].clone(),
                    longitude: coordinates[1].clone(),
                    clock: coordinates[2].clone(),
                    energy: coordinates[3].clone(),
                })
            })
            .collect::<Result<Vec<_>, holonic_engine::ObservationEcologyError>>()?;
        match product.split {
            Split::Training => {
                training_occurrences.append(&mut received);
                merge_cells(&mut training_cells, product.cells);
            }
            Split::HeldOut => {
                let episode = product
                    .held_out_episode
                    .ok_or("held-out product has no causal episode")?;
                let target = episode_sources
                    .get_mut(episode)
                    .ok_or("held-out product episode exceeds the declared chronology")?;
                target.occurrences.append(&mut received);
                merge_cells(&mut target.cells, product.cells);
            }
            Split::Outside => unreachable!("outside products were filtered"),
        }
    }
    let acquisition_elapsed = acquisition_started.elapsed();
    if episode_sources
        .iter()
        .any(|episode| episode.occurrences.is_empty())
    {
        return Err("one declared held-out causal episode is empty".into());
    }
    let held_out_occurrences = episode_sources
        .iter()
        .flat_map(|episode| episode.occurrences.iter().cloned())
        .collect::<Vec<_>>();

    let training_batch = ReceiverBatch {
        family: GLM_FAMILY,
        chronology: 0,
        source: "GOES-16 GLM L2 LCFA 2018-12-13 22:50--23:00 UTC".to_owned(),
        aperture: aperture.clone(),
        occurrences: training_occurrences
            .iter()
            .map(|occurrence| occurrence.testimony.clone())
            .collect(),
    };
    let training_receipt =
        observation_world.receive(&ObservationEcologyEvent::ConditionReturnedBatch {
            event: take_event(&mut observation_event),
            batch: training_batch,
            returned: partition(GLM_GROUP_ALGORITHM, training_cells),
        })?;

    // The transducer retains both ABI scans and every native band for every
    // later occurrence.  Loading once is administrative reuse; each episode
    // still selects contacts by its own receiver clock.
    let abi_started = Instant::now();
    let contacts = load_abi_contacts(&abi_raw, &held_out_occurrences, workers)?;
    let abi_elapsed = abi_started.elapsed();
    let profile = load_igra_profile(&igra)?;
    let doctrine = OpaqueThermalChordDoctrine {
        thermal_band: SpectralBandId(13),
        specific_gas_constant: Rat::new(BigInt::from(28_705), BigInt::from(100)),
        logarithm_terms: 24,
    };
    let mut inverse_world = CausalWorld::new(
        AtmosphericInverseLaw::multicore(workers),
        AtmosphericInverseStanding::default(),
    );
    let mut inverse_event = 1_u64;
    inverse_world.receive(&AtmosphericInverseEvent::ReceiveProfile {
        event: take_event(&mut inverse_event),
        profile: Box::new(profile.clone()),
    })?;
    let mut coupled_world = ExactWorldOrgan::new(
        CausalWorld::new(
            CoupledInformantLaw::multicore(workers),
            CoupledInformantStanding::default(),
        ),
        CoupledInformantCurrentAdapter::new(),
    );
    let mut coupled_machine = LiveCurrentMachine::new(
        SparseStandingSurface::empty_rank(8).map_err(|error| format!("{error:?}"))?,
    );
    let (mut coupled_executor, coupled_device): (Box<dyn LiveCurrentExecutor>, String) =
        if std::env::var_os("SOMA_RELAMPAGO_HOST").is_some() {
            (
                Box::new(HostLiveCurrentExecutor),
                "host exact reference".to_owned(),
            )
        } else {
            let cuda = CudaLiveCurrentExecutor::new(0).map_err(|error| format!("{error:?}"))?;
            let device = cuda.device_name().to_owned();
            (Box::new(cuda), device)
        };
    coupled_world.found(&mut coupled_machine)?;
    let mut coupled_event = 1_u64;
    let mut unconditioned_control_world = CausalWorld::new(
        CoupledInformantLaw::multicore(workers),
        CoupledInformantStanding::default(),
    );
    let mut unconditioned_control_event = 1_u64;
    let mut prior_optical_grade: Option<ReceiverGradeId> = None;
    let mut episode_results = Vec::with_capacity(HELD_OUT_EPISODES);

    for (ordinal, source) in episode_sources.into_iter().enumerate() {
        let lower_minute = ordinal * 2;
        let upper_minute = lower_minute + 2;
        let returned = partition(GLM_GROUP_ALGORITHM, source.cells);
        let batch = ReceiverBatch {
            family: GLM_FAMILY,
            chronology: u64::try_from(ordinal + 1)?,
            source: format!(
                "GOES-16 GLM L2 LCFA held-out 2018-12-13 23:{lower_minute:02}--23:{upper_minute:02} UTC"
            ),
            aperture: aperture.clone(),
            occurrences: source
                .occurrences
                .iter()
                .map(|occurrence| occurrence.testimony.clone())
                .collect(),
        };
        let prediction_started = Instant::now();
        let prediction_receipt =
            observation_world.receive(&ObservationEcologyEvent::PredictUnpartitionedBatch {
                event: take_event(&mut observation_event),
                algorithm: GLM_GROUP_ALGORITHM,
                batch,
            })?;
        let prediction_ms = prediction_started.elapsed().as_millis();
        let optical_prediction = prediction_receipt.radiation[0]
            .prediction
            .as_ref()
            .ok_or("GLM prediction event emitted no prediction")?
            .clone();
        let spectral_occurrences = source
            .occurrences
            .iter()
            .map(|occurrence| {
                Ok(SpectralReceiverOccurrence {
                    testimony: occurrence.testimony.id,
                    source_identity: occurrence.testimony.source_identity,
                    latitude_degree: occurrence.latitude.clone(),
                    longitude_degree: occurrence.longitude.clone(),
                    clock: occurrence.clock.clone(),
                    radiant_energy: occurrence.energy.clone(),
                    contacts: contacts
                        .get(&occurrence.testimony.id)
                        .cloned()
                        .ok_or("ABI contact transducer omitted a held-out occurrence")?,
                })
            })
            .collect::<Result<Vec<_>, Box<dyn Error>>>()?;

        let inverse_started = Instant::now();
        let inverse_receipt =
            inverse_world.receive(&AtmosphericInverseEvent::ResolvePrediction {
                event: take_event(&mut inverse_event),
                profile: profile.id,
                prediction: optical_prediction.clone(),
                occurrences: spectral_occurrences,
                doctrine: doctrine.clone(),
            })?;
        let inverse_ms = inverse_started.elapsed().as_millis();
        let atmospheric_resolution = inverse_receipt.radiation[0]
            .resolution
            .as_ref()
            .ok_or("atmospheric inverse emitted no resolution")?
            .clone();

        let coupled_standing_before = coupled_world.world().standing().clone();
        let coupled_generation_event = take_event(&mut coupled_event);
        let coupled_started = Instant::now();
        let (coupled_prediction_receipt, generation_current) = coupled_world
            .receive_into(
                &CoupledInformantEvent::Generate {
                    event: coupled_generation_event,
                    chronology: u64::try_from(ordinal + 1)?,
                    source_grade_precondition: prior_optical_grade,
                    resolution: atmospheric_resolution.clone(),
                },
                &mut coupled_machine,
                coupled_executor.as_mut(),
            )
            .map_err(|error| {
                format!(
                    "RELAMPAGO episode {} generation crossing failed: {error:?}",
                    ordinal + 1
                )
            })?;
        let coupled_ms = coupled_started.elapsed().as_millis();
        let coupled_prediction = coupled_prediction_receipt.radiation[0]
            .prediction
            .as_ref()
            .ok_or("coupled informant event emitted no prediction")?
            .clone();
        let mut delivery_control_world = CausalWorld::new(
            CoupledInformantLaw::multicore(workers),
            coupled_standing_before,
        );
        let delivery_control_receipt =
            delivery_control_world.receive(&CoupledInformantEvent::Generate {
                event: coupled_generation_event,
                chronology: u64::try_from(ordinal + 1)?,
                source_grade_precondition: prior_optical_grade,
                resolution: reverse_administrative_delivery(&atmospheric_resolution),
            })?;
        let delivery_control_prediction = delivery_control_receipt.radiation[0]
            .prediction
            .as_ref()
            .ok_or("delivery-order control emitted no prediction")?;
        if delivery_control_prediction.as_ref() != coupled_prediction.as_ref() {
            return Err(
                "reversing administrative source delivery changed the coupled prediction".into(),
            );
        }
        let unconditioned_control_receipt =
            unconditioned_control_world.receive(&CoupledInformantEvent::Generate {
                event: take_event(&mut unconditioned_control_event),
                chronology: u64::try_from(ordinal + 1)?,
                source_grade_precondition: prior_optical_grade,
                resolution: atmospheric_resolution.clone(),
            })?;
        let unconditioned_control_prediction = unconditioned_control_receipt.radiation[0]
            .prediction
            .as_ref()
            .ok_or("unconditioned control emitted no prediction")?
            .clone();
        if unconditioned_control_prediction
            .relations
            .iter()
            .any(|relation| {
                relation.state
                    != if relation.branches.is_empty() {
                        CoupledInformantRelationState::MissingSection
                    } else {
                        CoupledInformantRelationState::Open
                    }
            })
        {
            return Err("a no-return control acquired an uncaused coupled relation".into());
        }

        // The same native group partition now returns to two independently
        // generated receiver faces.  Neither face may condition standing
        // until both grades have been formed.
        let (coupled_grade_receipt, grade_current) = coupled_world
            .receive_into(
                &CoupledInformantEvent::GradeReturnedPartition {
                    event: take_event(&mut coupled_event),
                    prediction: coupled_prediction.id,
                    returned: returned.clone(),
                },
                &mut coupled_machine,
                coupled_executor.as_mut(),
            )
            .map_err(|error| {
                format!(
                    "RELAMPAGO episode {} grade crossing failed: {error:?}",
                    ordinal + 1
                )
            })?;
        let coupled_grade = coupled_grade_receipt.radiation[0]
            .grade
            .as_ref()
            .ok_or("coupled return emitted no grade")?
            .clone();
        let optical_grade_receipt =
            observation_world.receive(&ObservationEcologyEvent::GradeReturnedPartition {
                event: take_event(&mut observation_event),
                prediction: optical_prediction.id,
                returned: returned.clone(),
            })?;
        let optical_grade = optical_grade_receipt.radiation[0]
            .grade
            .as_ref()
            .ok_or("GLM return emitted no grade")?
            .clone();

        let (_, admission_current) = coupled_world
            .receive_into(
                &CoupledInformantEvent::AdmitGradedReturn {
                    event: take_event(&mut coupled_event),
                    grade: coupled_grade.id,
                },
                &mut coupled_machine,
                coupled_executor.as_mut(),
            )
            .map_err(|error| {
                format!(
                    "RELAMPAGO episode {} admission crossing failed: {error:?}",
                    ordinal + 1
                )
            })?;
        observation_world.receive(&ObservationEcologyEvent::AdmitGradedReturn {
            event: take_event(&mut observation_event),
            grade: optical_grade.id,
        })?;
        prior_optical_grade = Some(optical_grade.id);
        episode_results.push(EpisodeResult {
            ordinal,
            occurrences: source.occurrences,
            optical_prediction,
            optical_grade,
            atmospheric_resolution,
            coupled_prediction,
            unconditioned_control_prediction,
            coupled_grade,
            optical_prediction_work: prediction_receipt.radiation[0].work.clone(),
            optical_grade_work: optical_grade_receipt.radiation[0].work.clone(),
            coupled_generation_work: coupled_prediction_receipt.radiation[0].work.clone(),
            prediction_ms,
            inverse_ms,
            coupled_ms,
            generation_current: LiveCrossingReceipt::from(&generation_current),
            grade_current: LiveCrossingReceipt::from(&grade_current),
            admission_current: LiveCrossingReceipt::from(&admission_current),
        });
    }
    observation_world.standing().validate()?;
    inverse_world.standing().validate()?;
    coupled_world.world().standing().validate()?;
    unconditioned_control_world.standing().validate()?;

    let coupled_native = ron::ser::to_string(coupled_world.world().standing())?;
    let remounted: CoupledInformantStanding = ron::de::from_str(&coupled_native)?;
    remounted.validate()?;
    if &remounted != coupled_world.world().standing() {
        return Err("coupled standing changed across exact rest/remount".into());
    }
    fs::write(
        output.join("coupled-standing.ron"),
        coupled_native.as_bytes(),
    )?;
    fs::write(
        output.join("coupled-next-ordinal.bin"),
        coupled_world.world().next_ordinal().to_le_bytes(),
    )?;

    let live_image = coupled_machine
        .rest_image()
        .map_err(|error| format!("{error:?}"))?;
    let live_native = live_image
        .encode_native_bytes()
        .map_err(|error| format!("{error:?}"))?;
    fs::write(output.join("coupled-live-current.bin"), &live_native)?;
    // THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*.
    let deposited = deposit_form(FORM_DRIVER, COUPLED_LIVE_CURRENT_FORM, &live_native)?;
    eprintln!("form deposited: {}", deposited.path.display());
    let adapter_words = coupled_world.adapter().checkpoint().encode_native_words();
    let mut adapter_native = Vec::with_capacity(adapter_words.len() * 4);
    for word in adapter_words {
        adapter_native.extend_from_slice(&word.to_le_bytes());
    }
    fs::write(output.join("coupled-live-organs.bin"), &adapter_native)?;

    let remounted_live_image = LiveCurrentRestImage::from_native_bytes(&live_native)
        .map_err(|error| format!("{error:?}"))?;
    let remounted_machine = LiveCurrentMachine::from_rest_image(remounted_live_image)
        .map_err(|error| format!("{error:?}"))?;
    let remounted_adapter_image =
        life::coupled_informant_current::CoupledInformantCurrentAdapterImage::from_native_words(
            &adapter_words,
            &remounted_machine,
        )?;
    let remounted_adapter =
        CoupledInformantCurrentAdapter::recover(remounted_adapter_image, &remounted_machine)?;
    let remounted_world = CausalWorld::from_rest(
        CoupledInformantLaw::multicore(workers),
        remounted,
        coupled_world.world().next_ordinal(),
    )?;
    let remounted_organ = ExactWorldOrgan::new(remounted_world, remounted_adapter);
    if remounted_organ.world().standing() != coupled_world.world().standing()
        || remounted_organ.world().next_ordinal() != coupled_world.world().next_ordinal()
        || remounted_machine
            .rest_image()
            .map_err(|error| format!("{error:?}"))?
            != live_image
        || remounted_organ.adapter().checkpoint() != coupled_world.adapter().checkpoint()
    {
        return Err("the typed RELAMPAGO organ changed across exact rest/remount".into());
    }
    let causal_body = construct_relampago_causal_body(&episode_results)?;
    write_causal_body_research(&output, &causal_body)?;
    write_profile_layers(&output, &profile, &doctrine)?;
    for result in &episode_results {
        let episode_output = output.join(format!("episode-{:02}", result.ordinal + 1));
        fs::create_dir_all(&episode_output)?;
        write_spectral_contacts(&episode_output, &result.atmospheric_resolution)?;
        write_vertical_fibers(&episode_output, &result.atmospheric_resolution)?;
        write_lifted_relations(&episode_output, &result.atmospheric_resolution)?;
        write_bodies(&episode_output, &result.atmospheric_resolution)?;
        write_obstructions(&episode_output, &result.atmospheric_resolution)?;
        write_coupled_relations(
            &episode_output,
            &result.coupled_prediction,
            &result.coupled_grade,
        )?;
    }
    write_live_current_receipts(&output, &episode_results)?;
    write_coupled_summary(
        &output,
        &manifest,
        &glm_raw,
        &abi_raw,
        &igra,
        total_native_events,
        training_occurrences.len(),
        held_out_occurrences.len(),
        &loader_receipt,
        &training_receipt.radiation[0].work,
        &profile,
        &doctrine,
        &episode_results,
        coupled_world.world().standing(),
        acquisition_elapsed.as_millis(),
        abi_elapsed.as_millis(),
        &coupled_device,
        &live_image,
        &coupled_native,
        &causal_body,
    )?;
    write_source_digests(&output, &glm_raw, &abi_raw, &igra, &requests)?;

    let total_relations = episode_results.iter().try_fold(0_usize, |total, result| {
        total
            .checked_add(result.coupled_prediction.relations.len())
            .ok_or("coupled relation count overflow")
    })?;
    let total_fibers = episode_results.iter().try_fold(0_usize, |total, result| {
        total
            .checked_add(result.atmospheric_resolution.vertical_fibers.len())
            .ok_or("vertical fiber count overflow")
    })?;
    println!(
        "training={} held_out={} episodes={} coupled_relations={} vertical_fibers={} positive_front={} negative_front={} retained_branches={} causal_body_f_vector={:?} open_boundaries={} workers={} live_device={}",
        training_occurrences.len(),
        held_out_occurrences.len(),
        episode_results.len(),
        total_relations,
        total_fibers,
        coupled_world
            .world()
            .standing()
            .morphology
            .positive_maxima
            .len(),
        coupled_world
            .world()
            .standing()
            .morphology
            .negative_minima
            .len(),
        coupled_world
            .world()
            .standing()
            .morphology
            .returned_together_branches
            + coupled_world
                .world()
                .standing()
                .morphology
                .returned_apart_branches,
        causal_body.standing.active_f_vector(),
        causal_body
            .standing
            .openings()
            .values()
            .filter(|opening| opening.state == CausalOpeningState::Open)
            .count(),
        workers,
        coupled_device,
    );
    Ok(())
}

fn take_event(next: &mut u64) -> EventId {
    let event = EventId(*next);
    *next = next.checked_add(1).expect("experiment event carrier");
    event
}

fn reverse_administrative_delivery(
    source: &std::sync::Arc<AtmosphericInverseResolution>,
) -> std::sync::Arc<AtmosphericInverseResolution> {
    let mut reversed = source.as_ref().clone();
    reversed.occurrences.reverse();
    reversed.spectral_occurrences.reverse();
    for occurrence in &mut reversed.spectral_occurrences {
        occurrence.contacts.reverse();
    }
    reversed.contact_selections.reverse();
    let mut source_prediction = reversed.source_prediction.as_ref().clone();
    source_prediction.occurrences.reverse();
    source_prediction.candidate_relations.reverse();
    source_prediction.forced_components.reverse();
    reversed.source_prediction = std::sync::Arc::new(source_prediction);
    std::sync::Arc::new(reversed)
}

fn read_manifest(path: &Path) -> Result<Vec<String>, Box<dyn Error>> {
    let reader = BufReader::new(File::open(path)?);
    let mut keys = reader
        .lines()
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .filter(|line| !line.trim().is_empty())
        .collect::<Vec<_>>();
    keys.sort();
    keys.dedup();
    Ok(keys)
}

fn parse_product_time(key: &str) -> Result<ProductTime, Box<dyn Error>> {
    let marker = key.find("_s").ok_or("GOES key has no start marker")? + 2;
    let encoded = key
        .get(marker..marker + 14)
        .ok_or("GOES key has a malformed start marker")?;
    Ok(ProductTime {
        year: encoded[0..4].parse()?,
        day: encoded[4..7].parse()?,
        hour: encoded[7..9].parse()?,
        minute: encoded[9..11].parse()?,
        second: encoded[11..13].parse()?,
        tenth: encoded[13..14].parse()?,
    })
}

fn relampago_aperture() -> Vec<ExactCoordinateInterval> {
    vec![
        ExactCoordinateInterval {
            coordinate: 0,
            lower: Rat::new(BigInt::from(-33_464), BigInt::from(1_000)),
            upper: Rat::new(BigInt::from(-29_856), BigInt::from(1_000)),
        },
        ExactCoordinateInterval {
            coordinate: 1,
            lower: Rat::new(BigInt::from(-66_166), BigInt::from(1_000)),
            upper: Rat::new(BigInt::from(-61_959), BigInt::from(1_000)),
        },
    ]
}

fn load_glm_product(
    key: &str,
    path: &Path,
    chart_id: ReceiverChartId,
    product_time: &ProductTime,
    aperture: &[ExactCoordinateInterval],
) -> Result<LoadedProduct, Box<dyn Error>> {
    let dumped = dump_native_glm(path, chart_id)?;
    let extent = dumped.latitude.raw.len();
    if [
        dumped.longitude.raw.len(),
        dumped.time.raw.len(),
        dumped.energy.raw.len(),
        dumped.event_ids.len(),
        dumped.parent_groups.len(),
    ]
    .iter()
    .any(|candidate| *candidate != extent)
    {
        return Err("GLM event datasets have different extents".into());
    }
    let clock_offset = product_time.seconds_from_training_day() + &dumped.time.offset;
    let chart = ReceiverAffineChart::new(
        chart_id,
        GLM_RECEIVER,
        GLM_FAMILY,
        key,
        vec![
            "packed event latitude".to_owned(),
            "packed event longitude".to_owned(),
            "packed event time".to_owned(),
            "packed event energy".to_owned(),
        ],
        vec![
            dumped.latitude.offset.clone(),
            dumped.longitude.offset.clone(),
            clock_offset,
            dumped.energy.offset.clone(),
            Rat::from_integer(BigInt::from(chart_id.0)),
        ],
        packed_basis([
            dumped.latitude.scale.clone(),
            dumped.longitude.scale.clone(),
            dumped.time.scale.clone(),
            dumped.energy.scale.clone(),
        ]),
    )?;
    let mut occurrences = Vec::new();
    let mut cells = BTreeMap::<ReturnedCellId, BTreeSet<ReceiverTestimonyId>>::new();
    for index in 0..extent {
        let latitude = &dumped.latitude.offset
            + &dumped.latitude.scale * Rat::from_integer(BigInt::from(dumped.latitude.raw[index]));
        let longitude = &dumped.longitude.offset
            + &dumped.longitude.scale
                * Rat::from_integer(BigInt::from(dumped.longitude.raw[index]));
        if latitude < aperture[0].lower
            || latitude > aperture[0].upper
            || longitude < aperture[1].lower
            || longitude > aperture[1].upper
        {
            continue;
        }
        let testimony = ReceiverTestimonyId(
            u64::try_from(occurrences.len())?
                .checked_add(1)
                .ok_or("testimony carrier overflow")?,
        );
        occurrences.push(ReceiverTestimony {
            id: testimony,
            receiver: GLM_RECEIVER,
            lineage: ReceiverLineageId(u64::from(product_time.day)),
            chart: chart_id,
            source_identity: dumped.event_ids[index],
            raw: vec![
                dumped.latitude.raw[index],
                dumped.longitude.raw[index],
                dumped.time.raw[index],
                dumped.energy.raw[index],
            ],
        });
        let cell = ReturnedCellId(
            chart_id
                .0
                .checked_shl(32)
                .ok_or("returned-cell carrier overflow")?
                | dumped.parent_groups[index],
        );
        cells.entry(cell).or_default().insert(testimony);
    }
    Ok(LoadedProduct {
        split: product_time.split(),
        held_out_episode: product_time.held_out_episode(),
        chart,
        occurrences,
        cells,
        total_events: extent,
    })
}

fn dump_native_glm(source: &Path, chart: ReceiverChartId) -> Result<NativeGlmDump, Box<dyn Error>> {
    let temporary = std::env::temp_dir().join(format!(
        "holonic-storm-glm-{}-{}",
        std::process::id(),
        chart.0
    ));
    fs::create_dir(&temporary)?;
    let raw_path = temporary.join("events.bin");
    let attribute_path = temporary.join("attributes.bin");
    run_h5dump(
        source,
        &raw_path,
        &[
            "-d",
            "event_lat",
            "-d",
            "event_lon",
            "-d",
            "event_time_offset",
            "-d",
            "event_energy",
            "-d",
            "event_id",
            "-d",
            "event_parent_group_id",
        ],
    )?;
    run_h5dump(
        source,
        &attribute_path,
        &[
            "-a",
            "/event_lat/add_offset",
            "-a",
            "/event_lat/scale_factor",
            "-a",
            "/event_lon/add_offset",
            "-a",
            "/event_lon/scale_factor",
            "-a",
            "/event_time_offset/add_offset",
            "-a",
            "/event_time_offset/scale_factor",
            "-a",
            "/event_energy/add_offset",
            "-a",
            "/event_energy/scale_factor",
        ],
    )?;
    let raw = fs::read(&raw_path)?;
    let attributes = fs::read(&attribute_path)?;
    fs::remove_file(raw_path)?;
    fs::remove_file(attribute_path)?;
    fs::remove_dir(temporary)?;
    if raw.len() % 16 != 0 || attributes.len() != 32 {
        return Err("unexpected native GLM dump extents".into());
    }
    let extent = raw.len() / 16;
    let mut cursor = 0_usize;
    let latitude = read_u16_segment(&raw, &mut cursor, extent)?;
    let longitude = read_u16_segment(&raw, &mut cursor, extent)?;
    let time = read_u16_segment(&raw, &mut cursor, extent)?;
    let energy = read_u16_segment(&raw, &mut cursor, extent)?;
    let event_ids = read_u32_segment(&raw, &mut cursor, extent)?;
    let parent_groups = read_u32_segment(&raw, &mut cursor, extent)?;
    if cursor != raw.len() {
        return Err("native GLM dump left unread bytes".into());
    }
    let attributes = exact_f32_attributes(&attributes)?;
    Ok(NativeGlmDump {
        latitude: PackedAxis {
            raw: latitude,
            offset: attributes[0].clone(),
            scale: attributes[1].clone(),
        },
        longitude: PackedAxis {
            raw: longitude,
            offset: attributes[2].clone(),
            scale: attributes[3].clone(),
        },
        time: PackedAxis {
            raw: time,
            offset: attributes[4].clone(),
            scale: attributes[5].clone(),
        },
        energy: PackedAxis {
            raw: energy,
            offset: attributes[6].clone(),
            scale: attributes[7].clone(),
        },
        event_ids,
        parent_groups,
    })
}

fn rebase_product(
    product: &mut LoadedProduct,
    next_testimony: &mut u64,
) -> Result<(), Box<dyn Error>> {
    let mut rebase = BTreeMap::new();
    for occurrence in &mut product.occurrences {
        let global = ReceiverTestimonyId(*next_testimony);
        *next_testimony = next_testimony
            .checked_add(1)
            .ok_or("testimony carrier overflow")?;
        rebase.insert(occurrence.id, global);
        occurrence.id = global;
    }
    for members in product.cells.values_mut() {
        *members = members
            .iter()
            .map(|member| {
                rebase
                    .get(member)
                    .copied()
                    .ok_or_else(|| "local GLM testimony is absent from rebase".into())
            })
            .collect::<Result<BTreeSet<_>, Box<dyn Error>>>()?;
    }
    Ok(())
}

fn merge_cells(
    target: &mut BTreeMap<ReturnedCellId, BTreeSet<ReceiverTestimonyId>>,
    source: BTreeMap<ReturnedCellId, BTreeSet<ReceiverTestimonyId>>,
) {
    for (cell, members) in source {
        target.entry(cell).or_default().extend(members);
    }
}

fn partition(
    algorithm: ReturnedAlgorithmId,
    cells: BTreeMap<ReturnedCellId, BTreeSet<ReceiverTestimonyId>>,
) -> ReturnedReceiverPartition {
    ReturnedReceiverPartition {
        algorithm,
        coverage: ReturnedCellCoverage::CompleteExclusive,
        cells: cells
            .into_iter()
            .map(|(id, members)| ReturnedReceiverCell { id, members })
            .collect(),
    }
}

fn packed_basis(values: [Rat; 4]) -> Vec<Vec<Rat>> {
    let mut basis = values
        .into_iter()
        .enumerate()
        .map(|(row, value)| {
            (0..4)
                .map(|column| {
                    if row == column {
                        value.clone()
                    } else {
                        Rat::zero()
                    }
                })
                .collect()
        })
        .collect::<Vec<_>>();
    basis.push(vec![Rat::zero(); 4]);
    basis
}

fn run_h5dump(source: &Path, binary: &Path, selections: &[&str]) -> Result<(), Box<dyn Error>> {
    let status = Command::new("h5dump")
        .args(selections)
        .arg("-b")
        .arg("LE")
        .arg("-o")
        .arg(binary)
        .arg("-O")
        .arg("/dev/null")
        .arg(source)
        .status()?;
    if !status.success() {
        return Err(format!("h5dump failed for {}", source.display()).into());
    }
    Ok(())
}

fn run_h5dump_owned(
    source: &Path,
    binary: &Path,
    selections: &[String],
) -> Result<(), Box<dyn Error>> {
    let status = Command::new("h5dump")
        .args(selections)
        .arg("-b")
        .arg("LE")
        .arg("-o")
        .arg(binary)
        .arg("-O")
        .arg("/dev/null")
        .arg(source)
        .status()?;
    if !status.success() {
        return Err(format!("h5dump failed for {}", source.display()).into());
    }
    Ok(())
}

fn read_u16_segment(
    bytes: &[u8],
    cursor: &mut usize,
    extent: usize,
) -> Result<Vec<i64>, Box<dyn Error>> {
    let octets = extent.checked_mul(2).ok_or("u16 segment overflow")?;
    let end = cursor.checked_add(octets).ok_or("u16 cursor overflow")?;
    let segment = bytes.get(*cursor..end).ok_or("short u16 segment")?;
    *cursor = end;
    Ok(segment
        .chunks_exact(2)
        .map(|chunk| {
            i64::from(u16::from_le_bytes(
                chunk.try_into().expect("two-byte chunk"),
            ))
        })
        .collect())
}

fn read_u32_segment(
    bytes: &[u8],
    cursor: &mut usize,
    extent: usize,
) -> Result<Vec<u64>, Box<dyn Error>> {
    let octets = extent.checked_mul(4).ok_or("u32 segment overflow")?;
    let end = cursor.checked_add(octets).ok_or("u32 cursor overflow")?;
    let segment = bytes.get(*cursor..end).ok_or("short u32 segment")?;
    *cursor = end;
    Ok(segment
        .chunks_exact(4)
        .map(|chunk| {
            u64::from(u32::from_le_bytes(
                chunk.try_into().expect("four-byte chunk"),
            ))
        })
        .collect())
}

fn exact_f32_attributes(bytes: &[u8]) -> Result<Vec<Rat>, Box<dyn Error>> {
    bytes
        .chunks_exact(4)
        .map(|bytes| {
            exact_rational_from_f32_bits(u32::from_le_bytes(
                bytes.try_into().expect("four-byte chunk"),
            ))
            .map_err(|error| -> Box<dyn Error> { Box::new(error) })
        })
        .collect()
}

fn load_igra_profile(path: &Path) -> Result<AtmosphericProfile, Box<dyn Error>> {
    let output = Command::new("unzip").arg("-p").arg(path).output()?;
    if !output.status.success() {
        return Err(format!("unzip failed for {}", path.display()).into());
    }
    let text = String::from_utf8(output.stdout)?;
    let lines = text.lines().collect::<Vec<_>>();
    let (header_ordinal, header) = lines
        .iter()
        .enumerate()
        .find(|(_, line)| line.starts_with("#ARM00087344 2018 12 14 00 "))
        .ok_or("IGRA archive does not carry the requested 2018-12-14 00Z profile")?;
    let fields = header.split_whitespace().collect::<Vec<_>>();
    if fields.len() < 11 {
        return Err("IGRA profile header is malformed".into());
    }
    let level_count = fields[6].parse::<usize>()?;
    let latitude = Rat::new(
        BigInt::from(fields[9].parse::<i64>()?),
        BigInt::from(10_000),
    );
    let longitude = Rat::new(
        BigInt::from(fields[10].parse::<i64>()?),
        BigInt::from(10_000),
    );
    let body = lines
        .get(header_ordinal + 1..header_ordinal + 1 + level_count)
        .ok_or("IGRA profile body is shorter than its declared level count")?;
    let levels = body
        .iter()
        .map(|line| {
            let pressure = igra_field(line, 9, 15)?.map(|raw| Rat::from_integer(BigInt::from(raw)));
            let height = igra_field(line, 16, 21)?.map(|raw| Rat::from_integer(BigInt::from(raw)));
            let temperature = igra_field(line, 22, 27)?.map(|raw| {
                Rat::new(
                    BigInt::from(raw)
                        .checked_mul(&BigInt::from(10))
                        .expect("small IGRA temperature")
                        + BigInt::from(27_315),
                    BigInt::from(100),
                )
            });
            let humidity = igra_field(line, 28, 33)?.map(tenths_as_rational);
            let dewpoint = igra_field(line, 34, 39)?.map(tenths_as_rational);
            let wind_direction =
                igra_field(line, 40, 45)?.map(|raw| Rat::from_integer(BigInt::from(raw)));
            let wind_speed = igra_field(line, 46, 51)?.map(tenths_as_rational);
            Ok(AtmosphericProfileLevel {
                pressure_pascal: pressure,
                vertical_coordinate_metre: height,
                temperature_kelvin: temperature,
                relative_humidity_tenths_percent: humidity,
                dewpoint_depression_kelvin: dewpoint,
                wind_direction_degree: wind_direction,
                wind_speed_metre_per_second: wind_speed,
            })
        })
        .collect::<Result<Vec<_>, Box<dyn Error>>>()?;
    Ok(AtmosphericProfile::new(
        AtmosphericProfileId(1),
        IGRA_RECEIVER,
        IGRA_PROFILE_SOURCE,
        2_018_121_400,
        ExactInterval::point(Rat::from_integer(BigInt::from(86_400))),
        latitude,
        longitude,
        AtmosphericVerticalCoordinate::GeopotentialHeight,
        levels,
    )?)
}

fn igra_field(line: &str, start: usize, end: usize) -> Result<Option<i64>, Box<dyn Error>> {
    let field = line
        .get(start..end)
        .ok_or("IGRA fixed-width level is malformed")?
        .trim();
    let value = field.parse::<i64>()?;
    Ok((value > -8_000).then_some(value))
}

fn tenths_as_rational(value: i64) -> Rat {
    Rat::new(BigInt::from(value), BigInt::from(10))
}

#[derive(Clone, Debug)]
struct AbiBandRequest {
    band: SpectralBandId,
    path: PathBuf,
}

#[derive(Clone, Debug)]
struct AbiProjection {
    x_offset: f64,
    x_scale: f64,
    y_offset: f64,
    y_scale: f64,
    longitude_origin_radian: f64,
    perspective_height_metre: f64,
    semi_major_metre: f64,
    semi_minor_metre: f64,
    width: u32,
    height: u32,
}

#[derive(Clone, Debug)]
struct AbiBandSubset {
    band: SpectralBandId,
    offset: Rat,
    scale: Rat,
    raw: Vec<u16>,
    quality: Vec<u8>,
}

fn load_abi_contacts(
    directory: &Path,
    occurrences: &[ReceivedOccurrence],
    workers: NonZeroUsize,
) -> Result<BTreeMap<ReceiverTestimonyId, Vec<SpectralReceiverContact>>, Box<dyn Error>> {
    let requested_bands = BTreeSet::from([
        SpectralBandId(8),
        SpectralBandId(9),
        SpectralBandId(10),
        SpectralBandId(11),
        SpectralBandId(13),
    ]);
    let mut scans = BTreeMap::<String, Vec<AbiBandRequest>>::new();
    for entry in fs::read_dir(directory)? {
        let path = entry?.path();
        if path.extension().and_then(|extension| extension.to_str()) != Some("nc") {
            continue;
        }
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or("ABI path has no UTF-8 filename")?;
        let Some(band) = parse_abi_band(name) else {
            continue;
        };
        if !requested_bands.contains(&band) {
            continue;
        }
        let start = goes_time_marker(name, "_s")?;
        if start.year != 2018 || start.day != 347 {
            continue;
        }
        scans
            .entry(goes_encoded_marker(name, "_s")?.to_owned())
            .or_default()
            .push(AbiBandRequest { band, path });
    }
    if scans.is_empty() {
        return Err("no ABI receiver sections were found".into());
    }
    for requests in scans.values_mut() {
        requests.sort_by_key(|request| request.band);
        let supplied = requests
            .iter()
            .map(|request| request.band)
            .collect::<BTreeSet<_>>();
        if supplied != requested_bands {
            return Err("an ABI scan does not carry every declared spectral band".into());
        }
    }

    let first = scans
        .values()
        .next()
        .and_then(|scan| scan.first())
        .ok_or("ABI scan population is empty")?;
    let projection = load_abi_projection(&first.path)?;
    let addresses = occurrences
        .iter()
        .map(|occurrence| {
            abi_pixel(
                &projection,
                rational_to_f64(&occurrence.latitude)?,
                rational_to_f64(&occurrence.longitude)?,
            )
        })
        .collect::<Result<Vec<_>, Box<dyn Error>>>()?;
    let minimum_row = addresses
        .iter()
        .map(|(row, _)| *row)
        .min()
        .ok_or("held-out GLM population is empty")?;
    let maximum_row = addresses
        .iter()
        .map(|(row, _)| *row)
        .max()
        .ok_or("held-out GLM population is empty")?;
    let minimum_column = addresses
        .iter()
        .map(|(_, column)| *column)
        .min()
        .ok_or("held-out GLM population is empty")?;
    let maximum_column = addresses
        .iter()
        .map(|(_, column)| *column)
        .max()
        .ok_or("held-out GLM population is empty")?;
    let row_count = maximum_row
        .checked_sub(minimum_row)
        .and_then(|value| value.checked_add(1))
        .ok_or("ABI row aperture overflow")?;
    let column_count = maximum_column
        .checked_sub(minimum_column)
        .and_then(|value| value.checked_add(1))
        .ok_or("ABI column aperture overflow")?;
    let subset_extent = usize::try_from(row_count)?
        .checked_mul(usize::try_from(column_count)?)
        .ok_or("ABI subset extent overflow")?;

    let mut contacts = occurrences
        .iter()
        .map(|occurrence| (occurrence.testimony.id, Vec::new()))
        .collect::<BTreeMap<_, _>>();
    let loader = CpuExecutor::multicore(workers);
    for (scan_ordinal, (encoded_start, requests)) in scans.iter().enumerate() {
        let (subsets, _receipt) = loader
            .execute_indexed(requests, |_index, request| {
                load_abi_band_subset(
                    request,
                    minimum_row,
                    minimum_column,
                    row_count,
                    column_count,
                )
                .map_err(|error| error.to_string())
            })
            .map_err(|error| match error {
                CpuExecutionError::Operation(error) => error,
                CpuExecutionError::WorkerPanicked => {
                    "one ABI subset import worker panicked".to_owned()
                }
            })?;
        if subsets.iter().any(|subset| {
            subset.raw.len() != subset_extent || subset.quality.len() != subset_extent
        }) {
            return Err("an ABI band subset has the wrong extent".into());
        }
        let start = goes_time_marker(
            requests[0]
                .path
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or("ABI path has no filename")?,
            "_s",
        )?;
        let end = goes_time_marker(
            requests[0]
                .path
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or("ABI path has no filename")?,
            "_e",
        )?;
        let scan_clock = ExactInterval::new(
            start.seconds_from_training_day(),
            end.seconds_from_training_day(),
        )?;
        let scan = SpectralScanId(
            u64::try_from(scan_ordinal)?
                .checked_add(1)
                .ok_or("ABI scan carrier overflow")?,
        );
        for (occurrence, (row, column)) in occurrences.iter().zip(&addresses) {
            let relative_row = row
                .checked_sub(minimum_row)
                .ok_or("ABI relative row underflow")?;
            let relative_column = column
                .checked_sub(minimum_column)
                .ok_or("ABI relative column underflow")?;
            let index = usize::try_from(relative_row)?
                .checked_mul(usize::try_from(column_count)?)
                .and_then(|value| value.checked_add(usize::try_from(relative_column).ok()?))
                .ok_or("ABI subset address overflow")?;
            let mut brightness = BTreeMap::new();
            let mut quality = BTreeMap::new();
            for subset in &subsets {
                let value = &subset.offset
                    + &subset.scale * Rat::from_integer(BigInt::from(subset.raw[index]));
                brightness.insert(subset.band, value);
                quality.insert(subset.band, subset.quality[index]);
            }
            contacts
                .get_mut(&occurrence.testimony.id)
                .ok_or("ABI contact index omitted a GLM occurrence")?
                .push(SpectralReceiverContact {
                    scan,
                    receiver: ABI_RECEIVER,
                    source: format!(
                        "GOES-16 ABI L2 CMIPF native bands 08/09/10/11/13 scan {encoded_start}"
                    ),
                    clock: scan_clock.clone(),
                    row: *row,
                    column: *column,
                    address_status: SpectralAddressStatus::ImportedApproximateLandmark,
                    address_doctrine: "nearest ABI fixed-grid address from the source-declared GOES geostationary projection evaluated in IEEE-754 binary64; imported as an approximate landmark rather than exact world standing".to_owned(),
                    data_quality_flags: quality,
                    brightness_temperature_kelvin: brightness,
                });
        }
    }
    Ok(contacts)
}

fn parse_abi_band(name: &str) -> Option<SpectralBandId> {
    let marker = name.find("M3C")? + 3;
    let encoded = name.get(marker..marker + 2)?;
    encoded.parse().ok().map(SpectralBandId)
}

fn goes_encoded_marker<'a>(name: &'a str, marker: &str) -> Result<&'a str, Box<dyn Error>> {
    let start = name.find(marker).ok_or("GOES filename marker is absent")? + marker.len();
    name.get(start..start + 14)
        .ok_or_else(|| "GOES filename marker is malformed".into())
}

fn goes_time_marker(name: &str, marker: &str) -> Result<ProductTime, Box<dyn Error>> {
    let encoded = goes_encoded_marker(name, marker)?;
    Ok(ProductTime {
        year: encoded[0..4].parse()?,
        day: encoded[4..7].parse()?,
        hour: encoded[7..9].parse()?,
        minute: encoded[9..11].parse()?,
        second: encoded[11..13].parse()?,
        tenth: encoded[13..14].parse()?,
    })
}

fn load_abi_projection(path: &Path) -> Result<AbiProjection, Box<dyn Error>> {
    let temporary =
        std::env::temp_dir().join(format!("holonic-abi-projection-{}", std::process::id()));
    fs::create_dir(&temporary)?;
    let grid_path = temporary.join("grid.bin");
    let projection_path = temporary.join("projection.bin");
    run_h5dump(
        path,
        &grid_path,
        &[
            "-a",
            "/x/add_offset",
            "-a",
            "/x/scale_factor",
            "-a",
            "/y/add_offset",
            "-a",
            "/y/scale_factor",
        ],
    )?;
    run_h5dump(
        path,
        &projection_path,
        &[
            "-a",
            "/goes_imager_projection/longitude_of_projection_origin",
            "-a",
            "/goes_imager_projection/perspective_point_height",
            "-a",
            "/goes_imager_projection/semi_major_axis",
            "-a",
            "/goes_imager_projection/semi_minor_axis",
        ],
    )?;
    let grid = fs::read(&grid_path)?;
    let projection = fs::read(&projection_path)?;
    fs::remove_file(grid_path)?;
    fs::remove_file(projection_path)?;
    fs::remove_dir(temporary)?;
    if grid.len() != 16 || projection.len() != 32 {
        return Err("unexpected ABI projection attribute extent".into());
    }
    let grid = grid
        .chunks_exact(4)
        .map(|bytes| f32::from_bits(u32::from_le_bytes(bytes.try_into().unwrap())) as f64)
        .collect::<Vec<_>>();
    let projection = projection
        .chunks_exact(8)
        .map(|bytes| f64::from_bits(u64::from_le_bytes(bytes.try_into().unwrap())))
        .collect::<Vec<_>>();
    Ok(AbiProjection {
        x_offset: grid[0],
        x_scale: grid[1],
        y_offset: grid[2],
        y_scale: grid[3],
        longitude_origin_radian: projection[0].to_radians(),
        perspective_height_metre: projection[1],
        semi_major_metre: projection[2],
        semi_minor_metre: projection[3],
        width: 5_424,
        height: 5_424,
    })
}

fn abi_pixel(
    projection: &AbiProjection,
    latitude_degree: f64,
    longitude_degree: f64,
) -> Result<(u32, u32), Box<dyn Error>> {
    let latitude = latitude_degree.to_radians();
    let longitude = longitude_degree.to_radians();
    let equatorial = projection.semi_major_metre;
    let polar = projection.semi_minor_metre;
    let satellite_radius = projection.perspective_height_metre + equatorial;
    let geocentric_latitude = ((polar * polar) / (equatorial * equatorial) * latitude.tan()).atan();
    let eccentricity = (equatorial * equatorial - polar * polar) / (equatorial * equatorial);
    let local_radius = polar / (1.0 - eccentricity * geocentric_latitude.cos().powi(2)).sqrt();
    let longitude_departure = longitude - projection.longitude_origin_radian;
    let source_x =
        satellite_radius - local_radius * geocentric_latitude.cos() * longitude_departure.cos();
    let source_y = -local_radius * geocentric_latitude.cos() * longitude_departure.sin();
    let source_z = local_radius * geocentric_latitude.sin();
    let fixed_x = (-source_y).atan2(source_x);
    let fixed_y = source_z.atan2((source_x * source_x + source_y * source_y).sqrt());
    let column = ((fixed_x - projection.x_offset) / projection.x_scale).round();
    let row = ((fixed_y - projection.y_offset) / projection.y_scale).round();
    if !column.is_finite()
        || !row.is_finite()
        || column < 0.0
        || row < 0.0
        || column >= f64::from(projection.width)
        || row >= f64::from(projection.height)
    {
        return Err("a GLM occurrence falls outside the ABI receiver aperture".into());
    }
    Ok((row as u32, column as u32))
}

fn rational_to_f64(value: &Rat) -> Result<f64, Box<dyn Error>> {
    value
        .to_f64()
        .filter(|value| value.is_finite())
        .ok_or_else(|| "exact receiver coordinate exceeds the ABI transducer".into())
}

fn load_abi_band_subset(
    request: &AbiBandRequest,
    row: u32,
    column: u32,
    rows: u32,
    columns: u32,
) -> Result<AbiBandSubset, Box<dyn Error>> {
    let temporary = std::env::temp_dir().join(format!(
        "holonic-abi-subset-{}-{}-{}",
        std::process::id(),
        request.band.0,
        goes_encoded_marker(
            request
                .path
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or("ABI path has no filename")?,
            "_s"
        )?
    ));
    fs::create_dir(&temporary)?;
    let cmi_path = temporary.join("cmi.bin");
    let quality_path = temporary.join("quality.bin");
    let attribute_path = temporary.join("attributes.bin");
    let start = format!("{row},{column}");
    let count = format!("{rows},{columns}");
    run_h5dump_owned(
        &request.path,
        &cmi_path,
        &[
            "-d".to_owned(),
            "CMI".to_owned(),
            "-s".to_owned(),
            start.clone(),
            "-c".to_owned(),
            count.clone(),
        ],
    )?;
    run_h5dump_owned(
        &request.path,
        &quality_path,
        &[
            "-d".to_owned(),
            "DQF".to_owned(),
            "-s".to_owned(),
            start,
            "-c".to_owned(),
            count,
        ],
    )?;
    run_h5dump(
        &request.path,
        &attribute_path,
        &["-a", "/CMI/add_offset", "-a", "/CMI/scale_factor"],
    )?;
    let cmi = fs::read(&cmi_path)?;
    let quality = fs::read(&quality_path)?;
    let attributes = fs::read(&attribute_path)?;
    fs::remove_file(cmi_path)?;
    fs::remove_file(quality_path)?;
    fs::remove_file(attribute_path)?;
    fs::remove_dir(temporary)?;
    if cmi.len() % 2 != 0 || attributes.len() != 8 {
        return Err("unexpected ABI subset carrier extent".into());
    }
    let raw = cmi
        .chunks_exact(2)
        .map(|bytes| u16::from_le_bytes(bytes.try_into().unwrap()))
        .collect();
    let attributes = exact_f32_attributes(&attributes)?;
    Ok(AbiBandSubset {
        band: request.band,
        offset: attributes[0].clone(),
        scale: attributes[1].clone(),
        raw,
        quality,
    })
}

fn write_profile_layers(
    output: &Path,
    profile: &AtmosphericProfile,
    doctrine: &OpaqueThermalChordDoctrine,
) -> Result<(), Box<dyn Error>> {
    let mut writer = BufWriter::new(File::create(output.join("profile_layers.tsv"))?);
    writeln!(
        writer,
        "profile\tlower_level\tz_lower_m\tz_upper_m\tpressure_lower_pa\tpressure_upper_pa\ttemperature_lower_k\ttemperature_upper_k\tln_pressure_ratio_lower\tln_pressure_ratio_upper\tinverse_temperature_chord_m_per_k\teffective_acceleration_lower_m_per_s2\teffective_acceleration_upper_m_per_s2\tindependent_gravity_testimony"
    )?;
    for layer in profile.complete_layers(doctrine)? {
        writeln!(
            writer,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            layer.id.profile.0,
            layer.id.lower_level,
            layer.vertical_coordinate.lower,
            layer.vertical_coordinate.upper,
            layer.pressure_pascal.upper,
            layer.pressure_pascal.lower,
            layer.lower_temperature_kelvin,
            layer.upper_temperature_kelvin,
            layer.hydrostatic.pressure_log_ratio.lower,
            layer.hydrostatic.pressure_log_ratio.upper,
            layer.hydrostatic.inverse_temperature_chord,
            layer
                .hydrostatic
                .effective_acceleration_metre_per_second_squared
                .lower,
            layer
                .hydrostatic
                .effective_acceleration_metre_per_second_squared
                .upper,
            layer.hydrostatic.independent_gravity_testimony,
        )?;
    }
    Ok(())
}

fn write_spectral_contacts(
    output: &Path,
    resolution: &AtmosphericInverseResolution,
) -> Result<(), Box<dyn Error>> {
    let selections = resolution
        .contact_selections
        .iter()
        .map(|selection| (selection.testimony, selection))
        .collect::<BTreeMap<_, _>>();
    let mut writer = BufWriter::new(File::create(output.join("spectral_contacts.tsv"))?);
    writeln!(
        writer,
        "testimony\tsource_identity\tlatitude_degree\tlongitude_degree\toccurrence_clock_s\tradiant_energy\tscan\tselected\tscan_departure_s\tscan_clock_lower_s\tscan_clock_upper_s\trow\tcolumn\tquality_b08\ttemperature_b08_k\tquality_b09\ttemperature_b09_k\tquality_b10\ttemperature_b10_k\tquality_b11\ttemperature_b11_k\tquality_b13\ttemperature_b13_k\taddress_status\taddress_doctrine\tsource"
    )?;
    for occurrence in &resolution.spectral_occurrences {
        let selection = selections
            .get(&occurrence.testimony)
            .ok_or("spectral occurrence has no contact selection receipt")?;
        for contact in &occurrence.contacts {
            let selected = selection.selected_scans.contains(&contact.scan);
            let departure = if selected {
                selection
                    .minimum_departure_seconds
                    .as_ref()
                    .map(ToString::to_string)
                    .unwrap_or_default()
            } else {
                String::new()
            };
            write!(
                writer,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                occurrence.testimony.0,
                occurrence.source_identity,
                occurrence.latitude_degree,
                occurrence.longitude_degree,
                occurrence.clock,
                occurrence.radiant_energy,
                contact.scan.0,
                selected,
                departure,
                contact.clock.lower,
                contact.clock.upper,
                contact.row,
                contact.column,
            )?;
            for band in [8_u16, 9, 10, 11, 13] {
                let band = SpectralBandId(band);
                write!(
                    writer,
                    "\t{}\t{}",
                    contact
                        .data_quality_flags
                        .get(&band)
                        .map(ToString::to_string)
                        .unwrap_or_default(),
                    contact
                        .brightness_temperature_kelvin
                        .get(&band)
                        .map(ToString::to_string)
                        .unwrap_or_default(),
                )?;
            }
            writeln!(
                writer,
                "\t{:?}\t{}\t{}",
                contact.address_status,
                contact.address_doctrine.replace('\t', " "),
                contact.source.replace('\t', " "),
            )?;
        }
    }
    Ok(())
}

fn write_vertical_fibers(
    output: &Path,
    resolution: &AtmosphericInverseResolution,
) -> Result<(), Box<dyn Error>> {
    let mut writer = BufWriter::new(File::create(output.join("vertical_fibers.tsv"))?);
    writeln!(
        writer,
        "fiber\ttestimony\tsource_identity\tscan\tspectral_receiver\tprofile\tlayer_lower_level\tsupport_kind\tz_lower_m\tz_upper_m\tbrightness_temperature_k\tscan_departure_s\ttemporality\tpressure_lower_pa\tpressure_upper_pa"
    )?;
    for (ordinal, fiber) in resolution.vertical_fibers.iter().enumerate() {
        let support = fiber.support.enclosure();
        let support_kind = match fiber.support {
            VerticalFiberSupport::Point(_) => "point",
            VerticalFiberSupport::Layer(_) => "layer",
        };
        let temporality = match fiber.temporality {
            SpectralContactTemporality::Concurrent => "concurrent",
            SpectralContactTemporality::Carried => "carried",
        };
        writeln!(
            writer,
            "{ordinal}\t{}\t{}\t{}\t{}\t{}\t{}\t{support_kind}\t{}\t{}\t{}\t{}\t{temporality}\t{}\t{}",
            fiber.testimony.0,
            fiber.source_identity,
            fiber.scan.0,
            fiber.spectral_receiver.0,
            fiber.profile.0,
            fiber.layer.lower_level,
            support.lower,
            support.upper,
            fiber.brightness_temperature_kelvin,
            fiber.scan_departure_seconds,
            fiber.pressure_pascal.lower,
            fiber.pressure_pascal.upper,
        )?;
    }
    Ok(())
}

fn write_lifted_relations(
    output: &Path,
    resolution: &AtmosphericInverseResolution,
) -> Result<(), Box<dyn Error>> {
    let mut writer = BufWriter::new(File::create(output.join("lifted_relations.tsv"))?);
    writeln!(
        writer,
        "relation\tleft_testimony\tright_testimony\tleft_fiber\tright_fiber\tvertical_departure_lower_m\tvertical_departure_upper_m\tsource_difference"
    )?;
    for (ordinal, relation) in resolution.lifted_relations.iter().enumerate() {
        writeln!(
            writer,
            "{ordinal}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            relation.source_relation_members[0].0,
            relation.source_relation_members[1].0,
            relation.left_fiber,
            relation.right_fiber,
            relation.vertical_departure_metre.lower,
            relation.vertical_departure_metre.upper,
            rational_vector_text(&relation.source_difference.0),
        )?;
    }
    Ok(())
}

fn write_bodies(
    output: &Path,
    resolution: &AtmosphericInverseResolution,
) -> Result<(), Box<dyn Error>> {
    let mut writer = BufWriter::new(File::create(output.join("receiver_bodies.tsv"))?);
    writeln!(
        writer,
        "source_component\tmember_count\tvertical_fiber_count\tlifted_relation_count\tmembers\tvertical_fibers\tlifted_relations"
    )?;
    for body in &resolution.bodies {
        writeln!(
            writer,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}",
            body.source_component,
            body.members.len(),
            body.vertical_fibers.len(),
            body.lifted_relations.len(),
            body.members
                .iter()
                .map(|member| member.0.to_string())
                .collect::<Vec<_>>()
                .join(";"),
            integer_vector_text(&body.vertical_fibers),
            integer_vector_text(&body.lifted_relations),
        )?;
    }
    Ok(())
}

fn write_obstructions(
    output: &Path,
    resolution: &AtmosphericInverseResolution,
) -> Result<(), Box<dyn Error>> {
    let mut writer = BufWriter::new(File::create(output.join("obstructions.tsv"))?);
    writeln!(writer, "kind\ttestimony\tleft_testimony\tright_testimony")?;
    for obstruction in &resolution.obstructions {
        let testimony = obstruction
            .testimony
            .map(|value| value.0.to_string())
            .unwrap_or_default();
        let (left, right) = obstruction
            .relation_members
            .map(|members| (members[0].0.to_string(), members[1].0.to_string()))
            .unwrap_or_default();
        writeln!(
            writer,
            "{:?}\t{testimony}\t{left}\t{right}",
            obstruction.kind
        )?;
    }
    Ok(())
}

fn construct_relampago_causal_body(
    episodes: &[EpisodeResult],
) -> Result<RelampagoCausalBodyResearch, Box<dyn Error>> {
    let mut world = CausalWorld::new(ExactCausalBodyLaw, CausalBodyStanding::default());
    let mut receipts = Vec::with_capacity(episodes.len());
    let mut vertical_sections = BTreeMap::new();
    let mut relation_sections = BTreeMap::new();
    for episode in episodes {
        let mut deeds = Vec::new();
        let mut fiber_handles =
            Vec::with_capacity(episode.atmospheric_resolution.vertical_fibers.len());
        let mut next_handle = 1_u64;
        for (fiber_ordinal, fiber) in episode
            .atmospheric_resolution
            .vertical_fibers
            .iter()
            .enumerate()
        {
            let local = EventCellId(next_handle);
            next_handle = next_handle
                .checked_add(1)
                .ok_or("RELAMPAGO causal-body handle overflow")?;
            fiber_handles.push(local);
            deeds.push(CausalBodyDeed::FoundCell {
                local,
                name: format!(
                    "episode {} vertical fiber {} testimony {} source {} scan {} layer {}",
                    episode.ordinal + 1,
                    fiber_ordinal,
                    fiber.testimony.0,
                    fiber.source_identity,
                    fiber.scan.0,
                    fiber.layer.lower_level,
                ),
                grade: 0,
                boundary: Vec::new(),
            });
        }

        let mut relation_handles = Vec::new();
        for (relation_ordinal, relation) in episode.coupled_prediction.relations.iter().enumerate()
        {
            for (branch_ordinal, branch) in relation.branches.iter().enumerate() {
                let left_ordinal = usize::try_from(branch.vertical_fibers[0])?;
                let right_ordinal = usize::try_from(branch.vertical_fibers[1])?;
                let left = *fiber_handles
                    .get(left_ordinal)
                    .ok_or("coupled relation names an absent left vertical fiber")?;
                let right = *fiber_handles
                    .get(right_ordinal)
                    .ok_or("coupled relation names an absent right vertical fiber")?;
                let local = EventCellId(next_handle);
                next_handle = next_handle
                    .checked_add(1)
                    .ok_or("RELAMPAGO causal-body handle overflow")?;
                deeds.push(CausalBodyDeed::FoundCell {
                    local,
                    name: format!(
                        "episode {} coupled relation {} branch {} {:?}",
                        episode.ordinal + 1,
                        relation_ordinal,
                        branch_ordinal,
                        relation.state,
                    ),
                    grade: 1,
                    boundary: vec![
                        EventBoundaryTerm {
                            cell: CausalCellReference::Event(left),
                            coefficient: ComparativeMultiplicity::negative(1_u8),
                        },
                        EventBoundaryTerm {
                            cell: CausalCellReference::Event(right),
                            coefficient: ComparativeMultiplicity::positive(1_u8),
                        },
                    ],
                });
                relation_handles.push((
                    relation_ordinal,
                    branch_ordinal,
                    relation.state,
                    local,
                    RelampagoCausalRelationSection {
                        members: relation.members,
                        origin: relation.origin,
                        base_state: relation.base_state,
                        branch: branch.clone(),
                        generated_state: relation.state,
                    },
                ));
            }
        }

        let source_event = episode.coupled_prediction.caused_by;
        let chronology = episode.coupled_prediction.chronology;
        let transition = world.receive(&CausalBodyEvent {
            event: source_event,
            chronology,
            deeds,
        })?;
        let radiation = transition
            .radiation
            .first()
            .ok_or("causal body emitted no event radiation")?;
        let mut fiber_cells = Vec::with_capacity(fiber_handles.len());
        for (handle, fiber) in fiber_handles
            .into_iter()
            .zip(&episode.atmospheric_resolution.vertical_fibers)
        {
            let cell = *radiation
                .minted_cells
                .get(&handle)
                .ok_or("causal body omitted a vertical-fiber cell")?;
            fiber_cells.push(cell);
            vertical_sections.insert(cell, fiber.clone());
        }
        let mut relation_cells = Vec::with_capacity(relation_handles.len());
        for (relation_ordinal, branch_ordinal, state, handle, section) in relation_handles {
            let cell = *radiation
                .minted_cells
                .get(&handle)
                .ok_or("causal body omitted a coupled-relation cell")?;
            relation_cells.push(CausalBodyRelationCell {
                relation_ordinal,
                branch_ordinal,
                state,
                cell,
            });
            relation_sections.insert(cell, section);
        }
        receipts.push(CausalBodyEpisodeReceipt {
            episode: episode.ordinal + 1,
            source_event,
            chronology,
            fiber_cells,
            relation_cells,
            transition,
        });
    }
    world.standing().validate()?;
    Ok(RelampagoCausalBodyResearch {
        standing: world.standing().clone(),
        next_ordinal: world.next_ordinal(),
        episodes: receipts,
        vertical_sections,
        relation_sections,
    })
}

fn write_causal_body_research(
    output: &Path,
    research: &RelampagoCausalBodyResearch,
) -> Result<(), Box<dyn Error>> {
    research.standing.validate()?;
    let active_vertices = research.standing.active_cells_at_grade(0);
    let active_relations = research.standing.active_cells_at_grade(1);
    if research
        .vertical_sections
        .keys()
        .copied()
        .collect::<BTreeSet<_>>()
        != active_vertices
        || research
            .relation_sections
            .keys()
            .copied()
            .collect::<BTreeSet<_>>()
            != active_relations
    {
        return Err("RELAMPAGO typed sections do not exactly cover causal incidence".into());
    }
    for (cell, section) in &research.relation_sections {
        if section.branch.phase.0.len() != 18 {
            return Err("RELAMPAGO relation section lost its 18-coordinate phase".into());
        }
        if !research
            .standing
            .incidence
            .cell(*cell)?
            .boundary
            .support()
            .is_subset(&active_vertices)
        {
            return Err("RELAMPAGO relation boundary leaves its vertical-fiber population".into());
        }
    }

    let joined_native = ron::ser::to_string(research)?;
    let joined_remount: RelampagoCausalBodyResearch = ron::de::from_str(&joined_native)?;
    if joined_remount != *research {
        return Err("joined RELAMPAGO causal body changed across exact rest/remount".into());
    }
    fs::write(
        output.join("relampago-causal-body.ron"),
        joined_native.as_bytes(),
    )?;
    let native = ron::ser::to_string(&research.standing)?;
    let remounted: CausalBodyStanding = ron::de::from_str(&native)?;
    remounted.validate()?;
    if remounted != research.standing {
        return Err("RELAMPAGO causal body changed across exact rest/remount".into());
    }
    fs::write(output.join("causal-body-standing.ron"), native)?;
    fs::write(
        output.join("causal-body-next-ordinal.bin"),
        research.next_ordinal.to_le_bytes(),
    )?;
    let transitions = research
        .episodes
        .iter()
        .map(|episode| &episode.transition)
        .collect::<Vec<_>>();
    fs::write(
        output.join("causal-body-transitions.ron"),
        ron::ser::to_string(&transitions)?,
    )?;

    let mut events = BufWriter::new(File::create(output.join("causal-body-events.tsv"))?);
    writeln!(
        events,
        "episode\tsource_event\tchronology\tminted_vertical_fibers\tminted_relation_carriers\tf_vector_before\tf_vector_after\tchanged_open_boundaries\tchanged_holonomy_generators"
    )?;
    for episode in &research.episodes {
        let radiation = episode
            .transition
            .radiation
            .first()
            .ok_or("stored causal-body transition has no radiation")?;
        writeln!(
            events,
            "{}\t{}\t{}\t{}\t{}\t{:?}\t{:?}\t{}\t{}",
            episode.episode,
            episode.source_event.0,
            episode.chronology,
            episode.fiber_cells.len(),
            episode.relation_cells.len(),
            radiation.active_f_vector_before,
            radiation.active_f_vector_after,
            radiation.changed_openings.len(),
            radiation.holonomy_changed.len(),
        )?;
    }

    let mut cells = BufWriter::new(File::create(output.join("causal-body-cells.tsv"))?);
    writeln!(
        cells,
        "cell\tactive\tgrade\tname\tsource_events\toriented_boundary"
    )?;
    for (cell, body) in research.standing.incidence.cells() {
        let source_events = body
            .source_events
            .iter()
            .map(|event| event.0.to_string())
            .collect::<Vec<_>>()
            .join(";");
        writeln!(
            cells,
            "{}\t{}\t{}\t{}\t{}\t{}",
            cell.0,
            research.standing.active_cells().contains(cell),
            body.grade,
            body.name.replace('\t', " "),
            source_events,
            causal_chain_text(&body.boundary),
        )?;
    }

    let mut application = BufWriter::new(File::create(
        output.join("causal-body-application-map.tsv"),
    )?);
    writeln!(
        application,
        "episode\tapplication_member\tordinal\tbranch\tstate\tcausal_cell\texact_phase"
    )?;
    for episode in &research.episodes {
        for (ordinal, cell) in episode.fiber_cells.iter().enumerate() {
            writeln!(
                application,
                "{}\tvertical_fiber\t{}\t\t\t{}\t",
                episode.episode, ordinal, cell.0
            )?;
        }
        for relation in &episode.relation_cells {
            let section = &research.relation_sections[&relation.cell];
            writeln!(
                application,
                "{}\tcoupled_relation\t{}\t{}\t{:?}\t{}\t{}",
                episode.episode,
                relation.relation_ordinal,
                relation.branch_ordinal,
                relation.state,
                relation.cell.0,
                rational_vector_text(&section.branch.phase.0),
            )?;
        }
    }

    let mut section_writer = BufWriter::new(File::create(
        output.join("causal-body-relation-sections.tsv"),
    )?);
    writeln!(
        section_writer,
        "cell\tmembers\torigin\tbase_state\tgenerated_state\tscans\tvertical_fibers\texact_phase"
    )?;
    for (cell, section) in &research.relation_sections {
        writeln!(
            section_writer,
            "{}\t{};{}\t{:?}\t{:?}\t{:?}\t{};{}\t{};{}\t{}",
            cell.0,
            section.members[0].0,
            section.members[1].0,
            section.origin,
            section.base_state,
            section.generated_state,
            section.branch.scans[0].0,
            section.branch.scans[1].0,
            section.branch.vertical_fibers[0],
            section.branch.vertical_fibers[1],
            rational_vector_text(&section.branch.phase.0),
        )?;
    }

    let mut openings = BufWriter::new(File::create(output.join("causal-body-openings.tsv"))?);
    writeln!(
        openings,
        "opening\tboundary_grade\tstate\torigin\tfounded_by\tlast_changed_by\toriented_boundary\treceiver_measures"
    )?;
    for opening in research.standing.openings().values() {
        let measures = opening
            .receiver_measures
            .iter()
            .map(|(receiver, measure)| {
                format!(
                    "{}:{}/{}",
                    receiver.0,
                    measure.filled_population,
                    &measure.filled_population + &measure.unfilled_population,
                )
            })
            .collect::<Vec<_>>()
            .join(";");
        writeln!(
            openings,
            "{}\t{}\t{:?}\t{:?}\t{}\t{}\t{}\t{}",
            opening.id.0,
            opening.boundary_grade,
            opening.state,
            opening.origin,
            opening.founded_by.0,
            opening.last_changed_by.0,
            causal_chain_text(&opening.boundary),
            measures,
        )?;
    }

    let active_f_vector = research.standing.active_f_vector();
    let active_faces = active_f_vector.get(&2).copied().unwrap_or(0);
    let open_boundaries = research
        .standing
        .openings()
        .values()
        .filter(|opening| opening.state == CausalOpeningState::Open)
        .count();
    let filled_boundaries = research
        .standing
        .openings()
        .values()
        .filter(|opening| matches!(opening.state, CausalOpeningState::Filled { .. }))
        .count();
    let mut audit = BufWriter::new(File::create(output.join("causal-body-audit.tsv"))?);
    writeln!(audit, "measure\tvalue")?;
    writeln!(audit, "source_owner\tExactCausalBodyLaw")?;
    writeln!(audit, "active_f_vector\t{:?}", active_f_vector)?;
    writeln!(audit, "active_grade_two_cells\t{active_faces}")?;
    writeln!(
        audit,
        "typed_vertical_fiber_sections\t{}",
        research.vertical_sections.len()
    )?;
    writeln!(
        audit,
        "typed_phase_relation_sections\t{}",
        research.relation_sections.len()
    )?;
    writeln!(audit, "phase_coordinates_per_relation\t18")?;
    writeln!(audit, "open_boundary_fibers\t{open_boundaries}")?;
    writeln!(audit, "filled_boundary_fibers\t{filled_boundaries}")?;
    writeln!(
        audit,
        "connection_holonomy_generators\t{}",
        research.standing.holonomy_generators().len()
    )?;
    writeln!(
        audit,
        "projection_policy\tNo screen-space projection is emitted. Dense relation cycles remain exact open one-boundaries; they are not promoted to faces, volumes, tori, knots, or physical lightning channels."
    )?;
    writeln!(
        audit,
        "connection_policy\tNo comparison transport was declared by this application, so the body emits no fabricated holonomy."
    )?;
    writeln!(
        audit,
        "rest_remount_exact\t{}",
        remounted == research.standing
    )?;
    writeln!(
        audit,
        "joined_rest_remount_exact\t{}",
        joined_remount == *research
    )?;
    Ok(())
}

fn causal_chain_text(chain: &holonic_engine::CausalChain) -> String {
    chain
        .coefficients()
        .iter()
        .map(|(cell, coefficient)| format!("{}:{}", cell.0, coefficient.difference()))
        .collect::<Vec<_>>()
        .join(";")
}

fn write_coupled_relations(
    output: &Path,
    prediction: &CoupledInformantPrediction,
    grade: &CoupledInformantGrade,
) -> Result<(), Box<dyn Error>> {
    let mut cell_by_testimony = BTreeMap::new();
    for cell in &grade.returned.cells {
        for testimony in &cell.members {
            cell_by_testimony.insert(*testimony, cell.id);
        }
    }
    let mut kinds = BufWriter::new(File::create(output.join("phase_coordinates.tsv"))?);
    writeln!(kinds, "coordinate\tkind")?;
    for (coordinate, kind) in prediction
        .morphology_before
        .coordinate_kinds
        .iter()
        .enumerate()
    {
        writeln!(kinds, "{coordinate}\t{kind:?}")?;
    }

    let mut writer = BufWriter::new(File::create(output.join("coupled_relations.tsv"))?);
    let mut origin_counts = BTreeMap::<
        (
            holonic_engine::CoupledRelationOrigin,
            CoupledInformantRelationState,
            bool,
        ),
        usize,
    >::new();
    write!(
        writer,
        "left_testimony\tright_testimony\treturned_relation\torigin\tbase_state\tcoupled_state\tbranch\tleft_scan\tright_scan\tleft_vertical_fiber\tright_vertical_fiber\tbranch_state"
    )?;
    for coordinate in 0..holonic_engine::COUPLED_PHASE_EXTENT {
        write!(writer, "\tphase_{coordinate:02}")?;
    }
    writeln!(writer)?;
    for relation in &prediction.relations {
        let returned_together = cell_by_testimony.get(&relation.members[0])
            == cell_by_testimony.get(&relation.members[1]);
        *origin_counts
            .entry((relation.origin, relation.state, returned_together))
            .or_default() += 1;
        let returned_relation = if returned_together {
            "together"
        } else {
            "apart"
        };
        if relation.branches.is_empty() {
            write!(
                writer,
                "{}\t{}\t{returned_relation}\t{:?}\t{:?}\t{:?}\t\t\t\t\t\t",
                relation.members[0].0,
                relation.members[1].0,
                relation.origin,
                relation.base_state,
                relation.state,
            )?;
            for _ in 0..holonic_engine::COUPLED_PHASE_EXTENT {
                write!(writer, "\t")?;
            }
            writeln!(writer)?;
            continue;
        }
        for (branch, phase) in relation.branches.iter().enumerate() {
            write!(
                writer,
                "{}\t{}\t{returned_relation}\t{:?}\t{:?}\t{:?}\t{branch}\t{}\t{}\t{}\t{}\t{:?}",
                relation.members[0].0,
                relation.members[1].0,
                relation.origin,
                relation.base_state,
                relation.state,
                phase.scans[0].0,
                phase.scans[1].0,
                phase.vertical_fibers[0],
                phase.vertical_fibers[1],
                phase.state,
            )?;
            for coordinate in &phase.phase.0 {
                write!(writer, "\t{coordinate}")?;
            }
            writeln!(writer)?;
        }
    }
    let mut origin_writer = BufWriter::new(File::create(output.join("origin_grade.tsv"))?);
    writeln!(
        origin_writer,
        "origin\tgenerated_state\treturned_relation\trelations"
    )?;
    for ((origin, state, together), count) in origin_counts {
        writeln!(
            origin_writer,
            "{origin:?}\t{state:?}\t{}\t{count}",
            if together { "together" } else { "apart" }
        )?;
    }
    let mut summary = BufWriter::new(File::create(output.join("coupled_grade.tsv"))?);
    writeln!(summary, "measure\tvalue")?;
    writeln!(
        summary,
        "morphology_positive_front_before\t{}",
        prediction.morphology_before.positive_maxima.len()
    )?;
    writeln!(
        summary,
        "morphology_negative_front_before\t{}",
        prediction.morphology_before.negative_minima.len()
    )?;
    writeln!(
        summary,
        "morphology_negative_witnesses_before\t{}",
        prediction.morphology_before.negative_witnesses.len()
    )?;
    writeln!(
        summary,
        "morphology_recurrent_negative_witnesses_before\t{}",
        prediction
            .morphology_before
            .negative_witnesses
            .values()
            .filter(|multiplicity| **multiplicity >= 2)
            .count()
    )?;
    writeln!(
        summary,
        "returned_together\t{}",
        grade.counts.returned_together_relations
    )?;
    writeln!(
        summary,
        "returned_apart\t{}",
        grade.counts.returned_apart_relations
    )?;
    writeln!(
        summary,
        "forced_together_correct\t{}",
        grade.counts.forced_together_correct
    )?;
    writeln!(
        summary,
        "forced_apart_correct\t{}",
        grade.counts.forced_apart_correct
    )?;
    writeln!(
        summary,
        "returned_together_open\t{}",
        grade.counts.returned_together_open
    )?;
    writeln!(
        summary,
        "returned_apart_open\t{}",
        grade.counts.returned_apart_open
    )?;
    writeln!(
        summary,
        "returned_together_forced_apart\t{}",
        grade.counts.returned_together_forced_apart
    )?;
    writeln!(
        summary,
        "returned_apart_forced_together\t{}",
        grade.counts.returned_apart_forced_together
    )?;
    writeln!(
        summary,
        "conflicted_relations\t{}",
        grade.counts.conflicted_relations
    )?;
    writeln!(
        summary,
        "missing_section_relations\t{}",
        grade.counts.missing_section_relations
    )?;
    Ok(())
}

fn coupled_state_counts(
    prediction: &CoupledInformantPrediction,
) -> BTreeMap<CoupledInformantRelationState, usize> {
    let mut counts = BTreeMap::new();
    for relation in &prediction.relations {
        *counts.entry(relation.state).or_default() += 1;
    }
    counts
}

fn write_live_current_receipts(
    output: &Path,
    episodes: &[EpisodeResult],
) -> Result<(), Box<dyn Error>> {
    let mut writer = BufWriter::new(File::create(
        output.join("coupled-live-current-receipts.tsv"),
    )?);
    writeln!(
        writer,
        "episode\tpassage\tbefore_rank\tafter_rank\tbefore_cells\tafter_cells\tcurrents\tdirected_relations"
    )?;
    for episode in episodes {
        for (passage, receipt) in [
            ("generate", episode.generation_current),
            ("grade", episode.grade_current),
            ("admit", episode.admission_current),
        ] {
            writeln!(
                writer,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                episode.ordinal + 1,
                passage,
                receipt.before_rank,
                receipt.after_rank,
                receipt.before_cells,
                receipt.after_cells,
                receipt.currents,
                receipt.directed_relations,
            )?;
        }
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn write_coupled_summary(
    output: &Path,
    manifest: &Path,
    glm_raw: &Path,
    abi_raw: &Path,
    igra: &Path,
    total_native_events: usize,
    training_occurrences: usize,
    held_out_occurrences: usize,
    loader: &CpuExecutionReceipt,
    training_work: &ObservationEcologyWork,
    profile: &AtmosphericProfile,
    doctrine: &OpaqueThermalChordDoctrine,
    episodes: &[EpisodeResult],
    standing: &CoupledInformantStanding,
    acquisition_ms: u128,
    abi_ms: u128,
    live_device: &str,
    live_image: &LiveCurrentRestImage,
    native: &str,
    causal_body: &RelampagoCausalBodyResearch,
) -> Result<(), Box<dyn Error>> {
    let mut digest = Sha256::new();
    digest.update(native.as_bytes());
    let standing_digest = lowercase_hex(digest.finalize().as_ref());
    let mut summary = Vec::<(String, String)>::new();
    push_summary(
        &mut summary,
        "question",
        "Can successive real optical, spectral, geolocational, chronological, and atmospheric occurrences condition one recurrent intermediate morphology which generates before each native return and changes its later conduct?",
    );
    push_summary(
        &mut summary,
        "result_semantics",
        "The coupled phase face is a receiver-relative comparison over preserved source sections. A generated relation is not a lightning channel, and an IGRA thermal intersection is not an independently measured discharge altitude.",
    );
    push_summary(
        &mut summary,
        "causal_body_owner",
        "ExactCausalBodyLaw over complete event-indexed arbitrary-grade incidence",
    );
    push_summary(
        &mut summary,
        "causal_body_active_f_vector",
        format!("{:?}", causal_body.standing.active_f_vector()),
    );
    push_summary(
        &mut summary,
        "causal_body_open_boundaries",
        causal_body
            .standing
            .openings()
            .values()
            .filter(|opening| opening.state == CausalOpeningState::Open)
            .count(),
    );
    push_summary(
        &mut summary,
        "causal_body_grade_two_cells",
        causal_body
            .standing
            .active_f_vector()
            .get(&2)
            .copied()
            .unwrap_or(0),
    );
    push_summary(
        &mut summary,
        "projection_correction",
        "The former cumulative four-panel raster and video are retired. RELAMPAGO supplies grade-zero vertical-fiber holons and grade-one coupled-relation carriers only. Fundamental cycles are retained as OPEN exact boundaries unless an independent caused higher cell returns.",
    );
    push_summary(&mut summary, "live_current_device", live_device);
    push_summary(
        &mut summary,
        "live_current_lineages",
        live_image.lineages().len(),
    );
    push_summary(
        &mut summary,
        "live_current_next_lineage",
        live_image.next_lineage(),
    );
    push_summary(
        &mut summary,
        "chronology",
        "22:50--23:00 GLM groups condition the optical relation; five successive 2-minute episodes from 23:00--23:10 generate, receive ABI/profile restrictions, grade the later GLM group return, then admit that complete return before the next episode.",
    );
    push_summary(
        &mut summary,
        "coupled_coordinates",
        "4 optical differences + 5 cross-occurrence ABI band differences + 4 within-spectrum chord differences relative to band 13 + scan-departure difference + 3 vertical-fiber differences + scan-identity difference",
    );
    push_summary(
        &mut summary,
        "sparse_horizon",
        "Production traverses the optical relation horizon together with spectral local-star edges between chronologically adjacent occurrences at the same selected ABI scan/address. The complete occurrence-pair product is not enumerated.",
    );
    push_summary(
        &mut summary,
        "no_return_control",
        "The same five atmospheric resolutions also crossed a second production ecology which received no group returns. Every branch-bearing relation remained OPEN in all five episodes; missing sections remained missing.",
    );
    push_summary(
        &mut summary,
        "administrative_delivery_control",
        "Reversing source-prediction relations, occurrence delivery, contact delivery, and contact-selection delivery while preserving receiver clocks returned byte-equal coupled predictions in every episode.",
    );
    push_summary(&mut summary, "manifest", manifest.display());
    push_summary(&mut summary, "glm_raw_directory", glm_raw.display());
    push_summary(&mut summary, "abi_raw_directory", abi_raw.display());
    push_summary(&mut summary, "igra_archive", igra.display());
    push_summary(&mut summary, "total_native_glm_events", total_native_events);
    push_summary(&mut summary, "training_occurrences", training_occurrences);
    push_summary(&mut summary, "held_out_occurrences", held_out_occurrences);
    push_summary(&mut summary, "causal_episodes", episodes.len());
    push_summary(&mut summary, "atmospheric_profile_source", &profile.source);
    push_summary(
        &mut summary,
        "atmospheric_vertical_coordinate",
        format!("{:?}", profile.vertical_coordinate),
    );
    push_summary(
        &mut summary,
        "specific_gas_constant_m2_per_s2_k",
        &doctrine.specific_gas_constant,
    );
    push_summary(
        &mut summary,
        "spectral_lineage_enacted",
        "ABI bands 08/09/10/11/13, their four exact phase chords relative to band 13, independent quality flags, both native scan clocks, and the selected scan departure",
    );
    push_summary(
        &mut summary,
        "vertical_law",
        "band 13 opaque-thermal chord restricted through the separately received IGRA pressure/temperature/geopotential-height profile",
    );
    push_summary(
        &mut summary,
        "glm_to_abi_address_status",
        "imported approximate landmark under the source-declared geostationary projection; never promoted to exact world standing",
    );
    push_summary(
        &mut summary,
        "final_positive_front",
        standing.morphology.positive_maxima.len(),
    );
    push_summary(
        &mut summary,
        "final_negative_front",
        standing.morphology.negative_minima.len(),
    );
    push_summary(
        &mut summary,
        "final_exact_negative_witnesses",
        standing.morphology.negative_witnesses.len(),
    );
    push_summary(
        &mut summary,
        "final_recurrent_negative_witnesses",
        standing
            .morphology
            .negative_witnesses
            .values()
            .filter(|multiplicity| **multiplicity >= 2)
            .count(),
    );
    push_summary(
        &mut summary,
        "maximum_negative_witness_multiplicity",
        standing
            .morphology
            .negative_witnesses
            .values()
            .copied()
            .max()
            .unwrap_or(0),
    );
    push_summary(
        &mut summary,
        "negative_transport_doctrine",
        "A returned-apart phase fiber is retained exactly. Its upward envelope can obstruct positive support but cannot force separation outside that support without exact recurrence; heterogeneous spectral distance was not assumed globally monotone.",
    );
    push_summary(
        &mut summary,
        "conditioned_together_branches",
        standing.morphology.returned_together_branches,
    );
    push_summary(
        &mut summary,
        "conditioned_apart_branches",
        standing.morphology.returned_apart_branches,
    );
    push_summary(&mut summary, "native_standing_bytes", native.len());
    push_summary(&mut summary, "native_standing_sha256", &standing_digest);
    push_summary(&mut summary, "rest_remount_exact", true);
    push_summary(
        &mut summary,
        "source_lineage_retained",
        "Every atmospheric resolution retains the complete originating optical prediction, spectral occurrences, selected contacts, vertical fibers, lifted relations, and obstructions.",
    );
    push_summary(
        &mut summary,
        "remaining_physical_boundary",
        "No independent lightning-altitude, electric-field, charge-density, or dense time-resolved radiosonde receiver entered this run; thermal vertical fibers remain conditional alternatives.",
    );
    push_summary(&mut summary, "loader_tasks", &loader.tasks);
    push_summary(&mut summary, "loader_workers_used", &loader.workers_used);
    push_summary(
        &mut summary,
        "training_cuda_classified_relations",
        training_work.cuda_classified_relations,
    );
    push_summary(&mut summary, "acquisition_ms", acquisition_ms);
    push_summary(&mut summary, "abi_transduction_ms", abi_ms);
    let mut summary_writer = BufWriter::new(File::create(output.join("summary.tsv"))?);
    writeln!(summary_writer, "measure\tvalue")?;
    for (measure, value) in summary {
        writeln!(summary_writer, "{measure}\t{value}")?;
    }

    let mut episode_writer = BufWriter::new(File::create(output.join("episodes.tsv"))?);
    writeln!(
        episode_writer,
        "episode\toccurrences\toptical_relations\tcoupled_relations\toptical_horizon_relations\tspectral_local_star_relations\tshared_horizon_relations\tvertical_fibers\tlifted_relations\tinverse_obstructions\tcoupled_branches\tcontrol_open\tcontrol_missing\tpositive_front_before\tnegative_front_before\tnegative_witnesses_before\trecurrent_negative_witnesses_before\tforced_together\tforced_apart\topen\tconflicted\tmissing\treturned_together\treturned_apart\tforced_together_correct\tforced_apart_correct\tfalse_together\tfalse_apart\toptical_grade_obstructions\tprediction_cuda_relations\tgrade_cuda_relations\tcoupled_workers\tprediction_ms\tinverse_ms\tcoupled_ms"
    )?;
    for episode in episodes {
        let states = coupled_state_counts(&episode.coupled_prediction);
        writeln!(
            episode_writer,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            episode.ordinal + 1,
            episode.occurrences.len(),
            episode.optical_prediction.candidate_relations.len(),
            episode.coupled_prediction.relations.len(),
            episode.coupled_generation_work.optical_horizon_relations,
            episode
                .coupled_generation_work
                .spectral_local_star_relations,
            episode.coupled_generation_work.shared_horizon_relations,
            episode.atmospheric_resolution.vertical_fibers.len(),
            episode.atmospheric_resolution.lifted_relations.len(),
            episode.atmospheric_resolution.obstructions.len(),
            episode.coupled_generation_work.phase_branches,
            episode
                .unconditioned_control_prediction
                .relations
                .iter()
                .filter(|relation| relation.state == CoupledInformantRelationState::Open)
                .count(),
            episode
                .unconditioned_control_prediction
                .relations
                .iter()
                .filter(|relation| {
                    relation.state == CoupledInformantRelationState::MissingSection
                })
                .count(),
            episode
                .coupled_prediction
                .morphology_before
                .positive_maxima
                .len(),
            episode
                .coupled_prediction
                .morphology_before
                .negative_minima
                .len(),
            episode
                .coupled_prediction
                .morphology_before
                .negative_witnesses
                .len(),
            episode
                .coupled_prediction
                .morphology_before
                .negative_witnesses
                .values()
                .filter(|multiplicity| **multiplicity >= 2)
                .count(),
            states
                .get(&CoupledInformantRelationState::ForcedTogether)
                .copied()
                .unwrap_or(0),
            states
                .get(&CoupledInformantRelationState::ForcedApart)
                .copied()
                .unwrap_or(0),
            states
                .get(&CoupledInformantRelationState::Open)
                .copied()
                .unwrap_or(0),
            states
                .get(&CoupledInformantRelationState::Conflicted)
                .copied()
                .unwrap_or(0),
            states
                .get(&CoupledInformantRelationState::MissingSection)
                .copied()
                .unwrap_or(0),
            episode.coupled_grade.counts.returned_together_relations,
            episode.coupled_grade.counts.returned_apart_relations,
            episode.coupled_grade.counts.forced_together_correct,
            episode.coupled_grade.counts.forced_apart_correct,
            episode.coupled_grade.counts.returned_apart_forced_together,
            episode.coupled_grade.counts.returned_together_forced_apart,
            episode.optical_grade.obstructions.len(),
            episode.optical_prediction_work.cuda_classified_relations,
            episode.optical_grade_work.cuda_classified_relations,
            episode.coupled_generation_work.cpu_workers_used,
            episode.prediction_ms,
            episode.inverse_ms,
            episode.coupled_ms,
        )?;
    }
    Ok(())
}

#[allow(dead_code, clippy::too_many_arguments)]
fn write_summary(
    output: &Path,
    manifest: &Path,
    glm_raw: &Path,
    abi_raw: &Path,
    igra: &Path,
    total_native_events: usize,
    training_occurrences: usize,
    held_out_occurrences: usize,
    loader: &CpuExecutionReceipt,
    training_work: &ObservationEcologyWork,
    prediction_work: &ObservationEcologyWork,
    grade_work: &ObservationEcologyWork,
    prediction: &ReceiverRelationPrediction,
    grade: &ReceiverRelationGrade,
    profile: &AtmosphericProfile,
    doctrine: &OpaqueThermalChordDoctrine,
    resolution: &AtmosphericInverseResolution,
    acquisition_ms: u128,
    prediction_ms: u128,
    abi_ms: u128,
    inverse_ms: u128,
) -> Result<(), Box<dyn Error>> {
    let mut summary = Vec::<(String, String)>::new();
    push_summary(
        &mut summary,
        "question",
        "Can independently caused atmospheric receiver sections restrict a prior machine-generated GLM relation into a growing branched vertical topology before the native return is revealed?",
    );
    push_summary(
        &mut summary,
        "result_semantics",
        "Every listed vertical fiber is admitted by the declared opaque-thermal chord relation; none is asserted to be lightning altitude or a discharge channel.",
    );
    push_summary(&mut summary, "manifest", manifest.display());
    push_summary(&mut summary, "glm_raw_directory", glm_raw.display());
    push_summary(&mut summary, "abi_raw_directory", abi_raw.display());
    push_summary(&mut summary, "igra_archive", igra.display());
    push_summary(
        &mut summary,
        "glm_to_abi_address_status",
        "imported approximate landmark",
    );
    push_summary(
        &mut summary,
        "glm_to_abi_address_doctrine",
        "nearest ABI fixed-grid address under the source-declared GOES projection evaluated in IEEE-754 binary64; the engine does not call the address an exact world coordinate",
    );
    push_summary(&mut summary, "total_native_glm_events", total_native_events);
    push_summary(&mut summary, "training_occurrences", training_occurrences);
    push_summary(&mut summary, "held_out_occurrences", held_out_occurrences);
    push_summary(
        &mut summary,
        "generated_candidate_relations",
        prediction.candidate_relations.len(),
    );
    push_summary(
        &mut summary,
        "generated_forced_components",
        prediction.forced_components.len(),
    );
    push_summary(&mut summary, "atmospheric_profile_source", &profile.source);
    push_summary(
        &mut summary,
        "atmospheric_vertical_coordinate",
        format!("{:?}", profile.vertical_coordinate),
    );
    push_summary(
        &mut summary,
        "specific_gas_constant_m2_per_s2_k",
        &doctrine.specific_gas_constant,
    );
    push_summary(
        &mut summary,
        "specific_gas_constant_status",
        "inherited doctrine parameter, not inferred",
    );
    let layers = profile.complete_layers(doctrine)?;
    let effective_acceleration_lower = layers
        .iter()
        .map(|layer| {
            &layer
                .hydrostatic
                .effective_acceleration_metre_per_second_squared
                .lower
        })
        .min()
        .ok_or("profile emitted no hydrostatic layer")?;
    let effective_acceleration_upper = layers
        .iter()
        .map(|layer| {
            &layer
                .hydrostatic
                .effective_acceleration_metre_per_second_squared
                .upper
        })
        .max()
        .ok_or("profile emitted no hydrostatic layer")?;
    push_summary(
        &mut summary,
        "hydrostatic_effective_acceleration_lower_m_per_s2",
        effective_acceleration_lower,
    );
    push_summary(
        &mut summary,
        "hydrostatic_effective_acceleration_upper_m_per_s2",
        effective_acceleration_upper,
    );
    push_summary(
        &mut summary,
        "hydrostatic_gravity_interpretation",
        "Because IGRA supplies geopotential height, the exact hydrostatic acceleration quotient is physically useful but circular as an independent observation of local g.",
    );
    push_summary(&mut summary, "local_g_independently_identified", false);
    push_summary(&mut summary, "newton_G_identified", false);
    push_summary(
        &mut summary,
        "newton_G_missing_receivers",
        "independent geometric altitude; independently constrained source mass and geometry; calibrated acceleration/force testimony",
    );
    push_summary(
        &mut summary,
        "electrical_topology_missing_receivers",
        "independent lightning altitude return (for example LMA); electric-field or charge testimony; denser atmospheric chronology",
    );
    push_summary(
        &mut summary,
        "vertical_fibers",
        resolution.vertical_fibers.len(),
    );
    push_summary(
        &mut summary,
        "source_spectral_occurrences_retained",
        resolution.spectral_occurrences.len(),
    );
    push_summary(
        &mut summary,
        "source_spectral_contacts_retained",
        resolution
            .spectral_occurrences
            .iter()
            .map(|occurrence| occurrence.contacts.len())
            .sum::<usize>(),
    );
    push_summary(
        &mut summary,
        "selected_spectral_contacts",
        resolution.work.selected_spectral_contacts,
    );
    push_summary(
        &mut summary,
        "spectral_constraint_enacted",
        "ABI band 13 opaque-thermal chord only",
    );
    push_summary(
        &mut summary,
        "spectral_lineage_carried_not_yet_enacted",
        "ABI bands 08/09/10/11",
    );
    push_summary(
        &mut summary,
        "lifted_relations",
        resolution.lifted_relations.len(),
    );
    push_summary(&mut summary, "receiver_bodies", resolution.bodies.len());
    push_summary(
        &mut summary,
        "inverse_obstructions",
        resolution.obstructions.len(),
    );

    let mut fibers_by_testimony = BTreeMap::<ReceiverTestimonyId, usize>::new();
    let mut concurrent = 0_usize;
    let mut carried = 0_usize;
    let mut scan_ids = BTreeSet::new();
    for fiber in &resolution.vertical_fibers {
        *fibers_by_testimony.entry(fiber.testimony).or_default() += 1;
        scan_ids.insert(fiber.scan);
        match fiber.temporality {
            SpectralContactTemporality::Concurrent => concurrent += 1,
            SpectralContactTemporality::Carried => carried += 1,
        }
    }
    let zero_fibers = held_out_occurrences.saturating_sub(fibers_by_testimony.len());
    let one_fiber = fibers_by_testimony
        .values()
        .filter(|count| **count == 1)
        .count();
    let ambiguous = fibers_by_testimony
        .values()
        .filter(|count| **count > 1)
        .count();
    let maximum = fibers_by_testimony.values().copied().max().unwrap_or(0);
    push_summary(
        &mut summary,
        "occurrences_without_vertical_fiber",
        zero_fibers,
    );
    push_summary(
        &mut summary,
        "occurrences_with_one_vertical_fiber",
        one_fiber,
    );
    push_summary(
        &mut summary,
        "occurrences_with_ambiguous_vertical_fibers",
        ambiguous,
    );
    push_summary(&mut summary, "maximum_fibers_per_occurrence", maximum);
    push_summary(&mut summary, "concurrent_vertical_fibers", concurrent);
    push_summary(&mut summary, "carried_vertical_fibers", carried);
    push_summary(&mut summary, "selected_abi_scans", scan_ids.len());
    let profile_temperature_lower = layers
        .iter()
        .map(|layer| &layer.temperature_kelvin.lower)
        .min()
        .ok_or("profile emitted no temperature support")?;
    let profile_temperature_upper = layers
        .iter()
        .map(|layer| &layer.temperature_kelvin.upper)
        .max()
        .ok_or("profile emitted no temperature support")?;
    let selections = resolution
        .contact_selections
        .iter()
        .map(|selection| (selection.testimony, selection))
        .collect::<BTreeMap<_, _>>();
    let selected_thermal = resolution
        .spectral_occurrences
        .iter()
        .flat_map(|occurrence| {
            let selected = selections
                .get(&occurrence.testimony)
                .expect("resolution validation paired every selection");
            occurrence
                .contacts
                .iter()
                .filter(|contact| selected.selected_scans.contains(&contact.scan))
                .filter_map(|contact| {
                    contact
                        .brightness_temperature_kelvin
                        .get(&doctrine.thermal_band)
                })
        })
        .collect::<Vec<_>>();
    let selected_thermal_lower = selected_thermal
        .iter()
        .copied()
        .min()
        .ok_or("no selected thermal contact was retained")?;
    let selected_thermal_upper = selected_thermal
        .iter()
        .copied()
        .max()
        .ok_or("no selected thermal contact was retained")?;
    push_summary(
        &mut summary,
        "profile_temperature_lower_k",
        profile_temperature_lower,
    );
    push_summary(
        &mut summary,
        "profile_temperature_upper_k",
        profile_temperature_upper,
    );
    push_summary(
        &mut summary,
        "selected_b13_temperature_lower_k",
        selected_thermal_lower,
    );
    push_summary(
        &mut summary,
        "selected_b13_temperature_upper_k",
        selected_thermal_upper,
    );
    push_summary(
        &mut summary,
        "selected_b13_below_profile_temperature",
        selected_thermal
            .iter()
            .filter(|temperature| **temperature < profile_temperature_lower)
            .count(),
    );
    push_summary(
        &mut summary,
        "selected_b13_above_profile_temperature",
        selected_thermal
            .iter()
            .filter(|temperature| **temperature > profile_temperature_upper)
            .count(),
    );
    for kind in [
        AtmosphericObstructionKind::MissingOccurrence,
        AtmosphericObstructionKind::MissingGoodThermalContact,
        AtmosphericObstructionKind::ThermalProfileHasNoIntersection,
        AtmosphericObstructionKind::RelationEndpointHasNoVerticalFiber,
    ] {
        let count = resolution
            .obstructions
            .iter()
            .filter(|obstruction| obstruction.kind == kind)
            .count();
        push_summary(&mut summary, format!("inverse_obstruction_{kind:?}"), count);
    }
    push_summary(
        &mut summary,
        "glm_returned_together_pairs",
        grade.counts.returned_together_pairs,
    );
    push_summary(
        &mut summary,
        "glm_returned_apart_pairs",
        grade.counts.returned_apart_pairs,
    );
    push_summary(
        &mut summary,
        "glm_forced_together_correct",
        grade.counts.forced_together_correct,
    );
    push_summary(
        &mut summary,
        "glm_returned_apart_forced_together",
        grade.counts.returned_apart_forced_together,
    );
    push_summary(
        &mut summary,
        "glm_grade_obstructions",
        grade.obstructions.len(),
    );
    push_summary(&mut summary, "loader_mode", &loader.mode);
    push_summary(&mut summary, "loader_tasks", &loader.tasks);
    push_summary(&mut summary, "loader_worker_limit", &loader.worker_limit);
    push_summary(&mut summary, "loader_workers_used", &loader.workers_used);
    append_observation_work(&mut summary, "training", training_work);
    append_observation_work(&mut summary, "prediction", prediction_work);
    append_observation_work(&mut summary, "grade", grade_work);
    push_summary(&mut summary, "inverse_cpu_tasks", resolution.work.cpu_tasks);
    push_summary(
        &mut summary,
        "inverse_cpu_workers_used",
        resolution.work.cpu_workers_used,
    );
    push_summary(
        &mut summary,
        "inverse_cpu_antichains",
        resolution.work.cpu_antichains,
    );
    push_summary(&mut summary, "acquisition_ms", acquisition_ms);
    push_summary(&mut summary, "prediction_ms", prediction_ms);
    push_summary(&mut summary, "abi_transduction_ms", abi_ms);
    push_summary(&mut summary, "atmospheric_inverse_ms", inverse_ms);

    let mut writer = BufWriter::new(File::create(output.join("summary.tsv"))?);
    writeln!(writer, "measure\tvalue")?;
    for (measure, value) in summary {
        writeln!(writer, "{measure}\t{value}")?;
    }
    Ok(())
}

fn append_observation_work(
    summary: &mut Vec<(String, String)>,
    prefix: &str,
    work: &ObservationEcologyWork,
) {
    push_summary(summary, format!("{prefix}_cpu_tasks"), work.cpu_tasks);
    push_summary(
        summary,
        format!("{prefix}_cpu_workers_used"),
        work.cpu_workers_used,
    );
    push_summary(
        summary,
        format!("{prefix}_cuda_classified_relations"),
        work.cuda_classified_relations,
    );
    push_summary(
        summary,
        format!("{prefix}_cuda_returned_relations"),
        work.cuda_returned_relations,
    );
    push_summary(
        summary,
        format!("{prefix}_cuda_parity_relations"),
        work.cuda_parity_relations,
    );
    push_summary(
        summary,
        format!("{prefix}_cuda_launches"),
        work.cuda_launches,
    );
    push_summary(
        summary,
        format!("{prefix}_cuda_device"),
        work.cuda_device.as_deref().unwrap_or("none"),
    );
}

fn push_summary(summary: &mut Vec<(String, String)>, measure: impl ToString, value: impl ToString) {
    summary.push((measure.to_string(), value.to_string()));
}

fn rational_vector_text(values: &[Rat]) -> String {
    values
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(";")
}

fn integer_vector_text(values: &[u64]) -> String {
    values
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(";")
}

fn write_source_digests(
    output: &Path,
    glm_raw: &Path,
    abi_raw: &Path,
    igra: &Path,
    requests: &[ProductRequest],
) -> Result<(), Box<dyn Error>> {
    let mut sources = vec![
        ("igra", igra.to_path_buf()),
        ("glm_directory", glm_raw.to_path_buf()),
        ("abi_directory", abi_raw.to_path_buf()),
    ];
    sources.extend(requests.iter().map(|request| ("glm", request.path.clone())));
    let mut abi_paths = fs::read_dir(abi_raw)?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().and_then(|extension| extension.to_str()) == Some("nc"))
        .collect::<Vec<_>>();
    abi_paths.sort();
    sources.extend(abi_paths.into_iter().map(|path| ("abi", path)));
    let mut writer = BufWriter::new(File::create(output.join("source_digests.tsv"))?);
    writeln!(writer, "kind\tpath\tsha256")?;
    for (kind, path) in sources {
        if path.is_dir() {
            writeln!(writer, "{kind}\t{}\tdirectory", path.display())?;
        } else {
            writeln!(
                writer,
                "{kind}\t{}\t{}",
                path.display(),
                sha256_file(&path)?
            )?;
        }
    }
    Ok(())
}

fn sha256_file(path: &Path) -> Result<String, Box<dyn Error>> {
    let mut source = BufReader::new(File::open(path)?);
    let mut digest = Sha256::new();
    let mut buffer = vec![0_u8; 1024 * 1024];
    loop {
        let count = source.read(&mut buffer)?;
        if count == 0 {
            break;
        }
        digest.update(&buffer[..count]);
    }
    Ok(lowercase_hex(digest.finalize().as_ref()))
}

fn lowercase_hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        encoded.push(char::from(DIGITS[usize::from(byte >> 4)]));
        encoded.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
    }
    encoded
}

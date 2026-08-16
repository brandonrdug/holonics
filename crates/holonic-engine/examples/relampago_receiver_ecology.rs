//! Full-storm receiver-relation experiment over native GOES-16 GLM products.
//!
//! The experiment conditions the production observation ecology on three
//! hours immediately preceding the 13--14 December 2018 RELAMPAGO storm,
//! emits one relation fiber for the complete ten-hour storm before any GLM
//! parent-group return enters, grades that return, and admits it only after
//! grading.  GLM groups remain external algorithm testimony; they are never
//! called lightning channels or world cells.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs::{self, File};
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use holonic_engine::{
    CausalWorld, CpuExecutionError, CpuExecutionReceipt, CpuExecutor, EventId,
    ExactCoordinateInterval, ExistingReceiverBatch, ObservationEcologyEvent, ObservationEcologyLaw,
    ObservationEcologyStanding, ObservationEcologyWork, ReceiverAffineChart, ReceiverBatch,
    ReceiverCellReturn, ReceiverChartId, ReceiverCoordinateFamily, ReceiverCoordinateFamilyId,
    ReceiverGradeId, ReceiverLineageId, ReceiverPerspectiveAddress, ReceiverPerspectiveSpec,
    ReceiverPredictionId, ReceiverRelationObstructionKind, ReceiverTestimony, ReceiverTestimonyId,
    ReturnedAlgorithmId, ReturnedCellCoverage, ReturnedCellId, ReturnedReceiverCell,
    ReturnedReceiverCellAddress, ReturnedReceiverPartition, exact_rational_from_f32_bits,
};
use image::{DynamicImage, Rgb, RgbImage};
use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};
use relational_geometry::{Rat, ReceiverId};
use sha2::{Digest, Sha256};

const FAMILY: ReceiverCoordinateFamilyId = ReceiverCoordinateFamilyId(0x474c_4d);
const GLM_GROUP_ALGORITHM: ReturnedAlgorithmId = ReturnedAlgorithmId(0x474c_4d_4752_4f55);
const GLM_RECEIVER: ReceiverId = ReceiverId(16);
const GROUP_FAMILY: ReceiverCoordinateFamilyId = ReceiverCoordinateFamilyId(0x474c_4d_4752);
const GLM_FLASH_ALGORITHM: ReturnedAlgorithmId = ReturnedAlgorithmId(0x474c_4d_464c_4153);
const GROUP_RECEIVER: ReceiverId = ReceiverId(17);
const FLASH_FAMILY: ReceiverCoordinateFamilyId = ReceiverCoordinateFamilyId(0x474c_4d_464c);
const FLASH_RECEIVER: ReceiverId = ReceiverId(18);
const GROUP_CHART_NAMESPACE: u64 = 1_u64 << 40;
const FLASH_CHART_NAMESPACE: u64 = 2_u64 << 40;
const DYADIC_GEO_SHIFT: usize = 20;

const DEFAULT_MANIFEST: &str =
    "target/holonic-engine/relampago-lightning/manifests/glm_relampago_full_window.keys";
const DEFAULT_RAW: &str = "target/holonic-engine/relampago-lightning/raw/glm";
const DEFAULT_OUTPUT: &str =
    "target/holonic-engine/relampago-lightning/receiver-relation-experiment";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Split {
    Training,
    HeldOut,
    OutsideExperiment,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ExperimentProfile {
    FullStorm,
    ReceiverDynamics,
}

impl ExperimentProfile {
    fn parse(value: Option<&str>) -> Result<Self, Box<dyn Error>> {
        match value {
            None | Some("full-storm") => Ok(Self::FullStorm),
            Some("receiver-dynamics") => Ok(Self::ReceiverDynamics),
            Some(other) => Err(format!(
                "unknown experiment profile {other:?}; expected full-storm or receiver-dynamics"
            )
            .into()),
        }
    }

    fn carries_native_hierarchy(self) -> bool {
        self == Self::ReceiverDynamics
    }
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
    fn split(&self, profile: ExperimentProfile) -> Split {
        match profile {
            ExperimentProfile::FullStorm => match (self.year, self.day, self.hour) {
                (2018, 347, 20..=22) => Split::Training,
                (2018, 347, 23) | (2018, 348, 0..=8) => Split::HeldOut,
                _ => Split::OutsideExperiment,
            },
            ExperimentProfile::ReceiverDynamics => {
                match (self.year, self.day, self.hour, self.minute) {
                    (2018, 347, 22, 50..=59) => Split::Training,
                    (2018, 347, 23, 0..=9) => Split::HeldOut,
                    _ => Split::OutsideExperiment,
                }
            }
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
}

#[derive(Clone, Debug)]
struct LoadedProduct {
    split: Split,
    chart: ReceiverAffineChart,
    occurrences: Vec<ReceiverTestimony>,
    cells: BTreeMap<ReturnedCellId, BTreeSet<ReceiverTestimonyId>>,
    hierarchy: Option<LoadedHierarchyProduct>,
    total_events: usize,
}

#[derive(Clone, Debug)]
struct LoadedHierarchyProduct {
    group_chart: ReceiverAffineChart,
    flash_chart: ReceiverAffineChart,
    groups: Vec<ReceiverTestimony>,
    flashes: Vec<ReceiverTestimony>,
    flash_cells: BTreeMap<ReturnedCellId, BTreeSet<ReceiverTestimonyId>>,
    group_returns: Vec<ReceiverCellReturn>,
    flash_returns: Vec<ReceiverCellReturn>,
}

#[derive(Clone, Debug)]
struct ProductRequest {
    key: String,
    time: ProductTime,
    chart: ReceiverChartId,
    path: PathBuf,
}

#[derive(Clone, Debug, Default)]
struct ProductReceipt {
    key: String,
    split: String,
    total_events: usize,
    aperture_events: usize,
    aperture_groups: usize,
    aperture_flashes: usize,
}

fn main() -> Result<(), Box<dyn Error>> {
    let arguments = std::env::args().skip(1).collect::<Vec<_>>();
    let manifest = PathBuf::from(
        arguments
            .first()
            .map(String::as_str)
            .unwrap_or(DEFAULT_MANIFEST),
    );
    let raw_directory = PathBuf::from(arguments.get(1).map(String::as_str).unwrap_or(DEFAULT_RAW));
    let output_directory = PathBuf::from(
        arguments
            .get(2)
            .map(String::as_str)
            .unwrap_or(DEFAULT_OUTPUT),
    );
    let profile = ExperimentProfile::parse(arguments.get(3).map(String::as_str))?;
    let carries_hierarchy = profile.carries_native_hierarchy();
    fs::create_dir_all(&output_directory)?;

    let aperture = relampago_aperture();
    let family = ReceiverCoordinateFamily::new(
        FAMILY,
        vec![
            "reported latitude".to_owned(),
            "reported longitude".to_owned(),
            "receiver clock".to_owned(),
            "reported radiant energy".to_owned(),
            "receiver product aperture".to_owned(),
        ],
        match profile {
            ExperimentProfile::FullStorm => vec![0, 1, 2],
            ExperimentProfile::ReceiverDynamics => vec![0, 1, 2, 3],
        },
        vec![4],
    )?;
    let workers = std::thread::available_parallelism()
        .unwrap_or_else(|_| NonZeroUsize::new(1).expect("one is nonzero"));
    let mut world = CausalWorld::new(
        ObservationEcologyLaw::multicore_cuda(workers),
        ObservationEcologyStanding::default(),
    );
    let mut next_event = 1_u64;
    world.receive(&ObservationEcologyEvent::DeclareFamily {
        event: take_event(&mut next_event),
        family,
    })?;
    if carries_hierarchy {
        declare_hierarchy_families(&mut world, &mut next_event)?;
    }

    let keys = read_manifest(&manifest)?;
    let mut next_testimony = 1_u64;
    let mut training_occurrences = Vec::new();
    let mut held_out_occurrences = Vec::new();
    let mut training_cells = BTreeMap::<ReturnedCellId, BTreeSet<ReceiverTestimonyId>>::new();
    let mut held_out_cells = BTreeMap::<ReturnedCellId, BTreeSet<ReceiverTestimonyId>>::new();
    let mut training_groups = Vec::new();
    let mut held_out_groups = Vec::new();
    let mut training_flashes = Vec::new();
    let mut held_out_flashes = Vec::new();
    let mut training_flash_cells = BTreeMap::<ReturnedCellId, BTreeSet<ReceiverTestimonyId>>::new();
    let mut held_out_flash_cells = BTreeMap::<ReturnedCellId, BTreeSet<ReceiverTestimonyId>>::new();
    let mut training_group_returns = Vec::new();
    let mut held_out_group_returns = Vec::new();
    let mut training_flash_returns = Vec::new();
    let mut held_out_flash_returns = Vec::new();
    let mut product_receipts = Vec::new();
    let acquisition_started = Instant::now();
    let requests = keys
        .iter()
        .enumerate()
        .map(|(ordinal, key)| {
            let product_time = parse_product_time(key)?;
            if product_time.split(profile) == Split::OutsideExperiment {
                return Ok(None);
            }
            let chart_id = ReceiverChartId(
                u64::try_from(ordinal)
                    .map_err(|_| "chart ordinal overflow")?
                    .checked_add(1)
                    .ok_or("chart ordinal overflow")?,
            );
            let path = raw_directory.join(
                Path::new(key)
                    .file_name()
                    .ok_or("manifest key has no filename")?,
            );
            Ok(Some(ProductRequest {
                key: key.clone(),
                time: product_time,
                chart: chart_id,
                path,
            }))
        })
        .collect::<Result<Vec<_>, Box<dyn Error>>>()?
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    let loader = CpuExecutor::multicore(workers);
    let (loaded_products, loader_receipt) = loader
        .execute_indexed(&requests, |_index, request| {
            load_product(
                &request.key,
                &request.path,
                request.chart,
                &request.time,
                &aperture,
                profile,
            )
            .map_err(|error| error.to_string())
        })
        .map_err(|error| match error {
            CpuExecutionError::Operation(error) => error,
            CpuExecutionError::WorkerPanicked => {
                "one native GLM import worker panicked before rejoining".to_owned()
            }
        })?;

    for (request, mut loaded) in requests.iter().zip(loaded_products) {
        rebase_testimonies(&mut loaded, &mut next_testimony)?;
        world.receive(&ObservationEcologyEvent::DeclareChart {
            event: take_event(&mut next_event),
            chart: loaded.chart,
        })?;
        if let Some(hierarchy) = loaded.hierarchy.as_ref() {
            world.receive(&ObservationEcologyEvent::DeclareChart {
                event: take_event(&mut next_event),
                chart: hierarchy.group_chart.clone(),
            })?;
            world.receive(&ObservationEcologyEvent::DeclareChart {
                event: take_event(&mut next_event),
                chart: hierarchy.flash_chart.clone(),
            })?;
        }
        let aperture_flashes = loaded
            .hierarchy
            .as_ref()
            .map_or(0, |hierarchy| hierarchy.flashes.len());
        let split_name = match loaded.split {
            Split::Training => {
                training_occurrences.extend(loaded.occurrences.iter().cloned());
                merge_cells(&mut training_cells, loaded.cells.clone());
                if let Some(hierarchy) = loaded.hierarchy.take() {
                    training_groups.extend(hierarchy.groups);
                    training_flashes.extend(hierarchy.flashes);
                    merge_cells(&mut training_flash_cells, hierarchy.flash_cells);
                    training_group_returns.extend(hierarchy.group_returns);
                    training_flash_returns.extend(hierarchy.flash_returns);
                }
                "training"
            }
            Split::HeldOut => {
                held_out_occurrences.extend(loaded.occurrences.iter().cloned());
                merge_cells(&mut held_out_cells, loaded.cells.clone());
                if let Some(hierarchy) = loaded.hierarchy.take() {
                    held_out_groups.extend(hierarchy.groups);
                    held_out_flashes.extend(hierarchy.flashes);
                    merge_cells(&mut held_out_flash_cells, hierarchy.flash_cells);
                    held_out_group_returns.extend(hierarchy.group_returns);
                    held_out_flash_returns.extend(hierarchy.flash_returns);
                }
                "held-out"
            }
            Split::OutsideExperiment => unreachable!("outside products were skipped"),
        };
        product_receipts.push(ProductReceipt {
            key: request.key.clone(),
            split: split_name.to_owned(),
            total_events: loaded.total_events,
            aperture_events: loaded.occurrences.len(),
            aperture_groups: loaded.cells.len(),
            aperture_flashes,
        });
    }
    let acquisition_elapsed = acquisition_started.elapsed();
    write_product_receipts(&output_directory, &product_receipts)?;

    let training_batch = ReceiverBatch {
        family: FAMILY,
        chronology: 0,
        source: match profile {
            ExperimentProfile::FullStorm => {
                "GOES-16 GLM L2 LCFA, 2018 day 347 20:00--23:00 UTC".to_owned()
            }
            ExperimentProfile::ReceiverDynamics => {
                "GOES-16 GLM L2 LCFA, 2018 day 347 22:50--23:00 UTC".to_owned()
            }
        },
        aperture: aperture.clone(),
        occurrences: training_occurrences,
    };
    let training_partition = partition(GLM_GROUP_ALGORITHM, training_cells);
    let training_started = Instant::now();
    let training_partition_event = take_event(&mut next_event);
    let training_receipt = world.receive(&ObservationEcologyEvent::ConditionReturnedBatch {
        event: training_partition_event,
        batch: training_batch,
        returned: training_partition,
    })?;
    let training_elapsed = training_started.elapsed();
    let training_work = training_receipt.radiation[0].work.clone();
    let mut hierarchy_training_work = Vec::<(&'static str, ObservationEcologyWork)>::new();
    let mut training_flash_partition_event = None;
    if carries_hierarchy {
        let event = take_event(&mut next_event);
        let receipt = world.receive(&ObservationEcologyEvent::ReturnPartitionAsReceivers {
            event,
            partition_event: training_partition_event,
            upper_batch: ReceiverBatch {
                family: GROUP_FAMILY,
                chronology: 0,
                source: "native GLM group faces returned from the 22:50--23:00 event cells"
                    .to_owned(),
                aperture: Vec::new(),
                occurrences: training_groups.clone(),
            },
            returns: training_group_returns,
        })?;
        hierarchy_training_work.push(("training_group_return", receipt.radiation[0].work.clone()));

        let event = take_event(&mut next_event);
        let receipt = world.receive(&ObservationEcologyEvent::ConditionExistingReceiverBatch {
            event,
            batch: existing_batch(
                GROUP_FAMILY,
                0,
                "native GLM group receivers conditioned by later flash return",
                &training_groups,
            ),
            returned: partition(GLM_FLASH_ALGORITHM, training_flash_cells),
        })?;
        training_flash_partition_event = Some(event);
        hierarchy_training_work.push((
            "training_flash_condition",
            receipt.radiation[0].work.clone(),
        ));

        let event = take_event(&mut next_event);
        let receipt = world.receive(&ObservationEcologyEvent::ReturnPartitionAsReceivers {
            event,
            partition_event: training_flash_partition_event
                .expect("training flash partition event was just caused"),
            upper_batch: ReceiverBatch {
                family: FLASH_FAMILY,
                chronology: 0,
                source: "native GLM flash faces returned from the 22:50--23:00 group cells"
                    .to_owned(),
                aperture: Vec::new(),
                occurrences: training_flashes,
            },
            returns: training_flash_returns,
        })?;
        hierarchy_training_work.push(("training_flash_return", receipt.radiation[0].work.clone()));
    }

    let held_out_batch = ReceiverBatch {
        family: FAMILY,
        chronology: 1,
        source: match profile {
            ExperimentProfile::FullStorm => {
                "GOES-16 GLM L2 LCFA, complete RELAMPAGO storm 2018-12-13 23:00--2018-12-14 09:00 UTC"
                    .to_owned()
            }
            ExperimentProfile::ReceiverDynamics => {
                "GOES-16 GLM L2 LCFA, held-out 2018 day 347 23:00--23:10 UTC".to_owned()
            }
        },
        aperture: aperture.clone(),
        occurrences: held_out_occurrences,
    };
    let held_out_partition = partition(GLM_GROUP_ALGORITHM, held_out_cells);
    let prediction_started = Instant::now();
    let prediction_receipt =
        world.receive(&ObservationEcologyEvent::PredictUnpartitionedBatch {
            event: take_event(&mut next_event),
            algorithm: GLM_GROUP_ALGORITHM,
            batch: held_out_batch,
        })?;
    let prediction_elapsed = prediction_started.elapsed();
    let prediction = prediction_receipt.radiation[0]
        .prediction
        .as_ref()
        .ok_or("prediction event emitted no prediction")?;
    let prediction_id = prediction.id;
    let prediction_work = prediction_receipt.radiation[0].work.clone();
    write_prediction(&output_directory, prediction)?;

    let grade_started = Instant::now();
    let grade_receipt = world.receive(&ObservationEcologyEvent::GradeReturnedPartition {
        event: take_event(&mut next_event),
        prediction: prediction_id,
        returned: held_out_partition,
    })?;
    let grade_elapsed = grade_started.elapsed();
    let grade = grade_receipt.radiation[0]
        .grade
        .as_ref()
        .ok_or("grade event emitted no grade")?;
    let grade_id = grade.id;
    let grade_work = grade_receipt.radiation[0].work.clone();
    write_grade(&output_directory, grade)?;

    let admitted_before = world.standing().admitted_testimony_count();
    let admission_started = Instant::now();
    let held_out_group_partition_event = take_event(&mut next_event);
    let admission_receipt = world.receive(&ObservationEcologyEvent::AdmitGradedReturn {
        event: held_out_group_partition_event,
        grade: grade_id,
    })?;
    let admission_elapsed = admission_started.elapsed();
    let admission_work = admission_receipt.radiation[0].work.clone();
    let admitted_after = world.standing().admitted_testimony_count();

    let mut flash_prediction_id = None;
    let mut flash_grade_id = None;
    let mut held_out_flash_partition_event = None;
    let mut hierarchy_held_out_work = Vec::<(&'static str, ObservationEcologyWork)>::new();
    if carries_hierarchy {
        let event = take_event(&mut next_event);
        let receipt = world.receive(&ObservationEcologyEvent::ReturnPartitionAsReceivers {
            event,
            partition_event: held_out_group_partition_event,
            upper_batch: ReceiverBatch {
                family: GROUP_FAMILY,
                chronology: 1,
                source: "native GLM group faces returned from the held-out event cells".to_owned(),
                aperture: Vec::new(),
                occurrences: held_out_groups.clone(),
            },
            returns: held_out_group_returns,
        })?;
        hierarchy_held_out_work.push(("held_out_group_return", receipt.radiation[0].work.clone()));

        let prediction_receipt =
            world.receive(&ObservationEcologyEvent::PredictExistingReceiverBatch {
                event: take_event(&mut next_event),
                algorithm: GLM_FLASH_ALGORITHM,
                batch: existing_batch(
                    GROUP_FAMILY,
                    1,
                    "held-out native GLM group receivers before flash return",
                    &held_out_groups,
                ),
            })?;
        let prediction = prediction_receipt.radiation[0]
            .prediction
            .as_ref()
            .ok_or("group receiver prediction emitted no flash prediction")?;
        let current_flash_prediction = prediction.id;
        flash_prediction_id = Some(current_flash_prediction);
        write_named_prediction(&output_directory, "flash", prediction)?;
        hierarchy_held_out_work.push((
            "flash_prediction",
            prediction_receipt.radiation[0].work.clone(),
        ));

        let grade_receipt = world.receive(&ObservationEcologyEvent::GradeReturnedPartition {
            event: take_event(&mut next_event),
            prediction: current_flash_prediction,
            returned: partition(GLM_FLASH_ALGORITHM, held_out_flash_cells),
        })?;
        let grade = grade_receipt.radiation[0]
            .grade
            .as_ref()
            .ok_or("native flash return emitted no receiver grade")?;
        let current_flash_grade = grade.id;
        flash_grade_id = Some(current_flash_grade);
        write_named_grade(&output_directory, "flash", grade)?;
        hierarchy_held_out_work.push(("flash_grade", grade_receipt.radiation[0].work.clone()));

        let event = take_event(&mut next_event);
        let receipt = world.receive(&ObservationEcologyEvent::AdmitGradedReturn {
            event,
            grade: current_flash_grade,
        })?;
        held_out_flash_partition_event = Some(event);
        hierarchy_held_out_work.push(("flash_admission", receipt.radiation[0].work.clone()));

        let receipt = world.receive(&ObservationEcologyEvent::ReturnPartitionAsReceivers {
            event: take_event(&mut next_event),
            partition_event: event,
            upper_batch: ReceiverBatch {
                family: FLASH_FAMILY,
                chronology: 1,
                source: "native GLM flash faces returned from the held-out group cells".to_owned(),
                aperture: Vec::new(),
                occurrences: held_out_flashes,
            },
            returns: held_out_flash_returns,
        })?;
        hierarchy_held_out_work.push(("held_out_flash_return", receipt.radiation[0].work.clone()));
    }
    world.standing().validate()?;

    write_fronts(&output_directory, world.standing())?;
    if carries_hierarchy {
        let flash_prediction =
            flash_prediction_id.ok_or("receiver dynamics omitted its flash prediction")?;
        let flash_grade = flash_grade_id.ok_or("receiver dynamics omitted its flash grade")?;
        let training_flash_partition = training_flash_partition_event
            .ok_or("receiver dynamics omitted its training flash partition")?;
        let held_out_flash_partition = held_out_flash_partition_event
            .ok_or("receiver dynamics omitted its held-out flash partition")?;
        write_hierarchy_fronts(&output_directory, world.standing())?;
        write_receiver_perspectives(
            &output_directory,
            world.standing(),
            &[
                (
                    "training-group",
                    training_partition_event,
                    2_u32,
                    vec![0, 1, 2],
                ),
                (
                    "training-flash",
                    training_flash_partition,
                    2_u32,
                    vec![0, 1, 2, 3, 4],
                ),
                (
                    "held-out-group",
                    held_out_group_partition_event,
                    2_u32,
                    vec![0, 1, 2],
                ),
                (
                    "held-out-flash",
                    held_out_flash_partition,
                    2_u32,
                    vec![0, 1, 2, 3, 4],
                ),
            ],
        )?;
        write_receiver_dynamics_summary(
            &output_directory,
            world.standing(),
            prediction_id,
            grade_id,
            flash_prediction,
            flash_grade,
            &hierarchy_training_work,
            &hierarchy_held_out_work,
        )?;
        render_receiver_dynamics(
            &output_directory,
            world.standing(),
            prediction_id,
            flash_prediction,
            held_out_group_partition_event,
            held_out_flash_partition,
            &aperture,
        )?;
    }
    write_summary(
        &output_directory,
        &manifest,
        &raw_directory,
        &product_receipts,
        prediction_id,
        grade_id,
        admitted_before,
        admitted_after,
        acquisition_elapsed.as_millis(),
        training_elapsed.as_millis(),
        prediction_elapsed.as_millis(),
        grade_elapsed.as_millis(),
        admission_elapsed.as_millis(),
        &loader_receipt,
        &[
            ("training", &training_work),
            ("prediction", &prediction_work),
            ("grade", &grade_work),
            ("admission", &admission_work),
        ],
        world.standing(),
    )?;
    write_standing_digest(&output_directory, world.standing())?;

    println!(
        "products={} training_events={} held_out_events={} candidate_relations={} obstructions={} admitted={} cpu_workers={} cuda_pairs={} cuda_launches={}",
        product_receipts.len(),
        admitted_before,
        admitted_after - admitted_before,
        world.standing().predictions[&prediction_id]
            .candidate_relations
            .len(),
        world.standing().grades[&grade_id].obstructions.len(),
        admitted_after,
        prediction_work
            .cpu_workers_used
            .max(grade_work.cpu_workers_used),
        prediction_work.cuda_classified_relations + grade_work.cuda_classified_relations,
        prediction_work.cuda_launches + grade_work.cuda_launches,
    );
    Ok(())
}

fn take_event(next: &mut u64) -> EventId {
    let event = EventId(*next);
    *next = next.checked_add(1).expect("experiment event carrier");
    event
}

fn declare_hierarchy_families(
    world: &mut CausalWorld<ObservationEcologyLaw>,
    next_event: &mut u64,
) -> Result<(), Box<dyn Error>> {
    world.receive(&ObservationEcologyEvent::DeclareFamily {
        event: take_event(next_event),
        family: ReceiverCoordinateFamily::new(
            GROUP_FAMILY,
            vec![
                "reported group latitude".to_owned(),
                "reported group longitude".to_owned(),
                "receiver group clock".to_owned(),
                "reported group area".to_owned(),
                "reported group radiant energy".to_owned(),
                "receiver product aperture".to_owned(),
            ],
            vec![0, 1, 2, 3, 4],
            vec![5],
        )?,
    })?;
    world.receive(&ObservationEcologyEvent::DeclareFamily {
        event: take_event(next_event),
        family: ReceiverCoordinateFamily::new(
            FLASH_FAMILY,
            vec![
                "reported flash latitude".to_owned(),
                "reported flash longitude".to_owned(),
                "receiver flash first-event clock".to_owned(),
                "receiver flash last-event clock".to_owned(),
                "reported flash area".to_owned(),
                "reported flash radiant energy".to_owned(),
                "receiver product aperture".to_owned(),
            ],
            vec![0, 1, 2, 3, 4, 5],
            vec![6],
        )?,
    })?;
    Ok(())
}

fn existing_batch(
    family: ReceiverCoordinateFamilyId,
    chronology: u64,
    source: &str,
    occurrences: &[ReceiverTestimony],
) -> ExistingReceiverBatch {
    ExistingReceiverBatch {
        family,
        chronology,
        source: source.to_owned(),
        aperture: Vec::new(),
        occurrences: occurrences.iter().map(|occurrence| occurrence.id).collect(),
    }
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
    let marker = key.find("_s").ok_or("GLM key has no start marker")? + 2;
    let encoded = key
        .get(marker..marker + 14)
        .ok_or("GLM key has a malformed start marker")?;
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

fn load_product(
    key: &str,
    path: &Path,
    chart_id: ReceiverChartId,
    product_time: &ProductTime,
    aperture: &[ExactCoordinateInterval],
    profile: ExperimentProfile,
) -> Result<LoadedProduct, Box<dyn Error>> {
    let dumped = dump_native_product(path, chart_id, profile.carries_native_hierarchy())?;
    let hierarchy_dump = dumped.hierarchy;
    let latitude = dumped.latitude;
    let longitude = dumped.longitude;
    let time = dumped.time;
    let energy = dumped.energy;
    let event_ids = dumped.event_ids;
    let parent_groups = dumped.parent_groups;
    let extent = latitude.raw.len();
    if [
        longitude.raw.len(),
        time.raw.len(),
        energy.raw.len(),
        event_ids.len(),
        parent_groups.len(),
    ]
    .iter()
    .any(|candidate| *candidate != extent)
    {
        return Err("GLM event datasets have different extents".into());
    }

    let absolute_clock_offset = product_time.seconds_from_training_day() + &time.offset;
    let chart = ReceiverAffineChart::new(
        chart_id,
        GLM_RECEIVER,
        FAMILY,
        key,
        vec![
            "packed event latitude".to_owned(),
            "packed event longitude".to_owned(),
            "packed event time".to_owned(),
            "packed event energy".to_owned(),
        ],
        vec![
            latitude.offset.clone(),
            longitude.offset.clone(),
            absolute_clock_offset,
            energy.offset.clone(),
            Rat::from_integer(BigInt::from(chart_id.0)),
        ],
        packed_basis([
            latitude.scale.clone(),
            longitude.scale.clone(),
            time.scale.clone(),
            energy.scale.clone(),
        ]),
    )?;

    let mut occurrences = Vec::new();
    let mut cells = BTreeMap::<ReturnedCellId, BTreeSet<ReceiverTestimonyId>>::new();
    for index in 0..extent {
        let lat = &latitude.offset
            + &latitude.scale * Rat::from_integer(BigInt::from(latitude.raw[index]));
        let lon = &longitude.offset
            + &longitude.scale * Rat::from_integer(BigInt::from(longitude.raw[index]));
        if lat < aperture[0].lower
            || lat > aperture[0].upper
            || lon < aperture[1].lower
            || lon > aperture[1].upper
        {
            continue;
        }
        let testimony = ReceiverTestimonyId(
            u64::try_from(occurrences.len())
                .map_err(|_| "testimony carrier overflow")?
                .checked_add(1)
                .ok_or("testimony carrier overflow")?,
        );
        occurrences.push(ReceiverTestimony {
            id: testimony,
            receiver: GLM_RECEIVER,
            lineage: ReceiverLineageId(u64::from(product_time.day)),
            chart: chart_id,
            source_identity: event_ids[index],
            raw: vec![
                latitude.raw[index],
                longitude.raw[index],
                time.raw[index],
                energy.raw[index],
            ],
        });
        let cell = ReturnedCellId(
            chart_id
                .0
                .checked_shl(32)
                .ok_or("returned cell carrier overflow")?
                | parent_groups[index],
        );
        cells.entry(cell).or_default().insert(testimony);
    }
    let hierarchy = hierarchy_dump
        .map(|dump| build_loaded_hierarchy(key, chart_id, product_time, dump, &cells))
        .transpose()?;
    Ok(LoadedProduct {
        split: product_time.split(profile),
        chart,
        occurrences,
        cells,
        hierarchy,
        total_events: extent,
    })
}

fn build_loaded_hierarchy(
    key: &str,
    event_chart: ReceiverChartId,
    product_time: &ProductTime,
    dump: NativeHierarchyDump,
    event_cells: &BTreeMap<ReturnedCellId, BTreeSet<ReceiverTestimonyId>>,
) -> Result<LoadedHierarchyProduct, Box<dyn Error>> {
    let group_extent = dump.group_ids.len();
    if [
        dump.group_latitude_bits.len(),
        dump.group_longitude_bits.len(),
        dump.group_time.raw.len(),
        dump.group_area.raw.len(),
        dump.group_energy.raw.len(),
        dump.group_parent_flashes.len(),
    ]
    .iter()
    .any(|extent| *extent != group_extent)
    {
        return Err("native GLM group datasets have different extents".into());
    }
    let flash_extent = dump.flash_ids.len();
    if [
        dump.flash_latitude_bits.len(),
        dump.flash_longitude_bits.len(),
        dump.flash_first_time.raw.len(),
        dump.flash_last_time.raw.len(),
        dump.flash_area.raw.len(),
        dump.flash_energy.raw.len(),
    ]
    .iter()
    .any(|extent| *extent != flash_extent)
    {
        return Err("native GLM flash datasets have different extents".into());
    }

    let group_chart_id = ReceiverChartId(
        GROUP_CHART_NAMESPACE
            .checked_add(event_chart.0)
            .ok_or("group chart carrier overflow")?,
    );
    let flash_chart_id = ReceiverChartId(
        FLASH_CHART_NAMESPACE
            .checked_add(event_chart.0)
            .ok_or("flash chart carrier overflow")?,
    );
    let dyadic_scale = Rat::new(BigInt::from(1), BigInt::from(1_u64 << DYADIC_GEO_SHIFT));
    let product_clock = product_time.seconds_from_training_day();
    let group_chart = ReceiverAffineChart::new(
        group_chart_id,
        GROUP_RECEIVER,
        GROUP_FAMILY,
        format!("{key} native group receiver faces"),
        vec![
            "exact dyadic group latitude".to_owned(),
            "exact dyadic group longitude".to_owned(),
            "packed group time".to_owned(),
            "packed group area".to_owned(),
            "packed group energy".to_owned(),
        ],
        vec![
            Rat::zero(),
            Rat::zero(),
            &product_clock + &dump.group_time.offset,
            dump.group_area.offset.clone(),
            dump.group_energy.offset.clone(),
            Rat::from_integer(BigInt::from(event_chart.0)),
        ],
        diagonal_basis(vec![
            dyadic_scale.clone(),
            dyadic_scale.clone(),
            dump.group_time.scale.clone(),
            dump.group_area.scale.clone(),
            dump.group_energy.scale.clone(),
        ]),
    )?;
    let flash_chart = ReceiverAffineChart::new(
        flash_chart_id,
        FLASH_RECEIVER,
        FLASH_FAMILY,
        format!("{key} native flash receiver faces"),
        vec![
            "exact dyadic flash latitude".to_owned(),
            "exact dyadic flash longitude".to_owned(),
            "packed flash first-event time".to_owned(),
            "packed flash last-event time".to_owned(),
            "packed flash area".to_owned(),
            "packed flash energy".to_owned(),
        ],
        vec![
            Rat::zero(),
            Rat::zero(),
            &product_clock + &dump.flash_first_time.offset,
            &product_clock + &dump.flash_last_time.offset,
            dump.flash_area.offset.clone(),
            dump.flash_energy.offset.clone(),
            Rat::from_integer(BigInt::from(event_chart.0)),
        ],
        diagonal_basis(vec![
            dyadic_scale.clone(),
            dyadic_scale,
            dump.flash_first_time.scale.clone(),
            dump.flash_last_time.scale.clone(),
            dump.flash_area.scale.clone(),
            dump.flash_energy.scale.clone(),
        ]),
    )?;

    let requested_groups = event_cells
        .keys()
        .map(|cell| cell.0 & u64::from(u32::MAX))
        .collect::<BTreeSet<_>>();
    let group_indices = dump
        .group_ids
        .iter()
        .enumerate()
        .map(|(index, id)| (*id, index))
        .collect::<BTreeMap<_, _>>();
    if requested_groups
        .iter()
        .any(|group| !group_indices.contains_key(group))
    {
        return Err("an aperture event cell has no native GLM group face".into());
    }
    let mut groups = Vec::with_capacity(requested_groups.len());
    let mut group_by_cell = BTreeMap::new();
    let mut flash_cells = BTreeMap::<ReturnedCellId, BTreeSet<ReceiverTestimonyId>>::new();
    for group in requested_groups {
        let index = group_indices[&group];
        let id = ReceiverTestimonyId(
            u64::try_from(groups.len())
                .map_err(|_| "group testimony carrier overflow")?
                .checked_add(1)
                .ok_or("group testimony carrier overflow")?,
        );
        let source_cell = composite_cell(event_chart, group)?;
        let flash_cell = composite_cell(event_chart, dump.group_parent_flashes[index])?;
        groups.push(ReceiverTestimony {
            id,
            receiver: GROUP_RECEIVER,
            lineage: ReceiverLineageId(u64::from(product_time.day)),
            chart: group_chart_id,
            source_identity: source_cell.0,
            raw: vec![
                f32_dyadic_carrier(dump.group_latitude_bits[index])?,
                f32_dyadic_carrier(dump.group_longitude_bits[index])?,
                dump.group_time.raw[index],
                dump.group_area.raw[index],
                dump.group_energy.raw[index],
            ],
        });
        group_by_cell.insert(source_cell, id);
        flash_cells.entry(flash_cell).or_default().insert(id);
    }
    let group_returns = event_cells
        .keys()
        .map(|cell| {
            Ok(ReceiverCellReturn {
                source_cell: *cell,
                target: *group_by_cell
                    .get(cell)
                    .ok_or("event cell omitted its native group face")?,
            })
        })
        .collect::<Result<Vec<_>, Box<dyn Error>>>()?;

    let flash_indices = dump
        .flash_ids
        .iter()
        .enumerate()
        .map(|(index, id)| (*id, index))
        .collect::<BTreeMap<_, _>>();
    let mut flashes = Vec::with_capacity(flash_cells.len());
    let mut flash_by_cell = BTreeMap::new();
    for cell in flash_cells.keys() {
        let flash = cell.0 & u64::from(u32::MAX);
        let index = *flash_indices
            .get(&flash)
            .ok_or("an aperture group cell has no native GLM flash face")?;
        let id = ReceiverTestimonyId(
            u64::try_from(flashes.len())
                .map_err(|_| "flash testimony carrier overflow")?
                .checked_add(1)
                .ok_or("flash testimony carrier overflow")?,
        );
        flashes.push(ReceiverTestimony {
            id,
            receiver: FLASH_RECEIVER,
            lineage: ReceiverLineageId(u64::from(product_time.day)),
            chart: flash_chart_id,
            source_identity: cell.0,
            raw: vec![
                f32_dyadic_carrier(dump.flash_latitude_bits[index])?,
                f32_dyadic_carrier(dump.flash_longitude_bits[index])?,
                dump.flash_first_time.raw[index],
                dump.flash_last_time.raw[index],
                dump.flash_area.raw[index],
                dump.flash_energy.raw[index],
            ],
        });
        flash_by_cell.insert(*cell, id);
    }
    let flash_returns = flash_cells
        .keys()
        .map(|cell| {
            Ok(ReceiverCellReturn {
                source_cell: *cell,
                target: *flash_by_cell
                    .get(cell)
                    .ok_or("group cell omitted its native flash face")?,
            })
        })
        .collect::<Result<Vec<_>, Box<dyn Error>>>()?;

    Ok(LoadedHierarchyProduct {
        group_chart,
        flash_chart,
        groups,
        flashes,
        flash_cells,
        group_returns,
        flash_returns,
    })
}

fn composite_cell(
    event_chart: ReceiverChartId,
    local_identity: u64,
) -> Result<ReturnedCellId, Box<dyn Error>> {
    if local_identity > u64::from(u32::MAX) {
        return Err("native GLM local identity exceeds the composite cell carrier".into());
    }
    Ok(ReturnedCellId(
        event_chart
            .0
            .checked_shl(32)
            .ok_or("returned cell carrier overflow")?
            | local_identity,
    ))
}

fn f32_dyadic_carrier(bits: u32) -> Result<i64, Box<dyn Error>> {
    let scaled = exact_rational_from_f32_bits(bits)?
        * Rat::from_integer(BigInt::from(1_u64 << DYADIC_GEO_SHIFT));
    if scaled.denom() != &BigInt::from(1) {
        return Err("GLM f32 coordinate exceeds the declared dyadic carrier".into());
    }
    scaled
        .numer()
        .to_i64()
        .ok_or_else(|| "GLM dyadic coordinate exceeds i64".into())
}

fn rebase_testimonies(
    loaded: &mut LoadedProduct,
    next_testimony: &mut u64,
) -> Result<(), Box<dyn Error>> {
    let rebase = rebase_occurrences(&mut loaded.occurrences, next_testimony)?;
    for members in loaded.cells.values_mut() {
        rebase_members(members, &rebase)?;
    }
    if let Some(hierarchy) = loaded.hierarchy.as_mut() {
        let group_rebase = rebase_occurrences(&mut hierarchy.groups, next_testimony)?;
        for members in hierarchy.flash_cells.values_mut() {
            rebase_members(members, &group_rebase)?;
        }
        for relation in &mut hierarchy.group_returns {
            relation.target = *group_rebase
                .get(&relation.target)
                .ok_or("local group return is absent from its product rebase")?;
        }
        let flash_rebase = rebase_occurrences(&mut hierarchy.flashes, next_testimony)?;
        for relation in &mut hierarchy.flash_returns {
            relation.target = *flash_rebase
                .get(&relation.target)
                .ok_or("local flash return is absent from its product rebase")?;
        }
    }
    Ok(())
}

fn rebase_occurrences(
    occurrences: &mut [ReceiverTestimony],
    next_testimony: &mut u64,
) -> Result<BTreeMap<ReceiverTestimonyId, ReceiverTestimonyId>, Box<dyn Error>> {
    let mut rebase = BTreeMap::new();
    for occurrence in occurrences {
        let global = ReceiverTestimonyId(*next_testimony);
        *next_testimony = next_testimony
            .checked_add(1)
            .ok_or("testimony carrier overflow")?;
        rebase.insert(occurrence.id, global);
        occurrence.id = global;
    }
    Ok(rebase)
}

fn rebase_members(
    members: &mut BTreeSet<ReceiverTestimonyId>,
    rebase: &BTreeMap<ReceiverTestimonyId, ReceiverTestimonyId>,
) -> Result<(), Box<dyn Error>> {
    *members = members
        .iter()
        .map(|member| {
            rebase
                .get(member)
                .copied()
                .ok_or_else(|| "local testimony is absent from its product rebase".into())
        })
        .collect::<Result<BTreeSet<_>, Box<dyn Error>>>()?;
    Ok(())
}

struct PackedAxis {
    raw: Vec<i64>,
    offset: Rat,
    scale: Rat,
}

struct NativeProductDump {
    latitude: PackedAxis,
    longitude: PackedAxis,
    time: PackedAxis,
    energy: PackedAxis,
    event_ids: Vec<u64>,
    parent_groups: Vec<u64>,
    hierarchy: Option<NativeHierarchyDump>,
}

struct NativeHierarchyDump {
    group_latitude_bits: Vec<u32>,
    group_longitude_bits: Vec<u32>,
    group_time: PackedAxis,
    group_area: PackedAxis,
    group_energy: PackedAxis,
    group_ids: Vec<u64>,
    group_parent_flashes: Vec<u64>,
    flash_latitude_bits: Vec<u32>,
    flash_longitude_bits: Vec<u32>,
    flash_first_time: PackedAxis,
    flash_last_time: PackedAxis,
    flash_area: PackedAxis,
    flash_energy: PackedAxis,
    flash_ids: Vec<u64>,
}

fn dump_native_product(
    source: &Path,
    chart: ReceiverChartId,
    carries_hierarchy: bool,
) -> Result<NativeProductDump, Box<dyn Error>> {
    let temporary =
        std::env::temp_dir().join(format!("holonic-glm-{}-{}", std::process::id(), chart.0));
    fs::create_dir(&temporary)?;
    let raw_path = temporary.join("events.bin");
    let attribute_path = temporary.join("attributes.bin");
    let group_raw_path = temporary.join("groups.bin");
    let group_attribute_path = temporary.join("group-attributes.bin");
    let flash_raw_path = temporary.join("flashes.bin");
    let flash_attribute_path = temporary.join("flash-attributes.bin");
    let null_path = Path::new("/dev/null");

    run_h5dump(
        source,
        &raw_path,
        null_path,
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
        null_path,
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
    if carries_hierarchy {
        dump_native_hierarchy(
            source,
            null_path,
            &group_raw_path,
            &group_attribute_path,
            &flash_raw_path,
            &flash_attribute_path,
        )?;
    }
    let raw = fs::read(&raw_path)?;
    let attributes = fs::read(&attribute_path)?;
    let hierarchy = if carries_hierarchy {
        Some(parse_native_hierarchy(
            &fs::read(&group_raw_path)?,
            &fs::read(&group_attribute_path)?,
            &fs::read(&flash_raw_path)?,
            &fs::read(&flash_attribute_path)?,
        )?)
    } else {
        None
    };
    fs::remove_file(&raw_path)?;
    fs::remove_file(&attribute_path)?;
    if carries_hierarchy {
        fs::remove_file(&group_raw_path)?;
        fs::remove_file(&group_attribute_path)?;
        fs::remove_file(&flash_raw_path)?;
        fs::remove_file(&flash_attribute_path)?;
    }
    fs::remove_dir(&temporary)?;
    if raw.len() % 16 != 0 || attributes.len() != 32 {
        return Err(format!(
            "unexpected native GLM dump extents: raw={} attributes={}",
            raw.len(),
            attributes.len()
        )
        .into());
    }
    let extent = raw.len() / 16;
    let mut cursor = 0_usize;
    let latitude_raw = read_u16_segment(&raw, &mut cursor, extent)?;
    let longitude_raw = read_u16_segment(&raw, &mut cursor, extent)?;
    let time_raw = read_u16_segment(&raw, &mut cursor, extent)?;
    let energy_raw = read_u16_segment(&raw, &mut cursor, extent)?;
    let event_ids = read_u32_segment(&raw, &mut cursor, extent)?;
    let parent_groups = read_u32_segment(&raw, &mut cursor, extent)?;
    if cursor != raw.len() {
        return Err("native GLM dump left unread bytes".into());
    }
    let exact_attributes = attributes
        .chunks_exact(4)
        .map(|bytes| {
            exact_rational_from_f32_bits(u32::from_le_bytes(
                bytes.try_into().expect("four-byte chunk"),
            ))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(NativeProductDump {
        latitude: PackedAxis {
            raw: latitude_raw,
            offset: exact_attributes[0].clone(),
            scale: exact_attributes[1].clone(),
        },
        longitude: PackedAxis {
            raw: longitude_raw,
            offset: exact_attributes[2].clone(),
            scale: exact_attributes[3].clone(),
        },
        time: PackedAxis {
            raw: time_raw,
            offset: exact_attributes[4].clone(),
            scale: exact_attributes[5].clone(),
        },
        energy: PackedAxis {
            raw: energy_raw,
            offset: exact_attributes[6].clone(),
            scale: exact_attributes[7].clone(),
        },
        event_ids,
        parent_groups,
        hierarchy,
    })
}

fn dump_native_hierarchy(
    source: &Path,
    null_path: &Path,
    group_raw_path: &Path,
    group_attribute_path: &Path,
    flash_raw_path: &Path,
    flash_attribute_path: &Path,
) -> Result<(), Box<dyn Error>> {
    run_h5dump(
        source,
        group_raw_path,
        null_path,
        &[
            "-d",
            "group_lat",
            "-d",
            "group_lon",
            "-d",
            "group_time_offset",
            "-d",
            "group_area",
            "-d",
            "group_energy",
            "-d",
            "group_id",
            "-d",
            "group_parent_flash_id",
        ],
    )?;
    run_h5dump(
        source,
        group_attribute_path,
        null_path,
        &[
            "-a",
            "/group_time_offset/add_offset",
            "-a",
            "/group_time_offset/scale_factor",
            "-a",
            "/group_area/add_offset",
            "-a",
            "/group_area/scale_factor",
            "-a",
            "/group_energy/add_offset",
            "-a",
            "/group_energy/scale_factor",
        ],
    )?;
    run_h5dump(
        source,
        flash_raw_path,
        null_path,
        &[
            "-d",
            "flash_lat",
            "-d",
            "flash_lon",
            "-d",
            "flash_time_offset_of_first_event",
            "-d",
            "flash_time_offset_of_last_event",
            "-d",
            "flash_area",
            "-d",
            "flash_energy",
            "-d",
            "flash_id",
        ],
    )?;
    run_h5dump(
        source,
        flash_attribute_path,
        null_path,
        &[
            "-a",
            "/flash_time_offset_of_first_event/add_offset",
            "-a",
            "/flash_time_offset_of_first_event/scale_factor",
            "-a",
            "/flash_time_offset_of_last_event/add_offset",
            "-a",
            "/flash_time_offset_of_last_event/scale_factor",
            "-a",
            "/flash_area/add_offset",
            "-a",
            "/flash_area/scale_factor",
            "-a",
            "/flash_energy/add_offset",
            "-a",
            "/flash_energy/scale_factor",
        ],
    )?;
    Ok(())
}

fn parse_native_hierarchy(
    group_raw: &[u8],
    group_attributes: &[u8],
    flash_raw: &[u8],
    flash_attributes: &[u8],
) -> Result<NativeHierarchyDump, Box<dyn Error>> {
    if group_raw.len() % 20 != 0
        || group_attributes.len() != 24
        || flash_raw.len() % 18 != 0
        || flash_attributes.len() != 32
    {
        return Err(format!(
            "unexpected native GLM hierarchy extents: groups={} group_attributes={} flashes={} flash_attributes={}",
            group_raw.len(),
            group_attributes.len(),
            flash_raw.len(),
            flash_attributes.len()
        )
        .into());
    }
    let group_extent = group_raw.len() / 20;
    let mut group_cursor = 0_usize;
    let group_latitude_bits = read_f32_bits_segment(group_raw, &mut group_cursor, group_extent)?;
    let group_longitude_bits = read_f32_bits_segment(group_raw, &mut group_cursor, group_extent)?;
    let group_time_raw = read_u16_segment(group_raw, &mut group_cursor, group_extent)?;
    let group_area_raw = read_u16_segment(group_raw, &mut group_cursor, group_extent)?;
    let group_energy_raw = read_u16_segment(group_raw, &mut group_cursor, group_extent)?;
    let group_ids = read_u32_segment(group_raw, &mut group_cursor, group_extent)?;
    let group_parent_flashes = read_u16_segment(group_raw, &mut group_cursor, group_extent)?
        .into_iter()
        .map(|value| u64::try_from(value).expect("u16 entered i64"))
        .collect();
    if group_cursor != group_raw.len() {
        return Err("native GLM group dump left unread bytes".into());
    }
    let group_attributes = exact_f32_attributes(group_attributes)?;

    let flash_extent = flash_raw.len() / 18;
    let mut flash_cursor = 0_usize;
    let flash_latitude_bits = read_f32_bits_segment(flash_raw, &mut flash_cursor, flash_extent)?;
    let flash_longitude_bits = read_f32_bits_segment(flash_raw, &mut flash_cursor, flash_extent)?;
    let flash_first_time_raw = read_u16_segment(flash_raw, &mut flash_cursor, flash_extent)?;
    let flash_last_time_raw = read_u16_segment(flash_raw, &mut flash_cursor, flash_extent)?;
    let flash_area_raw = read_u16_segment(flash_raw, &mut flash_cursor, flash_extent)?;
    let flash_energy_raw = read_u16_segment(flash_raw, &mut flash_cursor, flash_extent)?;
    let flash_ids = read_u16_segment(flash_raw, &mut flash_cursor, flash_extent)?
        .into_iter()
        .map(|value| u64::try_from(value).expect("u16 entered i64"))
        .collect();
    if flash_cursor != flash_raw.len() {
        return Err("native GLM flash dump left unread bytes".into());
    }
    let flash_attributes = exact_f32_attributes(flash_attributes)?;
    Ok(NativeHierarchyDump {
        group_latitude_bits,
        group_longitude_bits,
        group_time: PackedAxis {
            raw: group_time_raw,
            offset: group_attributes[0].clone(),
            scale: group_attributes[1].clone(),
        },
        group_area: PackedAxis {
            raw: group_area_raw,
            offset: group_attributes[2].clone(),
            scale: group_attributes[3].clone(),
        },
        group_energy: PackedAxis {
            raw: group_energy_raw,
            offset: group_attributes[4].clone(),
            scale: group_attributes[5].clone(),
        },
        group_ids,
        group_parent_flashes,
        flash_latitude_bits,
        flash_longitude_bits,
        flash_first_time: PackedAxis {
            raw: flash_first_time_raw,
            offset: flash_attributes[0].clone(),
            scale: flash_attributes[1].clone(),
        },
        flash_last_time: PackedAxis {
            raw: flash_last_time_raw,
            offset: flash_attributes[2].clone(),
            scale: flash_attributes[3].clone(),
        },
        flash_area: PackedAxis {
            raw: flash_area_raw,
            offset: flash_attributes[4].clone(),
            scale: flash_attributes[5].clone(),
        },
        flash_energy: PackedAxis {
            raw: flash_energy_raw,
            offset: flash_attributes[6].clone(),
            scale: flash_attributes[7].clone(),
        },
        flash_ids,
    })
}

fn exact_f32_attributes(bytes: &[u8]) -> Result<Vec<Rat>, Box<dyn Error>> {
    bytes
        .chunks_exact(4)
        .map(|value| {
            exact_rational_from_f32_bits(u32::from_le_bytes(
                value.try_into().expect("four-byte chunk"),
            ))
            .map_err(|error| -> Box<dyn Error> { Box::new(error) })
        })
        .collect()
}

fn run_h5dump(
    source: &Path,
    binary: &Path,
    ddl: &Path,
    selections: &[&str],
) -> Result<(), Box<dyn Error>> {
    let status = Command::new("h5dump")
        .args(selections)
        .arg("-b")
        .arg("LE")
        .arg("-o")
        .arg(binary)
        .arg("-O")
        .arg(ddl)
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

fn read_f32_bits_segment(
    bytes: &[u8],
    cursor: &mut usize,
    extent: usize,
) -> Result<Vec<u32>, Box<dyn Error>> {
    let octets = extent.checked_mul(4).ok_or("f32 segment overflow")?;
    let end = cursor.checked_add(octets).ok_or("f32 cursor overflow")?;
    let segment = bytes.get(*cursor..end).ok_or("short f32 segment")?;
    *cursor = end;
    Ok(segment
        .chunks_exact(4)
        .map(|chunk| u32::from_le_bytes(chunk.try_into().expect("four-byte chunk")))
        .collect())
}

fn packed_basis(values: [Rat; 4]) -> Vec<Vec<Rat>> {
    diagonal_basis(values.into_iter().collect())
}

fn diagonal_basis(values: Vec<Rat>) -> Vec<Vec<Rat>> {
    let extent = values.len();
    let mut basis = values
        .into_iter()
        .enumerate()
        .map(|(row, value)| {
            (0..extent)
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
    basis.push(vec![Rat::zero(); extent]);
    basis
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

fn write_product_receipts(
    output: &Path,
    products: &[ProductReceipt],
) -> Result<(), Box<dyn Error>> {
    let mut writer = BufWriter::new(File::create(output.join("products.tsv"))?);
    writeln!(
        writer,
        "key\tsplit\ttotal_glm_events\treceiver_aperture_events\treceiver_aperture_groups\treceiver_aperture_flashes"
    )?;
    for product in products {
        writeln!(
            writer,
            "{}\t{}\t{}\t{}\t{}\t{}",
            product.key,
            product.split,
            product.total_events,
            product.aperture_events,
            product.aperture_groups,
            product.aperture_flashes,
        )?;
    }
    Ok(())
}

fn write_prediction(
    output: &Path,
    prediction: &holonic_engine::ReceiverRelationPrediction,
) -> Result<(), Box<dyn Error>> {
    write_named_prediction(output, "", prediction)
}

fn write_named_prediction(
    output: &Path,
    prefix: &str,
    prediction: &holonic_engine::ReceiverRelationPrediction,
) -> Result<(), Box<dyn Error>> {
    let name = |stem: &str| {
        if prefix.is_empty() {
            format!("{stem}.tsv")
        } else {
            format!("{prefix}_{stem}.tsv")
        }
    };
    let mut relations = BufWriter::new(File::create(output.join(name("predicted_relations")))?);
    writeln!(
        relations,
        "left_testimony\tright_testimony\tstate\tdifference"
    )?;
    for relation in &prediction.candidate_relations {
        writeln!(
            relations,
            "{}\t{}\t{:?}\t{}",
            relation.members[0].0,
            relation.members[1].0,
            relation.state,
            ratio_vector(&relation.difference.0)
        )?;
    }
    let mut components = BufWriter::new(File::create(output.join(name("forced_components")))?);
    writeln!(components, "component\tmember_ordinal\ttestimony")?;
    for (component, members) in prediction.forced_components.iter().enumerate() {
        for (ordinal, member) in members.iter().enumerate() {
            writeln!(components, "{component}\t{ordinal}\t{}", member.0)?;
        }
    }
    Ok(())
}

fn write_grade(
    output: &Path,
    grade: &holonic_engine::ReceiverRelationGrade,
) -> Result<(), Box<dyn Error>> {
    write_named_grade(output, "", grade)
}

fn write_named_grade(
    output: &Path,
    prefix: &str,
    grade: &holonic_engine::ReceiverRelationGrade,
) -> Result<(), Box<dyn Error>> {
    let name = if prefix.is_empty() {
        "obstructions.tsv".to_owned()
    } else {
        format!("{prefix}_obstructions.tsv")
    };
    let mut writer = BufWriter::new(File::create(output.join(name))?);
    writeln!(writer, "kind\tleft_testimony\tright_testimony\tdifference")?;
    for obstruction in &grade.obstructions {
        writeln!(
            writer,
            "{:?}\t{}\t{}\t{}",
            obstruction.kind,
            obstruction.members[0].0,
            obstruction.members[1].0,
            ratio_vector(&obstruction.difference.0)
        )?;
    }
    Ok(())
}

fn write_fronts(
    output: &Path,
    standing: &ObservationEcologyStanding,
) -> Result<(), Box<dyn Error>> {
    let relation = standing
        .relation(FAMILY, GLM_GROUP_ALGORITHM)
        .ok_or("learned relation missing after experiment")?;
    let mut positive = BufWriter::new(File::create(output.join("positive_front.tsv"))?);
    writeln!(positive, "ordinal\tmaximum_difference")?;
    for (ordinal, difference) in relation.positive_maxima.iter().enumerate() {
        writeln!(positive, "{ordinal}\t{}", ratio_vector(&difference.0))?;
    }
    let mut negative = BufWriter::new(File::create(output.join("negative_front.tsv"))?);
    writeln!(negative, "ordinal\tminimum_difference")?;
    for (ordinal, difference) in relation.negative_minima.iter().enumerate() {
        writeln!(negative, "{ordinal}\t{}", ratio_vector(&difference.0))?;
    }
    Ok(())
}

fn write_hierarchy_fronts(
    output: &Path,
    standing: &ObservationEcologyStanding,
) -> Result<(), Box<dyn Error>> {
    let relation = standing
        .relation(GROUP_FAMILY, GLM_FLASH_ALGORITHM)
        .ok_or("learned group-to-flash relation missing after receiver dynamics")?;
    let mut writer = BufWriter::new(File::create(output.join("flash_relation_fronts.tsv"))?);
    writeln!(writer, "kind\tordinal\tdifference")?;
    for (ordinal, difference) in relation.positive_maxima.iter().enumerate() {
        writeln!(
            writer,
            "positive_maximum\t{ordinal}\t{}",
            ratio_vector(&difference.0)
        )?;
    }
    for (ordinal, difference) in relation.negative_minima.iter().enumerate() {
        writeln!(
            writer,
            "negative_minimum\t{ordinal}\t{}",
            ratio_vector(&difference.0)
        )?;
    }
    Ok(())
}

fn write_receiver_perspectives(
    output: &Path,
    standing: &ObservationEcologyStanding,
    partitions: &[(&str, EventId, u32, Vec<u32>)],
) -> Result<(), Box<dyn Error>> {
    let mut writer = BufWriter::new(File::create(output.join("receiver_perspectives.tsv"))?);
    writeln!(
        writer,
        "population\tpartition_event\tcell\tgauge_pivot\tcausal_basis\tsupport\ttangent_rank\thorizon\tdirection_fibers\tzero_transports\textents"
    )?;
    for (population, partition_event, causal_coordinate, directional_coordinates) in partitions {
        let partition = standing
            .admitted_partitions
            .iter()
            .find(|partition| partition.event == *partition_event)
            .ok_or("receiver perspective partition is absent")?;
        for cell in &partition.partition.cells {
            let perspective = standing.receiver_perspective(
                ReceiverPerspectiveAddress::Returned(ReturnedReceiverCellAddress {
                    partition_event: *partition_event,
                    cell: cell.id,
                }),
                &ReceiverPerspectiveSpec {
                    causal_coordinate: *causal_coordinate,
                    directional_coordinates: directional_coordinates.clone(),
                },
            )?;
            let extents = perspective
                .hypervolume
                .extents
                .iter()
                .map(|extent| {
                    format!(
                        "{}:-{}/{}:+{}/{}",
                        extent.coordinate,
                        extent.negative.numer(),
                        extent.negative.denom(),
                        extent.positive.numer(),
                        extent.positive.denom()
                    )
                })
                .collect::<Vec<_>>()
                .join(";");
            writeln!(
                writer,
                "{population}\t{}\t{}\t{}\t{}\t{}\t{}\t{:?}\t{}\t{}\t{}",
                partition_event.0,
                cell.id.0,
                perspective.pivot.0,
                perspective.causal_basis.len(),
                perspective.support.len(),
                perspective.hypervolume.tangent_rank,
                perspective.hypervolume.horizon,
                perspective.hypervolume.directions.len(),
                perspective.hypervolume.zero_transport_members.len(),
                extents,
            )?;
        }
    }
    Ok(())
}

fn write_receiver_dynamics_summary(
    output: &Path,
    standing: &ObservationEcologyStanding,
    group_prediction: ReceiverPredictionId,
    group_grade: ReceiverGradeId,
    flash_prediction: ReceiverPredictionId,
    flash_grade: ReceiverGradeId,
    training_work: &[(&str, ObservationEcologyWork)],
    held_out_work: &[(&str, ObservationEcologyWork)],
) -> Result<(), Box<dyn Error>> {
    let group_prediction = &standing.predictions[&group_prediction];
    let group_grade = &standing.grades[&group_grade];
    let flash_prediction = &standing.predictions[&flash_prediction];
    let flash_grade = &standing.grades[&flash_grade];
    let mut writer = BufWriter::new(File::create(output.join("receiver_dynamics_summary.tsv"))?);
    writeln!(writer, "measure\tvalue")?;
    writeln!(
        writer,
        "interpretation\tGLM optical event/group/flash receiver topology; not a reconstructed discharge channel"
    )?;
    writeln!(
        writer,
        "window\ttraining 2018-12-13 22:50--23:00 UTC; held-out 23:00--23:10 UTC"
    )?;
    writeln!(
        writer,
        "receiver_grain_quotients\t{}",
        standing.receiver_quotients.len()
    )?;
    write_prediction_grade_summary(&mut writer, "event_to_group", group_prediction, group_grade)?;
    write_prediction_grade_summary(&mut writer, "group_to_flash", flash_prediction, flash_grade)?;
    for (phase, work) in training_work.iter().chain(held_out_work) {
        writeln!(writer, "{phase}_cpu_tasks\t{}", work.cpu_tasks)?;
        writeln!(
            writer,
            "{phase}_cpu_workers_used\t{}",
            work.cpu_workers_used
        )?;
        writeln!(
            writer,
            "{phase}_cuda_classified_relations\t{}",
            work.cuda_classified_relations
        )?;
        writeln!(writer, "{phase}_cuda_launches\t{}", work.cuda_launches)?;
    }
    let mut bidegrees = BufWriter::new(File::create(
        output.join("receiver_morphology_bidegrees.tsv"),
    )?);
    writeln!(
        bidegrees,
        "transition\tproposed_receivers\treturned_receivers\tcomponents"
    )?;
    for (transition, grade) in [
        ("event_to_group", group_grade),
        ("group_to_flash", flash_grade),
    ] {
        for ((proposed, returned), population) in &grade.receiver_morphology.component_bidegrees {
            writeln!(
                bidegrees,
                "{transition}\t{proposed}\t{returned}\t{population}"
            )?;
        }
    }
    Ok(())
}

fn write_prediction_grade_summary(
    writer: &mut impl Write,
    prefix: &str,
    prediction: &holonic_engine::ReceiverRelationPrediction,
    grade: &holonic_engine::ReceiverRelationGrade,
) -> Result<(), Box<dyn Error>> {
    let morphology = &grade.receiver_morphology;
    writeln!(
        writer,
        "{prefix}_candidate_relations\t{}",
        prediction.candidate_relations.len()
    )?;
    writeln!(
        writer,
        "{prefix}_proposed_receivers\t{}",
        morphology.proposed_receivers
    )?;
    writeln!(
        writer,
        "{prefix}_returned_receivers\t{}",
        morphology.returned_receivers
    )?;
    writeln!(
        writer,
        "{prefix}_overlap_relations\t{}",
        morphology.overlap_relations
    )?;
    writeln!(
        writer,
        "{prefix}_exact_closures\t{}",
        morphology.exact_closures
    )?;
    writeln!(writer, "{prefix}_subdivisions\t{}", morphology.subdivisions)?;
    writeln!(writer, "{prefix}_growths\t{}", morphology.growths)?;
    writeln!(
        writer,
        "{prefix}_mixed_branches\t{}",
        morphology.mixed_branches
    )?;
    writeln!(
        writer,
        "{prefix}_obstructions\t{}",
        grade.obstructions.len()
    )?;
    Ok(())
}

#[derive(Clone, Copy, Debug)]
struct DisplayPoint {
    latitude: f64,
    longitude: f64,
    clock: f64,
}

type DisplayTracePopulation = BTreeMap<u64, Vec<Vec<DisplayPoint>>>;

fn render_receiver_dynamics(
    output: &Path,
    standing: &ObservationEcologyStanding,
    group_prediction: ReceiverPredictionId,
    flash_prediction: ReceiverPredictionId,
    group_partition_event: EventId,
    flash_partition_event: EventId,
    aperture: &[ExactCoordinateInterval],
) -> Result<(), Box<dyn Error>> {
    let returned_groups = display_traces_from_partition(standing, group_partition_event)?;
    let proposed_groups = display_traces_from_prediction(standing, group_prediction)?;
    let returned_flashes = display_traces_from_partition(standing, flash_partition_event)?;
    let proposed_flashes = display_traces_from_prediction(standing, flash_prediction)?;
    let frames = returned_groups
        .keys()
        .chain(proposed_groups.keys())
        .chain(returned_flashes.keys())
        .chain(proposed_flashes.keys())
        .copied()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    if frames.is_empty() {
        return Err("receiver dynamics produced no displayable causal frames".into());
    }
    let declared_latitude = aperture
        .iter()
        .find(|interval| interval.coordinate == 0)
        .ok_or("receiver dynamics aperture has no latitude coordinate")?;
    let declared_longitude = aperture
        .iter()
        .find(|interval| interval.coordinate == 1)
        .ok_or("receiver dynamics aperture has no longitude coordinate")?;
    let display = DisplayAperture::from_populations([
        &returned_groups,
        &proposed_groups,
        &returned_flashes,
        &proposed_flashes,
    ])?;
    let frame_directory = output.join("receiver-dynamics-frames");
    fs::create_dir_all(&frame_directory)?;
    for entry in fs::read_dir(&frame_directory)? {
        let path = entry?.path();
        if path
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.starts_with("frame-") && name.ends_with(".png"))
        {
            fs::remove_file(path)?;
        }
    }

    let width = 1_024_u32;
    let height = 768_u32;
    let trail = 5_usize;
    let mut manifest = BufWriter::new(File::create(output.join("receiver_dynamics_frames.tsv"))?);
    writeln!(
        manifest,
        "frame\tchart\tsource\tproposed_groups\treturned_groups\tproposed_flashes\treturned_flashes"
    )?;
    let mut final_image = None;
    for (frame_index, frame) in frames.iter().enumerate() {
        let mut image = RgbImage::from_pixel(width, height, Rgb([3, 8, 12]));
        draw_display_aperture(&mut image);
        let first = frame_index.saturating_sub(trail - 1);
        for history_index in first..=frame_index {
            let history = frames[history_index];
            let age = frame_index - history_index;
            let fade = u8::try_from(255_usize.saturating_sub(age * 42)).unwrap_or(45);
            draw_population(
                &mut image,
                proposed_groups.get(&history),
                &display,
                [18, 214, 226],
                fade.saturating_mul(2) / 5,
                1,
            );
            draw_population(
                &mut image,
                returned_groups.get(&history),
                &display,
                [255, 151, 36],
                fade.saturating_mul(3) / 5,
                2,
            );
            draw_population(
                &mut image,
                proposed_flashes.get(&history),
                &display,
                [158, 93, 255],
                fade.saturating_mul(2) / 5,
                2,
            );
            draw_population(
                &mut image,
                returned_flashes.get(&history),
                &display,
                [246, 244, 205],
                fade.saturating_mul(4) / 5,
                3,
            );
        }
        draw_phase_key(&mut image);
        let path = frame_directory.join(format!("frame-{frame_index:04}.png"));
        DynamicImage::ImageRgb8(image.clone()).save(&path)?;
        let source = standing
            .charts
            .get(&ReceiverChartId(*frame))
            .map(|chart| chart.source.as_str())
            .unwrap_or("unknown receiver chart");
        writeln!(
            manifest,
            "{frame_index}\t{frame}\t{source}\t{}\t{}\t{}\t{}",
            proposed_groups.get(frame).map_or(0, Vec::len),
            returned_groups.get(frame).map_or(0, Vec::len),
            proposed_flashes.get(frame).map_or(0, Vec::len),
            returned_flashes.get(frame).map_or(0, Vec::len),
        )?;
        final_image = Some(image);
    }
    if let Some(image) = final_image {
        DynamicImage::ImageRgb8(image).save(output.join("receiver-dynamics-final.png"))?;
    }
    let mut semantics = BufWriter::new(File::create(
        output.join("receiver_dynamics_visual_semantics.tsv"),
    )?);
    writeln!(semantics, "color\trelation\tclaim")?;
    writeln!(
        semantics,
        "cyan\tmachine event-to-group proposal\tforced receiver support before native return"
    )?;
    writeln!(
        semantics,
        "amber\tnative GLM event-to-group return\toptical detection grouping, not a physical discharge channel"
    )?;
    writeln!(
        semantics,
        "violet\tmachine group-to-flash proposal\tforced coarser receiver support before native return"
    )?;
    writeln!(
        semantics,
        "white\tnative GLM group-to-flash return\toptical flash grouping, not a physical discharge channel"
    )?;
    writeln!(
        semantics,
        "trail\tfive successive 20-second receiver products\tterminal chronology only; it does not alter standing"
    )?;
    writeln!(
        semantics,
        "declared_aperture\tlatitude {}/{}..{}/{}; longitude {}/{}..{}/{}\tsource receiver restriction",
        declared_latitude.lower.numer(),
        declared_latitude.lower.denom(),
        declared_latitude.upper.numer(),
        declared_latitude.upper.denom(),
        declared_longitude.lower.numer(),
        declared_longitude.lower.denom(),
        declared_longitude.upper.numer(),
        declared_longitude.upper.denom(),
    )?;
    writeln!(
        semantics,
        "display_aperture\tlatitude {}..{}; longitude {}..{}\tone terminal chart derived once from the complete held-out support",
        display.latitude_lower,
        display.latitude_upper,
        display.longitude_lower,
        display.longitude_upper,
    )?;

    let video = output.join("receiver-dynamics.mp4");
    let status = Command::new("ffmpeg")
        .arg("-y")
        .arg("-loglevel")
        .arg("error")
        .arg("-framerate")
        .arg("6")
        .arg("-i")
        .arg(frame_directory.join("frame-%04d.png"))
        .arg("-c:v")
        .arg("libx264")
        .arg("-pix_fmt")
        .arg("yuv420p")
        .arg(&video)
        .status()?;
    if !status.success() {
        return Err("ffmpeg failed to encode the receiver-dynamics video".into());
    }
    Ok(())
}

fn display_traces_from_partition(
    standing: &ObservationEcologyStanding,
    event: EventId,
) -> Result<DisplayTracePopulation, Box<dyn Error>> {
    let partition = standing
        .admitted_partitions
        .iter()
        .find(|partition| partition.event == event)
        .ok_or("display partition is absent")?;
    display_traces(
        standing,
        partition
            .partition
            .cells
            .iter()
            .map(|cell| cell.members.iter().copied().collect::<Vec<_>>()),
    )
}

fn display_traces_from_prediction(
    standing: &ObservationEcologyStanding,
    prediction: ReceiverPredictionId,
) -> Result<DisplayTracePopulation, Box<dyn Error>> {
    let prediction = standing
        .predictions
        .get(&prediction)
        .ok_or("display prediction is absent")?;
    display_traces(standing, prediction.forced_components.iter().cloned())
}

fn display_traces(
    standing: &ObservationEcologyStanding,
    supports: impl Iterator<Item = Vec<ReceiverTestimonyId>>,
) -> Result<DisplayTracePopulation, Box<dyn Error>> {
    let mut population = DisplayTracePopulation::new();
    for support in supports {
        let mut frame = None;
        let mut trace = Vec::with_capacity(support.len());
        for member in support {
            let body = standing
                .testimonies
                .get(&member)
                .ok_or("display support testimony is absent")?;
            let chart = standing
                .charts
                .get(&body.occurrence.chart)
                .ok_or("display support chart is absent")?;
            let current_frame = match chart.family {
                FAMILY => chart.id.0,
                GROUP_FAMILY => chart
                    .id
                    .0
                    .checked_sub(GROUP_CHART_NAMESPACE)
                    .ok_or("group display chart has no event-chart base")?,
                _ => return Err("display support has an unsupported receiver family".into()),
            };
            if frame
                .replace(current_frame)
                .is_some_and(|prior| prior != current_frame)
            {
                return Err("one receiver support crossed product strata".into());
            }
            let coordinates = chart.receive(&body.occurrence.raw)?;
            trace.push(DisplayPoint {
                latitude: exact_to_f64(&coordinates[0])?,
                longitude: exact_to_f64(&coordinates[1])?,
                clock: exact_to_f64(&coordinates[2])?,
            });
        }
        trace.sort_by(|left, right| left.clock.total_cmp(&right.clock));
        if let Some(frame) = frame {
            population.entry(frame).or_default().push(trace);
        }
    }
    Ok(population)
}

fn exact_to_f64(value: &Rat) -> Result<f64, Box<dyn Error>> {
    value
        .to_f64()
        .filter(|value| value.is_finite())
        .ok_or_else(|| "exact display coordinate cannot enter the monitor quotient".into())
}

struct DisplayAperture {
    latitude_lower: f64,
    latitude_upper: f64,
    longitude_lower: f64,
    longitude_upper: f64,
}

impl DisplayAperture {
    fn from_populations<const N: usize>(
        populations: [&DisplayTracePopulation; N],
    ) -> Result<Self, Box<dyn Error>> {
        let mut latitude_lower = f64::INFINITY;
        let mut latitude_upper = f64::NEG_INFINITY;
        let mut longitude_lower = f64::INFINITY;
        let mut longitude_upper = f64::NEG_INFINITY;
        for point in populations
            .into_iter()
            .flat_map(|population| population.values())
            .flatten()
            .flatten()
        {
            latitude_lower = latitude_lower.min(point.latitude);
            latitude_upper = latitude_upper.max(point.latitude);
            longitude_lower = longitude_lower.min(point.longitude);
            longitude_upper = longitude_upper.max(point.longitude);
        }
        if !latitude_lower.is_finite()
            || !latitude_upper.is_finite()
            || !longitude_lower.is_finite()
            || !longitude_upper.is_finite()
        {
            return Err("receiver display support has no finite local extent".into());
        }
        let latitude_span = (latitude_upper - latitude_lower).max(1.0 / 1_048_576.0);
        let longitude_span = (longitude_upper - longitude_lower).max(1.0 / 1_048_576.0);
        Ok(Self {
            latitude_lower: latitude_lower - latitude_span / 20.0,
            latitude_upper: latitude_upper + latitude_span / 20.0,
            longitude_lower: longitude_lower - longitude_span / 20.0,
            longitude_upper: longitude_upper + longitude_span / 20.0,
        })
    }
}

fn draw_population(
    image: &mut RgbImage,
    population: Option<&Vec<Vec<DisplayPoint>>>,
    aperture: &DisplayAperture,
    color: [u8; 3],
    alpha: u8,
    thickness: i32,
) {
    let Some(population) = population else {
        return;
    };
    for trace in population {
        let points = trace
            .iter()
            .map(|point| display_pixel(image, aperture, point))
            .collect::<Vec<_>>();
        for (ordinal, point) in points.iter().enumerate() {
            let phase_alpha = ((u16::from(alpha) * u16::try_from(ordinal + 1).unwrap_or(u16::MAX))
                / u16::try_from(points.len().max(1)).unwrap_or(u16::MAX))
            .max(u16::from(alpha) / 3) as u8;
            draw_glow(image, point.0, point.1, color, phase_alpha, thickness + 2);
        }
        for (ordinal, segment) in points.windows(2).enumerate() {
            let phase_alpha = ((u16::from(alpha) * u16::try_from(ordinal + 2).unwrap_or(u16::MAX))
                / u16::try_from(points.len().max(1)).unwrap_or(u16::MAX))
                as u8;
            draw_line(image, segment[0], segment[1], color, phase_alpha, thickness);
        }
    }
}

fn display_pixel(image: &RgbImage, aperture: &DisplayAperture, point: &DisplayPoint) -> (i32, i32) {
    let margin = 28.0;
    let x = (point.longitude - aperture.longitude_lower)
        / (aperture.longitude_upper - aperture.longitude_lower);
    let y = (point.latitude - aperture.latitude_lower)
        / (aperture.latitude_upper - aperture.latitude_lower);
    let width = f64::from(image.width()) - margin * 2.0;
    let height = f64::from(image.height()) - margin * 2.0;
    (
        (margin + x.clamp(0.0, 1.0) * width).round() as i32,
        (margin + (1.0 - y.clamp(0.0, 1.0)) * height).round() as i32,
    )
}

fn draw_display_aperture(image: &mut RgbImage) {
    let color = [20, 46, 53];
    let width = i32::try_from(image.width()).unwrap_or(i32::MAX);
    let height = i32::try_from(image.height()).unwrap_or(i32::MAX);
    draw_line(image, (27, 27), (width - 28, 27), color, 180, 1);
    draw_line(
        image,
        (width - 28, 27),
        (width - 28, height - 28),
        color,
        180,
        1,
    );
    draw_line(
        image,
        (width - 28, height - 28),
        (27, height - 28),
        color,
        180,
        1,
    );
    draw_line(image, (27, height - 28), (27, 27), color, 180, 1);
}

fn draw_phase_key(image: &mut RgbImage) {
    for (index, color) in [
        [18, 214, 226],
        [255, 151, 36],
        [158, 93, 255],
        [246, 244, 205],
    ]
    .into_iter()
    .enumerate()
    {
        let left = 38 + i32::try_from(index).unwrap_or_default() * 22;
        for x in left..left + 14 {
            for y in 38..52 {
                blend_pixel(image, x, y, color, 230);
            }
        }
    }
}

fn draw_glow(image: &mut RgbImage, x: i32, y: i32, color: [u8; 3], alpha: u8, radius: i32) {
    for dy in -radius..=radius {
        for dx in -radius..=radius {
            let distance = dx * dx + dy * dy;
            if distance <= radius * radius {
                let falloff = u8::try_from(
                    (u16::from(alpha)
                        * u16::try_from(radius * radius - distance + 1).unwrap_or_default())
                        / u16::try_from(radius * radius + 1).unwrap_or(1),
                )
                .unwrap_or(alpha);
                blend_pixel(image, x + dx, y + dy, color, falloff);
            }
        }
    }
}

fn draw_line(
    image: &mut RgbImage,
    start: (i32, i32),
    end: (i32, i32),
    color: [u8; 3],
    alpha: u8,
    thickness: i32,
) {
    let (mut x, mut y) = start;
    let dx = (end.0 - x).abs();
    let sx = if x < end.0 { 1 } else { -1 };
    let dy = -(end.1 - y).abs();
    let sy = if y < end.1 { 1 } else { -1 };
    let mut error = dx + dy;
    loop {
        for offset_y in -thickness..=thickness {
            for offset_x in -thickness..=thickness {
                if offset_x * offset_x + offset_y * offset_y <= thickness * thickness {
                    blend_pixel(image, x + offset_x, y + offset_y, color, alpha);
                }
            }
        }
        if (x, y) == end {
            break;
        }
        let doubled = error * 2;
        if doubled >= dy {
            error += dy;
            x += sx;
        }
        if doubled <= dx {
            error += dx;
            y += sy;
        }
    }
}

fn blend_pixel(image: &mut RgbImage, x: i32, y: i32, color: [u8; 3], alpha: u8) {
    let Ok(x) = u32::try_from(x) else {
        return;
    };
    let Ok(y) = u32::try_from(y) else {
        return;
    };
    if x >= image.width() || y >= image.height() {
        return;
    }
    let pixel = image.get_pixel_mut(x, y);
    for channel in 0..3 {
        let old = u16::from(pixel[channel]);
        let new = u16::from(color[channel]);
        pixel[channel] =
            u8::try_from((old * (255 - u16::from(alpha)) + new * u16::from(alpha)) / 255)
                .unwrap_or(color[channel]);
    }
}

#[allow(clippy::too_many_arguments)]
fn write_summary(
    output: &Path,
    manifest: &Path,
    raw: &Path,
    products: &[ProductReceipt],
    prediction: ReceiverPredictionId,
    grade: ReceiverGradeId,
    admitted_before: usize,
    admitted_after: usize,
    acquisition_ms: u128,
    training_ms: u128,
    prediction_ms: u128,
    grade_ms: u128,
    admission_ms: u128,
    loader: &CpuExecutionReceipt,
    execution: &[(&str, &ObservationEcologyWork)],
    standing: &ObservationEcologyStanding,
) -> Result<(), Box<dyn Error>> {
    let prediction = &standing.predictions[&prediction];
    let grade = &standing.grades[&grade];
    let relation = standing
        .relation(FAMILY, GLM_GROUP_ALGORITHM)
        .ok_or("learned relation missing after experiment")?;
    let training_products = products
        .iter()
        .filter(|product| product.split == "training")
        .count();
    let held_out_products = products.len() - training_products;
    let mut obstruction_kinds = BTreeMap::<ReceiverRelationObstructionKind, usize>::new();
    for obstruction in &grade.obstructions {
        *obstruction_kinds.entry(obstruction.kind).or_default() += 1;
    }
    let mut writer = BufWriter::new(File::create(output.join("summary.tsv"))?);
    writeln!(writer, "measure\tvalue")?;
    writeln!(writer, "manifest\t{}", manifest.display())?;
    writeln!(writer, "raw_directory\t{}", raw.display())?;
    writeln!(writer, "training_products\t{training_products}")?;
    writeln!(writer, "held_out_products\t{held_out_products}")?;
    writeln!(writer, "loader_tasks\t{}", loader.tasks)?;
    writeln!(writer, "loader_worker_limit\t{}", loader.worker_limit)?;
    writeln!(writer, "loader_workers_used\t{}", loader.workers_used)?;
    writeln!(writer, "loader_batches\t{}", loader.batches)?;
    writeln!(writer, "loader_joins\t{}", loader.joins)?;
    writeln!(writer, "training_testimonies\t{admitted_before}")?;
    writeln!(
        writer,
        "held_out_testimonies\t{}",
        admitted_after - admitted_before
    )?;
    writeln!(writer, "positive_front\t{}", relation.positive_maxima.len())?;
    writeln!(writer, "negative_front\t{}", relation.negative_minima.len())?;
    writeln!(
        writer,
        "candidate_relations\t{}",
        prediction.candidate_relations.len()
    )?;
    writeln!(
        writer,
        "forced_components\t{}",
        prediction.forced_components.len()
    )?;
    writeln!(
        writer,
        "returned_together_pairs\t{}",
        grade.counts.returned_together_pairs
    )?;
    writeln!(
        writer,
        "returned_apart_pairs\t{}",
        grade.counts.returned_apart_pairs
    )?;
    writeln!(
        writer,
        "forced_together_correct\t{}",
        grade.counts.forced_together_correct
    )?;
    writeln!(
        writer,
        "forced_apart_correct\t{}",
        grade.counts.forced_apart_correct
    )?;
    writeln!(
        writer,
        "returned_together_open\t{}",
        grade.counts.returned_together_open
    )?;
    writeln!(
        writer,
        "returned_together_forced_apart\t{}",
        grade.counts.returned_together_forced_apart
    )?;
    writeln!(
        writer,
        "returned_apart_forced_together\t{}",
        grade.counts.returned_apart_forced_together
    )?;
    writeln!(
        writer,
        "conflicted_pairs\t{}",
        grade.counts.conflicted_pairs
    )?;
    writeln!(writer, "obstructions\t{}", grade.obstructions.len())?;
    for (kind, population) in obstruction_kinds {
        writeln!(writer, "obstruction_{kind:?}\t{population}")?;
    }
    writeln!(writer, "acquisition_ms\t{acquisition_ms}")?;
    writeln!(writer, "training_ms\t{training_ms}")?;
    writeln!(writer, "prediction_ms\t{prediction_ms}")?;
    writeln!(writer, "grade_ms\t{grade_ms}")?;
    writeln!(writer, "admission_ms\t{admission_ms}")?;
    for (phase, work) in execution {
        writeln!(writer, "{phase}_cpu_tasks\t{}", work.cpu_tasks)?;
        writeln!(
            writer,
            "{phase}_cpu_workers_used\t{}",
            work.cpu_workers_used
        )?;
        writeln!(writer, "{phase}_cpu_antichains\t{}", work.cpu_antichains)?;
        writeln!(writer, "{phase}_cpu_joins\t{}", work.cpu_joins)?;
        writeln!(
            writer,
            "{phase}_cuda_classified_relations\t{}",
            work.cuda_classified_relations
        )?;
        writeln!(
            writer,
            "{phase}_cuda_returned_relations\t{}",
            work.cuda_returned_relations
        )?;
        writeln!(
            writer,
            "{phase}_cuda_parity_relations\t{}",
            work.cuda_parity_relations
        )?;
        writeln!(
            writer,
            "{phase}_cuda_mode_admissions\t{}",
            work.cuda_mode_admissions
        )?;
        writeln!(
            writer,
            "{phase}_cuda_mode_reuses\t{}",
            work.cuda_mode_reuses
        )?;
        writeln!(
            writer,
            "{phase}_cuda_resident_modes\t{}",
            work.cuda_resident_modes
        )?;
        writeln!(writer, "{phase}_cuda_launches\t{}", work.cuda_launches)?;
        writeln!(
            writer,
            "{phase}_cuda_device\t{}",
            work.cuda_device.as_deref().unwrap_or("none")
        )?;
        writeln!(
            writer,
            "{phase}_cuda_kernel_sha256\t{}",
            work.cuda_kernel_sha256.as_deref().unwrap_or("none")
        )?;
        writeln!(
            writer,
            "{phase}_cuda_cpu_to_device_octets\t{}",
            work.cuda_cpu_to_device_octets
        )?;
        writeln!(
            writer,
            "{phase}_cuda_device_to_cpu_octets\t{}",
            work.cuda_device_to_cpu_octets
        )?;
        writeln!(
            writer,
            "{phase}_cuda_front_uploads\t{}",
            work.cuda_front_uploads
        )?;
        writeln!(
            writer,
            "{phase}_cuda_allocation_resizes\t{}",
            work.cuda_allocation_resizes
        )?;
        writeln!(
            writer,
            "{phase}_cpu_relation_fallbacks\t{}",
            work.cpu_relation_fallbacks
        )?;
    }
    Ok(())
}

fn write_standing_digest(
    output: &Path,
    standing: &ObservationEcologyStanding,
) -> Result<(), Box<dyn Error>> {
    let encoded = ron::to_string(standing)?;
    let digest = Sha256::digest(encoded.as_bytes());
    let mut writer = BufWriter::new(File::create(output.join("standing.sha256"))?);
    writeln!(
        writer,
        "{digest:x}\tobservation-ecology-standing.ron-memory"
    )?;
    let remounted: ObservationEcologyStanding = ron::from_str(&encoded)?;
    if &remounted != standing {
        return Err("observation ecology standing changed across exact remount".into());
    }
    remounted.validate()?;
    Ok(())
}

fn ratio_vector(values: &[Rat]) -> String {
    values
        .iter()
        .map(|value| format!("{}/{}", value.numer(), value.denom()))
        .collect::<Vec<_>>()
        .join(",")
}

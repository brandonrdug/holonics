//! Real four-receiver magnetopause traversal over the 16 October 2015 MMS event.
//!
//! Three MMS sections define the changing magnetic field, electric field, ion
//! bulk velocity, and ion density on one face of the measured spacecraft
//! tetrahedron.  The fourth receiver remains outside that face.  Its previously
//! returned normal-fiber difference is retained as reactive boundary current.
//! At every later occurrence the three face sections propagate their exact
//! change through caused tetrahedral edges, generating every MMS4 species
//! before its return enters.  The returned residual then changes the retained
//! current used by the following occurrence.
//!
//! This is not a least-squares fit and does not promote the planar quotient to
//! the complete source field.  Every imported decimal is retained as the exact
//! rational denoted by the CDAWeb text, receiver-clock offsets remain in the
//! receipts, and the unresolved fourth-direction difference remains explicit.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fs::{self, File};
use std::io::{BufRead, BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};

use holonic_engine::{
    CausalBodyDeed, CausalBodyEvent, CausalBodyStanding, CausalCellId, CausalCellReference,
    CausalTraversalPassageId, CausalTraversalSpeciesId, CausalWorld, ComparativeMultiplicity,
    EventBoundaryTerm, EventCellId, EventId, ExactCausalBodyLaw, ExactCausalTraversalEvent,
    ExactCausalTraversalImpulse, ExactCausalTraversalLaw, ExactCausalTraversalPassage,
    ExactCausalTraversalStanding, ExactEventLaw, ExactRatMatrix, ExactReactiveTraversalInteraction,
    ExactTraversalCurrentSpecies, ExactTraversalLinearBalance,
};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::{Rat, ReceiverId};
use sha2::{Digest, Sha256};

const DEFAULT_DATA: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../.local/data/mms-reconnection/2015-10-16T130655-130710Z"
);
const DEFAULT_OUTPUT: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../.local/artifacts/mms-reconnection/causal-traversal"
);
const CONDITIONING_END: &str = "2015-10-16T13:07:00.000000000Z";
const SAMPLE_STRIDE: usize = 8;
const TRAVEL_EXTENT: usize = 10;

#[derive(Clone, Copy)]
struct SpeciesDescriptor {
    id: u64,
    name: &'static str,
    unit: &'static str,
    start: usize,
    extent: usize,
}

const SPECIES: [SpeciesDescriptor; 4] = [
    SpeciesDescriptor {
        id: 1,
        name: "magnetic_field_gse",
        unit: "nT",
        start: 0,
        extent: 3,
    },
    SpeciesDescriptor {
        id: 2,
        name: "electric_field_gse",
        unit: "mV_per_m",
        start: 3,
        extent: 3,
    },
    SpeciesDescriptor {
        id: 3,
        name: "ion_bulk_velocity_gse",
        unit: "km_per_s",
        start: 6,
        extent: 3,
    },
    SpeciesDescriptor {
        id: 4,
        name: "ion_number_density",
        unit: "per_cm3",
        start: 9,
        extent: 1,
    },
];

#[derive(Clone, Debug, PartialEq, Eq)]
struct ExactVec3([Rat; 3]);

impl ExactVec3 {
    fn add(&self, other: &Self) -> Self {
        Self([
            &self.0[0] + &other.0[0],
            &self.0[1] + &other.0[1],
            &self.0[2] + &other.0[2],
        ])
    }

    fn subtract(&self, other: &Self) -> Self {
        Self([
            &self.0[0] - &other.0[0],
            &self.0[1] - &other.0[1],
            &self.0[2] - &other.0[2],
        ])
    }

    fn scale(&self, coefficient: &Rat) -> Self {
        Self([
            coefficient * &self.0[0],
            coefficient * &self.0[1],
            coefficient * &self.0[2],
        ])
    }

    fn dot(&self, other: &Self) -> Rat {
        &self.0[0] * &other.0[0] + &self.0[1] * &other.0[1] + &self.0[2] * &other.0[2]
    }

    fn cross(&self, other: &Self) -> Self {
        Self([
            &self.0[1] * &other.0[2] - &self.0[2] * &other.0[1],
            &self.0[2] * &other.0[0] - &self.0[0] * &other.0[2],
            &self.0[0] * &other.0[1] - &self.0[1] * &other.0[0],
        ])
    }

    fn as_slice(&self) -> &[Rat] {
        &self.0
    }
}

fn add_current(left: &[Rat], right: &[Rat]) -> Result<Vec<Rat>, Box<dyn Error>> {
    if left.len() != right.len() {
        return Err("current species extents do not agree".into());
    }
    Ok(left
        .iter()
        .zip(right)
        .map(|(left, right)| left + right)
        .collect())
}

fn subtract_current(left: &[Rat], right: &[Rat]) -> Result<Vec<Rat>, Box<dyn Error>> {
    if left.len() != right.len() {
        return Err("current species extents do not agree".into());
    }
    Ok(left
        .iter()
        .zip(right)
        .map(|(left, right)| left - right)
        .collect())
}

fn scale_current(current: &[Rat], coefficient: &Rat) -> Vec<Rat> {
    current.iter().map(|value| coefficient * value).collect()
}

#[derive(Clone, Debug)]
struct TimedVector {
    source_time: String,
    chronology_ns: u64,
    value: ExactVec3,
}

#[derive(Clone, Debug)]
struct SpacecraftTrace {
    magnetic: Vec<TimedVector>,
    electric: Vec<TimedVector>,
    ion: Vec<TimedIonMoment>,
    position: Vec<TimedVector>,
}

#[derive(Clone, Debug)]
struct TimedIonMoment {
    chronology_ns: u64,
    density: Rat,
    velocity: ExactVec3,
}

#[derive(Clone, Debug)]
struct JoinedReceiverSample {
    source_time: String,
    chronology_ns: u64,
    magnetic: [ExactVec3; 4],
    electric: [ExactVec3; 4],
    ion_velocity: [ExactVec3; 4],
    ion_density: [Rat; 4],
    position: [ExactVec3; 4],
    magnetic_clock_offsets_ns: [i64; 4],
    electric_clock_offsets_ns: [i64; 4],
    ion_clock_offsets_ns: [i64; 4],
}

impl JoinedReceiverSample {
    fn current(&self, spacecraft: usize) -> Vec<Rat> {
        let mut current = Vec::with_capacity(TRAVEL_EXTENT);
        current.extend_from_slice(self.magnetic[spacecraft].as_slice());
        current.extend_from_slice(self.electric[spacecraft].as_slice());
        current.extend_from_slice(self.ion_velocity[spacecraft].as_slice());
        current.push(self.ion_density[spacecraft].clone());
        current
    }
}

#[derive(Clone, Debug)]
struct TetrahedralSection {
    weights: [Rat; 3],
    face_contributions: [Vec<Rat>; 3],
    face_field: Vec<Rat>,
    gram_determinant: Rat,
    signed_six_volume: Rat,
}

#[derive(Clone, Copy, Debug)]
struct TetrahedralCells {
    spacecraft: [CausalCellId; 4],
    to_fourth: [CausalCellId; 3],
}

#[derive(Clone, Debug)]
struct OmniContext {
    source_time: String,
    magnetic: ExactVec3,
    velocity: ExactVec3,
    proton_density: Rat,
    pressure: Rat,
}

#[derive(Clone, Debug, Default)]
struct SpeciesGrade {
    better_than_stale: usize,
    equal_to_stale: usize,
    worse_than_stale: usize,
    exact_zero_residual: usize,
    nonzero_residual: usize,
}

#[derive(Default)]
struct GradeCounts {
    species: [SpeciesGrade; 4],
    balance_receipts: usize,
    nonzero_balance_residuals: usize,
    maximum_clock_offset_ns: u64,
}

fn total_better(grades: &GradeCounts) -> usize {
    grades
        .species
        .iter()
        .map(|grade| grade.better_than_stale)
        .sum()
}

fn total_equal(grades: &GradeCounts) -> usize {
    grades
        .species
        .iter()
        .map(|grade| grade.equal_to_stale)
        .sum()
}

fn total_worse(grades: &GradeCounts) -> usize {
    grades
        .species
        .iter()
        .map(|grade| grade.worse_than_stale)
        .sum()
}

fn total_exact_zero(grades: &GradeCounts) -> usize {
    grades
        .species
        .iter()
        .map(|grade| grade.exact_zero_residual)
        .sum()
}

fn total_nonzero(grades: &GradeCounts) -> usize {
    grades
        .species
        .iter()
        .map(|grade| grade.nonzero_residual)
        .sum()
}

fn main() -> Result<(), Box<dyn Error>> {
    let data_directory = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_DATA));
    let output_directory = std::env::args()
        .nth(2)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_OUTPUT));
    fs::create_dir_all(&output_directory)?;

    let source_digests = verify_source_manifest(&data_directory)?;
    let traces = load_traces(&data_directory)?;
    let joined = join_receiver_samples(&traces)?;
    if joined.len() < 3 {
        return Err("the MMS receiver cut retained too few joined samples".into());
    }
    let omni = load_omni_context(&data_directory.join("omni_bow_shock.csv"))?;
    let conditioning_end = parse_timestamp_ns(CONDITIONING_END)?;
    let conditioning_samples = joined
        .iter()
        .filter(|sample| sample.chronology_ns < conditioning_end)
        .count();
    let held_out_samples = joined.len() - conditioning_samples;
    if conditioning_samples < 2 || held_out_samples == 0 {
        return Err("the declared MMS conditioning/held-out split is empty".into());
    }

    let (body, cells) = cause_tetrahedral_body()?;
    let body_f_vector = body.active_f_vector();
    let traversal = form_traversal(body, cells)?;
    let initial_standing = traversal.initial_standing();
    let mut world = CausalWorld::new(traversal, initial_standing);

    let geometry_path = output_directory.join("tetrahedral-sections.tsv");
    let generation_path = output_directory.join("generated-mms4.tsv");
    let traversal_path = output_directory.join("traversal-interactions.tsv");
    let mut geometry_writer = BufWriter::new(File::create(&geometry_path)?);
    let mut generation_writer = BufWriter::new(File::create(&generation_path)?);
    let mut traversal_writer = BufWriter::new(File::create(&traversal_path)?);
    writeln!(
        geometry_writer,
        "sample\tsplit\ttime\tmagnetic_clock_offset_1_ns\tmagnetic_clock_offset_2_ns\tmagnetic_clock_offset_3_ns\tmaximum_cross_modal_clock_offset_ns\tw1\tw2\tw3\tgram_determinant\tsigned_six_volume\tface_bx\tface_by\tface_bz\tnormal_fiber_bx\tnormal_fiber_by\tnormal_fiber_bz"
    )?;
    writeln!(
        generation_writer,
        "sample\tsplit\ttime\tspecies\tunit\tcomponent\tpredicted\treturned\tresidual\tstale_residual\tcorrection_before\tcorrection_after"
    )?;
    writeln!(
        traversal_writer,
        "event\tphysical_time\tkind\tfront_chronology\tsite\tarrival_population\tarriving_current\tpositive_current\tnegative_current\tstorage_before\tstorage_after\tbalance\tresidual"
    )?;

    let sections = joined
        .iter()
        .map(tetrahedral_section)
        .collect::<Result<Vec<_>, _>>()?;
    let mut next_event = 10_u64;
    let mut event_chronology = 1_u64;
    let mut traversal_clock = 1_u64;
    let mut grades = GradeCounts::default();
    grades.maximum_clock_offset_ns = joined
        .iter()
        .flat_map(|sample| {
            [
                sample.magnetic_clock_offsets_ns,
                sample.electric_clock_offsets_ns,
                sample.ion_clock_offsets_ns,
            ]
            .into_iter()
            .flatten()
        })
        .map(i64::unsigned_abs)
        .max()
        .unwrap_or(0);
    let initial = &joined[0];
    let initial_current = initial.current(3);
    receive_current(
        &mut world,
        &mut next_event,
        &mut event_chronology,
        traversal_clock,
        cells.spacecraft[3],
        initial_current.clone(),
        EventId(4_000_000),
        "inherited-mms4",
        &initial.source_time,
        &mut traversal_writer,
        &mut grades,
    )?;
    if world.standing().sites[&cells.spacecraft[3]].retained_storage != initial_current {
        return Err("the inherited MMS4 section did not enter reactive storage".into());
    }

    let mut previous = &joined[0];
    let mut previous_section = &sections[0];
    write_geometry_row(
        &mut geometry_writer,
        0,
        "conditioning",
        previous,
        previous_section,
    )?;

    for ordinal in 1..joined.len() {
        let sample = &joined[ordinal];
        let section = &sections[ordinal];
        let split = if sample.chronology_ns < conditioning_end {
            "conditioning"
        } else {
            "held-out"
        };
        write_geometry_row(&mut geometry_writer, ordinal, split, sample, section)?;

        let mut impulses = Vec::with_capacity(3);
        for source in 0..3 {
            let delta = section.face_contributions[source]
                .iter()
                .zip(&previous_section.face_contributions[source])
                .map(|(current, previous)| current - previous)
                .collect();
            impulses.push(ExactCausalTraversalImpulse {
                arrival_chronology: traversal_clock + 1,
                site: cells.spacecraft[source],
                current: delta,
                causes: BTreeSet::from([EventId(
                    1_000_000 + u64::try_from(source)? + 4 * u64::try_from(ordinal)?,
                )]),
            });
        }
        let generation = world.receive(&ExactCausalTraversalEvent {
            event: take_event(&mut next_event)?,
            event_chronology: take_chronology(&mut event_chronology)?,
            receiver_horizon: traversal_clock + 2,
            impulses,
        })?;
        traversal_clock += 2;
        write_traversal_receipts(
            &mut traversal_writer,
            generation.ordinal,
            &sample.source_time,
            "generation",
            &generation.radiation,
            &mut grades,
        )?;
        let predicted = world.standing().sites[&cells.spacecraft[3]]
            .retained_storage
            .clone();
        let actual = sample.current(3);
        let previous_actual = previous.current(3);
        let residual = subtract_current(&actual, &predicted)?;
        let stale_residual = subtract_current(&actual, &previous_actual)?;
        let correction_before = subtract_current(&previous_actual, &previous_section.face_field)?;
        let correction_after = subtract_current(&actual, &section.face_field)?;
        if predicted != add_current(&section.face_field, &correction_before)?
            || residual != subtract_current(&correction_after, &correction_before)?
        {
            return Err("the generated normal-fiber identity failed exactly".into());
        }
        if split == "held-out" {
            grade_components(&residual, &stale_residual, &mut grades)?;
        }
        write_generation_row(
            &mut generation_writer,
            ordinal,
            split,
            sample,
            &predicted,
            &actual,
            &residual,
            &stale_residual,
            &correction_before,
            &correction_after,
        )?;

        let returned = world.receive(&ExactCausalTraversalEvent {
            event: take_event(&mut next_event)?,
            event_chronology: take_chronology(&mut event_chronology)?,
            receiver_horizon: traversal_clock + 1,
            impulses: vec![ExactCausalTraversalImpulse {
                arrival_chronology: traversal_clock + 1,
                site: cells.spacecraft[3],
                current: residual.clone(),
                causes: BTreeSet::from([EventId(2_000_000 + u64::try_from(ordinal)?)]),
            }],
        })?;
        traversal_clock += 1;
        write_traversal_receipts(
            &mut traversal_writer,
            returned.ordinal,
            &sample.source_time,
            "return",
            &returned.radiation,
            &mut grades,
        )?;
        let stored_after_return = &world.standing().sites[&cells.spacecraft[3]].retained_storage;
        if stored_after_return != &actual {
            return Err("the returned MMS4 difference did not reform later standing".into());
        }
        previous = sample;
        previous_section = section;
    }

    geometry_writer.flush()?;
    generation_writer.flush()?;
    traversal_writer.flush()?;
    if !world.standing().is_at_rest() {
        return Err("the final MMS receiver cut retained an unreported open frontier".into());
    }
    if grades.nonzero_balance_residuals != 0 {
        return Err("one exact traversal balance failed in the MMS instrument".into());
    }

    let standing_ron =
        ron::ser::to_string_pretty(world.standing(), ron::ser::PrettyConfig::default())?;
    let remounted: ExactCausalTraversalStanding = ron::from_str(&standing_ron)?;
    world.law().validate_standing(&remounted)?;
    if &remounted != world.standing() {
        return Err("the exact traversal standing changed across rest/remount".into());
    }
    fs::write(
        output_directory.join("traversal-standing.ron"),
        standing_ron,
    )?;
    write_summary(
        &output_directory.join("summary.tsv"),
        joined.len(),
        conditioning_samples,
        held_out_samples,
        &body_f_vector,
        &omni,
        source_digests,
        &grades,
    )?;

    println!("MMS exact causal traversal completed");
    println!(
        "joined_samples={} conditioning={} generated_held_out={} source_files={}",
        joined.len(),
        conditioning_samples,
        held_out_samples,
        source_digests
    );
    println!(
        "tetrahedral_f_vector={:?} maximum_receiver_clock_offset_ns={}",
        body_f_vector, grades.maximum_clock_offset_ns
    );
    println!(
        "held_out_component_comparison better={} equal={} worse={} exact_zero={} nonzero={}",
        total_better(&grades),
        total_equal(&grades),
        total_worse(&grades),
        total_exact_zero(&grades),
        total_nonzero(&grades)
    );
    println!(
        "balance_receipts={} nonzero_balance_residuals={} rested={} remount_equal=true",
        grades.balance_receipts,
        grades.nonzero_balance_residuals,
        world.standing().is_at_rest()
    );
    println!("receipts={}", output_directory.display());
    Ok(())
}

fn form_traversal(
    body: CausalBodyStanding,
    cells: TetrahedralCells,
) -> Result<ExactCausalTraversalLaw, Box<dyn Error>> {
    let source_interaction = |cell| -> Result<_, Box<dyn Error>> {
        Ok(ExactReactiveTraversalInteraction {
            cell,
            name: "MMS face-section emitter".to_owned(),
            storage_extent: 0,
            material_extent: 0,
            morphology_extent: 0,
            base_operator: ExactRatMatrix::identity(TRAVEL_EXTENT)?,
            morphology_operators: Vec::new(),
            feedback: ExactRatMatrix::zero(0, 0)?,
            linear_balances: component_balances(TRAVEL_EXTENT, TRAVEL_EXTENT, 0, 0),
            quadratic_balances: Vec::new(),
        })
    };
    let mut target_rows = Vec::new();
    let mut balances = Vec::new();
    for axis in 0..TRAVEL_EXTENT {
        let mut row = vec![Rat::zero(); 2 * TRAVEL_EXTENT];
        row[axis] = Rat::one();
        row[TRAVEL_EXTENT + axis] = Rat::one();
        target_rows.push(row);
        let mut input_covector = vec![Rat::zero(); 2 * TRAVEL_EXTENT];
        input_covector[axis] = Rat::one();
        input_covector[TRAVEL_EXTENT + axis] = Rat::one();
        let mut output_covector = vec![Rat::zero(); TRAVEL_EXTENT];
        output_covector[axis] = Rat::one();
        balances.push(ExactTraversalLinearBalance {
            name: coordinate_name(axis),
            input_covector,
            output_covector,
        });
    }
    let target = ExactReactiveTraversalInteraction {
        cell: cells.spacecraft[3],
        name: "MMS4 reactive normal-fiber receiver".to_owned(),
        storage_extent: TRAVEL_EXTENT,
        material_extent: 0,
        morphology_extent: 0,
        base_operator: ExactRatMatrix::new(target_rows)?,
        morphology_operators: Vec::new(),
        feedback: ExactRatMatrix::zero(0, TRAVEL_EXTENT)?,
        linear_balances: balances,
        quadratic_balances: Vec::new(),
    };
    let interactions = vec![
        source_interaction(cells.spacecraft[0])?,
        source_interaction(cells.spacecraft[1])?,
        source_interaction(cells.spacecraft[2])?,
        target,
    ];
    let mut passages = Vec::new();
    for source in 0..3 {
        passages.push(ExactCausalTraversalPassage {
            id: CausalTraversalPassageId(u64::try_from(source + 1)?),
            name: format!("MMS{} to MMS4 caused tetrahedral edge", source + 1),
            carrier: cells.to_fourth[source],
            from: cells.spacecraft[source],
            to: cells.spacecraft[3],
            delay: 1,
            transport: ExactRatMatrix::identity(TRAVEL_EXTENT)?,
            linear_balances: component_balances(TRAVEL_EXTENT, TRAVEL_EXTENT, 0, 0),
            quadratic_balances: Vec::new(),
        });
    }
    Ok(ExactCausalTraversalLaw::new(
        body,
        SPECIES
            .iter()
            .map(|species| ExactTraversalCurrentSpecies {
                id: CausalTraversalSpeciesId(species.id),
                name: species.name.to_owned(),
                unit: species.unit.to_owned(),
                extent: species.extent,
            })
            .collect(),
        interactions,
        passages,
    )?)
}

fn component_balances(
    input_extent: usize,
    output_extent: usize,
    input_offset: usize,
    output_offset: usize,
) -> Vec<ExactTraversalLinearBalance> {
    let mut balances = Vec::new();
    for species in SPECIES {
        for component in 0..species.extent {
            let coordinate = species.start + component;
            let mut input_covector = vec![Rat::zero(); input_extent];
            input_covector[input_offset + coordinate] = Rat::one();
            let mut output_covector = vec![Rat::zero(); output_extent];
            output_covector[output_offset + coordinate] = Rat::one();
            balances.push(ExactTraversalLinearBalance {
                name: format!("{} component {component}", species.name),
                input_covector,
                output_covector,
            });
        }
    }
    balances
}

fn coordinate_name(coordinate: usize) -> String {
    for species in SPECIES {
        if coordinate >= species.start && coordinate < species.start + species.extent {
            return format!("{} component {}", species.name, coordinate - species.start);
        }
    }
    format!("undeclared current coordinate {coordinate}")
}

fn cause_tetrahedral_body() -> Result<(CausalBodyStanding, TetrahedralCells), Box<dyn Error>> {
    let law = ExactCausalBodyLaw;
    let vertices = [
        EventCellId(1),
        EventCellId(2),
        EventCellId(3),
        EventCellId(4),
    ];
    let upstream = EventCellId(5);
    let edges = [
        (EventCellId(12), 0_usize, 1_usize),
        (EventCellId(13), 0, 2),
        (EventCellId(14), 0, 3),
        (EventCellId(23), 1, 2),
        (EventCellId(24), 1, 3),
        (EventCellId(34), 2, 3),
    ];
    let mut deeds = Vec::new();
    for (ordinal, vertex) in vertices.iter().enumerate() {
        deeds.push(CausalBodyDeed::FoundCell {
            local: *vertex,
            name: format!("MMS{} moving receiver germ", ordinal + 1),
            grade: 0,
            boundary: Vec::new(),
        });
    }
    deeds.push(CausalBodyDeed::FoundCell {
        local: upstream,
        name: "OMNI bow-shock-shifted upstream receiver".to_owned(),
        grade: 0,
        boundary: Vec::new(),
    });
    for (edge, from, to) in edges {
        deeds.push(CausalBodyDeed::FoundCell {
            local: edge,
            name: format!("MMS{}-MMS{} tetrahedral edge", from + 1, to + 1),
            grade: 1,
            boundary: vec![positive(vertices[to]), negative(vertices[from])],
        });
    }
    let faces = [
        (
            EventCellId(123),
            vec![
                positive(EventCellId(23)),
                negative(EventCellId(13)),
                positive(EventCellId(12)),
            ],
        ),
        (
            EventCellId(124),
            vec![
                positive(EventCellId(24)),
                negative(EventCellId(14)),
                positive(EventCellId(12)),
            ],
        ),
        (
            EventCellId(134),
            vec![
                positive(EventCellId(34)),
                negative(EventCellId(14)),
                positive(EventCellId(13)),
            ],
        ),
        (
            EventCellId(234),
            vec![
                positive(EventCellId(34)),
                negative(EventCellId(24)),
                positive(EventCellId(23)),
            ],
        ),
    ];
    for (face, boundary) in faces {
        deeds.push(CausalBodyDeed::FoundCell {
            local: face,
            name: format!("MMS tetrahedral face {}", face.0),
            grade: 2,
            boundary,
        });
    }
    deeds.push(CausalBodyDeed::FoundCell {
        local: EventCellId(1234),
        name: "MMS measured tetrahedral hypervolume".to_owned(),
        grade: 3,
        boundary: vec![
            positive(EventCellId(234)),
            negative(EventCellId(134)),
            positive(EventCellId(124)),
            negative(EventCellId(123)),
        ],
    });
    for (ordinal, vertex) in vertices.iter().enumerate() {
        deeds.push(CausalBodyDeed::FoundReceiver {
            receiver: ReceiverId(u64::try_from(ordinal + 1)?),
            anchor: CausalCellReference::Event(*vertex),
            upper_horizon: 3,
        });
    }
    deeds.push(CausalBodyDeed::FoundReceiver {
        receiver: ReceiverId(5),
        anchor: CausalCellReference::Event(upstream),
        upper_horizon: 0,
    });
    let successor = law.enact(
        &CausalBodyStanding::default(),
        &CausalBodyEvent {
            event: EventId(1),
            chronology: 1,
            deeds,
        },
    )?;
    let radiation = &successor.radiation[0];
    let lookup = |local| -> Result<CausalCellId, Box<dyn Error>> {
        radiation
            .minted_cells
            .get(&local)
            .copied()
            .ok_or_else(|| format!("missing caused body cell {local:?}").into())
    };
    Ok((
        successor.standing_after,
        TetrahedralCells {
            spacecraft: [
                lookup(vertices[0])?,
                lookup(vertices[1])?,
                lookup(vertices[2])?,
                lookup(vertices[3])?,
            ],
            to_fourth: [
                lookup(EventCellId(14))?,
                lookup(EventCellId(24))?,
                lookup(EventCellId(34))?,
            ],
        },
    ))
}

fn positive(cell: EventCellId) -> EventBoundaryTerm {
    EventBoundaryTerm {
        cell: CausalCellReference::Event(cell),
        coefficient: ComparativeMultiplicity::positive(1_u32),
    }
}

fn negative(cell: EventCellId) -> EventBoundaryTerm {
    EventBoundaryTerm {
        cell: CausalCellReference::Event(cell),
        coefficient: ComparativeMultiplicity::negative(1_u32),
    }
}

fn load_traces(data: &Path) -> Result<[SpacecraftTrace; 4], Box<dyn Error>> {
    let mut traces = Vec::new();
    for spacecraft in 1..=4 {
        let magnetic = load_vector_csv(&data.join(format!("mms{spacecraft}_fgm_b_gse.csv")), true)?;
        let electric = load_vector_csv(&data.join(format!("mms{spacecraft}_edp_e_gse.csv")), true)?;
        let ion = load_ion_csv(&data.join(format!("mms{spacecraft}_fpi_ion_gse.csv")))?;
        let position =
            load_vector_csv(&data.join(format!("mms{spacecraft}_mec_r_gse.csv")), false)?;
        traces.push(SpacecraftTrace {
            magnetic,
            electric,
            ion,
            position,
        });
    }
    traces
        .try_into()
        .map_err(|_| "the MMS trace population is not four".into())
}

fn load_vector_csv(path: &Path, reject_fill: bool) -> Result<Vec<TimedVector>, Box<dyn Error>> {
    let file = BufReader::new(File::open(path)?);
    let mut values = Vec::new();
    for line in file.lines() {
        let line = line?;
        let fields = line.split(',').collect::<Vec<_>>();
        if fields.len() < 4 {
            return Err(format!("malformed HAPI vector row in {}", path.display()).into());
        }
        let vector = ExactVec3([
            parse_decimal_rat(fields[1])?,
            parse_decimal_rat(fields[2])?,
            parse_decimal_rat(fields[3])?,
        ]);
        if reject_fill
            && vector
                .as_slice()
                .iter()
                .any(|value| value.abs() >= Rat::from_integer(BigInt::from(10).pow(20)))
        {
            continue;
        }
        values.push(TimedVector {
            source_time: fields[0].to_owned(),
            chronology_ns: parse_timestamp_ns(fields[0])?,
            value: vector,
        });
    }
    if values.is_empty()
        || values
            .windows(2)
            .any(|pair| pair[0].chronology_ns >= pair[1].chronology_ns)
    {
        return Err(format!("empty or unordered HAPI vector source {}", path.display()).into());
    }
    Ok(values)
}

fn load_ion_csv(path: &Path) -> Result<Vec<TimedIonMoment>, Box<dyn Error>> {
    let file = BufReader::new(File::open(path)?);
    let mut values = Vec::new();
    for line in file.lines() {
        let line = line?;
        let fields = line.split(',').collect::<Vec<_>>();
        if fields.len() < 6 {
            return Err(format!("malformed FPI ion row in {}", path.display()).into());
        }
        let density = parse_decimal_rat(fields[2])?;
        let velocity = ExactVec3([
            parse_decimal_rat(fields[3])?,
            parse_decimal_rat(fields[4])?,
            parse_decimal_rat(fields[5])?,
        ]);
        let fill = Rat::from_integer(BigInt::from(10).pow(20));
        if density.abs() >= fill || velocity.as_slice().iter().any(|value| value.abs() >= fill) {
            continue;
        }
        values.push(TimedIonMoment {
            chronology_ns: parse_timestamp_ns(fields[0])?,
            density,
            velocity,
        });
    }
    if values.is_empty()
        || values
            .windows(2)
            .any(|pair| pair[0].chronology_ns >= pair[1].chronology_ns)
    {
        return Err(format!("empty or unordered FPI ion source {}", path.display()).into());
    }
    Ok(values)
}

fn join_receiver_samples(
    traces: &[SpacecraftTrace; 4],
) -> Result<Vec<JoinedReceiverSample>, Box<dyn Error>> {
    let target = &traces[3].magnetic;
    let mut joined = Vec::new();
    for target_sample in target.iter().step_by(SAMPLE_STRIDE) {
        let mut magnetic = Vec::new();
        let mut electric = Vec::new();
        let mut ion_velocity = Vec::new();
        let mut ion_density = Vec::new();
        let mut positions = Vec::new();
        let mut magnetic_offsets = Vec::new();
        let mut electric_offsets = Vec::new();
        let mut ion_offsets = Vec::new();
        for trace in traces {
            let nearest_magnetic = nearest_vector(&trace.magnetic, target_sample.chronology_ns)?;
            magnetic.push(nearest_magnetic.value.clone());
            magnetic_offsets.push(signed_time_difference(
                nearest_magnetic.chronology_ns,
                target_sample.chronology_ns,
            )?);
            let nearest_electric = nearest_vector(&trace.electric, target_sample.chronology_ns)?;
            electric.push(nearest_electric.value.clone());
            electric_offsets.push(signed_time_difference(
                nearest_electric.chronology_ns,
                target_sample.chronology_ns,
            )?);
            let nearest_ion = nearest_ion(&trace.ion, target_sample.chronology_ns)?;
            ion_velocity.push(nearest_ion.velocity.clone());
            ion_density.push(nearest_ion.density.clone());
            ion_offsets.push(signed_time_difference(
                nearest_ion.chronology_ns,
                target_sample.chronology_ns,
            )?);
            positions.push(interpolate_vector(
                &trace.position,
                target_sample.chronology_ns,
            )?);
        }
        joined.push(JoinedReceiverSample {
            source_time: target_sample.source_time.clone(),
            chronology_ns: target_sample.chronology_ns,
            magnetic: magnetic
                .try_into()
                .map_err(|_| "joined magnetic receiver population is not four")?,
            electric: electric
                .try_into()
                .map_err(|_| "joined electric receiver population is not four")?,
            ion_velocity: ion_velocity
                .try_into()
                .map_err(|_| "joined ion-velocity receiver population is not four")?,
            ion_density: ion_density
                .try_into()
                .map_err(|_| "joined ion-density receiver population is not four")?,
            position: positions
                .try_into()
                .map_err(|_| "joined position receiver population is not four")?,
            magnetic_clock_offsets_ns: magnetic_offsets
                .try_into()
                .map_err(|_| "joined magnetic-clock population is not four")?,
            electric_clock_offsets_ns: electric_offsets
                .try_into()
                .map_err(|_| "joined electric-clock population is not four")?,
            ion_clock_offsets_ns: ion_offsets
                .try_into()
                .map_err(|_| "joined ion-clock population is not four")?,
        });
    }
    Ok(joined)
}

fn nearest_ion(values: &[TimedIonMoment], target: u64) -> Result<&TimedIonMoment, Box<dyn Error>> {
    match values.binary_search_by_key(&target, |value| value.chronology_ns) {
        Ok(ordinal) => Ok(&values[ordinal]),
        Err(0) => Ok(&values[0]),
        Err(ordinal) if ordinal == values.len() => Ok(&values[ordinal - 1]),
        Err(ordinal) => {
            let before = &values[ordinal - 1];
            let after = &values[ordinal];
            if target - before.chronology_ns <= after.chronology_ns - target {
                Ok(before)
            } else {
                Ok(after)
            }
        }
    }
}

fn nearest_vector(values: &[TimedVector], target: u64) -> Result<&TimedVector, Box<dyn Error>> {
    match values.binary_search_by_key(&target, |value| value.chronology_ns) {
        Ok(ordinal) => Ok(&values[ordinal]),
        Err(0) => Ok(&values[0]),
        Err(ordinal) if ordinal == values.len() => Ok(&values[ordinal - 1]),
        Err(ordinal) => {
            let before = &values[ordinal - 1];
            let after = &values[ordinal];
            if target - before.chronology_ns <= after.chronology_ns - target {
                Ok(before)
            } else {
                Ok(after)
            }
        }
    }
}

fn interpolate_vector(values: &[TimedVector], target: u64) -> Result<ExactVec3, Box<dyn Error>> {
    match values.binary_search_by_key(&target, |value| value.chronology_ns) {
        Ok(ordinal) => Ok(values[ordinal].value.clone()),
        Err(0) => Err("receiver chronology lies outside position lineage".into()),
        Err(ordinal) if ordinal >= values.len() => {
            Err("receiver chronology lies outside position lineage".into())
        }
        Err(ordinal) => {
            let before = &values[ordinal - 1];
            let after = &values[ordinal];
            let numerator = target - before.chronology_ns;
            let denominator = after.chronology_ns - before.chronology_ns;
            let phase = Rat::new(BigInt::from(numerator), BigInt::from(denominator));
            Ok(before
                .value
                .add(&after.value.subtract(&before.value).scale(&phase)))
        }
    }
}

fn tetrahedral_section(
    sample: &JoinedReceiverSample,
) -> Result<TetrahedralSection, Box<dyn Error>> {
    let first = &sample.position[0];
    let v0 = sample.position[1].subtract(first);
    let v1 = sample.position[2].subtract(first);
    let v2 = sample.position[3].subtract(first);
    let d00 = v0.dot(&v0);
    let d01 = v0.dot(&v1);
    let d11 = v1.dot(&v1);
    let d20 = v2.dot(&v0);
    let d21 = v2.dot(&v1);
    let gram_determinant = &d00 * &d11 - &d01 * &d01;
    if gram_determinant.is_zero() {
        return Err("the MMS1-MMS2-MMS3 receiver face became degenerate".into());
    }
    let second_weight = (&d11 * &d20 - &d01 * &d21) / &gram_determinant;
    let third_weight = (&d00 * &d21 - &d01 * &d20) / &gram_determinant;
    let first_weight = Rat::one() - &second_weight - &third_weight;
    let weights = [first_weight, second_weight, third_weight];
    let face_contributions = [
        scale_current(&sample.current(0), &weights[0]),
        scale_current(&sample.current(1), &weights[1]),
        scale_current(&sample.current(2), &weights[2]),
    ];
    let face_field = add_current(
        &add_current(&face_contributions[0], &face_contributions[1])?,
        &face_contributions[2],
    )?;
    let signed_six_volume = v2.dot(&v0.cross(&v1));
    if signed_six_volume.is_zero() {
        return Err("the four MMS receivers ceased to span a tetrahedral volume".into());
    }
    Ok(TetrahedralSection {
        weights,
        face_contributions,
        face_field,
        gram_determinant,
        signed_six_volume,
    })
}

fn receive_current(
    world: &mut CausalWorld<ExactCausalTraversalLaw>,
    next_event: &mut u64,
    event_chronology: &mut u64,
    receiver_horizon: u64,
    site: CausalCellId,
    current: Vec<Rat>,
    cause: EventId,
    kind: &str,
    physical_time: &str,
    writer: &mut impl Write,
    grades: &mut GradeCounts,
) -> Result<(), Box<dyn Error>> {
    let receipt = world.receive(&ExactCausalTraversalEvent {
        event: take_event(next_event)?,
        event_chronology: take_chronology(event_chronology)?,
        receiver_horizon,
        impulses: vec![ExactCausalTraversalImpulse {
            arrival_chronology: receiver_horizon,
            site,
            current,
            causes: BTreeSet::from([cause]),
        }],
    })?;
    write_traversal_receipts(
        writer,
        receipt.ordinal,
        physical_time,
        kind,
        &receipt.radiation,
        grades,
    )
}

fn write_traversal_receipts(
    writer: &mut impl Write,
    ordinal: u64,
    physical_time: &str,
    kind: &str,
    radiation: &[holonic_engine::ExactCausalTraversalRadiation],
    grades: &mut GradeCounts,
) -> Result<(), Box<dyn Error>> {
    for emitted in radiation {
        for interaction in &emitted.interactions {
            for balance in &interaction.balances {
                grades.balance_receipts += 1;
                if !balance.residual.is_zero() {
                    grades.nonzero_balance_residuals += 1;
                }
                write!(
                    writer,
                    "{ordinal}\t{physical_time}\t{kind}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t",
                    interaction.chronology,
                    interaction.site.0,
                    interaction.arrival_population,
                    format_rat_slice(&interaction.arriving_current),
                    format_rat_slice(&interaction.arriving_positive_current),
                    format_rat_slice(&interaction.arriving_negative_current),
                    format_rat_slice(&interaction.storage_before),
                    format_rat_slice(&interaction.storage_after),
                )?;
                writeln!(
                    writer,
                    "{}\t{}",
                    balance.name,
                    format_rat(&balance.residual)
                )?;
            }
            for departure in &interaction.departures {
                for balance in &departure.balances {
                    grades.balance_receipts += 1;
                    if !balance.residual.is_zero() {
                        grades.nonzero_balance_residuals += 1;
                    }
                    write!(
                        writer,
                        "{ordinal}\t{physical_time}\t{kind}/passage-{}\t{}\t{}\t1\t{}\t\t\t\t\t",
                        departure.passage.0,
                        interaction.chronology,
                        interaction.site.0,
                        format_rat_slice(&departure.current),
                    )?;
                    writeln!(
                        writer,
                        "{}\t{}",
                        balance.name,
                        format_rat(&balance.residual)
                    )?;
                }
            }
        }
    }
    Ok(())
}

fn write_geometry_row(
    writer: &mut impl Write,
    ordinal: usize,
    split: &str,
    sample: &JoinedReceiverSample,
    section: &TetrahedralSection,
) -> Result<(), Box<dyn Error>> {
    let target_current = sample.current(3);
    let normal_fiber = subtract_current(&target_current, &section.face_field)?;
    let maximum_offset = [
        sample.magnetic_clock_offsets_ns,
        sample.electric_clock_offsets_ns,
        sample.ion_clock_offsets_ns,
    ]
    .into_iter()
    .flatten()
    .map(i64::unsigned_abs)
    .max()
    .unwrap_or(0);
    write!(
        writer,
        "{ordinal}\t{split}\t{}\t{}\t{}\t{}\t{}\t",
        sample.source_time,
        sample.magnetic_clock_offsets_ns[0],
        sample.magnetic_clock_offsets_ns[1],
        sample.magnetic_clock_offsets_ns[2],
        maximum_offset
    )?;
    write_rat_array(writer, &section.weights)?;
    write!(
        writer,
        "\t{}\t{}\t",
        format_rat(&section.gram_determinant),
        format_rat(&section.signed_six_volume)
    )?;
    write_rat_vector(writer, &section.face_field[..3])?;
    write!(writer, "\t")?;
    write_rat_vector(writer, &normal_fiber[..3])?;
    writeln!(writer)?;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn write_generation_row(
    writer: &mut impl Write,
    ordinal: usize,
    split: &str,
    sample: &JoinedReceiverSample,
    predicted: &[Rat],
    actual: &[Rat],
    residual: &[Rat],
    stale_residual: &[Rat],
    correction_before: &[Rat],
    correction_after: &[Rat],
) -> Result<(), Box<dyn Error>> {
    for species in SPECIES {
        for component in 0..species.extent {
            let coordinate = species.start + component;
            writeln!(
                writer,
                "{ordinal}\t{split}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                sample.source_time,
                species.name,
                species.unit,
                component,
                format_rat(&predicted[coordinate]),
                format_rat(&actual[coordinate]),
                format_rat(&residual[coordinate]),
                format_rat(&stale_residual[coordinate]),
                format_rat(&correction_before[coordinate]),
                format_rat(&correction_after[coordinate])
            )?;
        }
    }
    Ok(())
}

fn grade_components(
    residual: &[Rat],
    stale_residual: &[Rat],
    grades: &mut GradeCounts,
) -> Result<(), Box<dyn Error>> {
    if residual.len() != TRAVEL_EXTENT || stale_residual.len() != TRAVEL_EXTENT {
        return Err("graded current does not span the declared species".into());
    }
    for (species_ordinal, species) in SPECIES.iter().enumerate() {
        let grade = &mut grades.species[species_ordinal];
        for component in 0..species.extent {
            let coordinate = species.start + component;
            if residual[coordinate].is_zero() {
                grade.exact_zero_residual += 1;
            } else {
                grade.nonzero_residual += 1;
            }
            match residual[coordinate]
                .abs()
                .cmp(&stale_residual[coordinate].abs())
            {
                std::cmp::Ordering::Less => grade.better_than_stale += 1,
                std::cmp::Ordering::Equal => grade.equal_to_stale += 1,
                std::cmp::Ordering::Greater => grade.worse_than_stale += 1,
            }
        }
    }
    Ok(())
}

fn load_omni_context(path: &Path) -> Result<OmniContext, Box<dyn Error>> {
    let target = parse_timestamp_ns("2015-10-16T13:07:00.000000000Z")?;
    let file = BufReader::new(File::open(path)?);
    let mut candidates = Vec::new();
    for line in file.lines() {
        let line = line?;
        let fields = line.split(',').collect::<Vec<_>>();
        if fields.len() < 9 {
            return Err("malformed OMNI HAPI row".into());
        }
        let magnetic = ExactVec3([
            parse_decimal_rat(fields[1])?,
            parse_decimal_rat(fields[2])?,
            parse_decimal_rat(fields[3])?,
        ]);
        let velocity = ExactVec3([
            parse_decimal_rat(fields[4])?,
            parse_decimal_rat(fields[5])?,
            parse_decimal_rat(fields[6])?,
        ]);
        let proton_density = parse_decimal_rat(fields[7])?;
        let pressure = parse_decimal_rat(fields[8])?;
        if velocity
            .as_slice()
            .iter()
            .any(|value| value.abs() > Rat::from_integer(BigInt::from(10_000)))
            || proton_density > Rat::from_integer(BigInt::from(100))
        {
            continue;
        }
        candidates.push((
            parse_timestamp_ns(fields[0])?,
            OmniContext {
                source_time: fields[0].to_owned(),
                magnetic,
                velocity,
                proton_density,
                pressure,
            },
        ));
    }
    candidates
        .into_iter()
        .min_by_key(|(time, _)| time.abs_diff(target))
        .map(|(_, context)| context)
        .ok_or_else(|| "no valid OMNI upstream context reached the event".into())
}

#[allow(clippy::too_many_arguments)]
fn write_summary(
    path: &Path,
    joined_samples: usize,
    conditioning_samples: usize,
    held_out_samples: usize,
    body_f_vector: &BTreeMap<u32, usize>,
    omni: &OmniContext,
    source_digests: usize,
    grades: &GradeCounts,
) -> Result<(), Box<dyn Error>> {
    let mut writer = BufWriter::new(File::create(path)?);
    writeln!(writer, "property\tvalue")?;
    writeln!(
        writer,
        "source\tNASA CDAWeb MMS FGM/EDP/FPI/MEC and OMNI HRO2"
    )?;
    writeln!(
        writer,
        "event\t2015-10-16 magnetopause electron-diffusion-region crossing"
    )?;
    writeln!(writer, "joined_samples\t{joined_samples}")?;
    writeln!(writer, "conditioning_samples\t{conditioning_samples}")?;
    writeln!(writer, "generated_held_out_samples\t{held_out_samples}")?;
    writeln!(writer, "sample_stride\t{SAMPLE_STRIDE}")?;
    writeln!(writer, "source_files_verified\t{source_digests}")?;
    writeln!(writer, "causal_body_f_vector\t{body_f_vector:?}")?;
    writeln!(
        writer,
        "maximum_receiver_clock_offset_ns\t{}",
        grades.maximum_clock_offset_ns
    )?;
    writeln!(
        writer,
        "generated_components_better_than_stale\t{}",
        total_better(grades)
    )?;
    writeln!(
        writer,
        "generated_components_equal_to_stale\t{}",
        total_equal(grades)
    )?;
    writeln!(
        writer,
        "generated_components_worse_than_stale\t{}",
        total_worse(grades)
    )?;
    writeln!(
        writer,
        "exact_zero_prediction_residual_components\t{}",
        total_exact_zero(grades)
    )?;
    writeln!(
        writer,
        "nonzero_prediction_residual_components\t{}",
        total_nonzero(grades)
    )?;
    for (ordinal, species) in SPECIES.iter().enumerate() {
        let grade = &grades.species[ordinal];
        writeln!(
            writer,
            "{}_components_better_than_stale\t{}",
            species.name, grade.better_than_stale
        )?;
        writeln!(
            writer,
            "{}_components_equal_to_stale\t{}",
            species.name, grade.equal_to_stale
        )?;
        writeln!(
            writer,
            "{}_components_worse_than_stale\t{}",
            species.name, grade.worse_than_stale
        )?;
        writeln!(
            writer,
            "{}_exact_zero_residual\t{}",
            species.name, grade.exact_zero_residual
        )?;
        writeln!(
            writer,
            "{}_nonzero_residual\t{}",
            species.name, grade.nonzero_residual
        )?;
    }
    writeln!(
        writer,
        "exact_balance_receipts\t{}",
        grades.balance_receipts
    )?;
    writeln!(
        writer,
        "nonzero_balance_residuals\t{}",
        grades.nonzero_balance_residuals
    )?;
    writeln!(writer, "final_open_frontier\t0")?;
    writeln!(writer, "rest_remount_equal\ttrue")?;
    writeln!(writer, "omni_context_time\t{}", omni.source_time)?;
    writeln!(writer, "omni_b_gse\t{}", format_rat_array(&omni.magnetic.0))?;
    writeln!(writer, "omni_v_gse\t{}", format_rat_array(&omni.velocity.0))?;
    writeln!(
        writer,
        "omni_proton_density\t{}",
        format_rat(&omni.proton_density)
    )?;
    writeln!(writer, "omni_pressure\t{}", format_rat(&omni.pressure))?;
    writer.flush()?;
    Ok(())
}

fn verify_source_manifest(directory: &Path) -> Result<usize, Box<dyn Error>> {
    let manifest = BufReader::new(File::open(directory.join("source-sha256.tsv"))?);
    let mut verified = 0_usize;
    for line in manifest.lines() {
        let line = line?;
        let (expected, relative) = line
            .split_once("  ")
            .ok_or("malformed source SHA-256 manifest")?;
        let relative = relative.strip_prefix("./").unwrap_or(relative);
        let mut file = File::open(directory.join(relative))?;
        let mut hasher = Sha256::new();
        let mut buffer = [0_u8; 64 * 1024];
        loop {
            let read = file.read(&mut buffer)?;
            if read == 0 {
                break;
            }
            hasher.update(&buffer[..read]);
        }
        let actual = format!("{:x}", hasher.finalize());
        if actual != expected {
            return Err(format!("source digest changed for {relative}").into());
        }
        verified += 1;
    }
    if verified == 0 {
        return Err("the source digest manifest is empty".into());
    }
    Ok(verified)
}

fn parse_decimal_rat(value: &str) -> Result<Rat, Box<dyn Error>> {
    let value = value.trim();
    if value.is_empty() {
        return Err("an exact decimal landmark is empty".into());
    }
    let (mantissa, exponent) = match value.find(['e', 'E']) {
        Some(index) => (&value[..index], value[index + 1..].parse::<i32>()?),
        None => (value, 0),
    };
    let negative = mantissa.starts_with('-');
    let unsigned = mantissa.strip_prefix(['-', '+']).unwrap_or(mantissa);
    let (whole, fractional) = unsigned.split_once('.').unwrap_or((unsigned, ""));
    if whole.is_empty() && fractional.is_empty() {
        return Err("an exact decimal landmark has no digits".into());
    }
    let digits = format!("{whole}{fractional}");
    let mut numerator = digits.parse::<BigInt>()?;
    if negative {
        numerator = -numerator;
    }
    let decimal_exponent = exponent - i32::try_from(fractional.len())?;
    if decimal_exponent >= 0 {
        numerator *= BigInt::from(10).pow(u32::try_from(decimal_exponent)?);
        Ok(Rat::from_integer(numerator))
    } else {
        let denominator = BigInt::from(10).pow(u32::try_from(-decimal_exponent)?);
        Ok(Rat::new(numerator, denominator))
    }
}

fn parse_timestamp_ns(value: &str) -> Result<u64, Box<dyn Error>> {
    let time = value
        .split_once('T')
        .map(|(_, time)| time)
        .ok_or("HAPI timestamp has no time separator")?
        .strip_suffix('Z')
        .ok_or("HAPI timestamp has no UTC suffix")?;
    let mut fields = time.split(':');
    let hour = fields
        .next()
        .ok_or("timestamp has no hour")?
        .parse::<u64>()?;
    let minute = fields
        .next()
        .ok_or("timestamp has no minute")?
        .parse::<u64>()?;
    let second_field = fields.next().ok_or("timestamp has no second")?;
    if fields.next().is_some() {
        return Err("timestamp has excess clock fields".into());
    }
    let (second, fraction) = second_field.split_once('.').unwrap_or((second_field, ""));
    let second = second.parse::<u64>()?;
    if fraction.len() > 9 || !fraction.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err("timestamp subsecond field is malformed".into());
    }
    let mut nanos = fraction.parse::<u64>().unwrap_or(0);
    nanos *= 10_u64.pow(u32::try_from(9 - fraction.len())?);
    Ok((hour * 3_600 + minute * 60 + second) * 1_000_000_000 + nanos)
}

fn signed_time_difference(left: u64, right: u64) -> Result<i64, Box<dyn Error>> {
    if left >= right {
        Ok(i64::try_from(left - right)?)
    } else {
        Ok(-i64::try_from(right - left)?)
    }
}

fn take_event(next: &mut u64) -> Result<EventId, Box<dyn Error>> {
    let event = EventId(*next);
    *next = next.checked_add(1).ok_or("event identity overflow")?;
    Ok(event)
}

fn take_chronology(next: &mut u64) -> Result<u64, Box<dyn Error>> {
    let chronology = *next;
    *next = next.checked_add(1).ok_or("event chronology overflow")?;
    Ok(chronology)
}

fn format_rat(value: &Rat) -> String {
    if value.denom().is_one() {
        value.numer().to_string()
    } else {
        format!("{}/{}", value.numer(), value.denom())
    }
}

fn format_rat_array(values: &[Rat; 3]) -> String {
    format_rat_slice(values)
}

fn format_rat_slice(values: &[Rat]) -> String {
    values.iter().map(format_rat).collect::<Vec<_>>().join(",")
}

fn write_rat_array(writer: &mut impl Write, values: &[Rat; 3]) -> Result<(), std::io::Error> {
    write!(
        writer,
        "{}\t{}\t{}",
        format_rat(&values[0]),
        format_rat(&values[1]),
        format_rat(&values[2])
    )
}

fn write_rat_vector(writer: &mut impl Write, values: &[Rat]) -> Result<(), std::io::Error> {
    for axis in 0..3 {
        if axis != 0 {
            write!(writer, "\t")?;
        }
        if let Some(value) = values.get(axis) {
            write!(writer, "{}", format_rat(value))?;
        }
    }
    Ok(())
}

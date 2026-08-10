//! The channel population is the receiver's, and the comparison extent is the caller's.
//!
//! Three authored levels were excised on 2026-08-09 and this driver is their orbit
//! (`canon/THE_CONTAMINANT_PROTOCOL.md` §4, `canon/THE_AUTHORED_LEVEL.md` §5.1):
//!
//! ```text
//!   receiver_phase_atlas.rs:24   CHANNEL_COUNT = 3              -> the occurrence declares it
//!   coupled_informant.rs:40      COUPLED_PHASE_EXTENT = 18      -> read off the declared chart
//!   coupled_informant.rs:41      COUPLED_SPECTRAL_BANDS: [_; 5] -> the chart's band population
//! ```
//!
//! It returns the artifacts rather than counts: the germ addresses each receiver founds, the
//! coordinate kinds each chart names, and the exact rational phase vectors the coupled law emits at
//! three different extents (14, 18, 24).
//!
//! **The declared material is this driver's own**, and it says so. The RELAMPAGO run this organ was
//! built for needs `data/relampago-lightning/{raw/glm,raw/abi,raw/igra}`, which do not exist in this
//! tree; the tiger raster the atlas drivers default to
//! (`/tmp/codex-clipboard-T9jMYB.png`) does not either. Nothing below stands in for either of them.
//!
//! ```text
//! cargo run -p holonic-engine --example the_channel_population_is_the_receivers
//! ```

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::num::NonZeroUsize;
use std::sync::Arc;

use holonic_engine::{
    AtmosphericContactSelection, AtmosphericInverseResolution, AtmosphericInverseWork,
    AtmosphericLayerId, AtmosphericProfileId, AtmosphericReceiverBody, AtmosphericResolutionId,
    AtmosphericVerticalCoordinate, AtmosphericVerticalFiber, CausalWorld, CoupledInformantEvent,
    CoupledInformantLaw, CoupledInformantStanding, CoupledPhaseChart, EventId,
    ExactDifferenceVector, ExactInterval, HydrostaticChordReceipt, ImageExtent,
    LearnedPartitionRelation, OpaqueThermalChordDoctrine, PredictedReceiverRelation, RayFamily,
    ReceiverChannelSample, ReceiverCoordinateFamilyId, ReceiverPhaseAtlasError,
    ReceiverPhaseAtlasEvent, ReceiverPhaseAtlasLaw, ReceiverPhaseAtlasStanding,
    ReceiverPhaseSectionOccurrence, ReceiverPredictionId, ReceiverRelationPrediction,
    ReceiverRelationState, ReceiverTestimonyId, ReturnedAlgorithmId, SpectralAddressStatus,
    SpectralBandId, SpectralContactTemporality, SpectralReceiverContact,
    SpectralReceiverOccurrence, SpectralScanId, VerticalFiberSupport,
};
use num_bigint::BigInt;
use relational_geometry::{Rat, RatVec3, ReceiverId};

fn main() -> Result<(), Box<dyn Error>> {
    println!("== the phase atlas reads the channel population the receiver declares ==\n");
    let atlas = atlas_orbit()?;
    println!("\n== a sample that does not meet the declaration is refused by name ==\n");
    channel_refusal()?;
    println!(
        "\n== the coupled comparison membrane is declared, and the extent is read off it ==\n"
    );
    chart_orbit()?;
    println!("\n== the coupled law returns exact phase vectors at an extent that is not 18 ==\n");
    coupled_orbit()?;
    println!("\n== summary ==\n");
    println!("{atlas}");
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// The receiver phase atlas.
// ---------------------------------------------------------------------------------------------

/// One geometric scene, read at a declared channel population. Channel `c` carries a compact
/// quadratic bump at its own column over a deterministic ripple, so the summed energy landscape
/// that decides which addresses survive is a function of how many channels the receiver declares.
fn banded_reading(column: i32, row: i32, channel: usize) -> u8 {
    let ordinal = i32::try_from(channel).expect("channel ordinals fit i32");
    let horizontal = column - (6 + 7 * ordinal);
    let vertical = row - 20;
    let bump = 255 - 5 * (horizontal * horizontal + vertical * vertical);
    let ripple = 11 * (column * 3 + row * 5 + ordinal * 2).rem_euclid(7);
    u8::try_from((bump + ripple).clamp(0, 255)).expect("a clamped reading fits u8")
}

fn banded_section(channels: usize) -> ReceiverPhaseSectionOccurrence {
    let extent = ImageExtent {
        width: 41,
        height: 41,
    };
    let samples = (0..extent.height)
        .flat_map(|row| {
            (0..extent.width).map(move |column| {
                Some(ReceiverChannelSample(
                    (0..channels)
                        .map(|channel| {
                            banded_reading(
                                i32::try_from(column).expect("extent fits i32"),
                                i32::try_from(row).expect("extent fits i32"),
                                channel,
                            )
                        })
                        .collect(),
                ))
            })
        })
        .collect();
    ReceiverPhaseSectionOccurrence {
        source_image: None,
        source_lineage: 1,
        receiver: ReceiverId(1),
        rays: RayFamily::Central {
            center: RatVec3::zero(),
            forward: RatVec3::from_i64(0, 0, 1),
            horizontal: RatVec3::from_i64(1, 0, 0),
            vertical: RatVec3::from_i64(0, 1, 0),
        },
        extent,
        channels: NonZeroUsize::new(channels).expect("a receiver has at least one channel"),
        samples,
    }
}

fn read_at(channels: usize) -> Result<ReceiverPhaseAtlasStanding, Box<dyn Error>> {
    let law = ReceiverPhaseAtlasLaw;
    let mut world = CausalWorld::new(law.clone(), law.initial_standing());
    world.receive(&ReceiverPhaseAtlasEvent {
        event: EventId(1),
        chronology: 1,
        sections: vec![banded_section(channels)],
    })?;
    Ok(world.standing().clone())
}

fn addresses(standing: &ReceiverPhaseAtlasStanding) -> BTreeSet<(u32, u32)> {
    standing
        .germs
        .values()
        .map(|germ| (germ.witness.row, germ.witness.column))
        .collect()
}

fn atlas_orbit() -> Result<String, Box<dyn Error>> {
    let mut readings = BTreeMap::new();
    for channels in 1_usize..=5 {
        let standing = read_at(channels)?;
        standing.validate()?;
        println!(
            "channels {channels}: {} germs, {} passages, {} connections, {} cycles",
            standing.germs.len(),
            standing.germ_populations.len(),
            standing.connections.len(),
            standing.cycles.len()
        );
        for germ in standing.germs.values() {
            println!(
                "    row {:>3} column {:>3}  dominant {}  horizon {}  radii {:?}  species {:?}  \
                 jet width {}",
                germ.witness.row,
                germ.witness.column,
                germ.dominant_coordinate,
                germ.horizon,
                germ.persistence_radii,
                germ.signature.conic_species,
                germ.jet.channel_population(),
            );
        }
        readings.insert(channels, standing);
    }

    // The distinguishing word: the least address on which two receivers disagree.
    let mut lines = Vec::new();
    for left in 1_usize..=5 {
        for right in left + 1..=5 {
            let separating = addresses(&readings[&left])
                .symmetric_difference(&addresses(&readings[&right]))
                .copied()
                .min();
            lines.push(match separating {
                Some((row, column)) => {
                    format!("  {left} vs {right} channels: separated at row {row} column {column}")
                }
                None => format!("  {left} vs {right} channels: NO SEPARATING ADDRESS"),
            });
        }
    }
    println!("\ndistinguishing addresses:");
    for line in &lines {
        println!("{line}");
    }

    Ok(readings
        .iter()
        .map(|(channels, standing)| {
            format!(
                "atlas at {channels} channels: {} germs, {} passages",
                standing.germs.len(),
                standing.germ_populations.len()
            )
        })
        .collect::<Vec<_>>()
        .join("\n"))
}

fn channel_refusal() -> Result<(), Box<dyn Error>> {
    let law = ReceiverPhaseAtlasLaw;
    for supplied in [2_usize, 4] {
        let mut section = banded_section(3);
        section.samples[7] = Some(ReceiverChannelSample(vec![9; supplied]));
        let mut world = CausalWorld::new(law.clone(), law.initial_standing());
        let returned = world.receive(&ReceiverPhaseAtlasEvent {
            event: EventId(1),
            chronology: 1,
            sections: vec![section],
        });
        match returned {
            Err(error @ ReceiverPhaseAtlasError::ChannelPopulationDisagreement { .. }) => {
                println!("  {supplied}-channel sample into a 3-channel receiver -> {error}");
            }
            other => return Err(format!("the refusal did not fire: {other:?}").into()),
        }
    }
    // The control can fail: the honest receiver is admitted.
    let honest = read_at(3)?;
    println!(
        "  the honest 3-channel receiver is admitted: {} germs",
        honest.germs.len()
    );
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// The coupled comparison membrane.
// ---------------------------------------------------------------------------------------------

fn chart_orbit() -> Result<(), Box<dyn Error>> {
    let charts = [
        (
            "RELAMPAGO: GOES-16 ABI 08/09/10/11/13 against 13, GLM's four optical scalars",
            CoupledPhaseChart::new(4, abi_bands().to_vec(), SpectralBandId(13))?,
        ),
        (
            "one band, one optical coordinate: no chords at all",
            CoupledPhaseChart::new(1, vec![SpectralBandId(4)], SpectralBandId(4))?,
        ),
        (
            "nine-band hyperspectral on a six-coordinate optical face",
            CoupledPhaseChart::new(
                6,
                (20..29).map(SpectralBandId).collect(),
                SpectralBandId(24),
            )?,
        ),
    ];
    for (name, chart) in &charts {
        println!("{name}\n  extent {}", chart.extent());
        for (coordinate, kind) in chart.coordinate_kinds().iter().enumerate() {
            println!("    {coordinate:>2}  {kind:?}");
        }
    }
    println!(
        "\n  extents: {:?}",
        charts
            .iter()
            .map(|(_, chart)| chart.extent())
            .collect::<Vec<_>>()
    );
    Ok(())
}

fn coupled_orbit() -> Result<(), Box<dyn Error>> {
    let populations: [&[SpectralBandId]; 3] = [
        &[SpectralBandId(8), SpectralBandId(11), SpectralBandId(13)],
        &abi_bands(),
        &[
            SpectralBandId(7),
            SpectralBandId(8),
            SpectralBandId(9),
            SpectralBandId(10),
            SpectralBandId(11),
            SpectralBandId(12),
            SpectralBandId(13),
            SpectralBandId(14),
        ],
    ];
    for bands in populations {
        let declared = CoupledPhaseChart::new(4, bands.to_vec(), SpectralBandId(13))?;
        let resolution = resolution_over(bands);

        // The same chart, read off the material rather than declared, and the two must agree.
        let material = CoupledPhaseChart::from_resolution(&resolution)?;
        if material != declared {
            return Err(format!(
                "declared and material charts disagree: {declared:?} vs {material:?}"
            )
            .into());
        }

        let mut world = CausalWorld::new(
            CoupledInformantLaw::serial(),
            CoupledInformantStanding::new(declared.clone()),
        );
        let successor = world.receive(&CoupledInformantEvent::Generate {
            event: EventId(1),
            chronology: 1,
            source_grade_precondition: None,
            resolution: Arc::new(resolution),
        })?;
        let work = &successor.radiation[0].work;
        let prediction = successor.radiation[0]
            .prediction
            .as_deref()
            .ok_or("the generation radiated no prediction")?;
        println!(
            "{} bands -> extent {} (work says {}), {} relations",
            bands.len(),
            declared.extent(),
            work.phase_extent,
            prediction.relations.len()
        );
        for relation in &prediction.relations {
            for branch in &relation.branches {
                let phase = branch
                    .phase
                    .0
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" ");
                println!(
                    "    {:?} {:?} [{}] {phase}",
                    relation.members,
                    relation.origin,
                    branch.phase.0.len()
                );
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------------------------
// A small declared atmospheric fixture. It is this driver's own and stands in for nothing.
// ---------------------------------------------------------------------------------------------

fn abi_bands() -> [SpectralBandId; 5] {
    [
        SpectralBandId(8),
        SpectralBandId(9),
        SpectralBandId(10),
        SpectralBandId(11),
        SpectralBandId(13),
    ]
}

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn contact_over(temperature_offset: i64, bands: &[SpectralBandId]) -> SpectralReceiverContact {
    let mut quality = BTreeMap::new();
    let mut temperatures = BTreeMap::new();
    for (offset, band) in bands.iter().copied().enumerate() {
        quality.insert(band, 0);
        temperatures.insert(
            band,
            rat(270 + temperature_offset + i64::try_from(offset).expect("band ordinals fit i64")),
        );
    }
    SpectralReceiverContact {
        scan: SpectralScanId(11),
        receiver: ReceiverId(19),
        source: "declared driver fixture, not a native ABI section".to_owned(),
        clock: ExactInterval::new(rat(0), rat(10)).expect("an ordered clock"),
        row: 7,
        column: 13,
        address_status: SpectralAddressStatus::SourceDeclaredExact,
        address_doctrine: "declared driver fixture".to_owned(),
        data_quality_flags: quality,
        brightness_temperature_kelvin: temperatures,
    }
}

fn hydrostatic(height: i64) -> HydrostaticChordReceipt {
    HydrostaticChordReceipt {
        schema: "declared-driver-fixture-hydrostatic".to_owned(),
        vertical_coordinate: AtmosphericVerticalCoordinate::IndependentGeometricHeight,
        pressure_log_ratio: ExactInterval::point(rat(1)),
        inverse_temperature_chord: rat(height),
        acceleration_over_gas_constant: ExactInterval::point(rat(1)),
        effective_acceleration_metre_per_second_squared: ExactInterval::point(rat(10)),
        specific_gas_constant: rat(287),
        independent_gravity_testimony: true,
    }
}

fn resolution_over(bands: &[SpectralBandId]) -> AtmosphericInverseResolution {
    let family = ReceiverCoordinateFamilyId(71);
    let algorithm = ReturnedAlgorithmId(73);
    let left = ReceiverTestimonyId(1);
    let right = ReceiverTestimonyId(2);
    let difference = ExactDifferenceVector(vec![rat(1), rat(2), rat(3), rat(4)]);
    let prediction = Arc::new(ReceiverRelationPrediction {
        schema: "declared-driver-fixture-prediction".to_owned(),
        id: ReceiverPredictionId(17),
        caused_by: EventId(19),
        family,
        algorithm,
        chronology: 1,
        source: "declared driver fixture optical horizon".to_owned(),
        aperture: Vec::new(),
        occurrences: vec![left, right],
        candidate_relations: vec![PredictedReceiverRelation {
            members: [left, right],
            difference,
            state: ReceiverRelationState::Open,
        }],
        forced_components: Vec::new(),
        relation_before: LearnedPartitionRelation {
            schema: "declared-driver-fixture-relation".to_owned(),
            family,
            algorithm,
            positive_maxima: Vec::new(),
            negative_minima: Vec::new(),
            testimony_events: BTreeSet::new(),
            returned_cells: 0,
        },
    });
    let profile = AtmosphericProfileId(23);
    let fiber = |testimony, identity, level, support, departure, height| AtmosphericVerticalFiber {
        testimony,
        source_identity: identity,
        scan: SpectralScanId(11),
        spectral_receiver: ReceiverId(19),
        profile,
        layer: AtmosphericLayerId {
            profile,
            lower_level: level,
        },
        support: VerticalFiberSupport::Point(rat(support)),
        brightness_temperature_kelvin: rat(270 + level as i64),
        scan_departure_seconds: rat(departure),
        temporality: SpectralContactTemporality::Concurrent,
        pressure_pascal: ExactInterval::point(rat(90_000 - 10_000 * level as i64)),
        layer_temperature_kelvin: ExactInterval::point(rat(270 + level as i64)),
        hydrostatic: hydrostatic(height),
    };
    AtmosphericInverseResolution {
        schema: "declared-driver-fixture-resolution".to_owned(),
        id: AtmosphericResolutionId(29),
        caused_by: EventId(31),
        profile,
        prediction: prediction.id,
        prediction_event: prediction.caused_by,
        source_prediction: prediction,
        doctrine: OpaqueThermalChordDoctrine {
            thermal_band: SpectralBandId(13),
            specific_gas_constant: rat(287),
            logarithm_terms: 8,
        },
        occurrences: vec![left, right],
        spectral_occurrences: vec![
            SpectralReceiverOccurrence {
                testimony: left,
                source_identity: 101,
                latitude_degree: rat(0),
                longitude_degree: rat(0),
                clock: rat(0),
                radiant_energy: rat(0),
                contacts: vec![contact_over(0, bands)],
            },
            SpectralReceiverOccurrence {
                testimony: right,
                source_identity: 102,
                latitude_degree: rat(1),
                longitude_degree: rat(2),
                clock: rat(3),
                radiant_energy: rat(4),
                contacts: vec![contact_over(1, bands)],
            },
        ],
        contact_selections: vec![
            AtmosphericContactSelection {
                testimony: left,
                source_identity: 101,
                selected_scans: vec![SpectralScanId(11)],
                minimum_departure_seconds: Some(rat(0)),
            },
            AtmosphericContactSelection {
                testimony: right,
                source_identity: 102,
                selected_scans: vec![SpectralScanId(11)],
                minimum_departure_seconds: Some(rat(1)),
            },
        ],
        vertical_fibers: vec![
            fiber(left, 101, 0, 100, 0, 100),
            fiber(right, 102, 1, 200, 1, 200),
        ],
        lifted_relations: Vec::new(),
        bodies: vec![AtmosphericReceiverBody {
            source_component: 0,
            members: vec![left, right],
            vertical_fibers: vec![0, 1],
            lifted_relations: Vec::new(),
        }],
        obstructions: Vec::new(),
        work: AtmosphericInverseWork::default(),
    }
}

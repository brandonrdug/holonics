use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt::Write as _;
use std::fs;
use std::path::PathBuf;

use holonic_engine::{
    AnalyticCirculationProbeId, AnalyticFieldArcId, AnalyticFieldJunctionId,
    AnalyticFieldJunctionOrigin, CausalFieldAtlasLaw, CausalFieldEvent, CausalFieldStanding,
    DimensionalWaveModeId, EventId, ExactAnalyticAdvectionEvent, ExactAnalyticAdvectionLaw,
    ExactAnalyticCirculationProbe, ExactAnalyticFieldArc, ExactAnalyticFieldJunction,
    ExactAnalyticFieldMode, ExactAnalyticFieldWaveEvent, ExactAnalyticFieldWaveImpulse,
    ExactAnalyticFieldWaveLaw, ExactAnalyticInterfaceAmplitudeFiber, ExactAnalyticOrbitGeometry,
    ExactComplexWaveCurrent, ExactEventLaw, ExactRatMatrix, ExactReceiverPrimaryDoctrine,
    ExactRefractionHand, ExactRefractionRegime, ExactTorus, ExactTorusPhaseFrame,
    ExactUnitConicPhase, ExactWavePhaseTransport, FieldGermId, FieldOverlapId, FieldPhaseChannel,
    FieldRegionId, ImplicitCellId, OrientedFieldSample, SourceTorusOccurrence,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use num_traits::{One, Zero};
use relational_geometry::{RatVec3, ReceiverId, integer};

const MODE_PROPAGATING: DimensionalWaveModeId = DimensionalWaveModeId(1);
const MODE_GRAZING: DimensionalWaveModeId = DimensionalWaveModeId(2);
const MODE_EVANESCENT: DimensionalWaveModeId = DimensionalWaveModeId(3);

const INTERFACE_LOCAL_A: AnalyticFieldJunctionId = AnalyticFieldJunctionId(1);
const INTERFACE_SHARED: AnalyticFieldJunctionId = AnalyticFieldJunctionId(2);
const INTERFACE_LOCAL_B: AnalyticFieldJunctionId = AnalyticFieldJunctionId(3);

const INTERFACE_ARC_A: AnalyticFieldArcId = AnalyticFieldArcId(1);
const INTERFACE_ARC_B: AnalyticFieldArcId = AnalyticFieldArcId(2);
const TORUS_CYCLE: [AnalyticFieldArcId; 4] = [
    AnalyticFieldArcId(10),
    AnalyticFieldArcId(11),
    AnalyticFieldArcId(12),
    AnalyticFieldArcId(13),
];
const QUADRIC_CYCLE: [AnalyticFieldArcId; 4] = [
    AnalyticFieldArcId(20),
    AnalyticFieldArcId(21),
    AnalyticFieldArcId(22),
    AnalyticFieldArcId(23),
];

struct CausedField {
    standing: CausalFieldStanding,
    interface_a: FieldGermId,
    interface_b: FieldGermId,
    torus_cycle: FieldGermId,
    quadric_cycle: FieldGermId,
    overlap: FieldOverlapId,
}

fn main() -> Result<(), Box<dyn Error>> {
    let output = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(".local/artifacts/analytic-field-transport"));
    fs::create_dir_all(&output)?;

    let field = cause_field()?;
    let (wave, junctions) = form_wave_law(&field)?;
    write_geometry_trace(&output, &wave, &junctions)?;
    write_interface_trace(&output, &field, &wave)?;
    write_holonomy_trace(&output, &wave)?;
    let wave_summary = enact_wave_current(&output, &field, &wave)?;
    let advection_summary = enact_advection_current(&output, &wave)?;

    println!("exact analytic field transport completed");
    println!(
        "field_germs={} active_germs={} overlaps={}",
        field.standing.germs.len(),
        field.standing.active_germs().len(),
        field.standing.overlaps.len()
    );
    println!(
        "wave_arcs={} wave_modes={} ticks={} final_energy={} peak_sections={} peak_contacts={}",
        wave.arcs().len(),
        wave.modes().len(),
        wave_summary.ticks,
        wave_summary.final_energy,
        wave_summary.peak_sections,
        wave_summary.peak_contacts
    );
    println!(
        "advection_ticks={} total={} energy={} torus_circulation={} quadric_circulation={}",
        advection_summary.ticks,
        advection_summary.total,
        advection_summary.energy,
        advection_summary.torus_circulation,
        advection_summary.quadric_circulation
    );
    println!("all wave, interface, total, energy, and circulation residuals are exactly zero");
    println!("receipts={}", output.display());
    Ok(())
}

fn cause_field() -> Result<CausedField, Box<dyn Error>> {
    let law = CausalFieldAtlasLaw;
    let source_tori = vec![
        source_torus(1, 1, RatVec3::zero()),
        source_torus(2, 2, RatVec3::zero()),
        source_torus(4, 4, RatVec3::from_i64(12, 0, 0)),
    ];
    let first = law.enact(
        &law.initial_standing(),
        &CausalFieldEvent {
            event: EventId(1),
            chronology: 1,
            images: Vec::new(),
            oriented_samples: Vec::new(),
            source_tori,
        },
    )?;

    let sphere_center = RatVec3::from_i64(0, 12, 0);
    let mut oriented_samples = vec![OrientedFieldSample {
        regions: BTreeSet::from([FieldRegionId(1), FieldRegionId(2)]),
        point: RatVec3::from_i64(4, 0, 0),
        normal: RatVec3::from_i64(1, 0, 0),
        phase: BTreeMap::<FieldPhaseChannel, Rat>::new(),
        receiver_contact: None,
    }];
    oriented_samples.extend(
        [
            RatVec3::from_i64(2, 0, 0),
            RatVec3::from_i64(-2, 0, 0),
            RatVec3::from_i64(0, 2, 0),
            RatVec3::from_i64(0, -2, 0),
            RatVec3::from_i64(0, 0, 2),
            RatVec3::from_i64(0, 0, -2),
        ]
        .into_iter()
        .map(|offset| OrientedFieldSample {
            regions: BTreeSet::from([FieldRegionId(3)]),
            point: sphere_center.add(&offset),
            normal: offset,
            phase: BTreeMap::new(),
            receiver_contact: None,
        }),
    );
    let second = law.enact(
        &first.standing_after,
        &CausalFieldEvent {
            event: EventId(2),
            chronology: 2,
            images: Vec::new(),
            oriented_samples,
            source_tori: Vec::new(),
        },
    )?;
    let standing = second.standing_after;
    let active = |region| -> Result<FieldGermId, Box<dyn Error>> {
        let germs = standing
            .active_regions
            .get(&FieldRegionId(region))
            .ok_or("missing active field region")?;
        if germs.len() != 1 {
            return Err(format!("region {region} did not retain one active germ").into());
        }
        Ok(*germs.iter().next().expect("one germ was checked"))
    };
    let overlap = *second
        .radiation
        .first()
        .and_then(|receipt| receipt.overlaps.iter().next())
        .ok_or("the caused two-torus contact emitted no overlap")?;
    Ok(CausedField {
        interface_a: active(1)?,
        interface_b: active(2)?,
        quadric_cycle: active(3)?,
        torus_cycle: active(4)?,
        standing,
        overlap,
    })
}

fn source_torus(region: u64, implicit: u64, center: RatVec3) -> SourceTorusOccurrence {
    SourceTorusOccurrence {
        region: FieldRegionId(region),
        torus: ExactTorus::new(
            ImplicitCellId(implicit),
            EventId(1),
            center,
            RatVec3::from_i64(0, 0, 1),
            integer(3),
            integer(1),
        )
        .expect("declared exact torus is regular"),
        phases: BTreeMap::new(),
    }
}

fn form_wave_law(
    field: &CausedField,
) -> Result<
    (
        ExactAnalyticFieldWaveLaw,
        BTreeMap<AnalyticFieldJunctionId, ExactAnalyticFieldJunction>,
    ),
    Box<dyn Error>,
> {
    let frame = torus_frame();
    let identity = ExactUnitConicPhase::identity();
    let north = unit(integer(0), integer(1));
    let west = unit(integer(-1), integer(0));
    let south = unit(integer(0), integer(-1));
    let interface_geometry = |germ| ExactAnalyticOrbitGeometry::TorusLongitude {
        germ,
        frame: frame.clone(),
        meridian: identity.clone(),
    };
    let torus_cycle_geometry = ExactAnalyticOrbitGeometry::TorusLongitude {
        germ: field.torus_cycle,
        frame: frame.clone(),
        meridian: identity.clone(),
    };
    let quadric_cycle_geometry = ExactAnalyticOrbitGeometry::QuadricConic {
        germ: field.quadric_cycle,
        center: RatVec3::from_i64(0, 12, 0),
        cosine_axis: RatVec3::from_i64(2, 0, 0),
        sine_axis: RatVec3::from_i64(0, 0, 2),
    };

    let junctions = vec![
        local_junction(
            INTERFACE_LOCAL_A,
            "interface medium A",
            RatVec3::from_i64(0, 4, 0),
            field.interface_a,
        ),
        ExactAnalyticFieldJunction {
            id: INTERFACE_SHARED,
            name: "declared two-medium optical interface".to_owned(),
            point: RatVec3::from_i64(4, 0, 0),
            origin: AnalyticFieldJunctionOrigin::InteractingOverlap {
                overlap: field.overlap,
            },
        },
        local_junction(
            INTERFACE_LOCAL_B,
            "interface medium B",
            RatVec3::from_i64(0, 4, 0),
            field.interface_b,
        ),
        local_junction(
            AnalyticFieldJunctionId(10),
            "torus longitude east",
            RatVec3::from_i64(16, 0, 0),
            field.torus_cycle,
        ),
        local_junction(
            AnalyticFieldJunctionId(11),
            "torus longitude north",
            RatVec3::from_i64(12, 4, 0),
            field.torus_cycle,
        ),
        local_junction(
            AnalyticFieldJunctionId(12),
            "torus longitude west",
            RatVec3::from_i64(8, 0, 0),
            field.torus_cycle,
        ),
        local_junction(
            AnalyticFieldJunctionId(13),
            "torus longitude south",
            RatVec3::from_i64(12, -4, 0),
            field.torus_cycle,
        ),
        local_junction(
            AnalyticFieldJunctionId(20),
            "quadric conic east",
            RatVec3::from_i64(2, 12, 0),
            field.quadric_cycle,
        ),
        local_junction(
            AnalyticFieldJunctionId(21),
            "quadric conic north",
            RatVec3::from_i64(0, 12, 2),
            field.quadric_cycle,
        ),
        local_junction(
            AnalyticFieldJunctionId(22),
            "quadric conic west",
            RatVec3::from_i64(-2, 12, 0),
            field.quadric_cycle,
        ),
        local_junction(
            AnalyticFieldJunctionId(23),
            "quadric conic south",
            RatVec3::from_i64(0, 12, -2),
            field.quadric_cycle,
        ),
    ];
    let indexed_junctions = junctions
        .iter()
        .cloned()
        .map(|junction| (junction.id, junction))
        .collect();

    let quarter = phase_transport(integer(0), integer(1));
    let inverse_quarter = phase_transport(integer(0), integer(-1));
    let three_four = phase_transport(fraction(3, 5), fraction(4, 5));
    let inverse_three_four = phase_transport(fraction(3, 5), fraction(-4, 5));
    let identity_transport = ExactWavePhaseTransport::identity();
    let interface_a_steps = BTreeMap::from([
        (MODE_PROPAGATING, quarter.clone()),
        (MODE_GRAZING, three_four.clone()),
        (MODE_EVANESCENT, inverse_three_four.clone()),
    ]);
    let interface_b_steps = BTreeMap::from([(MODE_PROPAGATING, identity_transport)]);
    let torus_steps = BTreeMap::from([
        (MODE_PROPAGATING, quarter.clone()),
        (MODE_GRAZING, three_four.clone()),
        (MODE_EVANESCENT, inverse_quarter.clone()),
    ]);
    let quadric_steps = BTreeMap::from([
        (MODE_PROPAGATING, three_four),
        (MODE_GRAZING, quarter),
        (MODE_EVANESCENT, inverse_three_four),
    ]);

    let mut arcs = vec![
        ExactAnalyticFieldArc {
            id: INTERFACE_ARC_A,
            name: "medium A quarter orbit".to_owned(),
            source_event: EventId(1),
            from: INTERFACE_LOCAL_A,
            to: INTERFACE_SHARED,
            geometry: interface_geometry(field.interface_a),
            start_phase: north.clone(),
            geometric_step: phase_transport(integer(0), integer(-1)),
            delay: 1,
            admittance: Rat::one(),
            modal_admittance: BTreeMap::from([
                (MODE_PROPAGATING, integer(1)),
                (MODE_GRAZING, integer(2)),
                (MODE_EVANESCENT, integer(3)),
            ]),
            modal_phase_step: interface_a_steps,
        },
        ExactAnalyticFieldArc {
            id: INTERFACE_ARC_B,
            name: "medium B quarter orbit".to_owned(),
            source_event: EventId(1),
            from: INTERFACE_SHARED,
            to: INTERFACE_LOCAL_B,
            geometry: interface_geometry(field.interface_b),
            start_phase: identity.clone(),
            geometric_step: phase_transport(integer(0), integer(1)),
            delay: 1,
            admittance: integer(2),
            modal_admittance: BTreeMap::from([(MODE_PROPAGATING, integer(2))]),
            modal_phase_step: interface_b_steps,
        },
    ];
    let cycle_phases = [identity, north, west, south];
    for ordinal in 0..4 {
        arcs.push(ExactAnalyticFieldArc {
            id: TORUS_CYCLE[ordinal],
            name: format!("torus circulation quarter {ordinal}"),
            source_event: EventId(1),
            from: AnalyticFieldJunctionId(10 + ordinal as u64),
            to: AnalyticFieldJunctionId(10 + ((ordinal + 1) % 4) as u64),
            geometry: torus_cycle_geometry.clone(),
            start_phase: cycle_phases[ordinal].clone(),
            geometric_step: phase_transport(integer(0), integer(1)),
            delay: 1,
            admittance: Rat::one(),
            modal_admittance: BTreeMap::new(),
            modal_phase_step: torus_steps.clone(),
        });
        arcs.push(ExactAnalyticFieldArc {
            id: QUADRIC_CYCLE[ordinal],
            name: format!("quadric circulation quarter {ordinal}"),
            source_event: EventId(2),
            from: AnalyticFieldJunctionId(20 + ordinal as u64),
            to: AnalyticFieldJunctionId(20 + ((ordinal + 1) % 4) as u64),
            geometry: quadric_cycle_geometry.clone(),
            start_phase: cycle_phases[ordinal].clone(),
            geometric_step: phase_transport(integer(0), integer(1)),
            delay: 1,
            admittance: Rat::one(),
            modal_admittance: BTreeMap::new(),
            modal_phase_step: quadric_steps.clone(),
        });
    }

    let germs = [
        field.interface_a,
        field.interface_b,
        field.torus_cycle,
        field.quadric_cycle,
    ];
    let mode =
        |id, name: &str, frequency, interface_b_wave_number, interface_a_y, interface_b_y| {
            ExactAnalyticFieldMode {
                id,
                name: name.to_owned(),
                coherence_lineage: BTreeSet::from([EventId(1), EventId(2)]),
                frequency_square: integer(frequency),
                wave_number_square: BTreeMap::from([
                    (germs[0], integer(25)),
                    (germs[1], integer(interface_b_wave_number)),
                    (germs[2], integer(16)),
                    (germs[3], integer(4)),
                ]),
                interface_admittance: BTreeMap::from([
                    (germs[0], integer(interface_a_y)),
                    (germs[1], integer(interface_b_y)),
                    (germs[2], integer(1)),
                    (germs[3], integer(1)),
                ]),
            }
        };
    let modes = vec![
        mode(MODE_PROPAGATING, "propagating band", 1, 25, 1, 2),
        mode(MODE_GRAZING, "critical band", 4, 16, 2, 3),
        mode(MODE_EVANESCENT, "evanescent band", 9, 9, 3, 1),
    ];
    Ok((
        ExactAnalyticFieldWaveLaw::new(field.standing.clone(), junctions, arcs, modes)?,
        indexed_junctions,
    ))
}

fn local_junction(
    id: AnalyticFieldJunctionId,
    name: &str,
    point: RatVec3,
    germ: FieldGermId,
) -> ExactAnalyticFieldJunction {
    ExactAnalyticFieldJunction {
        id,
        name: name.to_owned(),
        point,
        origin: AnalyticFieldJunctionOrigin::LocalSupport { germ },
    }
}

fn torus_frame() -> ExactTorusPhaseFrame {
    ExactTorusPhaseFrame {
        radial_cosine: RatVec3::from_i64(1, 0, 0),
        radial_sine: RatVec3::from_i64(0, 1, 0),
        axial: RatVec3::from_i64(0, 0, 1),
    }
}

fn unit(cosine: Rat, sine: Rat) -> ExactUnitConicPhase {
    ExactUnitConicPhase::new(cosine, sine).expect("declared phase lies on the unit conic")
}

fn phase_transport(cosine: Rat, sine: Rat) -> ExactWavePhaseTransport {
    ExactWavePhaseTransport::new(cosine, sine)
        .expect("declared current transport lies on the unit conic")
}

fn fraction(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn write_geometry_trace(
    output: &PathBuf,
    wave: &ExactAnalyticFieldWaveLaw,
    junctions: &BTreeMap<AnalyticFieldJunctionId, ExactAnalyticFieldJunction>,
) -> Result<(), Box<dyn Error>> {
    let mut trace = String::from(
        "arc\tname\tsupport\tfrom\tto\tstart_x\tstart_y\tstart_z\tend_x\tend_y\tend_z\tstart_tx\tstart_ty\tstart_tz\n",
    );
    for arc in wave.arcs().values() {
        let start = &junctions[&arc.from].point;
        let end = &junctions[&arc.to].point;
        let tangent = arc.geometry.tangent(wave.field(), &arc.start_phase)?;
        writeln!(
            trace,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            arc.id.0,
            arc.name,
            arc.geometry.germ().0,
            arc.from.0,
            arc.to.0,
            start.x,
            start.y,
            start.z,
            end.x,
            end.y,
            end.z,
            tangent.x,
            tangent.y,
            tangent.z
        )?;
    }
    fs::write(output.join("analytic_geometry.tsv"), trace)?;
    Ok(())
}

fn write_interface_trace(
    output: &PathBuf,
    field: &CausedField,
    wave: &ExactAnalyticFieldWaveLaw,
) -> Result<(), Box<dyn Error>> {
    let mut trace = String::from(
        "mode\tregime\tamplitude_fiber\tincident_arc\ttransmitted_arc\treflection\ttransmission\tenergy_residual\treflected_x\treflected_y\treflected_z\tnormal_square_face\n",
    );
    for mode in [MODE_PROPAGATING, MODE_GRAZING, MODE_EVANESCENT] {
        let receipt = wave.interface_optics(
            field.overlap,
            mode,
            INTERFACE_ARC_A,
            INTERFACE_ARC_B,
            RatVec3::from_i64(3, 4, 0),
            ExactRefractionHand::AlongNormal,
        )?;
        let (regime, normal_square) = match &receipt.refraction.transmitted_regime {
            ExactRefractionRegime::Propagating {
                normal_coefficient_square,
                ..
            } => ("PROPAGATING", normal_coefficient_square.clone()),
            ExactRefractionRegime::Grazing => ("GRAZING", Rat::zero()),
            ExactRefractionRegime::Evanescent {
                normal_coefficient_square_deficit,
            } => ("EVANESCENT", -normal_coefficient_square_deficit),
        };
        let (amplitude_fiber, reflection, transmission, energy_residual) = match &receipt.amplitude
        {
            ExactAnalyticInterfaceAmplitudeFiber::Traveling(coefficients) => (
                "TRAVELING",
                coefficients.reflection.to_string(),
                coefficients.transmission.to_string(),
                coefficients.energy_residual.to_string(),
            ),
            ExactAnalyticInterfaceAmplitudeFiber::GrazingOpen { .. } => (
                "GRAZING_OPEN",
                "OPEN".to_owned(),
                "OPEN".to_owned(),
                "OPEN".to_owned(),
            ),
            ExactAnalyticInterfaceAmplitudeFiber::EvanescentOpen { .. } => (
                "EVANESCENT_OPEN",
                "OPEN".to_owned(),
                "OPEN".to_owned(),
                "OPEN".to_owned(),
            ),
        };
        let reflected = &receipt.refraction.reflected_covector;
        writeln!(
            trace,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            mode.0,
            regime,
            amplitude_fiber,
            receipt.incident_arc.0,
            receipt.transmitted_arc.0,
            reflection,
            transmission,
            energy_residual,
            reflected.x,
            reflected.y,
            reflected.z,
            normal_square,
        )?;
    }
    fs::write(output.join("interface_optics.tsv"), trace)?;
    Ok(())
}

fn write_holonomy_trace(
    output: &PathBuf,
    wave: &ExactAnalyticFieldWaveLaw,
) -> Result<(), Box<dyn Error>> {
    let mut trace = String::from(
        "cycle\tmode\tcosine\tsine\tadmits_nonzero_fixed_current\tsupport_count\tarc_count\n",
    );
    for (name, cycle) in [
        ("torus-longitude", TORUS_CYCLE.as_slice()),
        ("quadric-conic", QUADRIC_CYCLE.as_slice()),
    ] {
        for mode in [MODE_PROPAGATING, MODE_GRAZING, MODE_EVANESCENT] {
            let receipt = wave.cycle_phase_holonomy(cycle, mode)?;
            writeln!(
                trace,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}",
                name,
                mode.0,
                receipt.phase_transport.cosine,
                receipt.phase_transport.sine,
                receipt.admits_nonzero_fixed_current,
                receipt.support_germs.len(),
                receipt.arcs.len(),
            )?;
        }
    }
    fs::write(output.join("cycle_holonomy.tsv"), trace)?;
    Ok(())
}

struct WaveSummary {
    ticks: u64,
    final_energy: Rat,
    peak_sections: usize,
    peak_contacts: usize,
}

fn enact_wave_current(
    output: &PathBuf,
    field: &CausedField,
    wave: &ExactAnalyticFieldWaveLaw,
) -> Result<WaveSummary, Box<dyn Error>> {
    let receiver_doctrine = ExactReceiverPrimaryDoctrine::new(Rat::one(), Rat::zero())?;
    let mut standing = wave.initial_standing();
    let mut cumulative_source_work = Rat::zero();
    let mut peak_sections = 0;
    let mut peak_contacts = 0;
    let mut tick_trace = String::from(
        "tick\tevent\tenergy\tsource_work\tcumulative_source_work\tsections\tcontacts\tarrivals\tscatters\tdepartures\n",
    );
    let mut section_trace = String::from(
        "tick\tmode\tarc\tsupport\tfrom\tto\tphase_c\tphase_s\tx\ty\tz\ttangent_x\ttangent_y\ttangent_z\tcurrent_real\tcurrent_imaginary\tenergy\n",
    );
    let mut contact_trace = String::from(
        "tick\tcontact\tx\ty\tz\tgerms\tsections\talpha\ttransmittance\tprimary_0\tprimary_1\tprimary_2\tmode_population\n",
    );
    let mut interface_trace = String::from(
        "tick\tjunction\tmode\tenergy_entered\tenergy_departed\tsource_work\tpassive_residual\tarrivals\tdepartures\n",
    );

    for tick in 0..24_u64 {
        let event = EventId(100 + tick);
        let mut impulses = Vec::new();
        if tick == 0 {
            impulses.extend([
                impulse(
                    field,
                    MODE_PROPAGATING,
                    INTERFACE_LOCAL_A,
                    integer(1),
                    integer(0),
                ),
                impulse(
                    field,
                    MODE_GRAZING,
                    INTERFACE_LOCAL_A,
                    integer(1),
                    integer(0),
                ),
                impulse(
                    field,
                    MODE_EVANESCENT,
                    INTERFACE_LOCAL_A,
                    integer(0),
                    integer(1),
                ),
                impulse(
                    field,
                    MODE_PROPAGATING,
                    AnalyticFieldJunctionId(10),
                    integer(1),
                    integer(0),
                ),
                impulse(
                    field,
                    MODE_GRAZING,
                    AnalyticFieldJunctionId(10),
                    integer(1),
                    integer(1),
                ),
                impulse(
                    field,
                    MODE_EVANESCENT,
                    AnalyticFieldJunctionId(20),
                    integer(1),
                    integer(0),
                ),
            ]);
        }
        if tick == 6 {
            impulses.extend([
                impulse(
                    field,
                    MODE_PROPAGATING,
                    AnalyticFieldJunctionId(22),
                    integer(1),
                    integer(0),
                ),
                impulse(
                    field,
                    MODE_PROPAGATING,
                    AnalyticFieldJunctionId(12),
                    integer(-1),
                    integer(0),
                ),
            ]);
        }
        if tick == 12 {
            impulses.push(impulse(
                field,
                MODE_EVANESCENT,
                INTERFACE_LOCAL_A,
                integer(1),
                integer(0),
            ));
        }
        let successor = wave.enact(&standing, &ExactAnalyticFieldWaveEvent { event, impulses })?;
        let receipt = successor
            .radiation
            .first()
            .ok_or("wave event emitted no receipt")?;
        if !receipt.wave.exact_energy_residual.is_zero()
            || receipt
                .interface_scatters
                .iter()
                .any(|scatter| !scatter.passive_residual.is_zero())
        {
            return Err("wave current violated an exact passive certificate".into());
        }
        cumulative_source_work += &receipt.wave.source_work;
        standing = successor.standing_after;
        if standing.energy != cumulative_source_work {
            return Err("wave standing differs from cumulative exact source work".into());
        }
        let slice = wave.restrict(&standing, ReceiverId(77), &receiver_doctrine)?;
        peak_sections = peak_sections.max(slice.sections.len());
        peak_contacts = peak_contacts.max(slice.contacts.len());
        writeln!(
            tick_trace,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            tick,
            event.0,
            standing.energy,
            receipt.wave.source_work,
            cumulative_source_work,
            slice.sections.len(),
            slice.contacts.len(),
            receipt.wave.arrivals.len(),
            receipt.wave.scatters.len(),
            receipt.wave.departures.len(),
        )?;
        for section in &slice.sections {
            writeln!(
                section_trace,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                tick,
                section.mode.0,
                section.arc.0,
                section.support_germ.0,
                section.from.0,
                section.to.0,
                section.phase.cosine,
                section.phase.sine,
                section.point.x,
                section.point.y,
                section.point.z,
                section.tangent.x,
                section.tangent.y,
                section.tangent.z,
                section.current.real,
                section.current.imaginary,
                section.energy,
            )?;
        }
        for (ordinal, contact) in slice.contacts.iter().enumerate() {
            let germ_word = contact
                .germs
                .iter()
                .map(|germ| germ.0.to_string())
                .collect::<Vec<_>>()
                .join(",");
            let section_word = contact
                .sections
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(",");
            let mode_word = contact
                .population
                .coherent_modes
                .iter()
                .map(|(mode, current)| {
                    format!("{}:({},{})", mode.0, current.real, current.imaginary)
                })
                .collect::<Vec<_>>()
                .join(";");
            writeln!(
                contact_trace,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                tick,
                ordinal,
                contact.point.x,
                contact.point.y,
                contact.point.z,
                germ_word,
                section_word,
                contact.response.alpha,
                contact.response.transmittance,
                contact.response.primaries[0],
                contact.response.primaries[1],
                contact.response.primaries[2],
                mode_word,
            )?;
        }
        for scatter in &receipt.interface_scatters {
            writeln!(
                interface_trace,
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                tick,
                scatter.junction.0,
                scatter.mode.0,
                scatter.energy_entered,
                scatter.energy_departed,
                scatter.source_work,
                scatter.passive_residual,
                scatter.arrivals.len(),
                scatter.departures.len(),
            )?;
        }
    }
    wave.validate_standing(&standing)?;
    fs::write(output.join("wave_ticks.tsv"), tick_trace)?;
    fs::write(output.join("wave_sections.tsv"), section_trace)?;
    fs::write(output.join("receiver_contacts.tsv"), contact_trace)?;
    fs::write(output.join("interface_scattering.tsv"), interface_trace)?;
    Ok(WaveSummary {
        ticks: standing.tick,
        final_energy: standing.energy,
        peak_sections,
        peak_contacts,
    })
}

fn impulse(
    field: &CausedField,
    mode: DimensionalWaveModeId,
    junction: AnalyticFieldJunctionId,
    real: Rat,
    imaginary: Rat,
) -> ExactAnalyticFieldWaveImpulse {
    let source_event = match junction {
        INTERFACE_LOCAL_A => field.standing.germs[&field.interface_a].last_event,
        INTERFACE_LOCAL_B => field.standing.germs[&field.interface_b].last_event,
        AnalyticFieldJunctionId(10..=13) => field.standing.germs[&field.torus_cycle].last_event,
        AnalyticFieldJunctionId(20..=23) => field.standing.germs[&field.quadric_cycle].last_event,
        _ => EventId(2),
    };
    ExactAnalyticFieldWaveImpulse {
        source_event,
        mode,
        junction,
        departure: ExactComplexWaveCurrent::new(real, imaginary),
    }
}

struct AdvectionSummary {
    ticks: u64,
    total: Rat,
    energy: Rat,
    torus_circulation: Rat,
    quadric_circulation: Rat,
}

fn enact_advection_current(
    output: &PathBuf,
    wave: &ExactAnalyticFieldWaveLaw,
) -> Result<AdvectionSummary, Box<dyn Error>> {
    let arcs = TORUS_CYCLE
        .into_iter()
        .chain(QUADRIC_CYCLE)
        .collect::<Vec<_>>();
    let capacities = arcs.iter().copied().map(|arc| (arc, Rat::one())).collect();
    let generator = two_cycle_generator()?;
    let torus_probe = ExactAnalyticCirculationProbe {
        id: AnalyticCirculationProbeId(1),
        name: "torus longitude circulation".to_owned(),
        coefficients: TORUS_CYCLE
            .into_iter()
            .map(|arc| (arc, Rat::one()))
            .collect(),
    };
    let quadric_probe = ExactAnalyticCirculationProbe {
        id: AnalyticCirculationProbeId(2),
        name: "quadric conic circulation".to_owned(),
        coefficients: QUADRIC_CYCLE
            .into_iter()
            .map(|arc| (arc, Rat::one()))
            .collect(),
    };
    let law = ExactAnalyticAdvectionLaw::new_on_field(
        wave,
        capacities,
        generator,
        fraction(1, 2),
        vec![torus_probe, quadric_probe],
    )?;
    let initial_values = TORUS_CYCLE
        .into_iter()
        .zip([1, 2, 4, 8].map(integer))
        .chain(QUADRIC_CYCLE.into_iter().zip([3, 5, 7, 11].map(integer)))
        .collect::<BTreeMap<_, _>>();
    let mut standing = law.initial_standing(initial_values)?;
    let mut trace = String::from(
        "tick\ttotal\tenergy\ttotal_residual\tenergy_residual\ttorus_circulation\ttorus_residual\tquadric_circulation\tquadric_residual\tarc_10\tarc_11\tarc_12\tarc_13\tarc_20\tarc_21\tarc_22\tarc_23\n",
    );
    let mut last_total = Rat::zero();
    let mut last_energy = Rat::zero();
    let mut last_torus = Rat::zero();
    let mut last_quadric = Rat::zero();
    for tick in 0..24_u64 {
        let successor = law.enact(
            &standing,
            &ExactAnalyticAdvectionEvent {
                event: EventId(1_000 + tick),
            },
        )?;
        let receipt = &successor.radiation[0];
        if !receipt.weighted_total_residual.is_zero()
            || !receipt.quadratic_energy_residual.is_zero()
            || receipt
                .circulations
                .iter()
                .any(|circulation| !circulation.residual.is_zero())
        {
            return Err("advection current violated an exact certificate".into());
        }
        standing = successor.standing_after;
        last_total = receipt.weighted_total_after.clone();
        last_energy = receipt.quadratic_energy_after.clone();
        last_torus = receipt.circulations[0].after.clone();
        last_quadric = receipt.circulations[1].after.clone();
        writeln!(
            trace,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            standing.tick,
            last_total,
            last_energy,
            receipt.weighted_total_residual,
            receipt.quadratic_energy_residual,
            last_torus,
            receipt.circulations[0].residual,
            last_quadric,
            receipt.circulations[1].residual,
            standing.values[&TORUS_CYCLE[0]],
            standing.values[&TORUS_CYCLE[1]],
            standing.values[&TORUS_CYCLE[2]],
            standing.values[&TORUS_CYCLE[3]],
            standing.values[&QUADRIC_CYCLE[0]],
            standing.values[&QUADRIC_CYCLE[1]],
            standing.values[&QUADRIC_CYCLE[2]],
            standing.values[&QUADRIC_CYCLE[3]],
        )?;
    }
    fs::write(output.join("conservative_advection.tsv"), trace)?;
    Ok(AdvectionSummary {
        ticks: standing.tick,
        total: last_total,
        energy: last_energy,
        torus_circulation: last_torus,
        quadric_circulation: last_quadric,
    })
}

fn two_cycle_generator() -> Result<ExactRatMatrix, Box<dyn Error>> {
    let mut entries = vec![vec![Rat::zero(); 8]; 8];
    for offset in [0_usize, 4] {
        for ordinal in 0..4 {
            let next = offset + (ordinal + 1) % 4;
            let previous = offset + (ordinal + 3) % 4;
            entries[offset + ordinal][next] = Rat::one();
            entries[offset + ordinal][previous] = -Rat::one();
        }
    }
    Ok(ExactRatMatrix::new(entries)?)
}

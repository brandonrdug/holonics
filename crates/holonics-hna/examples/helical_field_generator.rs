//! Source-conditioned native field consumer for the situated `se(3)` bracket.
//!
//! The analytic chart has two sorted junctions.  Junction 1 carries `eta` with identity modal
//! transport; junction 2 is the receiving source `xi`, and incidence derives `c = eta - xi`.
//! The native incidence therefore supplies the complete source packet to one continuing field
//! session, rather than handing a private learner a preselected feature vector.  Observations
//! are computed by [`ScrewGenerator::bracket`] in one oriented Euclidean frame and the normal
//! material is allowed to retain its finite-data compatibility family and regularized residual.

use holonic_engine::{
    AnalyticFieldArcId, AnalyticFieldJunctionId, AnalyticFieldJunctionOrigin, CausalFieldAtlasLaw,
    CausalFieldEvent, CausalFieldStanding, DimensionalWaveModeId, EventId, ExactAnalyticFieldArc,
    ExactAnalyticFieldJunction, ExactAnalyticFieldMode, ExactAnalyticFieldWaveLaw,
    ExactAnalyticOrbitGeometry, ExactEventLaw, ExactTorus, ExactTorusPhaseFrame,
    ExactUnitConicPhase, FieldRegionId, FieldSupportStanding, ImplicitCellId,
    native_ecology::constitutive_fibre::{
        ConditionCoverage, ConstitutiveReading, NativeConstitutiveField, NativeJunctionSeed,
        NativePhaseCurrent, ResidentConstitutiveCurrent,
    },
    resident_section::{ResidentGrain, ResidentSection, ResidentSectionRest, ResidentSurface},
};
use holonics_hna::native::{
    GeometricFieldSpec, NativeFieldSession, NativeFieldSourceSpec, NativeFieldSources,
};
use num_traits::{One, ToPrimitive, Zero};
use relational_geometry::{Rat, RatVec3, ScrewGenerator, integer};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
};

type Result<T> = std::result::Result<T, Box<dyn Error>>;

const MODE: DimensionalWaveModeId = DimensionalWaveModeId(1);
const RECEIVER: AnalyticFieldJunctionId = AnalyticFieldJunctionId(2);
const NEIGHBOR: AnalyticFieldJunctionId = AnalyticFieldJunctionId(1);

fn current<'a, 'c>(
    section: &'a ResidentSection<'c>,
) -> Result<ResidentConstitutiveCurrent<'a, 'c>> {
    Ok(ResidentConstitutiveCurrent::rational(section)?)
}

/// Resident rational packets carry numerator coordinates followed by one common denominator.
fn packet<'c>(surface: &'c ResidentSurface<'c>, values: &[i64]) -> Result<ResidentSection<'c>> {
    let mut words = values.to_vec();
    words.push(1);
    Ok(surface.mount_section_rest(&ResidentSectionRest::found(
        1,
        words.len(),
        ResidentGrain(0),
        64,
        words.into_iter().map(|value| (value, value)).collect(),
    )?)?)
}

fn basis(index: usize, amplitude: i64) -> [i64; 6] {
    let mut value = [0; 6];
    value[index] = amplitude;
    value
}

fn add(left: [i64; 6], right: [i64; 6]) -> [i64; 6] {
    std::array::from_fn(|i| left[i] + right[i])
}

fn sub(left: [i64; 6], right: [i64; 6]) -> [i64; 6] {
    std::array::from_fn(|i| left[i] - right[i])
}

fn generator(value: [i64; 6]) -> ScrewGenerator {
    ScrewGenerator::new(
        RatVec3::from_i64(value[0], value[1], value[2]),
        RatVec3::from_i64(value[3], value[4], value[5]),
    )
}

fn coordinates(generator: &ScrewGenerator) -> [Rat; 6] {
    [
        generator.angular().x.clone(),
        generator.angular().y.clone(),
        generator.angular().z.clone(),
        generator.advance().x.clone(),
        generator.advance().y.clone(),
        generator.advance().z.clone(),
    ]
}

fn integer_coordinates(generator: &ScrewGenerator) -> Result<[i64; 6]> {
    let values = coordinates(generator);
    values
        .into_iter()
        .map(|value| {
            if value.denom() != &num_bigint::BigInt::from(1) {
                return Err(format!("nonintegral screw observation {value}").into());
            }
            value
                .numer()
                .to_i64()
                .ok_or_else(|| format!("screw observation out of i64 range {value}").into())
        })
        .collect::<Result<Vec<_>>>()?
        .try_into()
        .map_err(|_| "screw observation width".into())
}

fn complex_target(values: &[i64; 6]) -> Vec<holonic_engine::ExactComplexWaveCurrent> {
    values
        .iter()
        .map(|value| {
            holonic_engine::ExactComplexWaveCurrent::new(
                Rat::from_integer((*value).into()),
                Rat::zero(),
            )
        })
        .collect()
}

fn error_squared(
    reading: &holonic_engine::native_ecology::constitutive_fibre::NativeFieldCurrentBall,
    expected: &[i64; 6],
) -> Rat {
    reading
        .center
        .iter()
        .zip(complex_target(expected))
        .map(|(actual, wanted)| {
            let real = &actual.real - &wanted.real;
            let imaginary = &actual.imaginary - &wanted.imaginary;
            &real * &real + &imaginary * &imaginary
        })
        .fold(Rat::zero(), |sum, value| sum + value)
}

fn source_field() -> Result<(CausalFieldStanding, holonic_engine::FieldGermId)> {
    let torus = holonic_engine::SourceTorusOccurrence {
        region: FieldRegionId(1),
        torus: ExactTorus::new(
            ImplicitCellId(1),
            EventId(1),
            RatVec3::zero(),
            RatVec3::from_i64(0, 0, 1),
            integer(2),
            integer(1),
        )?,
        phases: BTreeMap::new(),
    };
    let standing = CausalFieldAtlasLaw
        .enact(
            &CausalFieldAtlasLaw.initial_standing(),
            &CausalFieldEvent {
                event: EventId(1),
                chronology: 1,
                images: Vec::new(),
                oriented_samples: Vec::new(),
                source_tori: vec![torus],
            },
        )?
        .standing_after;
    let germ = standing
        .active_regions
        .get(&FieldRegionId(1))
        .into_iter()
        .flatten()
        .filter(|id| matches!(&standing.germs[id].support, FieldSupportStanding::Torus(_)))
        .copied()
        .collect::<Vec<_>>();
    match germ.as_slice() {
        [germ] => Ok((standing, *germ)),
        _ => Err("one active torus germ was not retained".into()),
    }
}

/// Two junctions on one exact torus, with one incoming identity phase at the receiver.
fn geometry() -> Result<GeometricFieldSpec> {
    let (field, germ) = source_field()?;
    let frame = ExactTorusPhaseFrame {
        radial_cosine: RatVec3::from_i64(1, 0, 0),
        radial_sine: RatVec3::from_i64(0, 1, 0),
        axial: RatVec3::from_i64(0, 0, 1),
    };
    let orbit = ExactAnalyticOrbitGeometry::TorusLongitude {
        germ,
        frame,
        meridian: ExactUnitConicPhase::new(-Rat::one(), Rat::zero())?,
    };
    let first_phase = ExactUnitConicPhase::identity();
    let second_phase = ExactUnitConicPhase::new(Rat::zero(), Rat::one())?;
    let junctions = vec![
        ExactAnalyticFieldJunction {
            id: NEIGHBOR,
            name: "incoming screw contrast".to_owned(),
            point: orbit.point(&field, &first_phase)?,
            origin: AnalyticFieldJunctionOrigin::LocalSupport { germ },
        },
        ExactAnalyticFieldJunction {
            id: RECEIVER,
            name: "receiving screw source".to_owned(),
            point: orbit.point(&field, &second_phase)?,
            origin: AnalyticFieldJunctionOrigin::LocalSupport { germ },
        },
    ];
    let step = first_phase.transport_to(&second_phase);
    let arcs = vec![ExactAnalyticFieldArc {
        id: AnalyticFieldArcId(1),
        name: "identity modal incoming contrast".to_owned(),
        source_event: EventId(1),
        from: NEIGHBOR,
        to: RECEIVER,
        geometry: orbit,
        start_phase: first_phase,
        geometric_step: step,
        delay: 1,
        admittance: Rat::one(),
        modal_admittance: BTreeMap::from([(MODE, Rat::one())]),
        modal_phase_step: BTreeMap::from([(
            MODE,
            holonic_engine::ExactWavePhaseTransport::identity(),
        )]),
    }];
    let mode = ExactAnalyticFieldMode {
        id: MODE,
        name: "unit torus screw chart".to_owned(),
        coherence_lineage: BTreeSet::from([EventId(1)]),
        frequency_square: Rat::one(),
        wave_number_square: BTreeMap::from([(germ, Rat::one())]),
        interface_admittance: BTreeMap::from([(germ, Rat::one())]),
    };
    ExactAnalyticFieldWaveLaw::new(
        field.clone(),
        junctions.clone(),
        arcs.clone(),
        vec![mode.clone()],
    )?;
    Ok(GeometricFieldSpec {
        field,
        junctions,
        arcs,
        modes: vec![mode],
        mode: MODE,
        slot_junctions: vec![NEIGHBOR, RECEIVER],
        self_comparison: false,
        beta_significand: 1,
        beta_exponent: 0,
        series_terms: 16,
        refinement_steps: 1,
        relaxation_bits: 1,
    })
}

fn verify_incidence<'c>(session: &NativeFieldSession<'c, NativeFieldSources<'c>>) -> Result<()> {
    let rows = session.incidence().condition_restriction().to_rows();
    // Two junctions × six complex coordinates are laid out as neighbor then receiver.  The
    // first real row must therefore be +neighbor.real - receiver.real for identity transport.
    if rows.len() != 12
        || rows[0].len() != 24
        || rows[0][0] != Rat::one()
        || rows[0][12] != -Rat::one()
    {
        return Err("analytic incidence did not emit the declared eta - xi restriction".into());
    }
    Ok(())
}

fn train<'c>(
    session: &mut NativeFieldSession<'c, NativeFieldSources<'c>>,
    surface: &'c ResidentSurface<'c>,
) -> Result<usize> {
    let mut count = 0;
    for i in 0..6 {
        for j in 0..6 {
            let sx = if i % 2 == 0 {
                (i + 2) as i64
            } else {
                -((i + 2) as i64)
            };
            let cc = if j % 2 == 0 {
                (j + 3) as i64
            } else {
                -((j + 3) as i64)
            };
            for source_sign in [1_i64, -1] {
                for contrast_sign in [1_i64, -1] {
                    let source = basis(i, source_sign * sx);
                    let contrast = basis(j, contrast_sign * cc);
                    let neighbor = add(source, contrast);
                    let target =
                        integer_coordinates(&generator(source).bracket(&generator(neighbor)))?;
                    // The packet carries eta at the incoming junction. The compiled incidence
                    // restriction performs the declared transported subtraction eta - xi.
                    let mut values = neighbor.iter().flat_map(|v| [*v, 0]).collect::<Vec<_>>();
                    values.extend(source.iter().flat_map(|v| [*v, 0]));
                    let input = packet(surface, &values)?;
                    let observed = packet(
                        surface,
                        &target.iter().flat_map(|v| [*v, 0]).collect::<Vec<_>>(),
                    )?;
                    let preparation = session.prepare_native(&input)?;
                    session.form_native_reaction(preparation, current(&observed)?)?;
                    count += 1;
                }
            }
        }
    }
    Ok(count)
}

fn main() -> Result<()> {
    let readout = holonic_engine::embedding_fiber::ResidentReadout::new()?;
    let surface = ResidentSurface::on(&readout)?;
    let field = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        vec![
            NativeJunctionSeed {
                incoming_admittance: 1,
                held_admittance: 1,
                incoming_transport: NativePhaseCurrent::unit(),
                initial_held: NativePhaseCurrent::zero(),
            },
            NativeJunctionSeed {
                incoming_admittance: 1,
                held_admittance: 1,
                incoming_transport: NativePhaseCurrent::unit(),
                initial_held: NativePhaseCurrent::zero(),
            },
        ],
        ResidentGrain(48),
    )?;
    let geometry = geometry()?;
    let mut session = NativeFieldSession::from_native_field(
        &surface,
        field,
        NativeFieldSourceSpec {
            geometry,
            receiver: RECEIVER,
        },
    )
    .map_err(|r| r.reason)?;
    verify_incidence(&session)?;
    let formation_started = std::time::Instant::now();
    let observations = train(&mut session, &surface)?;
    let formation_seconds = formation_started.elapsed().as_secs_f64();

    let xi = [3, -2, 4, -5, 6, -7];
    let eta = [-4, 5, 2, 8, -3, 6];
    let contrast = sub(eta, xi);
    let expected = integer_coordinates(&generator(xi).bracket(&generator(eta)))?;
    // The packet carries eta; the analytic restriction returns the actual contrast eta - xi.
    let mut values = eta.iter().flat_map(|v| [*v, 0]).collect::<Vec<_>>();
    values.extend(xi.iter().flat_map(|v| [*v, 0]));
    let input = packet(&surface, &values)?;
    let preparation = session.prepare_native(&input)?;
    let compilation_started = std::time::Instant::now();
    let compatibility = session.contextual_section(preparation)?;
    let contextual_compile_seconds = compilation_started.elapsed().as_secs_f64();
    let change = packet(
        &surface,
        &contrast.iter().flat_map(|v| [*v, 0]).collect::<Vec<_>>(),
    )?;
    let inferred = compatibility.read_change(current(&change)?)?.inspect()?;
    let expected_exact = expected
        .iter()
        .flat_map(|v| [Rat::from_integer((*v).into()), Rat::zero()])
        .collect::<Vec<_>>();
    if inferred.predecessor_reading
        != (ConstitutiveReading::Unique {
            current: expected_exact,
        })
    {
        return Err(format!(
            "formed contextual generator did not infer the held bracket: {inferred:?}"
        )
        .into());
    }
    let generation_started = std::time::Instant::now();
    let generated = session.generate_native(preparation, true, false)?;
    let generation_seconds = generation_started.elapsed().as_secs_f64();
    let reaction = generated.reaction_output().inspect()?;
    if reaction.center.len() != expected.len() {
        return Err(format!(
            "held screw bracket width mismatch: expected {}, emitted {}",
            expected.len(),
            reaction.center.len()
        )
        .into());
    }
    let residual_squared = error_squared(&reaction, &expected);
    let tolerance_squared = Rat::new(1.into(), 100.into());
    if residual_squared > tolerance_squared {
        return Err(format!(
            "held screw bracket mismatch: residual²={residual_squared}, tolerance²={tolerance_squared}, expected={expected:?}, reaction={reaction:?}"
        ).into());
    }
    let joint = generated.inspect()?;
    let material = session.inspect_material()?;
    let normal = &material["predictive_material"];
    let fit = json!({"source_complex":48,"target_complex":6,"observations":observations,
        "coefficients":normal["material"]["coefficients"],
        "normal_residual_upper": normal["normal_residual_upper"],
        "scope":"stored dyadic M, with the declared identity normal prior"});
    // Now receive the held return. Its preimage is a family: a single bracket does not
    // identify a unique second generator. Carry that family to another receiving source.
    let observed = packet(
        &surface,
        &expected.iter().flat_map(|v| [*v, 0]).collect::<Vec<_>>(),
    )?;
    session.form_native_reaction(preparation, current(&observed)?)?;
    let reused_contrast = [2, 0, -1, 1, 3, 2];
    let reused_expected = integer_coordinates(&generator(xi).bracket(&generator(reused_contrast)))?;
    let reused_packet = packet(
        &surface,
        &reused_contrast
            .iter()
            .flat_map(|v| [*v, 0])
            .collect::<Vec<_>>(),
    )?;
    let reuse_started = std::time::Instant::now();
    let reused_return = compatibility.read_change(current(&reused_packet)?)?;
    let contextual_reuse_seconds = reuse_started.elapsed().as_secs_f64();
    let reused = reused_return.inspect()?;
    if reused.predecessor_reading
        != (ConstitutiveReading::Unique {
            current: reused_expected
                .iter()
                .flat_map(|v| [Rat::from_integer((*v).into()), Rat::zero()])
                .collect(),
        })
    {
        return Err(format!(
            "retained contextual generator failed on another condition: {reused:?}"
        )
        .into());
    }
    let condition_family = session
        .body()
        .field_last_evidence()
        .ok_or("missing condition family")?
        .family
        .inspect()?;
    let next_source = [1, 2, -1, 3, 0, 2];
    let mut next_values = eta.iter().flat_map(|v| [*v, 0]).collect::<Vec<_>>();
    next_values.extend(next_source.iter().flat_map(|v| [*v, 0]));
    let next_packet = packet(&surface, &next_values)?;
    let standing_id = session.prepare_native(&next_packet)?;
    let family_image = session.condition_family_image(standing_id)?.inspect()?;
    if family_image.coverage != ConditionCoverage::Complete
        || !matches!(
            family_image.supported_outputs,
            ConstitutiveReading::Plural { .. }
        )
    {
        return Err(format!(
            "new-source image lost the unresolved screw condition: {family_image:?}"
        )
        .into());
    }
    let standing = session
        .generate_native_standing(standing_id, false, false)?
        .inspect()?;
    session.release_native(standing_id)?;

    let report: Value = json!({
        "scope": "source-conditioned helical field consumer",
        "frame": "one common positively oriented Euclidean frame",
        "units": {"sources": "angular and translation coordinates in declared angular/length units per parameter", "bracket": "the corresponding units per squared parameter", "normal_metric": "identity prior in these nondimensional numerical coordinates"},
        "source_chart": "six complex coordinates (real screw coordinates, zero imaginary face)",
        "incidence": {"receiver": RECEIVER.0, "neighbor": NEIGHBOR.0, "incoming_modal_phase": "identity", "condition": "eta - xi"},
        "observations": observations,
        "formation_seconds": formation_seconds,
        "generation_seconds": generation_seconds,
        "census": surface.census(),
        "held_pair": {"xi": xi, "eta": eta, "contrast": contrast, "expected_bracket": expected,
            "reaction_output": reaction, "center_residual_squared": residual_squared.to_string(),
            "compatibility_origin": compatibility.origin(),
            "inferred_contextual_generator": inferred},
        "reused_contextual_generator": {"original_relation_cut":compatibility.origin(), "new_contrast":reused_contrast, "expected_bracket":reused_expected, "returned":reused},
        "contextual_compile_seconds": contextual_compile_seconds,
        "contextual_reuse_seconds": contextual_reuse_seconds,
        "normal_material_fit": fit,
        "generated_joint_field": joint,
        "returned_condition_family": condition_family,
        "new_source": next_source,
        "new_source_condition_image": family_image,
        "standing_generation": standing,
        "continuing_epoch": session.body().epoch(),
        "claim_boundary": "this is a source-qualified finite normal fit to the se(3) bracket family; it is not a general encoder or Athena product",
    });
    println!("{}", serde_json::to_string_pretty(&report)?);
    Ok(())
}

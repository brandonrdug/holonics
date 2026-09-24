//! Small fixed-generator session factory for native integration and emitter examples.
//!
//! The generator population is a model choice independent of source and response apertures.
//! This fixture declares exact screw/configuration data, finite proper actions, clocks, source
//! and receiver roles, pair contacts, and four source-contact condition kinds.  It demonstrates
//! a situated source/receiver boundary; it does not claim general text success or a continuous
//! generator/clock correspondence.

use crate::native::{
    FieldSessionSpec, FieldSourceChart, FieldTextCodec, GeneratorIncidentFieldSpec,
    GeneratorPhasePort, GeneratorPhaseReceiverBinding, GeneratorSessionOptions,
    GeneratorSourceBinding, GeneratorSourceContactKind, IncidentFieldSolver, ReactionLaw,
    field_geometry::machine::{
        ClockSpec, GeneratorMachineSpec, GeneratorPairArcSpec, GeneratorSiteSpec, MachineUnitsSpec,
        PhaseSpec,
    },
};
use holonics::exact_linear::ExactRatMatrix;
use holonics::inertia::SymmetricForm;
use holonic_engine::{native_ecology::constitutive_fibre::NativeEnclosurePropagation};
use num_bigint::BigInt;
use num_traits::Zero;
use holonics::geometry::{AffineMap3, Rat, RatMat3, RatVec3, cayley_rotation_z};

fn rat(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn units() -> MachineUnitsSpec {
    MachineUnitsSpec {
        spatial: ["length".into(), "length".into(), "length".into()],
        current: std::array::from_fn(|_| "length".into()),
    }
}

fn clock(lineage: &str) -> ClockSpec {
    ClockSpec {
        lineage: lineage.into(),
        duration: Rat::from_integer(1.into()),
        unit: "step".into(),
    }
}

fn response() -> SymmetricForm {
    SymmetricForm::from_rows(vec![
        vec![Rat::from_integer(1.into()), Rat::zero(), Rat::zero()],
        vec![Rat::zero(), Rat::from_integer(1.into()), Rat::zero()],
        vec![Rat::zero(), Rat::zero(), Rat::from_integer(1.into())],
    ])
    .expect("identity response is symmetric")
}

fn rate_port() -> Result<ExactRatMatrix, String> {
    let mut rows = vec![vec![Rat::zero(); 12]; 2];
    rows[0][0] = Rat::from_integer(1.into());
    rows[1][6] = Rat::from_integer(1.into());
    ExactRatMatrix::shaped(2, 12, rows).map_err(|error| error.to_string())
}

fn site(index: usize, count: usize) -> GeneratorSiteSpec {
    let denominator = i64::try_from(index + 2).expect("fixture index");
    let is_source = count == 1 || index + 1 < count;
    let is_receiver = count == 1 || index + 1 == count;
    GeneratorSiteSpec {
        id: format!("g{index}"),
        angular: RatVec3::new(Rat::zero(), Rat::zero(), rat(1, denominator)),
        advance: RatVec3::new(Rat::zero(), Rat::zero(), rat(1, denominator * 2)),
        initial: RatVec3::from_i64((index + 1) as i64, 0, 0),
        phase: PhaseSpec {
            parameter: rat(1, denominator + 1),
            extra_turns: 0,
            origin_exponent: 0,
            step: AffineMap3 {
                linear: cayley_rotation_z(&rat(1, denominator + 1)),
                translation: RatVec3::from_i64(0, 0, 1),
            },
            period: None,
        },
        clock: clock(&format!("generator-clock-{index}")),
        source: is_source,
        receiver: is_receiver,
        material: Some([
            [Rat::from_integer(1.into()), Rat::zero()],
            [Rat::zero(), Rat::from_integer(1.into())],
        ]),
    }
}

fn machine(generators: usize) -> Result<GeneratorMachineSpec, String> {
    if generators == 0 {
        return Err("generator count must be positive".into());
    }
    let sites = (0..generators)
        .map(|index| site(index, generators))
        .collect::<Vec<_>>();
    let arcs = if generators > 1 {
        (0..generators)
            .map(|index| {
                let next = (index + 1) % generators;
                Ok(GeneratorPairArcSpec {
                    id: format!("arc-{index}-{next}"),
                    source: format!("g{index}"),
                    receiver: format!("g{next}"),
                    source_to_receiver: AffineMap3 {
                        linear: RatMat3::identity(),
                        translation: RatVec3::zero(),
                    },
                    rate_port: rate_port()?,
                    response: response(),
                    weight: rat(1, 16),
                    clock: clock(&format!("arc-clock-{index}")),
                    parameter_units: ["receiver-rate".into(), "source-rate".into()],
                })
            })
            .collect::<Result<Vec<_>, String>>()?
    } else {
        Vec::new()
    };
    GeneratorMachineSpec::declare("generator-world", units(), sites, arcs, Vec::new())
        .map_err(|error| error.to_string())
}

fn source_binding(generators: usize) -> GeneratorSourceBinding {
    let injection_sites = if generators == 1 {
        vec!["g0".into()]
    } else {
        (0..generators - 1)
            .map(|index| format!("g{index}"))
            .collect()
    };
    let clocks = (0..generators)
        .map(|index| GeneratorPhasePort {
            site_id: format!("g{index}"),
            origin_exponent: 0,
            step_exponent: if generators == 1 || index + 1 < generators {
                1
            } else {
                0
            },
        })
        .collect();
    GeneratorSourceBinding {
        source_id: "generator-source".into(),
        clock: clock("generator-source-clock"),
        clocks,
        injection_sites,
        contact_kinds: vec![
            GeneratorSourceContactKind::IntraPart,
            GeneratorSourceContactKind::DirectJoin,
            GeneratorSourceContactKind::RecordedParent,
            GeneratorSourceContactKind::RecordedReply,
        ],
        offsets: vec![],
    }
}

/// Construct a validated public field session declaration. The machine's generator count does
/// not scale with either aperture; source ingestion and response reading remain separate costs.
pub fn generator_session_spec(
    generators: usize,
    source_aperture: usize,
    response_aperture: usize,
) -> Result<FieldSessionSpec, String> {
    if source_aperture == 0 || response_aperture == 0 {
        return Err("source and response apertures must be positive".into());
    }
    let section_symbols = source_aperture
        .checked_add(response_aperture)
        .ok_or_else(|| "session aperture overflow".to_owned())?;
    let machine = machine(generators)?;
    let source = source_binding(generators);
    let receiver_site = format!("g{}", generators - 1);
    let receiver = GeneratorPhaseReceiverBinding {
        receiver_id: receiver_site.clone(),
        ports: vec![GeneratorPhasePort {
            site_id: receiver_site.clone(),
            origin_exponent: 0,
            step_exponent: 1,
        }],
        clock: clock("generator-receiver-clock"),
        aperture: response_aperture
            .checked_add(1)
            .ok_or_else(|| "receiver aperture overflow".to_owned())?,
        termination_receiver_id: receiver_site,
    };
    let field = GeneratorIncidentFieldSpec {
        machine,
        source_condition_ports: 4,
        self_comparison: true,
        beta_significand: 1,
        beta_exponent: -4,
        series_terms: 40,
        refinement_steps: 1,
        relaxation_bits: 2,
        material_owners: Vec::new(),
        solve_steps: 128,
        solver: IncidentFieldSolver::Richardson,
        enclosure_propagation: NativeEnclosurePropagation::JointBall,
        // A newly founded generator body declares the power-neutral reaction law.
        reaction_law: ReactionLaw::PowerNeutral,
    };
    let options = GeneratorSessionOptions {
        field,
        source,
        receiver,
        material_seed: 0x8a5c_19d3,
    };
    let compiled = options
        .field
        .machine
        .compile()
        .map_err(|error| error.to_string())?;
    options
        .source
        .validate_scope(&compiled, 0, 1)
        .map_err(|error| error.to_string())?;
    if options.field.source_condition_ports != options.source.contact_kinds.len()
        || options.source.contact_kinds.len() != 4
        || options.receiver.ports.len() != 1
        || options.receiver.aperture != response_aperture + 1
        || options.receiver.ports.iter().any(|port| {
            !compiled
                .sites()
                .iter()
                .any(|site| site.id() == port.site_id && site.is_receiver())
        })
    {
        return Err("generator source/receiver condition binding is inconsistent".into());
    }
    let spec = FieldSessionSpec {
        symbols: vec!["a".into(), "b".into(), " ".into()],
        section_symbols,
        context_symbols: source_aperture,
        region_offsets: Vec::new(),
        source_chart: FieldSourceChart::GeneratorMachine,
        geometry: None,
        incident: None,
        generator: Some(options),
        codec: FieldTextCodec::UnicodeScalars,
        fractional_bits: 48,
    };
    Ok(spec)
}

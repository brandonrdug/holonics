//! The two-site generator-machine declaration shared by the incident owners' host tests.

use super::*;
use crate::hnn::field_geometry::machine::{
    ClockSpec, GeneratorMachineSpec, GeneratorPairArcSpec, GeneratorSiteSpec, MachineUnitsSpec,
    PhaseSpec,
};
use holonics::exact_linear::ExactRatMatrix;
use holonics::inertia::SymmetricForm;
use crate::native_ecology::constitutive_fibre::NativeEnclosurePropagation;
use num_bigint::BigInt;
use holonics::geometry::{AffineMap3, Rat, RatVec3, cayley_rotation_z};

fn r(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn units() -> MachineUnitsSpec {
    MachineUnitsSpec {
        spatial: std::array::from_fn(|_| "length".into()),
        current: std::array::from_fn(|_| "length".into()),
    }
}

fn clock(lineage: &str) -> ClockSpec {
    ClockSpec {
        lineage: lineage.into(),
        duration: r(1),
        unit: "s".into(),
    }
}

fn site(id: &str, initial: RatVec3, source: bool, receiver: bool) -> GeneratorSiteSpec {
    GeneratorSiteSpec {
        id: id.into(),
        angular: RatVec3::zero(),
        advance: RatVec3::from_i64(0, 1, 0),
        initial,
        phase: PhaseSpec {
            parameter: r(0),
            extra_turns: 0,
            origin_exponent: 0,
            step: AffineMap3::identity(),
            period: Some(1),
        },
        clock: clock(id),
        source,
        receiver,
        material: Some([[r(2), r(0)], [r(0), r(3)]]),
    }
}

fn response() -> SymmetricForm {
    SymmetricForm::from_rows(vec![
        vec![r(1), r(0), r(0)],
        vec![r(0), r(1), r(0)],
        vec![r(0), r(0), r(1)],
    ])
    .unwrap()
}

fn rate_port() -> ExactRatMatrix {
    let mut rows = vec![vec![r(0); 12]; 2];
    rows[0][0] = r(1);
    rows[1][6] = r(1);
    ExactRatMatrix::shaped(2, 12, rows).unwrap()
}

fn arc(id: &str, source: &str, receiver: &str) -> GeneratorPairArcSpec {
    GeneratorPairArcSpec {
        id: id.into(),
        source: source.into(),
        receiver: receiver.into(),
        source_to_receiver: AffineMap3 {
            linear: cayley_rotation_z(&Rat::new(1.into(), 2.into())),
            translation: RatVec3::from_i64(1, -1, 0),
        },
        rate_port: rate_port(),
        response: response(),
        weight: r(1),
        clock: clock(id),
        parameter_units: ["receiver-rate".into(), "source-rate".into()],
    }
}

fn machine() -> GeneratorMachineSpec {
    GeneratorMachineSpec::declare(
        "world",
        units(),
        vec![
            site("a", RatVec3::from_i64(0, 0, 0), true, false),
            site("b", RatVec3::from_i64(2, 1, 0), false, true),
        ],
        vec![arc("ab", "a", "b")],
        vec![],
    )
    .unwrap()
}

pub(super) fn spec() -> GeneratorIncidentFieldSpec {
    GeneratorIncidentFieldSpec {
        source_condition_ports: 0,
        machine: machine(),
        self_comparison: true,
        beta_significand: 1,
        beta_exponent: 0,
        series_terms: 40,
        refinement_steps: 1,
        relaxation_bits: 2,
        material_owners: vec![],
        solve_steps: 128,
        solver: IncidentFieldSolver::Richardson,
        enclosure_propagation: NativeEnclosurePropagation::ComponentIntervals,
        reaction_law: ReactionLaw::Legacy,
    }
}

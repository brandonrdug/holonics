//! Bounded generator-machine integration tests.
//!
//! The CUDA cases keep the source current resident through prepare, publication,
//! return, and remount.  The input uses the native realification of an original
//! complex3 current: native channels 1, 3, and 5 carry nonzero original
//! imaginary coordinates as their real faces.

use super::*;
use crate::native::field_geometry::machine::{
    ClockSpec, GeneratorMachineSpec, GeneratorPairArcSpec, GeneratorSiteSpec, MachineUnitsSpec,
    PhaseSpec,
};
use holonics::exact_linear::ExactRatMatrix;
use holonics::inertia::SymmetricForm;
use holonic_engine::{embedding_fiber::ResidentReadout, native_ecology::constitutive_fibre::{
        NativeEnclosurePropagation, ResidentConstitutiveSection, ResidentNormalEnclosure,
        ResidentNormalEnclosureSection,
    }, resident_section::{ResidentGrain, ResidentSectionRest, ResidentSurface}};
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use relational_geometry::{AffineMap3, Rat, RatVec3, cayley_rotation_z};

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

pub(super) fn make_machine_anchor<'c>(
    surface: &'c ResidentSurface<'c>,
    grain: ResidentGrain,
    shift: i64,
) -> ResidentNormalEnclosure<'c> {
    // Two sites × six native complex channels.  Within each site, scalar
    // channels 1, 3, and 5 are the original complex3 imaginary coordinates.
    let site_values = [17_i64, 5, 29, 7, 41, 11];
    let values = site_values
        .iter()
        .copied()
        .chain(site_values.iter().copied())
        .flat_map(|value| {
            let value = (value << 10) + shift;
            [(value, value), (0, 0)]
        })
        .chain(std::iter::once((65536, 65536)))
        .collect();
    let raw = surface
        .mount_section_rest(
            &ResidentSectionRest::found(1, 25, ResidentGrain(0), 64, values).unwrap(),
        )
        .unwrap();
    ResidentNormalEnclosureSection::from_points(
        ResidentConstitutiveSection::rationals(&raw).unwrap(),
        grain,
    )
    .unwrap()
    .row(0)
    .unwrap()
    .to_owned()
    .unwrap()
}

fn pairing(
    left: &[holonic_engine::ExactComplexWaveCurrent],
    right: &[holonic_engine::ExactComplexWaveCurrent],
) -> Rat {
    left.iter()
        .zip(right)
        .map(|(a, b)| &a.real * &b.real + &a.imaginary * &b.imaginary)
        .sum()
}

#[test]
fn generator_machine_declaration_roundtrips_and_preserves_fixed_counts() {
    let declaration = machine();
    let compiled = declaration.compile().unwrap();
    assert_eq!(compiled.sites().len(), 2);
    assert_eq!(compiled.arcs().len(), 1);
    assert!(
        compiled.arcs()[0]
            .source_to_receiver()
            .linear
            .is_special_orthogonal()
    );
    assert_eq!(compiled.arcs()[0].source(), "a");
    assert_eq!(compiled.arcs()[0].receiver(), "b");
    let encoded = serde_json::to_string(&declaration).unwrap();
    let decoded: GeneratorMachineSpec = serde_json::from_str(&encoded).unwrap();
    assert_eq!(declaration, decoded);
}

#[test]
#[ignore = "requires CUDA; fixed generator operation, realified imaginary modes, return and remount"]
fn generator_body_preserves_native_imaginary_modes_and_frozen_pair_contact() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let grain = ResidentGrain(48);
    let mut body = NativeCoupledBody::found_generator_field(&surface, spec(), grain).unwrap();
    assert_eq!(body.roots(), 4);
    assert_eq!(body.members(), 2);
    assert_eq!(body.scope(), "incident-field-joint");

    let source_before = body.incident_current_boundary().unwrap().inspect().unwrap();
    let anchor = make_machine_anchor(&surface, grain, 0);
    let anchor_reading = anchor.inspect().unwrap();
    assert!(anchor_reading.center[1].real != Rat::zero());
    assert!(anchor_reading.center[3].real != Rat::zero());
    assert!(anchor_reading.center[5].real != Rat::zero());
    assert!(anchor_reading.center[1].imaginary.is_zero());
    let held = vec![false; anchor.view().components() / 2];
    let prepared = body.prepare_incident_field(anchor.view(), &held).unwrap();
    assert_eq!(prepared.boundary_components(), 24);
    let prepared_output = prepared.joint_output().inspect().unwrap();
    assert_eq!(prepared_output.center.len(), 15); // 12 boundary + 3 contact channels
    assert!(prepared_output.center.iter().all(|q| q.imaginary.is_zero()));
    assert!(prepared_output.center[1].real != Rat::zero());
    assert!(prepared_output.center[3].real != Rat::zero());
    assert!(prepared_output.center[5].real != Rat::zero());
    let generated = body.publish_incident_field(prepared, false, true).unwrap();
    let comparison = generated.comparison_id().unwrap();
    let frozen_output = generated.joint_output().inspect().unwrap();
    assert_eq!(body.pending_coupled_predictions(), 1);
    assert_eq!(
        body.incident_current_boundary().unwrap().inspect().unwrap(),
        source_before
    );

    let mut restored = body.rest().unwrap().remount(&surface).unwrap();
    // The retained boundary read at the (unchanged) contemporary cut is the producing word.
    let restored_output = restored.contemporary_incident_comparison(comparison).unwrap();
    assert_eq!(
        restored_output.joint_output().inspect().unwrap(),
        frozen_output
    );
    assert_eq!(restored.pending_coupled_predictions(), 1);

    let shifted_anchor = make_machine_anchor(&surface, grain, 1);
    let shifted = restored
        .prepare_incident_field(shifted_anchor.view(), &held)
        .unwrap();
    let shifted_output = shifted.joint_output().inspect().unwrap();
    let negative_anchor = make_machine_anchor(&surface, grain, -1);
    let negative = restored
        .prepare_incident_field(negative_anchor.view(), &held)
        .unwrap();
    let negative_output = negative.joint_output().inspect().unwrap();
    let baseline_output = frozen_output.clone();
    let half = Rat::new(1.into(), 2.into());
    let delta_output = negative_output
        .center
        .iter()
        .zip(&shifted_output.center)
        .map(|(before, after)| {
            holonic_engine::ExactComplexWaveCurrent::new(
                (&after.real - &before.real) * &half,
                (&after.imaginary - &before.imaginary) * &half,
            )
        })
        .collect::<Vec<_>>();
    let baseline_source = anchor.inspect().unwrap();
    let shifted_source = shifted_anchor.inspect().unwrap();
    let delta_source = baseline_source
        .center
        .iter()
        .zip(&shifted_source.center)
        .map(|(before, after)| after.subtract(before))
        .collect::<Vec<_>>();
    let current_before_return = restored.inspect_current().unwrap();
    let returned = restored
        .prepare_incident_material_return(comparison, restored_output.joint_output(), 4)
        .unwrap();
    assert!(returned.contact.is_none());
    let scale = returned
        .contact_scale_covector()
        .expect("pair material derivative");
    assert_eq!((scale.rows(), scale.components()), (1, 2));
    assert!(
        scale
            .inspect_rows()
            .unwrap()
            .iter()
            .all(|r| r.center[0].imaginary.is_zero())
    );
    let direction_forward = pairing(&baseline_output.center, &delta_output);
    let direction_adjoint = pairing(
        &returned.anchor_covector().inspect().unwrap().center,
        &delta_source,
    );
    let residual = (&direction_forward - &direction_adjoint).abs();
    let scale = direction_forward.abs().max(direction_adjoint.abs());
    assert!(scale > Rat::zero());
    assert!(
        residual < &scale / r(1000),
        "full central-difference pairing residual {residual}, forward {direction_forward}, adjoint {direction_adjoint}"
    );
    assert!(
        returned
            .anchor_covector()
            .inspect()
            .unwrap()
            .center
            .iter()
            .any(|value| !value.is_zero())
    );
    restored.publish_incident_material_return(returned).unwrap();
    assert_eq!(restored.pending_coupled_predictions(), 0);
    let current_after_return = restored.inspect_current().unwrap();
    assert_eq!(
        current_before_return["joint"],
        current_after_return["joint"]
    );
    assert_eq!(
        current_before_return["sites"],
        current_after_return["sites"]
    );
}

#[test]
#[ignore = "requires CUDA; generator declaration rejects incompatible owners and restrictions"]
fn generator_body_rejects_incompatible_material_owners_and_missing_self_support() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let grain = ResidentGrain(48);
    let mut bad_owners = spec();
    bad_owners.material_owners = vec![0];
    assert!(NativeCoupledBody::found_generator_field(&surface, bad_owners, grain).is_err());
    let mut no_self = spec();
    no_self.self_comparison = false;
    assert!(NativeCoupledBody::found_generator_field(&surface, no_self, grain).is_err());

    let mut body = NativeCoupledBody::found_generator_field(&surface, spec(), grain).unwrap();
    let anchor = make_machine_anchor(&surface, grain, 0);
    let held = vec![false; anchor.view().components() / 2];
    assert!(
        body.prepare_incident_field_restricted(anchor.view(), &held, &[0], &[])
            .is_err()
    );
}

/// The reaction law is a declared wire field: absent on saved declarations (decoded as
/// `Legacy`, so existing files keep their law and bytes), explicit when `PowerNeutral`; the
/// power-neutral feature chart is `6 + 13c` against the legacy `6 + 7c`.
#[test]
fn reaction_law_wire_defaults_to_legacy_and_sets_the_realified_extent() {
    let legacy = spec();
    let wire = serde_json::to_value(&legacy).unwrap();
    assert!(wire.get("reaction_law").is_none(), "legacy wire unchanged");
    let decoded: IncidentModelSpec = serde_json::from_value(wire).unwrap();
    assert_eq!(decoded, IncidentModelSpec::Generator(legacy.clone()));
    let mut neutral = legacy.clone();
    neutral.reaction_law = ReactionLaw::PowerNeutral;
    let wire = serde_json::to_value(&neutral).unwrap();
    assert_eq!(wire["reaction_law"], "power-neutral");
    let decoded: IncidentModelSpec = serde_json::from_value(wire).unwrap();
    assert_eq!(decoded, IncidentModelSpec::Generator(neutral.clone()));
    let (old, new) = (
        IncidentModelSpec::Generator(legacy.clone())
            .compile()
            .unwrap(),
        IncidentModelSpec::Generator(neutral.clone())
            .compile()
            .unwrap(),
    );
    assert_eq!(new.reaction, ReactionLaw::PowerNeutral);
    assert!(old.material_features.iter().any(|f| *f > 6));
    for (a, b) in old.material_features.iter().zip(&new.material_features) {
        assert_eq!((a - 6) % 7, 0);
        assert_eq!(*b, 6 + 13 * ((a - 6) / 7));
    }
    // The legacy slot chart cannot declare the generator-only law.
    let mut slot = serde_json::to_value(&neutral).unwrap();
    slot.as_object_mut().unwrap().remove("machine");
    assert!(serde_json::from_value::<IncidentModelSpec>(slot).is_err());
}

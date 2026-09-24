use super::super::super::tests::{populate, seed};
use super::*;
use crate::embedding_fiber::ResidentReadout;
use crate::native_ecology::constitutive_fibre::PairedJunctionLinearization;
use crate::native_ecology::constitutive_fibre::{ResidentConstitutiveCurrent, ResidentNormalInput};
use crate::resident_section::ResidentSectionRest;
use num_traits::Zero;

fn point<'c>(s: &'c ResidentSurface<'c>, values: &[i64]) -> ResidentSection<'c> {
    s.mount_section_rest(
        &ResidentSectionRest::found(
            1,
            values.len(),
            ResidentGrain(0),
            64,
            values.iter().map(|v| (*v, *v)).collect(),
        )
        .unwrap(),
    )
    .unwrap()
}

fn enclosed<'c>(
    s: &'c ResidentSurface<'c>,
    values: &[i64],
    grain: ResidentGrain,
) -> ResidentNormalEnclosure<'c> {
    ResidentNormalInput::from(ResidentConstitutiveCurrent::integers(&point(s, values)).unwrap())
        .enclosure(s, grain)
        .unwrap()
}

fn contains(
    actual: &[ExactComplexWaveCurrent],
    expected: &[ExactComplexWaveCurrent],
    radius: &Rat,
) {
    assert_eq!(actual.len(), expected.len());
    let error: Rat = actual
        .iter()
        .zip(expected)
        .map(|(a, b)| a.subtract(b).norm_square())
        .sum();
    assert!(
        error <= radius * radius,
        "cotangent outside returned ball: {error} > {}",
        radius * radius
    );
}

/// Reflection-target parity: the device target comparison returns input and material covectors
/// that contain the exact host pullback of `target − outgoing` through `PairedJunctionLinearization`.
#[test]
#[ignore = "requires CUDA; source target uses the resident operative adjoint"]
fn reflected_target_matches_exact_paired_pullback_and_boundary_target() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let grain = ResidentGrain(32);
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(), grain).unwrap();
    populate(&mut field);
    let source = field.read_current_source().unwrap();
    let input = source.enclosure();
    let reflected = source.reflect(input).unwrap();
    let mut target_values = vec![0; source.boundary_components()];
    // Nonzero target only on the visible boundary; internal target coordinates remain zero.
    target_values[0] = 3;
    target_values[1] = -2;
    target_values[2] = 1;
    let target_enclosure = enclosed(&surface, &target_values, grain);
    let target = target_enclosure.view();
    let returned = reflected.compare_target(target, 0).unwrap();
    let x = input.inspect().unwrap();
    let t = target.inspect().unwrap();
    let m = source.boundary_components() / 2;
    let k = source.births().len();
    let material = source.material().unwrap().unwrap().inspect().unwrap();
    let columns = material
        .center
        .chunks_exact(m)
        .map(|v| v.to_vec())
        .collect::<Vec<_>>();
    let exact_forward =
        PairedJunctionLinearization::at(columns, &x.center[..m], &x.center[m..]).unwrap();
    // Form the reference residual from the exact forward face; the resident reflection carries
    // its own solve and rounding enclosure and is not assumed to equal that face exactly.
    let exact = exact_forward
        .pullback(
            &t.center
                .iter()
                .zip(exact_forward.outgoing())
                .map(|(a, b)| a.subtract(b))
                .collect::<Vec<_>>(),
            &vec![ExactComplexWaveCurrent::zero(); k],
        )
        .unwrap();
    let input_expected = exact
        .source
        .iter()
        .chain(&exact.incoming_internal)
        .cloned()
        .collect::<Vec<_>>();
    let input_actual = returned.input_covector().inspect().unwrap();
    contains(&input_actual.center, &input_expected, &input_actual.radius);
    let (actual, material_radius) = returned.material_covector().unwrap();
    let actual_columns: Vec<_> = (0..k).flat_map(|j| actual.contact(j).unwrap()).collect();
    let exact_columns: Vec<_> = (0..k)
        .flat_map(|j| exact.contacts.contact(j).unwrap())
        .collect();
    contains(&actual_columns, &exact_columns, &material_radius);
    assert!(exact_columns.iter().any(|v| v.norm_square() > Rat::zero()));
}

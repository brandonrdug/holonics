use super::super::super::tests::{populate, seed};
use super::*;
use crate::embedding_fiber::ResidentReadout;
use crate::native_ecology::constitutive_fibre::PairedJunctionLinearization;
use crate::native_ecology::constitutive_fibre::{
    ResidentConstitutiveCurrent, ResidentHeldSection, ResidentNormalInput,
};
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

#[test]
#[ignore = "requires CUDA; held coordinates are zeroed before the operative paired adjoint"]
fn held_target_matches_cold_pullback_with_held_residual_removed() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let grain = ResidentGrain(32);
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(), grain).unwrap();
    populate(&mut field);
    let source = field.read_current_source().unwrap();
    let input = source.enclosure();
    let reflected = source.reflect(input).unwrap();
    let d = source.boundary_components();
    let given = input.restrict(0..d).unwrap();
    let held = ResidentHeldSection::found(given.view(), &[true, false, true]).unwrap();
    let target_enclosure = enclosed(&surface, &[3, -2, 1, 0, 0, 0], grain);
    let returned = reflected
        .compare_received_target(target_enclosure.view(), 0, &held)
        .unwrap();
    let x = input.inspect().unwrap();
    let t = target_enclosure.inspect().unwrap();
    let m = d / 2;
    let k = source.births().len();
    let material = source.material().unwrap().unwrap().inspect().unwrap();
    let columns = material
        .center
        .chunks_exact(m)
        .map(|v| v.to_vec())
        .collect::<Vec<_>>();
    let exact_forward =
        PairedJunctionLinearization::at(columns, &x.center[..m], &x.center[m..]).unwrap();
    let raw = t
        .center
        .iter()
        .zip(exact_forward.outgoing())
        .enumerate()
        .map(|(j, (target, output))| {
            if held.held()[j] {
                ExactComplexWaveCurrent::zero()
            } else {
                target.subtract(output)
            }
        })
        .collect::<Vec<_>>();
    let exact = exact_forward
        .pullback(&raw, &vec![ExactComplexWaveCurrent::zero(); k])
        .unwrap();
    let input_expected = exact
        .source
        .iter()
        .chain(&exact.incoming_internal)
        .cloned()
        .collect::<Vec<_>>();
    assert!(
        input_expected
            .iter()
            .skip(m)
            .any(|v| v.norm_square() > Rat::zero()),
        "the held output mask must not erase the internal input pullback"
    );
    let prefix = target_enclosure.view().restrict(0..4).unwrap();
    let prefix_return = reflected
        .compare_received_target(prefix.view(), 0, &held)
        .unwrap();
    let prefix_input = prefix_return.input_covector().inspect().unwrap();
    contains(&prefix_input.center, &input_expected, &prefix_input.radius);
    assert!(reflected.compare_target(prefix.view(), 0).is_err());
    let all_held = ResidentHeldSection::found(given.view(), &[true, true, true]).unwrap();
    let zero = reflected
        .compare_received_target(target_enclosure.view(), 0, &all_held)
        .unwrap();
    let zero = zero.input_covector().inspect().unwrap();
    assert!(zero.center.iter().all(|v| v.norm_square() == Rat::zero()));
    assert_eq!(zero.radius, Rat::zero());
    // Holding every visible boundary coordinate must still permit a target on the interior.
    let mut joint_target = vec![0i64; 2 * (m + k)];
    joint_target[2 * m] = 1;
    let joint_target = enclosed(&surface, &joint_target, grain);
    let interior_return = reflected
        .compare_received_target(joint_target.view(), 0, &all_held)
        .unwrap();
    let jt = joint_target.inspect().unwrap();
    let inner_residual = jt.center[m..]
        .iter()
        .zip(exact_forward.internal())
        .map(|(a, b)| a.subtract(b))
        .collect::<Vec<_>>();
    let inner_exact = exact_forward
        .pullback(&vec![ExactComplexWaveCurrent::zero(); m], &inner_residual)
        .unwrap();
    let inner_expected = inner_exact
        .source
        .iter()
        .chain(&inner_exact.incoming_internal)
        .cloned()
        .collect::<Vec<_>>();
    let inner_actual = interior_return.input_covector().inspect().unwrap();
    contains(&inner_actual.center, &inner_expected, &inner_actual.radius);
    assert!(inner_expected.iter().any(|v| v.norm_square() > Rat::zero()));
    let input_actual = returned.input_covector().inspect().unwrap();
    contains(&input_actual.center, &input_expected, &input_actual.radius);
    let (actual, material_radius) = returned.material_covector().unwrap();
    let actual_columns: Vec<_> = (0..k).flat_map(|j| actual.contact(j).unwrap()).collect();
    let exact_columns: Vec<_> = (0..k)
        .flat_map(|j| exact.contacts.contact(j).unwrap())
        .collect();
    contains(&actual_columns, &exact_columns, &material_radius);
}

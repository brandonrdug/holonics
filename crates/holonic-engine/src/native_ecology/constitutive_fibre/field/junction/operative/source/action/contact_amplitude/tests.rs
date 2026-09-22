use super::super::contact_scale::tests::{current, declared_field};
use super::*;
use crate::embedding_fiber::ResidentReadout;
use num_traits::{Signed, Zero};
use relational_geometry::Rat;

#[test]
#[ignore = "requires CUDA; positive pair publication, old source, fixed template and bounded state"]
fn amplitude_publication_changes_the_action_without_an_update_archive() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let grain = ResidentGrain(32);
    let mut field = declared_field(&surface, grain, false, 1);
    let input = current(&surface, &(1..=18).collect::<Vec<i64>>(), grain);
    let gy = current(&surface, &(1..=18).rev().collect::<Vec<i64>>(), grain);
    let old = field.read_current_source().unwrap();
    let before = old
        .action_matrix_free_auto(input.row(0).unwrap(), 128)
        .unwrap();
    let frozen = before.output().inspect().unwrap();
    let pullback = before.pullback_full_auto(gy.row(0).unwrap(), 128).unwrap();
    let mut old_wire = Vec::new();
    old.rest().unwrap().write(&mut old_wire).unwrap();
    let proposal = field
        .prepare_declared_contact_amplitude_return(&[&pullback], 3, 8)
        .unwrap();
    let amplitudes = proposal.inspect_amplitudes().unwrap();
    assert!(amplitudes.iter().all(|r| r > &Rat::zero()));
    assert!(amplitudes.iter().any(|r| r != &Rat::from_integer(1.into())));
    let steps = proposal.inspect_step_bits().unwrap();
    for (g, k) in proposal
        .gradient()
        .inspect_rows()
        .unwrap()
        .iter()
        .zip(steps)
    {
        let eta = Rat::new(1.into(), num_bigint::BigInt::from(1) << k);
        assert!(eta * (g.center[0].real.abs() + &g.radius) <= Rat::new(1.into(), 2.into()));
    }
    // Two concurrently staged proposals do not license publishing a stale successor.
    let stale = field
        .prepare_declared_contact_amplitude_return(&[&pullback], 3, 8)
        .unwrap();
    field
        .commit_declared_contact_amplitude_return(proposal)
        .unwrap();
    assert!(
        field
            .commit_declared_contact_amplitude_return(stale)
            .is_err()
    );
    let now = field.read_current_source().unwrap();
    assert_eq!(
        now.inspect_declared_amplitudes().unwrap().unwrap(),
        amplitudes
    );
    let after = now
        .action_matrix_free_auto(input.row(0).unwrap(), 128)
        .unwrap()
        .output()
        .inspect()
        .unwrap();
    assert_ne!(after.center, frozen.center);
    assert_eq!(
        old.action_matrix_free_auto(input.row(0).unwrap(), 128)
            .unwrap()
            .output()
            .inspect()
            .unwrap(),
        frozen
    );
    let mut old_again = Vec::new();
    old.rest().unwrap().write(&mut old_again).unwrap();
    assert_eq!(old_wire, old_again);
    // The complete old cotangent is still valid; its current relative basis must change.
    let rebased = field
        .prepare_declared_contact_amplitude_return(&[&pullback], 3, 8)
        .unwrap();
    let old_gradient = old.declared_factor_scale_gradient(&pullback, 3).unwrap();
    let old_rows = old_gradient.gradient().inspect_rows().unwrap();
    let current_rows = rebased.gradient().inspect_rows().unwrap();
    for ((previous, current), rho) in old_rows.iter().zip(&current_rows).zip(&amplitudes) {
        let expected = &previous.center[0].real * rho;
        assert!(
            (&current.center[0].real - expected).abs() <= &current.radius + rho * &previous.radius
        );
    }
    field
        .commit_declared_contact_amplitude_return(rebased)
        .unwrap();
    let op = field.junction.as_ref().unwrap().operative.as_ref().unwrap();
    let template = Rc::clone(
        &op.sections
            .factor_program
            .as_ref()
            .unwrap()
            .amplitude_family
            .as_ref()
            .unwrap()
            .template_values,
    );
    let mut resting_size = None;
    for _ in 0..4 {
        let p = field
            .prepare_declared_contact_amplitude_return(&[&pullback], 3, 8)
            .unwrap();
        field.commit_declared_contact_amplitude_return(p).unwrap();
        let op = field.junction.as_ref().unwrap().operative.as_ref().unwrap();
        let program = op.sections.factor_program.as_ref().unwrap();
        assert_eq!(program.rank, 0);
        assert!(Rc::ptr_eq(
            &template,
            &program.amplitude_family.as_ref().unwrap().template_values
        ));
        assert_eq!(field.operative_return_storage().unwrap().returns, 0);
        assert!(field.history.is_empty());
        let mut snapshot = Vec::new();
        field.rest(&[], &[]).unwrap().write(&mut snapshot).unwrap();
        if let Some(size) = resting_size {
            assert_eq!(
                snapshot.len(),
                size,
                "completed update storage must not grow"
            );
        }
        resting_size = Some(snapshot.len());
    }
    eprintln!(
        "fixed pair material rest size after repeated updates: {} bytes",
        resting_size.unwrap()
    );
    // The cold admission check validates the parameter/template equation, including its transpose.
    {
        use super::super::super::super::rest::{
            OperativeFactorProgramFrame, validate_amplitude_family_sections,
        };
        let op = field.junction.as_ref().unwrap().operative.as_ref().unwrap();
        let p = op.sections.factor_program.as_ref().unwrap();
        let f = p.amplitude_family.as_ref().unwrap();
        let read = |s: &ResidentSection<'_>| surface.detach_section(s, 64).unwrap();
        let factor = [
            read(&p.row_offsets),
            read(&p.columns),
            read(&p.values),
            read(&p.transpose_offsets),
            read(&p.transpose_rows),
            read(&p.transpose_values),
            read(&p.left),
            read(&p.right),
            read(&p.defects),
        ];
        let family = [
            read(&f.template_values),
            read(&f.template_transpose_values),
            read(&f.template_bounds),
            read(&f.amplitudes),
        ];
        let bounds = read(&op.sections.bounds);
        let frame = OperativeFactorProgramFrame {
            rows: p.rows,
            boundary_components: p.boundary_components,
            rank: p.rank,
            nonzeros: p.nonzeros,
            group_width: Some(3),
        };
        let check = |f: &[ResidentSectionRest; 4], p: &[ResidentSectionRest; 9]| {
            validate_amplitude_family_sections(
                &frame,
                f,
                p,
                &bounds,
                grain.0,
                frame.rows,
                frame.boundary_components,
            )
        };
        check(&family, &factor).unwrap();
        let mut wrong = family.clone();
        wrong[3].intervals[0].0 += 1;
        wrong[3].intervals[0].1 += 1;
        assert!(
            check(&wrong, &factor).is_err(),
            "changed rho with old map must be refused"
        );
        let mut wrong = factor.clone();
        wrong[5].intervals[0].0 += 1;
        wrong[5].intervals[0].1 += 1;
        assert!(
            check(&family, &wrong).is_err(),
            "changed transpose must be refused"
        );
        let mut wrong = family.clone();
        wrong[3].intervals[..6].fill((0, 0));
        assert!(
            check(&wrong, &factor).is_err(),
            "zero amplitude must be refused"
        );
    }
    // A future unconstrained append would destroy the declared family and is rejected.
    let current_source = field.read_current_source().unwrap();
    let action = current_source
        .action_matrix_free_auto(input.row(0).unwrap(), 128)
        .unwrap();
    let g = action.pullback_full_auto(gy.row(0).unwrap(), 128).unwrap();
    assert!(
        field
            .prepare_global_action_material_return(
                &[&g],
                8,
                NativeContactRealization::DyadicDeposit
            )
            .is_err()
    );
    let field_rest = field.rest(&[], &[]).unwrap();
    let mut bytes = Vec::new();
    field_rest.write(&mut bytes).unwrap();
    let parsed = crate::native_ecology::constitutive_fibre::NativeFieldRest::read(
        &mut bytes.as_slice(),
        bytes.len() as u64,
    )
    .unwrap();
    let (mut restored, _, _) = NativeConstitutiveField::remount(&surface, parsed).unwrap();
    let restored_source = restored.read_current_source().unwrap();
    assert_eq!(
        restored_source.inspect_declared_amplitudes().unwrap(),
        current_source.inspect_declared_amplitudes().unwrap()
    );
    assert_eq!(
        restored_source
            .action_matrix_free_auto(input.row(0).unwrap(), 128)
            .unwrap()
            .output()
            .inspect()
            .unwrap(),
        action.output().inspect().unwrap()
    );
}

#[test]
#[ignore = "requires CUDA; low-grain positive point and unsigned-128 gradient bound"]
fn positive_amplitude_proposal_handles_extreme_signed_gradient() {
    use super::super::contact_scale::tests::packet;
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let gradient = packet(
        &surface,
        2,
        6,
        vec![i128::MIN, 0, i128::MAX, i128::MAX, 0, i128::MAX],
    );
    let old = packet(&surface, 2, 6, vec![1, 0, 0, 1, 0, 0]);
    let next = surface.fresh_section(2, 6, ResidentGrain(0)).unwrap();
    let steps = surface.fresh_section(2, 2, ResidentGrain(0)).unwrap();
    let reference = surface.fresh_section(2, 6, ResidentGrain(0)).unwrap();
    let flags = surface
        .fresh_section(2, SLOT_WORDS / 2, ResidentGrain(0))
        .unwrap();
    let mut pass = surface.begin_passage(&[vec![]]).unwrap();
    {
        let lane = pass.open(0, &[]).unwrap();
        surface
            .record_contact_amplitude_proposal(
                &lane,
                &gradient,
                &old,
                2,
                0,
                1,
                &next,
                &steps,
                Some(&reference),
                &flags,
            )
            .unwrap();
        surface.collect_phase_status(&lane, &flags, 2).unwrap();
    }
    pass.close(0, &next, 64).unwrap();
    let receipt = pass.finish().unwrap().launch().unwrap();
    assert!(receipt.obstruction.is_empty(), "{:?}", receipt.obstruction);
    assert_eq!(
        wides(&surface.detach_section(&next, 64).unwrap().intervals).unwrap(),
        vec![1, 0, 0, 1, 0, 0]
    );
    assert_eq!(
        wides(&surface.detach_section(&steps, 64).unwrap().intervals).unwrap(),
        vec![128, 128]
    );
}

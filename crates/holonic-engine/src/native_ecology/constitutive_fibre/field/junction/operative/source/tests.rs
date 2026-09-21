//! **These `#[ignore]`d tests mount a CUDA context; run them serially.**
//! `ResidentSurface::on` calibrates the allocator grain from `cuMemGetInfo_v2`, which reports the
//! **whole device's** free extent. Another allocation on the card between its samples — a second
//! test thread, a second cargo test process, any other GPU program — enters the difference and the
//! calibration refuses with `one-word charge … and restored free extent … do not close`. That is
//! apparatus, not the law under test. Run `-- --include-ignored --test-threads=1` with the card
//! otherwise idle; see `docs/DEVELOPMENT.md`'s verification cadence.

use super::super::tests::{populate, seed};
use super::*;
use crate::embedding_fiber::ResidentReadout;
use crate::native_ecology::constitutive_fibre::ResidentNormalEnclosureSection;
use num_bigint::BigInt;
use num_traits::Zero;

#[test]
#[ignore = "requires CUDA; exact rank-one reference discriminates full b adjoint and one sigma on a sum of D factors"]
fn global_contact_return_matches_exact_rank_one_derivative_and_step() {
    use crate::native_ecology::constitutive_fibre::{
        ResidentConstitutiveSection, ResidentNormalEnclosureSection,
    };
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let grain = ResidentGrain(32);
    let scale = 1i128 << 32;
    let mut field = NativeConstitutiveField::found_with_enclosed_junction(
        &s,
        seed().into_iter().take(1).collect(),
        grain,
    )
    .unwrap();
    let mount = |rows, width, values: Vec<i128>| {
        let words = values
            .into_iter()
            .flat_map(|v| [v as i64, (v >> 64) as i64])
            .map(|v| (v, v))
            .collect();
        s.mount_section_rest(
            &ResidentSectionRest::found(rows, width, ResidentGrain(0), 64, words).unwrap(),
        )
        .unwrap()
    };
    field
        .register_declared_contact_map(
            mount(1, 12, vec![scale / 4, 0, 0, 0, 0, 0]),
            mount(1, 4, vec![0, 0]),
            mount(1, 4, vec![0, 0]),
            vec![NativeFieldContactOrigin::declared(0, 0, 0)],
        )
        .unwrap();
    let input = s
        .mount_section_rest(
            &ResidentSectionRest::found(
                1,
                8,
                ResidentGrain(0),
                64,
                [1, 0, 0, 0, 0, 0, 1, 0]
                    .into_iter()
                    .map(|v| (v, v))
                    .collect(),
            )
            .unwrap(),
        )
        .unwrap();
    let g = s
        .mount_section_rest(
            &ResidentSectionRest::found(
                1,
                8,
                ResidentGrain(0),
                64,
                [0, 0, 0, 0, 0, 0, 1, 0]
                    .into_iter()
                    .map(|v| (v, v))
                    .collect(),
            )
            .unwrap(),
        )
        .unwrap();
    let input = ResidentNormalEnclosureSection::from_points(
        ResidentConstitutiveSection::integers(&input).unwrap(),
        grain,
    )
    .unwrap();
    let g = ResidentNormalEnclosureSection::from_points(
        ResidentConstitutiveSection::integers(&g).unwrap(),
        grain,
    )
    .unwrap();
    let source = field.read_current_source().unwrap();
    let before = source.enclosure().inspect().unwrap();
    let action = source
        .action_matrix_free_auto(input.row(0).unwrap(), 128)
        .unwrap();
    let pull = action.pullback_full_auto(g.row(0).unwrap(), 128).unwrap();
    let mut expected = vec![ExactComplexWaveCurrent::zero(); 4];
    expected[0] = ExactComplexWaveCurrent::new(Rat::new(8.into(), 17.into()), Rat::zero());
    expected[3] = ExactComplexWaveCurrent::new(Rat::new((-15).into(), 17.into()), Rat::zero());
    assert!(pull.input_covector().inspect().unwrap().contains(&expected));
    let proposed = field
        .prepare_global_action_material_return(
            &[&pull, &pull],
            2,
            NativeContactRealization::EnclosedFlow,
        )
        .unwrap();
    field
        .commit_global_action_material_return(proposed)
        .unwrap();
    let after = field.read_current_source().unwrap();
    assert_eq!(after.enclosure().inspect().unwrap(), before);
    let delta = after
        .material_difference(&source)
        .unwrap()
        .inspect()
        .unwrap();
    let mut expected = vec![ExactComplexWaveCurrent::zero(); 3];
    expected[0] = ExactComplexWaveCurrent::new(Rat::new(368.into(), 289.into()), Rat::zero());
    assert!(delta.contains(&expected), "{delta:?}");
    assert!(delta.radius < Rat::new(1.into(), 1000.into()), "{delta:?}");
}

#[test]
#[ignore = "requires CUDA; sparse declared D0 exercises forward, full joint pullback, factor material return, current update and transpose admission"]
fn sparse_declared_rank_one_packet_matches_reference_and_rejects_bad_transpose() {
    use crate::native_ecology::constitutive_fibre::{
        ResidentConstitutiveSection, ResidentNormalEnclosureSection,
    };
    let ro = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&ro).unwrap();
    let grain = ResidentGrain(32);
    let scale = 1i128 << grain.0;
    let packet = |rows: usize, width: usize, values: Vec<i128>| {
        let intervals = values
            .into_iter()
            .flat_map(|value| [value as i64, (value >> 64) as i64].map(|word| (word, word)))
            .collect();
        surface
            .mount_section_rest(
                &ResidentSectionRest::found(rows, width, ResidentGrain(0), 64, intervals).unwrap(),
            )
            .unwrap()
    };
    let input = surface
        .mount_section_rest(
            &ResidentSectionRest::found(
                1,
                8,
                ResidentGrain(0),
                64,
                [1, 0, 0, 0, 0, 0, 1, 0]
                    .into_iter()
                    .map(|v| (v, v))
                    .collect(),
            )
            .unwrap(),
        )
        .unwrap();
    let covector = surface
        .mount_section_rest(
            &ResidentSectionRest::found(
                1,
                8,
                ResidentGrain(0),
                64,
                [0, 0, 0, 0, 0, 0, 1, 0]
                    .into_iter()
                    .map(|v| (v, v))
                    .collect(),
            )
            .unwrap(),
        )
        .unwrap();
    let input = ResidentNormalEnclosureSection::from_points(
        ResidentConstitutiveSection::integers(&input).unwrap(),
        grain,
    )
    .unwrap();
    let covector = ResidentNormalEnclosureSection::from_points(
        ResidentConstitutiveSection::integers(&covector).unwrap(),
        grain,
    )
    .unwrap();
    let incidence = || NativeFieldDeclaredIncidence {
        row_offsets: packet(1, 4, vec![0, 1]),
        columns: packet(1, 2, vec![0]),
        values: packet(1, 4, vec![scale / 4, 0]),
        transpose_offsets: packet(1, 8, vec![0, 1, 1, 1]),
        transpose_rows: packet(1, 2, vec![0]),
        transpose_values: packet(1, 4, vec![scale / 4, 0]),
        left: packet(1, 12, vec![0; 6]),
        right: packet(1, 4, vec![0; 2]),
        defects: packet(1, 2, vec![0]),
        rows: 1,
        boundary_components: 6,
        rank: 0,
        nonzeros: 1,
    };
    let origins = vec![NativeFieldContactOrigin::declared(0, 0, 0)];
    let mut field = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        seed().into_iter().take(1).collect(),
        grain,
    )
    .unwrap();
    field
        .register_declared_incidence(
            incidence(),
            packet(1, 4, vec![0, 0]),
            packet(1, 4, vec![0, 0]),
            origins.clone(),
        )
        .unwrap();
    let source = field.read_current_source().unwrap();
    assert!(
        source.material().is_err(),
        "sparse sources must not expose dense material storage"
    );
    let action = source
        .action_matrix_free_auto(input.row(0).unwrap(), 128)
        .unwrap();
    let one = Rat::from_integer(1.into());
    let t = Rat::new(1.into(), 4.into());
    let denominator = one.clone() + t.clone() * t.clone();
    let v = Rat::from_integer(2.into()) * (one.clone() + t.clone()) / denominator;
    let expected = vec![
        ExactComplexWaveCurrent::new(v.clone() - one.clone(), Rat::zero()),
        ExactComplexWaveCurrent::zero(),
        ExactComplexWaveCurrent::zero(),
        ExactComplexWaveCurrent::new(t * v - one, Rat::zero()),
    ];
    let initial = action.output().inspect().unwrap();
    assert!(initial.contains(&expected), "sparse forward: {initial:?}");
    assert!(
        initial.radius < Rat::new(1.into(), 1000.into()),
        "{initial:?}"
    );
    let pullback = action.pullback_full_auto(covector.row(0).unwrap(), 128).unwrap();
    let mut expected_input = vec![ExactComplexWaveCurrent::zero(); 4];
    expected_input[0] = ExactComplexWaveCurrent::new(Rat::new(8.into(), 17.into()), Rat::zero());
    expected_input[3] =
        ExactComplexWaveCurrent::new(Rat::new((-15).into(), 17.into()), Rat::zero());
    assert!(
        pullback
            .input_covector()
            .inspect()
            .unwrap()
            .contains(&expected_input)
    );
    let prepared = field
        .prepare_global_action_material_return(
            &[&pullback, &pullback],
            2,
            NativeContactRealization::DyadicDeposit,
        )
        .unwrap();
    field
        .commit_global_action_material_return(prepared)
        .unwrap();
    let updated = field.read_current_source().unwrap();
    assert_eq!(
        updated.enclosure().inspect().unwrap(),
        source.enclosure().inspect().unwrap()
    );
    updated.rest().unwrap();
    let delta = field
        .operative_return_storage()
        .expect("sparse return journal")
        .returns;
    assert_eq!(delta, 2);
    let action = updated
        .action_matrix_free_auto(input.row(0).unwrap(), 128)
        .unwrap();
    let t = Rat::new(1761.into(), 1156.into());
    let denominator = Rat::from_integer(1.into()) + t.clone() * t.clone();
    let v = Rat::from_integer(2.into()) * (Rat::from_integer(1.into()) + t.clone()) / denominator;
    let expected = vec![
        ExactComplexWaveCurrent::new(v.clone() - Rat::from_integer(1.into()), Rat::zero()),
        ExactComplexWaveCurrent::zero(),
        ExactComplexWaveCurrent::zero(),
        ExactComplexWaveCurrent::new(t * v - Rat::from_integer(1.into()), Rat::zero()),
    ];
    let updated_output = action.output().inspect().unwrap();
    assert!(
        updated_output.contains(&expected),
        "updated sparse forward: {updated_output:?}"
    );
    assert!(
        updated_output.radius < Rat::new(1.into(), 1000.into()),
        "{updated_output:?}"
    );

    let mut malformed = NativeConstitutiveField::found_with_enclosed_junction(
        &surface,
        seed().into_iter().take(1).collect(),
        grain,
    )
    .unwrap();
    let mut bad = incidence();
    bad.transpose_values = packet(1, 4, vec![scale / 2, 0]);
    assert!(
        malformed
            .register_declared_incidence(
                bad,
                packet(1, 4, vec![0, 0]),
                packet(1, 4, vec![0, 0]),
                origins
            )
            .is_err()
    );
    assert!(
        !malformed.has_operative_contacts(),
        "malformed transpose must not publish an operative map"
    );
}

#[test]
#[ignore = "requires CUDA; resident field source joins outgoing and operative internal carriers"]
fn source_packs_boundary_and_internal_b_without_host_readout() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(&surface, seed(), ResidentGrain(72))
            .unwrap();
    populate(&mut field);
    let before = field.census().section_read_outs;
    let source = field.read_current_source().unwrap();
    assert_eq!(field.census().section_read_outs, before);
    assert_eq!(source.field_cut(), field.occurrence_count());
    assert_eq!(source.occurrence(), Some(field.occurrence_count() - 1));
    assert_eq!(source.boundary_components(), 6);
    assert!(source.internal_components() >= 4);
    assert_eq!(
        source.enclosure().components(),
        6 + source.internal_components()
    );
    assert!(source.same_owner(&source));
    let births = source.births().to_vec();
    let actual = source.enclosure().inspect().unwrap();
    let boundary = field
        .inspect_junction_enclosure(3)
        .unwrap()
        .unwrap()
        .outgoing;
    let interior = field
        .stage_operative_contacts()
        .unwrap()
        .inspect()
        .unwrap()
        .internal;
    let expected = boundary
        .center
        .into_iter()
        .chain(interior.center)
        .collect::<Vec<_>>();
    assert_eq!(actual.center, expected);
    assert_eq!(actual.radius, boundary.radius + interior.radius);
    assert!(
        actual.center[3..]
            .iter()
            .any(|v| *v != ExactComplexWaveCurrent::zero())
    );
    let mut later =
        NativeFieldOccurrence::entering(vec![NativePhaseCurrent::new(2, 0, 1).unwrap()]);
    field.advance_resident(&mut later).unwrap();
    assert_eq!(source.field_cut(), 4);
    assert_eq!(source.internal_components(), 2 * births.len());
    assert_eq!(source.births(), births);
    assert_eq!(source.enclosure().inspect().unwrap(), actual);
}

#[test]
#[ignore = "requires CUDA; an aggregate-dark boundary still exposes its opposite internal currents"]
fn source_retains_dark_internal_pair() {
    use crate::native_ecology::constitutive_fibre::field::internal_current::tests::dark;
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let (mut field, _) = dark(&s, true, NativePhaseCurrent::new(0, 1, 1).unwrap());
    let exact = field.inspect_internal_currents().unwrap().unwrap();
    let source = field.read_current_source().unwrap();
    let read = source.enclosure().inspect().unwrap();
    let boundary = field
        .inspect_junction_enclosure(field.occurrence_count() - 1)
        .unwrap()
        .unwrap();
    let zero = ExactComplexWaveCurrent::zero();
    assert!(boundary.outgoing.contains(&vec![zero.clone(); 3]));
    assert!(boundary.held_current.contains(&vec![zero.clone(); 3]));
    assert!(exact.iter().any(|v| v.current != zero));
    let mut complete = vec![zero; 3];
    complete.extend(exact.into_iter().map(|v| v.current));
    assert!(read.contains(&complete));
}

#[test]
#[ignore = "requires CUDA; operative material is a source with its own bound and caused column identities"]
fn material_source_retains_geometry_and_only_proven_points_enter_point_ports() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(&s, seed(), ResidentGrain(72))
            .unwrap();
    let empty = field.read_current_source().unwrap();
    assert!(empty.material().unwrap().is_none());
    let mut previous = None;
    for at in 0..4 {
        let incoming = vec![NativePhaseCurrent::new(at + 1, 1, 1).unwrap()];
        let mut event = match previous.take() {
            Some(old) => NativeFieldOccurrence::through(old, incoming),
            None => NativeFieldOccurrence::entering(incoming),
        };
        previous = Some(field.advance_resident(&mut event).unwrap().source);
    }
    let source = field.read_current_source().unwrap();
    let before = s.census().section_read_outs;
    let material = source.material().unwrap().unwrap();
    let point = material.read_exact_point().unwrap();
    assert_eq!(s.census().section_read_outs, before);
    let actual = material.inspect().unwrap();
    assert_eq!(actual.radius, Rat::zero());
    assert_eq!(actual.center.len(), 3 * source.births().len());
    let words = s.read_out(&point).unwrap();
    let den = BigInt::from(words.last().unwrap().0);
    for (pair, v) in words[..words.len() - 1].chunks_exact(2).zip(&actual.center) {
        assert_eq!(v.real, Rat::new(pair[0].0.into(), den.clone()));
        assert_eq!(v.imaginary, Rat::new(pair[1].0.into(), den.clone()));
    }
    assert_eq!(
        source
            .material_difference(&source)
            .unwrap()
            .inspect()
            .unwrap()
            .radius,
        Rat::zero()
    );
    let mut event = NativeFieldOccurrence::entering(vec![NativePhaseCurrent::unit()]);
    field.advance_resident(&mut event).unwrap();
    assert_eq!(
        source.material().unwrap().unwrap().inspect().unwrap(),
        actual
    );
    let current = field.read_current_source().unwrap();
    assert!(current.material_difference(&source).is_ok());
    let mut other =
        NativeConstitutiveField::found_with_enclosed_junction(&s, seed(), ResidentGrain(72))
            .unwrap();
    populate(&mut other);
    let uncertain = other.read_current_source().unwrap();
    assert!(uncertain.material_difference(&source).is_err());
    assert!(
        uncertain
            .material()
            .unwrap()
            .unwrap()
            .inspect()
            .unwrap()
            .radius
            > Rat::zero()
    );
    assert!(
        uncertain
            .material()
            .unwrap()
            .unwrap()
            .read_exact_point()
            .is_err()
    );
    let bound = [0i128, 0, 1];
    let values = bound
        .into_iter()
        .flat_map(|v| [v as i64, (v >> 64) as i64])
        .map(|v| (v, v))
        .collect();
    let packet = s
        .mount_section_rest(
            &ResidentSectionRest::found(1, 6, ResidentGrain(0), 64, values).unwrap(),
        )
        .unwrap();
    assert!(
        ResidentNormalEnclosureView {
            surface: &s,
            section: &packet,
            offset: 0,
            width: 2,
            grain: ResidentGrain(72)
        }
        .read_exact_point()
        .is_err()
    );
}

#[test]
#[ignore = "requires CUDA; the compiled material reflection encloses the exact physical operator and retains its signed residual"]
fn reflection_source_reuses_its_factor_and_preserves_the_complete_bound() {
    use crate::native_ecology::constitutive_fibre::PairedJunctionLinearization;
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(&s, seed(), ResidentGrain(32))
            .unwrap();
    populate(&mut field);
    let source = field.read_current_source().unwrap();
    let input = source.enclosure();
    let before = s.census().section_read_outs;
    let reflected = source.reflect(input).unwrap();
    assert_eq!(s.census().section_read_outs, before);
    let factor = source.reflection.get().unwrap() as *const _;
    let again = source.reflect(input).unwrap();
    assert_eq!(source.reflection.get().unwrap() as *const _, factor);
    assert_eq!(
        reflected.output().inspect().unwrap(),
        again.output().inspect().unwrap()
    );
    let x = input.inspect().unwrap();
    let material = source.material().unwrap().unwrap().inspect().unwrap();
    let m = source.boundary_components() / 2;
    let columns = material
        .center
        .chunks_exact(m)
        .map(|v| v.to_vec())
        .collect::<Vec<_>>();
    let exact =
        PairedJunctionLinearization::at(columns.clone(), &x.center[..m], &x.center[m..]).unwrap();
    let expected = exact
        .outgoing()
        .iter()
        .chain(exact.internal())
        .cloned()
        .collect::<Vec<_>>();
    let actual = reflected.output().inspect().unwrap();
    assert!(actual.contains(&expected));
    let v = actual.center[..m]
        .iter()
        .zip(&x.center[..m])
        .map(|(a, b)| a.add(b))
        .collect::<Vec<_>>();
    let dots = columns
        .iter()
        .map(|d| {
            d.iter()
                .zip(&v)
                .fold(ExactComplexWaveCurrent::zero(), |a, (d, v)| {
                    a.add(&d.conjugate().multiply(v))
                })
        })
        .collect::<Vec<_>>();
    let residual = (0..m)
        .map(|j| {
            columns.iter().zip(&dots).zip(&x.center[m..]).fold(
                v[j].subtract(&x.center[j].scaled(&Rat::from_integer(2.into()))),
                |a, ((d, dv), b)| {
                    a.add(&d[j].multiply(&dv.subtract(&b.scaled(&Rat::from_integer(2.into())))))
                },
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(reflected.inspect_residual().unwrap(), residual);
    assert_eq!(field.occurrence_count(), source.field_cut());
}

#[test]
#[ignore = "requires CUDA; source action keeps one global resident joint state and its causal D columns"]
fn source_action_retains_global_layout_and_contact_origins() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(&s, seed(), ResidentGrain(32))
            .unwrap();
    populate(&mut field);
    let source = field.read_current_source().unwrap();
    let action = source.action(source.enclosure()).unwrap();
    let layout = action.layout();
    assert_eq!(layout.boundary_components, source.boundary_components());
    assert_eq!(layout.internal_components, source.internal_components());
    assert_eq!(layout.joint_components, source.enclosure().components());
    assert_eq!(layout.contact_count, source.births().len());
    assert_eq!(layout.field_cut, source.field_cut());
    assert_eq!(action.contact_origins().len(), layout.contact_count);
    for (column, origin) in action.contact_origins().iter().enumerate() {
        assert!(!origin.is_declared());
        assert_eq!(origin.column(), column);
        assert_eq!(origin.source(), source.births()[column].source);
        assert_eq!(origin.receiving(), source.births()[column].receiving);
    }
    assert_eq!(
        action.output().inspect().unwrap(),
        source
            .reflect(source.enclosure())
            .unwrap()
            .output()
            .inspect()
            .unwrap()
    );
    assert!(matches!(
        action.factorization(),
        NativeFieldActionFactorization::ResidentDenseReference { .. }
    ));
}

#[test]
#[ignore = "requires CUDA; matrix-free action exercises resident D/D* Richardson and residual carrier"]
fn matrix_free_source_action_keeps_joint_radius_and_residual_resident() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(&s, seed(), ResidentGrain(32))
            .unwrap();
    populate(&mut field);
    let source = field.read_current_source().unwrap();
    let action = source
        .action_matrix_free(source.enclosure(), 2, 120)
        .unwrap();
    assert!(matches!(
        action.factorization(),
        NativeFieldActionFactorization::ResidentRichardsonMatrixFree { .. }
    ));
    assert_eq!(
        action.output().components(),
        source.enclosure().components()
    );
    assert!(action.output().inspect().unwrap().radius >= Rat::zero());
    assert!(action.residual_bound().unwrap() >= Rat::zero());
}

#[test]
#[ignore = "requires CUDA; full joint pullback retains nonzero g_b and two rank-two material returns"]
fn matrix_free_full_pullback_stages_two_directions_without_changing_joint_current() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(&s, seed(), ResidentGrain(32))
            .unwrap();
    populate(&mut field);
    field.enable_operative_contacts().unwrap();
    let source = field.read_current_source().unwrap();
    let action = source
        .action_matrix_free_auto(source.enclosure(), 32)
        .unwrap();
    let dense = source.reflect(source.enclosure()).unwrap();
    assert!(
        action
            .output()
            .inspect()
            .unwrap()
            .contains(&dense.output().inspect().unwrap().center)
    );
    let first = action.pullback_full_auto(source.enclosure(), 32).unwrap();
    let second = action.pullback_full_auto(action.output(), 32).unwrap();
    let incoming = first.input_covector().inspect().unwrap();
    assert!(
        incoming.center[source.boundary_components() / 2..]
            .iter()
            .any(|value| value.norm_square() > Rat::zero())
    );
    let factor_words = s.read_out(&first.resident_currents()).unwrap();
    assert!(
        factor_words
            .iter()
            .any(|(lo, hi)| lo != hi || *lo != 0 || *hi != 0)
    );
    let before = source.enclosure().inspect().unwrap();
    let prepared = field
        .prepare_global_action_material_return(
            &[&first, &second],
            2,
            NativeContactRealization::DyadicDeposit,
        )
        .unwrap();
    field
        .commit_global_action_material_return(prepared)
        .unwrap();
    let after = field.read_current_source().unwrap();
    assert_eq!(after.enclosure().inspect().unwrap(), before);
    assert!(
        after
            .material_difference(&source)
            .unwrap()
            .inspect()
            .unwrap()
            .center
            .iter()
            .any(|value| value.norm_square() > Rat::zero())
    );
}

#[test]
#[ignore = "requires CUDA; shared section reflection and masked input adjoint enclose independent exact paired operators"]
fn reflection_section_shares_internal_source_and_fixed_d_pullback() {
    use crate::native_ecology::constitutive_fibre::{
        PairedJunctionLinearization, ResidentConstitutiveSection,
    };
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let grain = ResidentGrain(32);
    let mut field =
        NativeConstitutiveField::found_with_enclosed_junction(&s, seed(), grain).unwrap();
    populate(&mut field);
    let source = field.read_current_source().unwrap();
    let d = source.boundary_components();
    let m = d / 2;
    let k = source.births.len();
    let scale = 1i128 << grain.0;
    let mut vals = Vec::new();
    for (row, coordinates) in [[1, -2, 3, 1, -1, 2], [-3, 1, 1, -2, 0, 5]]
        .into_iter()
        .enumerate()
    {
        for x in coordinates
            .into_iter()
            .map(|v| i128::from(v) * scale)
            .chain([if row == 0 { scale / 8 } else { 0 }])
        {
            vals.extend([x as i64, (x >> 64) as i64].into_iter().map(|v| (v, v)));
        }
    }
    let packet = s
        .mount_section_rest(
            &ResidentSectionRest::found(2, 2 * (d + 1), ResidentGrain(0), 64, vals).unwrap(),
        )
        .unwrap();
    let boundary = ResidentNormalEnclosureSection::from_resident(&s, packet, 2, d, grain).unwrap();
    let reflected = source.reflect_section(&boundary).unwrap();
    let factor = source.reflection.get().unwrap() as *const _;
    let material = source.material().unwrap().unwrap().inspect().unwrap();
    let columns = material
        .center
        .chunks_exact(m)
        .map(|r| r.to_vec())
        .collect::<Vec<_>>();
    let target = s
        .mount_section_rest(
            &ResidentSectionRest::found(
                2,
                d,
                ResidentGrain(0),
                64,
                [2, -3, 1, 4, 0, -1, -1, 1, 3, -2, 2, 0]
                    .into_iter()
                    .map(|v| (v, v))
                    .collect(),
            )
            .unwrap(),
        )
        .unwrap();
    let targets = ResidentNormalEnclosureSection::from_points(
        ResidentConstitutiveSection::integers(&target).unwrap(),
        grain,
    )
    .unwrap();
    let mask = s
        .mount_section_rest(
            &ResidentSectionRest::found(1, m, ResidentGrain(0), 64, vec![(1, 1), (0, 0), (1, 1)])
                .unwrap(),
        )
        .unwrap();
    let covectors = reflected.input_covectors(&targets, Some(&mask), 3).unwrap();
    let step = Rat::new(1.into(), 8.into());
    let residuals = reflected.inspect_residuals().unwrap();
    for row in 0..2 {
        let x = reflected.joint_input().row(row).unwrap().inspect().unwrap();
        let exact =
            PairedJunctionLinearization::at(columns.clone(), &x.center[..m], &x.center[m..])
                .unwrap();
        let expected = exact
            .outgoing()
            .iter()
            .chain(exact.internal())
            .cloned()
            .collect::<Vec<_>>();
        assert!(
            reflected
                .output()
                .row(row)
                .unwrap()
                .inspect()
                .unwrap()
                .contains(&expected)
        );
        let t = targets.row(row).unwrap().inspect().unwrap();
        let g = t
            .center
            .iter()
            .zip(exact.outgoing())
            .enumerate()
            .map(|(i, (a, b))| {
                if i == 1 {
                    a.subtract(b).scaled(&step)
                } else {
                    ExactComplexWaveCurrent::zero()
                }
            })
            .collect::<Vec<_>>();
        let back = exact
            .pullback(&g, &vec![ExactComplexWaveCurrent::zero(); k])
            .unwrap();
        let expected = back
            .source
            .iter()
            .chain(&back.incoming_internal)
            .cloned()
            .collect::<Vec<_>>();
        assert!(
            covectors
                .row(row)
                .unwrap()
                .inspect()
                .unwrap()
                .contains(&expected)
        );
        assert!(expected[m..].iter().any(|v| v.norm_square() > Rat::zero()));
        let scalar = source
            .reflect(reflected.joint_input().row(row).unwrap())
            .unwrap();
        assert_eq!(
            reflected.output().row(row).unwrap().inspect().unwrap(),
            scalar.output().inspect().unwrap()
        );
        assert_eq!(residuals[row], scalar.inspect_residual().unwrap());
    }
    assert_eq!(source.reflection.get().unwrap() as *const _, factor);
    let held = s
        .mount_section_rest(
            &ResidentSectionRest::found(1, m, ResidentGrain(0), 64, vec![(1, 1); m]).unwrap(),
        )
        .unwrap();
    let zero = reflected.input_covectors(&targets, Some(&held), 3).unwrap();
    for row in 0..2 {
        let r = zero.row(row).unwrap().inspect().unwrap();
        assert!(r.radius.is_zero());
        assert!(r.center.iter().all(|v| v.norm_square().is_zero()));
    }
}

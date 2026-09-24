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
use num_traits::Zero;

/// Dense declared-map parity: the device pullback and material step contain the exact rank-one
/// Cayley derivative and deposit of the same declared contact.
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

/// Sparse factor-action parity: the CSR forward, Chebyshev forward, pullback and updated forward
/// contain the exact rank-one Cayley solution; a transpose that is not `D*` is refused.
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
    let chebyshev = source
        .action_matrix_free_chebyshev(input.row(0).unwrap(), 128)
        .unwrap();
    assert!(matches!(
        chebyshev.factorization(),
        NativeFieldActionFactorization::ResidentFactorProgramChebyshevMatrixFree { .. }
    ));
    assert!(chebyshev.output().inspect().unwrap().contains(&expected));
    let pullback = action
        .pullback_full_auto(covector.row(0).unwrap(), 128)
        .unwrap();
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

/// Reflection parity: section reflection and its masked input adjoint contain the exact host
/// `PairedJunctionLinearization` forward and pullback, row for row.
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

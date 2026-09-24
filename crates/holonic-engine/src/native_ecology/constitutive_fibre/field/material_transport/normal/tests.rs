use super::*;

#[test]
fn normal_objective_separates_fit_prior_solve_and_source_family() {
    let q = |n: i64, d: i64| Rat::new(n.into(), d.into());
    let wave = |r, i, d| ExactComplexWaveCurrent::new(q(r, d), q(i, d));
    // Two distinct target vectors at the same scalar source. The exact optimum cannot fit
    // both. Start at the optimum, then retain a deliberately complex, nonzero solve residual.
    let mut state = NormalConstitution {
        material: NativeFieldMaterialTransportState {
            coefficients: vec![vec![wave(1, 0, 3)], vec![wave(1, 0, 3)]],
            radius: Rat::zero(),
        },
        source_normal: vec![vec![wave(3, 0, 1)]],
        cross_source: vec![vec![wave(1, 0, 1)], vec![wave(1, 0, 1)]],
        target_energy: q(2, 1),
        source_normal_error: Rat::zero(),
        cross_source_error: Rat::zero(),
        target_energy_error: Rat::zero(),
        normal_residual_upper: Rat::zero(),
    };
    let exact = state.objective().unwrap();
    assert_eq!(exact.nominal_data_term, q(5, 9));
    assert_eq!(exact.prior_term, q(1, 9));
    assert_eq!(exact.nominal_minimum.lower, q(2, 3));
    assert_eq!(exact.nominal_minimum.upper, q(2, 3));
    assert!(exact.solve_gap_upper.is_zero());

    state.material.coefficients = vec![vec![wave(2, 1, 4)], vec![wave(5, -3, 15)]];
    let observed = state.objective().unwrap();
    let targets = [
        vec![wave(1, 0, 1), wave(0, 0, 1)],
        vec![wave(0, 0, 1), wave(1, 0, 1)],
    ];
    let direct_data: Rat = targets
        .iter()
        .flat_map(|y| {
            state
                .material
                .coefficients
                .iter()
                .zip(y)
                .map(|(m, y)| m[0].subtract(y).norm_square())
        })
        .sum::<Rat>()
        / q(2, 1);
    assert_eq!(observed.nominal_data_term, direct_data);
    assert!(observed.normal_residual_squared > Rat::zero());
    assert!(observed.nominal_minimum.lower <= q(2, 3));
    assert!(observed.nominal_minimum.upper >= q(2, 3));
    assert!(observed.nominal_regularized_objective - q(2, 3) <= observed.solve_gap_upper);

    // An actual member of the retained source/target balls: x1=9/8, y1=(17/16,0).
    // The second observation remains x2=1, y2=(0,1). Bounds include all mixed terms.
    state.source_normal_error = q(17, 64);
    state.cross_source_error = q(25, 128);
    state.target_energy_error = q(33, 256);
    let family = state.objective().unwrap();
    let actual = [
        (q(9, 8), vec![wave(17, 0, 16), wave(0, 0, 1)]),
        (q(1, 1), targets[1].clone()),
    ];
    let actual_data: Rat = actual
        .iter()
        .flat_map(|(x, y)| {
            state
                .material
                .coefficients
                .iter()
                .zip(y)
                .map(|(m, y)| m[0].scaled(x).subtract(y).norm_square())
        })
        .sum::<Rat>()
        / q(2, 1);
    let actual_minimum = (q(545, 256) - (q(153, 128).pow(2) + q(1, 1)) / q(209, 64)) / q(2, 1);
    assert!(
        family.family_data_term.lower <= actual_data
            && actual_data <= family.family_data_term.upper
    );
    assert!(
        family.family_minimum.lower <= actual_minimum
            && actual_minimum <= family.family_minimum.upper
    );
}

#[test]
fn nonzero_complex_prior_populates_applied_map_and_every_cross_source_coordinate() {
    let z = |r: i64, i: i64| {
        ExactComplexWaveCurrent::new(Rat::new(r.into(), 8.into()), Rat::new(i.into(), 8.into()))
    };
    let coefficients = vec![vec![z(3, -5), z(7, 1)], vec![z(-2, 9), z(11, -4)]];
    let prior = NativeNormalPrior::from_coefficients(coefficients.clone()).unwrap();
    let layout = NormalLayout::for_sources(2, 2).unwrap();
    let words = initial_words_for_sources_with_prior(2, 2, 16, &prior).unwrap();
    let rest =
        ResidentSectionRest::found(1, layout.state_words, ResidentGrain(0), 64, words).unwrap();
    let state = decode_state_layout(&rest, layout, 2, 16).unwrap();
    assert_eq!(state.material.coefficients, coefficients);
    assert_eq!(state.cross_source, coefficients);
    assert_eq!(state.target_energy, prior.target_energy);
    assert!(state.material.radius.is_zero());
    assert!(state.normal_residual_upper.is_zero());
    assert!(
        state
            .normal_residual()
            .unwrap()
            .iter()
            .flatten()
            .all(ExactComplexWaveCurrent::is_zero)
    );
}

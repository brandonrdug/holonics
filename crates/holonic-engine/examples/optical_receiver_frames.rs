//! Exact exterior optics, mode exchange and changing-frame comparisons through shared owners.
use holonic_engine::exact_linear::ExactRatMatrix;
use holonic_engine::exponentiated_ratio::RatioFamily;
use holonic_engine::surprisal::SymbolicSurprisal;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde_json::json;
use std::collections::BTreeMap;
type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
fn q(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}
fn matrix(rows: &[&[i64]], denominator: i64) -> Result<ExactRatMatrix> {
    Ok(ExactRatMatrix::new(
        rows.iter()
            .map(|row| row.iter().map(|x| q(*x, denominator)).collect())
            .collect(),
    )?)
}
fn receiver(density: &ExactRatMatrix, direction: &[Rat]) -> Result<Rat> {
    let returned = density.apply(direction)?;
    let norm: Rat = direction.iter().map(|x| x * x).sum();
    if norm.is_zero() {
        return Err("zero analyzer direction".into());
    }
    Ok(direction
        .iter()
        .zip(returned)
        .map(|(a, b)| a * b)
        .sum::<Rat>()
        / norm)
}
fn congruence(frame: &ExactRatMatrix, density: &ExactRatMatrix) -> Result<ExactRatMatrix> {
    Ok(frame.multiply(density)?.multiply(&frame.transpose()?)?)
}
fn wedge(a: &[Rat], b: &[Rat]) -> Rat {
    &a[0] * &b[1] - &a[1] * &b[0]
}
fn cross_ratio(a: &[Rat], b: &[Rat], c: &[Rat], d: &[Rat]) -> Result<Rat> {
    let denominator = wedge(a, d) * wedge(b, c);
    if denominator.is_zero() {
        return Err("undefined four-ray receiver".into());
    }
    Ok(wedge(a, c) * wedge(b, d) / denominator)
}
fn display(values: &[Rat]) -> Vec<String> {
    values.iter().map(ToString::to_string).collect()
}
fn main() -> Result<()> {
    let h = vec![q(1, 1), q(0, 1)];
    let v = vec![q(0, 1), q(1, 1)];
    let d = vec![q(1, 1), q(1, 1)];
    let a = vec![q(-1, 1), q(1, 1)];
    let mixed = matrix(&[&[1, 0], &[0, 1]], 2)?;
    let coherent = matrix(&[&[1, 1], &[1, 1]], 2)?;
    assert_eq!(receiver(&mixed, &h)?, q(1, 2));
    assert_eq!(receiver(&coherent, &h)?, q(1, 2));
    assert_eq!(receiver(&mixed, &d)?, q(1, 2));
    assert_eq!(receiver(&coherent, &d)?, Rat::one());
    let rotation = matrix(&[&[3, -4], &[4, 3]], 5)?;
    assert_eq!(
        rotation.transpose()?.multiply(&rotation)?,
        ExactRatMatrix::identity(2)?
    );
    assert_eq!(congruence(&rotation, &mixed)?, mixed);
    let coherent_rotated = congruence(&rotation, &coherent)?;
    assert_eq!(
        receiver(&coherent_rotated, &rotation.apply(&d)?)?,
        Rat::one()
    );
    let pure_h = matrix(&[&[1, 0], &[0, 0]], 1)?;
    assert_eq!(receiver(&congruence(&rotation, &pure_h)?, &h)?, q(9, 25));

    // Unit-determinant diattenuation core. Actual passive attenuation additionally has a
    // common amplitude scale; this algebraic core alone is not asserted to be a lossless device.
    let boost = matrix(&[&[4, 0], &[0, 1]], 2)?;
    let boosted = congruence(&boost, &mixed)?;
    let s0 = boosted.get(0, 0)? + boosted.get(1, 1)?;
    let s1 = boosted.get(0, 0)? - boosted.get(1, 1)?;
    assert_eq!(s0, q(17, 8));
    assert_eq!(s1, q(15, 8));
    assert_eq!(&s0 * &s0 - &s1 * &s1, Rat::one());
    let original_cross_ratio = cross_ratio(&h, &v, &d, &a)?;
    let transformed_cross_ratio = cross_ratio(
        &boost.apply(&h)?,
        &boost.apply(&v)?,
        &boost.apply(&d)?,
        &boost.apply(&a)?,
    )?;
    assert_eq!(original_cross_ratio, q(-1, 1));
    assert_eq!(transformed_cross_ratio, original_cross_ratio);

    // The frames at the source and target differ. The physical generator need not be stationary
    // for this relation; this instance supplies one exact nonunitary linear operation.
    let action = matrix(&[&[1, 1], &[0, 1]], 1)?;
    let changed_action = boost.multiply(&action)?.multiply(&rotation.inverse()?)?;
    let source = vec![q(2, 1), q(3, 1)];
    let represented_return = changed_action.apply(&rotation.apply(&source)?)?;
    assert_eq!(represented_return, boost.apply(&action.apply(&source)?)?);
    assert_eq!(represented_return, vec![q(10, 1), q(3, 2)]);

    // Existing finite CAR in the [vacuum, first, second, both] occupation chart.
    let create_first = matrix(
        &[&[0, 0, 0, 0], &[1, 0, 0, 0], &[0, 0, 0, 0], &[0, 0, 1, 0]],
        1,
    )?;
    let create_second = matrix(
        &[&[0, 0, 0, 0], &[0, 0, 0, 0], &[1, 0, 0, 0], &[0, -1, 0, 0]],
        1,
    )?;
    let create_u = create_first
        .scaled(&q(3, 5))
        .add(&create_second.scaled(&q(4, 5)))?;
    let create_w = create_first
        .scaled(&q(-4, 5))
        .add(&create_second.scaled(&q(3, 5)))?;
    assert_eq!(create_u.multiply(&create_u)?, ExactRatMatrix::zero(4, 4)?);
    let vacuum = vec![q(1, 1), q(0, 1), q(0, 1), q(0, 1)];
    let ordered = create_u.multiply(&create_w)?.apply(&vacuum)?;
    let exchanged = create_w.multiply(&create_u)?.apply(&vacuum)?;
    assert_eq!(ordered, vec![q(0, 1), q(0, 1), q(0, 1), q(1, 1)]);
    assert_eq!(exchanged, ordered.iter().map(|x| -x).collect::<Vec<_>>());

    // Hadamard-optics S-matrix, distinct from a unitary scattering matrix.
    let s_matrix = matrix(&[&[0, 1, 1], &[1, 0, 1], &[1, 1, 0]], 1)?;
    let decoder = s_matrix.inverse()?;
    let decoder_noise_mass: Rat = decoder.entries().iter().map(|x| x * x).sum();
    assert_eq!(decoder_noise_mass, q(9, 4));
    // One grand-canonical mode at beta*(mu-energy)=ln 2 has relative occupied weight 2.
    // The exact same public ratio receiver supplies occupation and vacancy.
    let thermal_weights = BTreeMap::from([
        (0, SymbolicSurprisal::zero()),
        (1, SymbolicSurprisal::term(2, q(-1, 1))?),
    ]);
    let thermal = RatioFamily::read(&thermal_weights)?.normalised_against(0)?;
    assert_eq!(thermal[&0], q(1, 3));
    assert_eq!(thermal[&1], q(2, 3));
    let report = json!({"schema":"holonics.optical-receiver-frames.v1",
        "scope":"exact finite rational operator comparisons; no calibrated optical or Fermi-gas apparatus",
        "directional_density":{"horizontal_mixed":"1/2","horizontal_coherent":"1/2","diagonal_mixed":"1/2","diagonal_coherent":"1"},
        "rotation_only_horizontal_transmission":"9/25","state_and_analyzer_covariance":true,
        "stokes_boost":{"trace":s0.to_string(),"contrast":s1.to_string(),"minkowski_square":"1"},
        "four_ray_cross_ratio":{"before":original_cross_ratio.to_string(),"after":transformed_cross_ratio.to_string()},
        "moving_frame_return":display(&represented_return),
        "fermionic_mode":{"coefficients":["3/5","4/5"],"repeated_creation_zero":true,"ordered_pair":display(&ordered),"exchanged_pair":display(&exchanged)},
        "hadamard_decoder":{"inverse":decoder.to_rows().iter().map(|row|display(row)).collect::<Vec<_>>(),"isotropic_unit_noise_mass":decoder_noise_mass.to_string(),"bound_squared":"9/4"},
        "thermal_fermionic_mode":{"logit":"ln 2","occupied":thermal[&1].to_string(),"vacant":thermal[&0].to_string()}});
    let text = serde_json::to_string_pretty(&report)?;
    if let Some(path) = std::env::args().nth(1) {
        std::fs::write(path, format!("{text}\n"))?;
    }
    println!("{text}");
    Ok(())
}

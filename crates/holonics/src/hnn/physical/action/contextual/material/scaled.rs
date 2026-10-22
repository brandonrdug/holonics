//! Same finite proposal on the declared dyadic lattice, with integer temporaries.
//! Original rational moments and the true residual stay in the parent owner.
use super::*;
use std::time::Instant;

fn encode(value: &Rat, scale: &BigInt) -> BigInt {
    #[cfg(test)]
    fit_work::integer(0);
    (value.numer() * scale) / value.denom()
}
/// `v / scale` toward zero. On the dyadic lattice the scale is a power of two, so the quotient is
/// the magnitude shifted with its sign kept: the same integer as the division.
fn unscale(v: BigInt, scale: &BigInt) -> BigInt {
    match scale.trailing_zeros() {
        Some(bits) if scale.is_positive() && scale.magnitude().count_ones() == 1 => {
            let (sign, magnitude) = v.into_parts();
            BigInt::from_biguint(sign, magnitude >> bits)
        }
        _ => v / scale,
    }
}
fn mul_grid(x: &BigInt, y: &BigInt, scale: &BigInt) -> BigInt {
    #[cfg(test)]
    fit_work::integer(1);
    unscale(x * y, scale)
}
fn div_grid(x: &BigInt, y: &BigInt, scale: &BigInt) -> Result<BigInt, HnnError> {
    #[cfg(test)]
    fit_work::integer(2);
    if y.is_zero() {
        return Err(refusal("positive bounded dyadic normal LDL proposal"));
    }
    Ok((x * scale) / y)
}
fn decode(value: BigInt, scale: &BigInt) -> Rat {
    #[cfg(test)]
    fit_work::integer(3);
    Rat::new(value, scale.clone())
}

/// Called only after the parent's unchanged all-real admission (including applied M).
/// BigInt is the declared execution: no narrower intermediate can wrap or saturate.
pub(super) fn propose(
    material: &mut EmpiricalMaterial,
    bounds: &ContextualBounds,
) -> Result<(), HnnError> {
    let m = material.h.len();
    let scale = BigInt::one() << bounds.precision_bits;
    let grid_start = Instant::now();
    let mut a: Vec<Vec<BigInt>> = material
        .h
        .iter()
        .map(|row| row.iter().map(|z| encode(&z[0], &scale)).collect())
        .collect();
    for (i, row) in a.iter_mut().enumerate() {
        // ORIGINAL full realification majorant 2*m/S, represented in lattice units.
        row[i] += BigInt::from(2 * m);
    }
    note_fit_work(|w| w.initial_grid += grid_start.elapsed());
    let factor_start = Instant::now();
    let mut diagonal = vec![BigInt::zero(); m];
    for k in 0..m {
        let correction: BigInt = (0..k)
            .map(|j| mul_grid(&mul_grid(&a[k][j], &a[k][j], &scale), &diagonal[j], &scale))
            .sum();
        diagonal[k] = &a[k][k] - correction;
        if diagonal[k] <= BigInt::zero() {
            return Err(refusal("positive bounded dyadic normal LDL proposal"));
        }
        for i in k + 1..m {
            let correction: BigInt = (0..k)
                .map(|j| mul_grid(&mul_grid(&a[i][j], &a[k][j], &scale), &diagonal[j], &scale))
                .sum();
            // Preserve the original upper entry, nested rounding and loop order.
            a[i][k] = div_grid(&(&a[k][i] - correction), &diagonal[k], &scale)?;
        }
    }
    note_fit_work(|w| w.factor += factor_start.elapsed());
    let solve_start = Instant::now();
    for (row, b) in material.applied.iter_mut().zip(&material.b) {
        let mut rhs: Vec<_> = b.iter().map(|z| encode(&z[0], &scale)).collect();
        for i in 0..m {
            for j in 0..i {
                let term = mul_grid(&a[i][j], &rhs[j], &scale);
                rhs[i] -= term;
            }
        }
        let mut v = rhs
            .iter()
            .zip(&diagonal)
            .map(|(x, y)| div_grid(x, y, &scale))
            .collect::<Result<Vec<_>, _>>()?;
        for i in (0..m).rev() {
            for j in i + 1..m {
                let term = mul_grid(&a[j][i], &v[j], &scale);
                v[i] -= term;
            }
        }
        for (z, value) in row.iter_mut().zip(v) {
            *z = [decode(value, &scale), Rat::zero()];
        }
    }
    note_fit_work(|w| w.solve += solve_start.elapsed());
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn scaled_integer_signed_grid_operations_preserve_toward_zero_and_unbounded_width() {
        let scale = BigInt::from(8);
        let grid = |r: Rat| {
            let q = r * Rat::from_integer(scale.clone());
            Rat::new(q.numer() / q.denom(), scale.clone())
        };
        for x in [-65, -16, -9, -8, -7, -1, 0, 1, 7, 8, 9, 16, 65] {
            for y in [-17, -8, -3, -1, 1, 3, 8, 17] {
                let a = BigInt::from(x);
                let b = BigInt::from(y);
                assert_eq!(
                    decode(mul_grid(&a, &b, &scale), &scale),
                    grid(Rat::new(a.clone(), scale.clone()) * Rat::new(b.clone(), scale.clone()))
                );
                assert_eq!(
                    decode(div_grid(&a, &b, &scale).unwrap(), &scale),
                    grid(Rat::new(a.clone(), scale.clone()) / Rat::new(b.clone(), scale.clone()))
                );
            }
        }
        assert_eq!(
            encode(&Rat::new((-1).into(), 17.into()), &scale),
            BigInt::zero()
        );
        let large = BigInt::one() << 512usize;
        assert_eq!(mul_grid(&large, &large, &scale), (&large * &large) / &scale);
        assert!(div_grid(&large, &BigInt::zero(), &scale).is_err());
    }
}

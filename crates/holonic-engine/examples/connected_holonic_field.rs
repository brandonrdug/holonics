//! Connected exact reference: learned normalized transport, two heads/two layers,
//! phase-sensitive friction, joint refinement and an implicit generated field.
//! This mounts supplied operands and calls public algebra/learning owners. It is
//! exterior reference execution, not a second native HNN implementation.
use holonics::exact_linear::ExactRatMatrix as Matrix;
use holonic_engine::exponentiated_ratio::NormalizedKernel;
use num_traits::{One, ToPrimitive, Zero};
use holonics::geometry::Rat;
use serde_json::{Value, json};
use std::{error::Error, fs, time::Instant};

fn rational(s: &str) -> Rat {
    s.parse().expect("input rational")
}
fn matrix(v: &Value) -> Matrix {
    Matrix::new(
        v.as_array()
            .unwrap()
            .iter()
            .map(|row| {
                row.as_array()
                    .unwrap()
                    .iter()
                    .map(|x| rational(x.as_str().unwrap()))
                    .collect()
            })
            .collect(),
    )
    .unwrap()
}
fn wire(m: &Matrix) -> Value {
    json!(
        m.to_rows()
            .iter()
            .map(|r| r.iter().map(ToString::to_string).collect::<Vec<_>>())
            .collect::<Vec<_>>()
    )
}
fn norm2(m: &Matrix) -> Rat {
    m.entries().iter().map(|x| x * x).sum()
}
fn flat(m: &Matrix) -> Matrix {
    Matrix::new(m.entries().iter().map(|x| vec![x.clone()]).collect()).unwrap()
}
fn complex_lift(a: &Matrix) -> Matrix {
    Matrix::new(
        (0..2 * a.rows())
            .map(|i| {
                (0..2 * a.columns())
                    .map(|j| {
                        if i % 2 == j % 2 {
                            a.get(i / 2, j / 2).unwrap().clone()
                        } else {
                            Rat::zero()
                        }
                    })
                    .collect()
            })
            .collect(),
    )
    .unwrap()
}
fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 3 {
        return Err("usage: connected_holonic_field input.json output.json".into());
    }
    let input: Value = serde_json::from_str(&fs::read_to_string(&args[1])?)?;
    let timer = Instant::now();
    let v = matrix(&input["input"]);
    let target = matrix(&input["observed"]);
    let n = v.rows();
    let a = NormalizedKernel::new(matrix(&input["head_a"]))?;
    let b = NormalizedKernel::new(matrix(&input["head_b"]))?;
    let rate = rational(input["material_rate"].as_str().unwrap());
    let learned = a.fit_step(&v, &target, &rate)?;
    let before = a.squared_discrepancy(&v, &target)?;
    let after = learned.squared_discrepancy(&v, &target)?;
    assert!(after < before);
    let error = a.apply(&v)?.subtract(&target)?;
    let (gradient, pulled_values) = a.pullback(&v, &error)?;
    let gate = NormalizedKernel::binary(&[rational(input["gate_odds"].as_str().unwrap())])?
        .apply(&Matrix::new(vec![vec![Rat::one()], vec![Rat::zero()]])?)?
        .get(0, 0)?
        .clone();
    let eye = Matrix::identity(2 * n)?;
    let i = input["contact_edge"][0].as_u64().unwrap() as usize;
    let j = input["contact_edge"][1].as_u64().unwrap() as usize;
    let re = rational(input["contact_phase"][0].as_str().unwrap());
    let im = rational(input["contact_phase"][1].as_str().unwrap());
    assert_eq!(&re * &re + &im * &im, Rat::one());
    let alpha = rational("1/4");
    let mut contact = eye.to_rows(); // supplied immutable matrix chart
    for c in 0..2 {
        contact[2 * i + c][2 * i + c] = Rat::one() - &alpha;
        contact[2 * j + c][2 * j + c] = Rat::one() - &alpha;
    }
    // xi'=(1-alpha)xi+alpha conjugate(u)xj; xj'=(1-alpha)xj+alpha u xi.
    for (row, col, val) in [
        (0, 0, re.clone()),
        (0, 1, im.clone()),
        (1, 0, -&im),
        (1, 1, re.clone()),
    ] {
        contact[2 * i + row][2 * j + col] = &alpha * &val;
    }
    for (row, col, val) in [
        (0, 0, re.clone()),
        (0, 1, -&im),
        (1, 0, im.clone()),
        (1, 1, re.clone()),
    ] {
        contact[2 * j + row][2 * i + col] = &alpha * &val;
    }
    let contact = Matrix::new(contact)?;
    let make_layer = |head: &NormalizedKernel| -> Result<Matrix, Box<dyn Error>> {
        let mean = head
            .probabilities()?
            .add(&b.probabilities()?)?
            .scaled(&rational("1/2"));
        Ok(contact.multiply(
            &eye.scaled(&(Rat::one() - &gate))
                .add(&complex_lift(&mean).scaled(&gate))?,
        )?)
    };
    let layer = make_layer(&learned)?;
    let operator = layer.multiply(&layer)?;
    let lambda = rational(input["iteration_factor"].as_str().unwrap());
    let h = flat(&v);
    let force = h.scaled(&(Rat::one() - &lambda));
    let lhs = eye.subtract(&operator.scaled(&lambda))?;
    eprintln!("normalized transport and two layers assembled; solving 30-axis field");
    let solve_timer = Instant::now();
    let inverse = lhs.inverse()?;
    let solution = inverse.multiply(&force)?;
    let solve_ms = solve_timer.elapsed().as_millis();
    assert!(
        lhs.multiply(&solution)?
            .subtract(&force)?
            .entries()
            .iter()
            .all(Zero::is_zero)
    );
    let mut x = h.clone(); // immutable supplied initial section
    let mut snapshots = Vec::new();
    for k in 0..=8 {
        let residual = lhs.multiply(&x)?.subtract(&force)?;
        snapshots.push(
            json!({"step":k,"state":wire(&x),"residual_squared":norm2(&residual).to_string(),
            "error_squared":norm2(&x.subtract(&solution)?).to_string()}),
        );
        if k < 8 {
            x = operator.multiply(&x)?.scaled(&lambda).add(&force)?;
        }
    }
    let old_layer = make_layer(&a)?;
    let old_solution = eye
        .subtract(&old_layer.multiply(&old_layer)?.scaled(&lambda))?
        .inverse()?
        .multiply(&force)?;
    let material_effect = solution.subtract(&old_solution)?;
    // Exact sensitivity through shared heads, both layers and implicit integration.
    let mut ds = vec![vec![Rat::zero(); n]; n];
    ds[i][j] = Rat::one();
    let ds = Matrix::new(ds)?;
    let da = learned.differential(&Matrix::identity(n)?, &ds, &Matrix::zero(n, n)?)?;
    let dl = contact.multiply(&complex_lift(&da).scaled(&(&gate * rational("1/2"))))?;
    let db = dl.multiply(&layer)?.add(&layer.multiply(&dl)?)?;
    let sensitivity = inverse.multiply(&db.multiply(&solution)?.scaled(&lambda))?;
    assert_eq!(
        lhs.multiply(&sensitivity)?,
        db.multiply(&solution)?.scaled(&lambda)
    );
    let contact_input = flat(&learned.apply(&v)?);
    let contact_output = contact.multiply(&contact_input)?;
    let xi = (
        contact_input.get(2 * i, 0)?,
        contact_input.get(2 * i + 1, 0)?,
    );
    let xj = (
        contact_input.get(2 * j, 0)?,
        contact_input.get(2 * j + 1, 0)?,
    );
    let dr = xj.0 - (&re * xi.0 - &im * xi.1);
    let di = xj.1 - (&im * xi.0 + &re * xi.1);
    let heat = rational("2") * &alpha * (Rat::one() - &alpha) * (&dr * &dr + &di * &di);
    assert_eq!(norm2(&contact_input) - norm2(&contact_output), heat);
    let elapsed_ms = timer.elapsed().as_millis();
    let report = json!({"scope":input["scope"],"input":input,"head_a_before":wire(&a.probabilities()?),
        "head_a_after":wire(&learned.probabilities()?),"head_b":wire(&b.probabilities()?),
        "log_potential_gradient":wire(&gradient),"value_pullback":wire(&pulled_values),
        "loss_before":before.to_string(),"loss_after":after.to_string(),"loss_drop":(&before-&after).to_string(),
        "sigmoid_gate":gate.to_string(),"layer":wire(&layer),"operator":wire(&operator),
        "layer_one_field":wire(&layer.multiply(&h)?),"layer_two_field":wire(&operator.multiply(&h)?),
        "solution":wire(&solution),"solution_before_learning":wire(&old_solution),"material_effect":wire(&material_effect),
        "sensitivity":wire(&sensitivity),"snapshots":snapshots,
        "contact_input":wire(&contact_input),"contact_output":wire(&contact_output),"contact_heat":heat.to_string(),
        "exact_residual_zero":true,"implicit_derivative_residual_zero":true,"energy_balance_exact":true,
        "elapsed_ms":elapsed_ms,"solve_ms":solve_ms,
        "maximum_solution_numerator_bits":solution.entries().iter().map(|q|q.numer().bits()).max(),
        "maximum_solution_denominator_bits":solution.entries().iter().map(|q|q.denom().bits()).max()});
    fs::write(&args[2], serde_json::to_string_pretty(&report)? + "\n")?;
    println!(
        "15 complex channels; 2 heads; 2 layers; loss {:.9} -> {:.9}; exact implicit residual=0; {:.0} ms",
        before.to_f64().unwrap(),
        after.to_f64().unwrap(),
        elapsed_ms as f64
    );
    Ok(())
}

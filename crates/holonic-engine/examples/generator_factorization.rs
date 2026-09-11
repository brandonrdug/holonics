//! Exterior exact algorithm synthesis through the standing rational preimage owner.
//! No native ecology, foreign model, floating arithmetic or replacement elimination engine.
use holonic_engine::exact_linear::ExactRatMatrix;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde_json::{Value, json};

fn q(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}
fn strings(xs: &[Rat]) -> Vec<String> {
    xs.iter().map(ToString::to_string).collect()
}
fn selections(
    n: usize,
    r: usize,
    start: usize,
    prefix: &mut Vec<usize>,
    out: &mut Vec<Vec<usize>>,
) {
    if prefix.len() == r {
        out.push(prefix.clone());
        return;
    }
    for i in start..n {
        prefix.push(i);
        selections(n, r, i + 1, prefix, out);
        prefix.pop();
    }
}
fn additions(form: &[Rat]) -> usize {
    form.iter()
        .filter(|x| !x.is_zero())
        .count()
        .saturating_sub(1)
}

fn multiplication_search() -> Result<Value, Box<dyn std::error::Error>> {
    // Declared finite coefficient vocabulary, modulo a sign absorbed by the output coefficient.
    let forms: Vec<Vec<Rat>> = [[1, 0], [0, 1], [1, 1], [1, -1]]
        .into_iter()
        .map(|v| v.into_iter().map(|x| q(x, 1)).collect())
        .collect();
    let atoms: Vec<(usize, usize, Vec<Rat>)> = (0..forms.len())
        .flat_map(|i| (0..forms.len()).map(move |j| (i, j)))
        .map(|(i, j)| {
            (
                i,
                j,
                forms[i]
                    .iter()
                    .flat_map(|a| forms[j].iter().map(move |b| a * b))
                    .collect(),
            )
        })
        .collect();
    // Coefficients of ac,ad,bc,bd in the two coordinates of complex multiplication.
    let targets = [
        vec![q(1, 1), q(0, 1), q(0, 1), q(-1, 1)],
        vec![q(0, 1), q(1, 1), q(1, 1), q(0, 1)],
    ];
    let mut reports = Vec::new();
    let mut certificates = Vec::new();
    for rank in 1..=3 {
        let mut choices = Vec::new();
        selections(atoms.len(), rank, 0, &mut Vec::new(), &mut choices);
        let mut found = 0;
        let mut first_obstruction = None;
        for selected in &choices {
            let matrix = ExactRatMatrix::new(
                (0..4)
                    .map(|row| selected.iter().map(|i| atoms[*i].2[row].clone()).collect())
                    .collect(),
            )?;
            let mut output = Vec::new();
            let mut fibres = Vec::new();
            for (coordinate, target) in targets.iter().enumerate() {
                if let Some((particular, kernel)) = matrix.preimage_fibre(target)? {
                    assert_eq!(matrix.apply(&particular)?, *target);
                    output.push(particular);
                    fibres.push(kernel);
                } else {
                    if first_obstruction.is_none() {
                        let separator = matrix
                            .preimage_obstruction(target)?
                            .expect("outside image has separator");
                        assert!(
                            matrix
                                .transpose()?
                                .apply(&separator)?
                                .iter()
                                .all(Zero::is_zero)
                        );
                        let paired: Rat = separator.iter().zip(target).map(|(a, b)| a * b).sum();
                        assert!(!paired.is_zero());
                        first_obstruction = Some(json!({"atoms":selected,"output":coordinate,
                            "annihilator":strings(&separator),"target_pairing":paired.to_string()}));
                    }
                    break;
                }
            }
            if output.len() != 2 {
                continue;
            }
            let residuals = output
                .iter()
                .zip(&targets)
                .map(|(weights, target)| {
                    let returned = matrix.apply(weights).expect("checked factor shape");
                    returned
                        .iter()
                        .zip(target)
                        .map(|(a, b)| a - b)
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            assert!(residuals.iter().flatten().all(Zero::is_zero));
            found += 1;
            let linear_additions: usize = selected
                .iter()
                .map(|i| additions(&forms[atoms[*i].0]) + additions(&forms[atoms[*i].1]))
                .sum::<usize>()
                + output.iter().map(|row| additions(row)).sum::<usize>();
            let nonunit_scales = output
                .iter()
                .flatten()
                .filter(|x| !x.is_zero() && **x != Rat::one() && **x != -Rat::one())
                .count();
            certificates.push(json!({"products":rank,"linear_additions":linear_additions,
                "nonunit_output_scales":nonunit_scales,
                "atoms":selected.iter().map(|i| json!({"left":strings(&forms[atoms[*i].0]),
                    "right":strings(&forms[atoms[*i].1])})).collect::<Vec<_>>(),
                "output_coefficients":output.iter().map(|row| strings(row)).collect::<Vec<_>>(),
                "output_coefficient_fibres":fibres.iter().map(|basis|
                    basis.iter().map(|row| strings(row)).collect::<Vec<_>>()).collect::<Vec<_>>(),
                "tensor_residual":residuals.iter().map(|r|strings(r)).collect::<Vec<_>>()}));
        }
        reports.push(json!({"products":rank,"candidate_supports":choices.len(),
            "valid_supports":found,"first_rejected_support":first_obstruction}));
    }
    assert!(!certificates.is_empty());
    certificates.sort_by_key(|c| {
        (
            c["products"].as_u64(),
            c["nonunit_output_scales"].as_u64(),
            c["linear_additions"].as_u64(),
        )
    });
    Ok(
        json!({"field":"Q; identities extend to commutative Q-algebras",
        "target":targets.iter().map(|x| strings(x)).collect::<Vec<_>>(),
        "declared_forms":forms.iter().map(|x|strings(x)).collect::<Vec<_>>(),
        "search":reports,"selected":certificates[0],"certificates":certificates,
        "selection_chart":"fewest products, then nonunit scales, then additions; no runtime claim"}),
    )
}

fn compile(rs: &[Rat]) -> (Rat, Rat) {
    let (mut alpha, mut beta) = (Rat::one(), Rat::zero());
    for r in rs {
        alpha *= r;
        beta += &alpha;
    }
    (alpha, beta)
}
fn act(block: &(Rat, Rat), state: &(Rat, Rat)) -> (Rat, Rat) {
    (&block.0 * &state.0, &state.1 + &block.1 * &state.0)
}
fn route_synthesis(
    name: &str,
    ratios: Vec<Rat>,
    initial: (Rat, Rat),
    next: Rat,
) -> Result<Value, Box<dyn std::error::Error>> {
    let block = compile(&ratios);
    // With first ratio t fixed, solve v+w=beta-t, w=alpha, where v=t*q,w=t*q*r.
    let relation = ExactRatMatrix::new(vec![vec![q(1, 1), q(1, 1)], vec![q(0, 1), q(1, 1)]])?;
    let mut candidates = Vec::new();
    for t in &ratios {
        let target = vec![&block.1 - t, block.0.clone()];
        let (vw, kernel) = relation.preimage_fibre(&target)?.expect("triangular solve");
        assert!(kernel.is_empty());
        assert_eq!(relation.apply(&vw)?, target);
        if t.is_zero() || vw[0].is_zero() {
            continue;
        }
        let route = vec![t.clone(), &vw[0] / t, &vw[1] / &vw[0]];
        assert_eq!(compile(&route), block);
        let mut state = initial.clone();
        let mut snapshots = Vec::new();
        for r in &route {
            state = act(&(r.clone(), r.clone()), &state);
            snapshots.push(strings(&[state.0.clone(), state.1.clone()]));
        }
        let future = act(&(next.clone(), next.clone()), &state);
        assert_eq!(
            future,
            act(&(next.clone(), next.clone()), &act(&block, &initial))
        );
        candidates.push(json!({"route":strings(&route),"snapshots":snapshots,
            "endpoint":strings(&[state.0,state.1]),"next_ratio":next.to_string(),
            "next_state":strings(&[future.0,future.1]),"clock_advance":route.len()}));
    }
    Ok(
        json!({"source":name,"source_ratios":strings(&ratios),"alpha":block.0.to_string(),
        "beta":block.1.to_string(),"clock_advance":ratios.len(),"candidates":candidates,
        "search_aperture":"first ratio drawn from this source block's own ratios"}),
    )
}

fn gamma_jet() -> Result<Value, Box<dyn std::error::Error>> {
    let z = q(1, 2);
    let mut matrix = ExactRatMatrix::identity(2)?;
    let (mut value, mut derivative) = (Rat::one(), Rat::zero());
    for k in 0..3 {
        let factor = &z + q(k, 1);
        derivative = &value + &factor * &derivative;
        value *= &factor;
        let step = ExactRatMatrix::new(vec![
            vec![factor.clone(), Rat::zero()],
            vec![Rat::one(), factor],
        ])?;
        matrix = step.multiply(&matrix)?;
    }
    let expected = ExactRatMatrix::new(vec![
        vec![value.clone(), Rat::zero()],
        vec![derivative.clone(), value.clone()],
    ])?;
    assert_eq!(matrix, expected);
    Ok(
        json!({"source":"Gamma value/derivative shift block", "z":z.to_string(),"clock_advance":3,
        "rising_factorial":value.to_string(),"derivative":derivative.to_string(),
        "transfer":matrix.to_rows().iter().map(|r|strings(r)).collect::<Vec<_>>(),
        "scope":"finite transfer; Gamma normalization, poles and base germ remain required"}),
    )
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let bilinear = multiplication_search()?;
    let result = json!({"schema":"holonics.exterior-generator-factorization.v1",
        "owner":"holonic_engine::exact_linear::ExactRatMatrix::preimage_fibre",
        "bilinear":bilinear,
        "series":[route_synthesis("arctan(1/5), Machin arm",
            vec![q(-1,75),q(-3,125),q(-1,35)],(q(1,5),q(1,5)),q(-7,225))?,
            route_synthesis("e factorial series",vec![q(1,1),q(1,2),q(1,3)],
                (q(1,1),q(1,1)),q(1,4))?],
        "gamma":gamma_jet()?,
        "scope":"bounded exact exterior synthesis and compilation; no HNN formation or GPU timing"});
    let printed = serde_json::to_string_pretty(&result)?;
    if let Some(path) = std::env::args().nth(1) {
        std::fs::write(path, format!("{printed}\n"))?;
    }
    println!("{printed}");
    Ok(())
}

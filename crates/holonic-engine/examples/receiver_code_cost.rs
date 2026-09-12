//! Exact exterior unequal-cost channel: code information, clock cost and endpoint potential.
use holonic_engine::exponentiated_ratio::RatioFamily;
use holonic_engine::surprisal::SymbolicSurprisal;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde_json::{Value, json};
use std::collections::BTreeMap;
type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;
fn q(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}
#[derive(Clone)]
struct Edge {
    name: &'static str,
    source: usize,
    target: usize,
    cost: u32,
    probability: Rat,
}
fn surprise(p: &Rat) -> Result<Rat> {
    let form = SymbolicSurprisal::of_probability(p)?;
    let b = form.enclosure_at(1, 8)?;
    if b.lower != b.upper {
        return Err("this dyadic control requires exact rational surprise".into());
    }
    Ok(b.lower)
}
fn enumerate(
    edges: &[Edge],
    start: usize,
    remaining: usize,
    path: &mut Vec<usize>,
    out: &mut Vec<Vec<usize>>,
) {
    if remaining == 0 {
        out.push(path.clone());
        return;
    }
    for (i, e) in edges.iter().enumerate().filter(|(_, e)| e.source == start) {
        path.push(i);
        enumerate(edges, e.target, remaining - 1, path, out);
        path.pop();
    }
}

// A declared finite statistical chart of the same description/cost receiver. All logarithmic
// arithmetic and normalization use the existing public owners; this is exterior theorem
// apparatus, not a second native training implementation.
fn generator_inference_control() -> Result<Value> {
    let success = [q(1, 4), q(3, 4)];
    // Actual prefix descriptions 0 and 10, conditional on this shared two-generator decoder.
    let description_words = ["0", "10"];
    let code_weights = [q(1, 2), q(1, 4)];
    let objective_at =
        |failures: i64, successes: i64| -> Result<BTreeMap<u64, SymbolicSurprisal>> {
            let mut objective = BTreeMap::new();
            for (i, probability) in success.iter().enumerate() {
                let description = SymbolicSurprisal::of_probability(&code_weights[i])?;
                let failure_loss = SymbolicSurprisal::of_probability(&(Rat::one() - probability))?;
                let success_loss = SymbolicSurprisal::of_probability(probability)?;
                objective.insert(
                    i as u64,
                    description
                        .plus(&failure_loss.scaled(&q(failures, 1)))
                        .plus(&success_loss.scaled(&q(successes, 1))),
                );
            }
            Ok(objective)
        };
    let counts = (2, 1);
    let objective = objective_at(counts.0, counts.1)?;
    let ratios = RatioFamily::read(&objective)?;
    let posterior = ratios.normalised_against(0)?;
    assert!(ratios.cocycle_holds());
    assert!(ratios.null_orbit_is_trivial()?);
    assert_eq!(posterior[&0], q(6, 7));
    assert_eq!(posterior[&1], q(1, 7));
    let histories = [[false, false, true], [false, true, false]];
    for history in histories {
        // Independent multiplicative likelihood calculation checks the symbolic-log/count chart.
        let unnormalised: Vec<_> = success
            .iter()
            .enumerate()
            .map(|(i, probability)| {
                history
                    .iter()
                    .fold(code_weights[i].clone(), |weight, event| {
                        weight
                            * if *event {
                                probability.clone()
                            } else {
                                Rat::one() - probability
                            }
                    })
            })
            .collect();
        let partition: Rat = unnormalised.iter().cloned().sum();
        for (i, weight) in unnormalised.iter().enumerate() {
            assert_eq!(&posterior[&(i as u64)], &(weight / &partition));
        }
    }
    // A common five-bit framing charge changes the total description, but no candidate odds.
    let header = SymbolicSurprisal::term(2, q(5, 1))?;
    let shifted = objective
        .iter()
        .map(|(id, value)| (*id, value.plus(&header)))
        .collect();
    assert_eq!(
        RatioFamily::read(&shifted)?.normalised_against(0)?,
        posterior
    );
    // Refine code 0 into 00 and 01, retaining its total Kraft mass. Both refined descriptions
    // decode to the first generator. Coarse graining sums their weights, rather than selecting
    // a representative or treating a duplicated description as new evidence.
    let one_bit = SymbolicSurprisal::term(2, Rat::one())?;
    let refined = BTreeMap::from([
        (0, objective[&0].plus(&one_bit)),
        (1, objective[&0].plus(&one_bit)),
        (2, objective[&1].clone()),
    ]);
    let fine_posterior = RatioFamily::read(&refined)?.normalised_against(0)?;
    assert_eq!(&fine_posterior[&0] + &fine_posterior[&1], posterior[&0]);
    assert_eq!(fine_posterior[&2], posterior[&1]);
    // Extend from the two counts alone. No prior symbol order is needed by this source law.
    let continued =
        RatioFamily::read(&objective_at(counts.0, counts.1 + 1)?)?.normalised_against(0)?;
    assert_eq!(continued[&0], q(2, 3));
    assert_eq!(continued[&1], q(1, 3));

    let trial = BTreeMap::from([(0, q(1, 2)), (1, q(1, 2))]);
    let functional = |weights: &BTreeMap<u64, Rat>| -> Result<SymbolicSurprisal> {
        let mut value = SymbolicSurprisal::zero();
        for (id, weight) in weights {
            value = value.plus(
                &objective[id]
                    .minus(&SymbolicSurprisal::of_probability(weight)?)
                    .scaled(weight),
            );
        }
        Ok(value)
    };
    let mut kl = SymbolicSurprisal::zero();
    for (id, weight) in &trial {
        kl = kl.plus(
            &SymbolicSurprisal::of_probability(&posterior[id])?
                .minus(&SymbolicSurprisal::of_probability(weight)?)
                .scaled(weight),
        );
    }
    let gap = functional(&trial)?.minus(&functional(&posterior)?);
    assert_eq!(gap, kl);
    assert_eq!(
        functional(&posterior)?,
        SymbolicSurprisal::of_probability(&q(21, 256))?
    );
    Ok(
        json!({"scope":"finite Bernoulli generator family with declared prefix descriptions and independent-observation likelihood",
        "success_probabilities":success.map(|p|p.to_string()), "conditional_description_words":description_words,
        "sufficient_counts":{"false":counts.0,"true":counts.1},"equal_count_histories":histories,
        "description_plus_data_bits":objective,"posterior":posterior.iter().map(|(id,p)|(id.to_string(),p.to_string())).collect::<BTreeMap<_,_>>(),
            "common_header_bits":5,"common_header_preserves_posterior":true,
            "refined_description_words":["00","01","10"],
            "refined_posterior":fine_posterior.iter().map(|(id,p)|(id.to_string(),p.to_string())).collect::<BTreeMap<_,_>>(),
            "pushed_forward_posterior_preserved":true,
        "next_true_from_counts":continued.iter().map(|(id,p)|(id.to_string(),p.to_string())).collect::<BTreeMap<_,_>>(),
        "variational_gap_bits":gap,"kl_bits":kl,"negative_log_partition_bits":functional(&posterior)?}),
    )
}
fn main() -> Result<()> {
    // A declared finite admissible channel, with parallel B->B passages retained separately.
    let grammar = [
        ("a-loop", 0, 0, 1),
        ("a-to-b", 0, 1, 2),
        ("b-to-a", 1, 0, 1),
        ("b-short-loop", 1, 1, 1),
        ("b-long-loop", 1, 1, 2),
    ];
    let h = [q(1, 1), q(2, 1)];
    let potential = [q(0, 1), q(1, 1)];
    let edges: Vec<_> = grammar
        .into_iter()
        .map(|(name, source, target, cost)| Edge {
            name,
            source,
            target,
            cost,
            probability: q(1, 1i64 << cost) * &h[target] / &h[source],
        })
        .collect();
    let mut edge_rows = Vec::new();
    let mut transfer = [[Rat::zero(), Rat::zero()], [Rat::zero(), Rat::zero()]];
    for e in &edges {
        transfer[e.source][e.target] += q(1, 1i64 << e.cost);
        let ell = surprise(&e.probability)?;
        let boundary = &potential[e.source] - &potential[e.target];
        assert_eq!(ell, q(i64::from(e.cost), 1) + &boundary);
        edge_rows.push(json!({"name":e.name,"source":e.source,"target":e.target,"cost_units":e.cost,
   "probability":e.probability.to_string(),"surprise_bits":ell.to_string(),"boundary_bits":boundary.to_string()}));
    }
    for state in 0..2 {
        assert_eq!(
            &transfer[state][0] * &h[0] + &transfer[state][1] * &h[1],
            h[state]
        );
        assert_eq!(
            edges
                .iter()
                .filter(|e| e.source == state)
                .map(|e| e.probability.clone())
                .sum::<Rat>(),
            Rat::one()
        );
    }
    let trace = &transfer[0][0] + &transfer[1][1];
    let determinant = &transfer[0][0] * &transfer[1][1] - &transfer[0][1] * &transfer[1][0];
    for root in [q(1, 1), q(1, 4)] {
        assert_eq!(&root * &root - &trace * &root + &determinant, Rat::zero());
    }
    let p_ab = edges[1].probability.clone();
    let p_ba = edges[2].probability.clone();
    let stationary = [&p_ba / (&p_ab + &p_ba), &p_ab / (&p_ab + &p_ba)];
    let mut entropy = Rat::zero();
    let mut cost = Rat::zero();
    for e in &edges {
        let mass = &stationary[e.source] * &e.probability;
        entropy += &mass * surprise(&e.probability)?;
        cost += mass * q(i64::from(e.cost), 1);
    }
    for target in 0..2 {
        assert_eq!(
            edges
                .iter()
                .filter(|e| e.target == target)
                .map(|e| &stationary[e.source] * &e.probability)
                .sum::<Rat>(),
            stationary[target]
        );
    }
    assert_eq!(entropy, cost);
    let mut histories = Vec::new();
    let mut checked = 0;
    for start in 0..2 {
        for depth in 0..=4 {
            let mut paths = Vec::new();
            enumerate(&edges, start, depth, &mut Vec::new(), &mut paths);
            let mut total = Rat::zero();
            let mut expected_information = Rat::zero();
            let mut expected_cost = Rat::zero();
            let mut expected_boundary = Rat::zero();
            let mut rows = Vec::new();
            for path in &paths {
                let mut probability = Rat::one();
                let mut passage_cost = Rat::zero();
                let mut information = Rat::zero();
                let mut current = start;
                for &i in path {
                    let e = &edges[i];
                    assert_eq!(e.source, current);
                    current = e.target;
                    probability *= &e.probability;
                    passage_cost += q(i64::from(e.cost), 1);
                    information += surprise(&e.probability)?;
                }
                let boundary = &potential[start] - &potential[current];
                assert_eq!(information, surprise(&probability)?);
                assert_eq!(information, &passage_cost + &boundary);
                // Same passage in a rescaled clock chart: capacity rescales inversely.
                assert_eq!(q(2, 3) * (&passage_cost * q(3, 2)) + &boundary, information);
                total += &probability;
                expected_information += &probability * &information;
                expected_cost += &probability * &passage_cost;
                expected_boundary += &probability * &boundary;
                rows.push(json!({"word":path.iter().map(|&i|edges[i].name).collect::<Vec<_>>(),
    "target":current,"probability":probability.to_string(),"information_bits":information.to_string(),
    "cost_units":passage_cost.to_string(),"endpoint_potential_bits":boundary.to_string()}));
                checked += 1;
            }
            assert_eq!(total, Rat::one());
            assert_eq!(expected_information, &expected_cost + &expected_boundary);
            histories.push(json!({"source":start,"depth":depth,"paths":rows,
   "expected_bits":expected_information.to_string(),"expected_cost":expected_cost.to_string(),
   "expected_boundary_bits":expected_boundary.to_string()}));
        }
    }
    let result: Value = json!({"schema":"holonics.hephaestus.receiver-code-cost.v1",
  "scope":"finite exterior channel and generator-inference charts; declared dimensionless cost and probability receivers",
      "capacity_bits_per_cost_unit":"1","state_potential_bits":["0","1"],"edges":edge_rows,
      "transfer_matrix":transfer.map(|row|row.map(|x|x.to_string())),
      "transfer_eigenvalues":["1","1/4"],"positive_eigenvector":["1","2"],
  "stationary_mass":stationary.map(|x|x.to_string()),"stationary_entropy_bits_per_step":entropy.to_string(),
  "stationary_cost_per_step":cost.to_string(),"transported_chart":{"cost_scale":"3/2","capacity":"2/3"},
  "checked_histories":checked,"histories":histories,"generator_inference":generator_inference_control()?,"native_model_changed":false});
    let text = serde_json::to_string_pretty(&result)?;
    if let Some(path) = std::env::args().nth(1) {
        std::fs::write(path, format!("{text}\n"))?;
    }
    println!("{text}");
    Ok(())
}

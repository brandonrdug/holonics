//! Exact exterior unequal-cost channel: code information, clock cost and endpoint potential.
use holonic_engine::surprisal::SymbolicSurprisal;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde_json::{Value, json};
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
  "scope":"finite exterior channel; dimensionless declared cost ruler; no physical constant or HNN learner",
      "capacity_bits_per_cost_unit":"1","state_potential_bits":["0","1"],"edges":edge_rows,
      "transfer_matrix":transfer.map(|row|row.map(|x|x.to_string())),
      "transfer_eigenvalues":["1","1/4"],"positive_eigenvector":["1","2"],
  "stationary_mass":stationary.map(|x|x.to_string()),"stationary_entropy_bits_per_step":entropy.to_string(),
  "stationary_cost_per_step":cost.to_string(),"transported_chart":{"cost_scale":"3/2","capacity":"2/3"},
  "checked_histories":checked,"histories":histories,"native_model_changed":false});
    let text = serde_json::to_string_pretty(&result)?;
    if let Some(path) = std::env::args().nth(1) {
        std::fs::write(path, format!("{text}\n"))?;
    }
    println!("{text}");
    Ok(())
}

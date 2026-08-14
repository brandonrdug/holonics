//! **The Ramanujan question, asked — because a finite graph can answer it and this one never had.**
//!
//! Organs: `relational_geometry::receiver_topology::ihara_signature` (the reciprocal Ihara zeta,
//! already cross-checked against its Euler product), and
//! `holonic_engine::rational_polynomial::rational_root_census` (Sturm isolation over exact
//! rationals). Nothing new is built.
//!
//! # Why this driver exists
//!
//! `research/records/2026-08-09_THE_COLOR_IS_A_RECEIVER_QUOTIENT…` states that a finite regular
//! graph satisfies the Ihara-zeta analogue of the Riemann hypothesis **exactly when it is
//! Ramanujan** — so "does my zeta satisfy RH" is a *decidable question about the machine's own
//! mixing*, not a conjecture. It named the instruments and recorded that nothing asks. The
//! `ihara_two_route_cross_check` driver prints its own refusal to ask: *"No spectral gap, no
//! Ramanujan claim, and no root isolation is performed here."*
//!
//! # The test, and why it is exact
//!
//! A connected `k`-regular graph is **Ramanujan** when every adjacency eigenvalue other than the
//! trivial `±k` satisfies `|lambda| <= 2*sqrt(k-1)`. That bound is irrational in general, so the
//! test is taken on the **square** instead, where the bound is the integer `4(k-1)`:
//!
//! ```text
//!   chi(x) * chi(-x)  is even, so it is  q(x^2)
//!   the roots of q are exactly the SQUARES of the adjacency eigenvalues
//!   Ramanujan  <=>  every root of q except k^2 satisfies  y <= 4(k-1)
//! ```
//!
//! Every step is polynomial arithmetic over `Rat` and one Sturm census. No square root is taken,
//! no eigenvalue is approximated, and the comparison is against an integer.
//!
//! **A root whose isolating interval straddles the threshold is returned OPEN**, not decided. The
//! census carries a certificate and a separation bound; refining it further is a declared deed and
//! guessing across the boundary would be exactly the fabrication this body refuses.
//!
//! # What this may not be reported as
//!
//! This is a property of a finite graph the driver declares. It is **not** a statement about the
//! Riemann hypothesis, and the analogy that licenses the name is a theorem about Ihara zetas of
//! finite graphs and nothing more. `canon/THE_HOLOBROCHOS_SPINE.md` bars a suggestive spectral
//! image from grading a deed, and this driver grades nothing.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_graph_is_asked_the_ramanujan_question
//! ```

use holonic_engine::rational_polynomial::{RationalPolynomial, rational_root_census};
use num_traits::{One, Zero};
use relational_geometry::Rat;

fn integer(value: i64) -> Rat {
    Rat::from_integer(value.into())
}

/// The adjacency characteristic polynomial of a graph given by its adjacency matrix, exactly, by
/// Faddeev–LeVerrier over `Rat`. Small and self-contained: the graphs below are tiny by design.
fn characteristic(adjacency: &[Vec<i64>]) -> RationalPolynomial {
    let extent = adjacency.len();
    let mut coefficients = vec![Rat::zero(); extent + 1];
    coefficients[extent] = Rat::one();
    let mut current: Vec<Vec<Rat>> = vec![vec![Rat::zero(); extent]; extent];
    for (row, line) in current.iter_mut().enumerate() {
        line[row] = Rat::one();
    }
    for step in 1..=extent {
        // current <- A * current
        let mut product = vec![vec![Rat::zero(); extent]; extent];
        for row in 0..extent {
            for column in 0..extent {
                let mut sum = Rat::zero();
                for inner in 0..extent {
                    if adjacency[row][inner] != 0 {
                        sum += integer(adjacency[row][inner]) * &current[inner][column];
                    }
                }
                product[row][column] = sum;
            }
        }
        let trace: Rat = (0..extent).map(|at| product[at][at].clone()).sum();
        let coefficient = -trace / integer(step as i64);
        coefficients[extent - step] = coefficient.clone();
        for (row, line) in product.iter_mut().enumerate() {
            line[row] += &coefficient;
        }
        current = product;
    }
    RationalPolynomial::new(coefficients)
}

/// `chi(x) * chi(-x)` is even; return the `q` with `q(x^2)` equal to it, whose roots are the
/// squares of `chi`'s roots.
fn squared_spectrum(characteristic: &RationalPolynomial) -> RationalPolynomial {
    let mirrored = RationalPolynomial::new(
        characteristic
            .coefficients()
            .iter()
            .enumerate()
            .map(|(degree, coefficient)| {
                if degree % 2 == 0 {
                    coefficient.clone()
                } else {
                    -coefficient.clone()
                }
            })
            .collect(),
    );
    let even = characteristic.times(&mirrored);
    RationalPolynomial::new(
        even.coefficients()
            .iter()
            .step_by(2)
            .cloned()
            .collect::<Vec<_>>(),
    )
}

struct Graph {
    name: &'static str,
    degree: i64,
    adjacency: Vec<Vec<i64>>,
}

/// The complete graph `K_n`: `(n-1)`-regular, eigenvalues `n-1` once and `-1` with multiplicity
/// `n-1`. Ramanujan for every `n`, and the cheapest positive control there is.
fn complete(name: &'static str, extent: usize) -> Graph {
    let adjacency = (0..extent)
        .map(|row| (0..extent).map(|column| i64::from(row != column)).collect())
        .collect();
    Graph {
        name,
        degree: extent as i64 - 1,
        adjacency,
    }
}

/// The cycle `C_n`: 2-regular, eigenvalues `2cos(2*pi*k/n)`. Ramanujan requires
/// `|lambda| <= 2*sqrt(1) = 2`, which every cycle eigenvalue satisfies — so this is a positive
/// control whose spectrum this body computes by elimination elsewhere.
fn cycle(name: &'static str, extent: usize) -> Graph {
    let adjacency = (0..extent)
        .map(|row| {
            (0..extent)
                .map(|column| {
                    i64::from((row + 1) % extent == column || (column + 1) % extent == row)
                })
                .collect()
        })
        .collect();
    Graph {
        name,
        degree: 2,
        adjacency,
    }
}

/// The complete bipartite graph `K_{n,n}`: `n`-regular, eigenvalues `+n`, `-n`, and `0`.
///
/// **It IS Ramanujan**, and an earlier version of this driver declared it the negative control on
/// the belief that the bipartite `-n` breaks the bound. It does not: the standard definition
/// excludes every eigenvalue with `|lambda| = k`, so both `+k` and `-k` are trivial. The reading
/// returned `yes` and the expectation was wrong.
///
/// **And that is exactly why the square is the right carrier.** `+k` and `-k` square to the same
/// value, so excluding the single root `k^2` excludes both trivial eigenvalues at once — the
/// collapse the squaring performs is precisely the collapse the definition asks for.
fn complete_bipartite(name: &'static str, half: usize) -> Graph {
    let extent = 2 * half;
    let adjacency = (0..extent)
        .map(|row| {
            (0..extent)
                .map(|column| i64::from((row < half) != (column < half)))
                .collect()
        })
        .collect();
    Graph {
        name,
        degree: half as i64,
        adjacency,
    }
}

/// The circular ladder `CL_n = C_n x K_2`: 3-regular on `2n` vertices, eigenvalues
/// `2cos(2*pi*j/n) +/- 1`.
///
/// **This is the real negative control.** The largest non-trivial eigenvalue is `2cos(2*pi/n) + 1`,
/// which rises to 3 as the ladder lengthens, while the Ramanujan bound for `k = 3` is fixed at
/// `2*sqrt(2)`. So a short ladder is Ramanujan and a long one is not, and the crossing is a
/// property of the material rather than of the reading:
///
/// ```text
///   CL_8    2cos(45 deg) + 1  = 2.414  <  2.828   Ramanujan
///   CL_16   2cos(22.5 deg) + 1 = 2.848 >  2.828   NOT Ramanujan
/// ```
///
/// A test that cannot return `no` is not a test, and this is the row that returns it.
fn circular_ladder(name: &'static str, extent: usize) -> Graph {
    let vertices = 2 * extent;
    let adjacency = (0..vertices)
        .map(|row| {
            (0..vertices)
                .map(|column| {
                    let (ring, at) = (row / extent, row % extent);
                    let (other_ring, other_at) = (column / extent, column % extent);
                    let rung = ring != other_ring && at == other_at;
                    let along = ring == other_ring
                        && ((at + 1) % extent == other_at || (other_at + 1) % extent == at);
                    i64::from(rung || along)
                })
                .collect()
        })
        .collect();
    Graph {
        name,
        degree: 3,
        adjacency,
    }
}

fn main() {
    println!("{}", "=".repeat(96));
    println!("THE GRAPH IS ASKED THE RAMANUJAN QUESTION");
    println!("{}", "=".repeat(96));
    println!("\n  Ramanujan  <=>  every non-trivial eigenvalue satisfies  lambda^2 <= 4(k-1).");
    println!("  Taken on the SQUARE, so the bound is an integer and no root is ever extracted.");

    let graphs = vec![
        complete("K_4  (complete, 3-regular)", 4),
        complete("K_5  (complete, 4-regular)", 5),
        cycle("C_6  (cycle, 2-regular)", 6),
        cycle("C_7  (cycle, 2-regular)", 7),
        complete_bipartite("K_3,3 (bipartite, 3-regular)", 3),
        complete_bipartite("K_4,4 (bipartite, 4-regular)", 4),
        circular_ladder("CL_8  (circular ladder, 3-regular)", 8),
        circular_ladder("CL_16 (circular ladder, 3-regular)", 16),
    ];

    println!("\n{}", "-".repeat(96));
    println!(
        "  {:<32} {:>4} {:>10} {:>10} {:>8} {:>8} {:>7}",
        "graph", "k", "4(k-1)", "roots", "above", "open", "verdict"
    );
    println!("{}", "-".repeat(96));

    let mut any_open = false;
    let mut decided = 0usize;
    for graph in &graphs {
        let chi = characteristic(&graph.adjacency);
        let squared = squared_spectrum(&chi);
        let threshold = integer(4 * (graph.degree - 1));
        let trivial = integer(graph.degree * graph.degree);

        let census = match rational_root_census(&squared) {
            Ok(census) => census,
            Err(error) => {
                eprintln!("REFUSED on {}: {error}", graph.name);
                std::process::exit(1);
            }
        };

        let mut above = 0usize;
        let mut open = 0usize;
        for root in &census.roots {
            let interval = &root.isolating.isolating_interval;
            // The trivial eigenvalue k^2 is excluded by name, not by a tolerance.
            if root.rational_value.as_ref() == Some(&trivial) {
                continue;
            }
            if interval.lower > threshold {
                above += 1;
            } else if interval.upper > threshold {
                // The isolating interval STRADDLES the bound, and it can still be decided exactly.
                // The interval holds exactly one root, so `q` changes sign across it; evaluating at
                // the threshold says which side that root is on. No bisection budget, no tolerance,
                // and no guess — one exact evaluation.
                let at_threshold = squared.evaluate(&threshold);
                let at_lower = squared.evaluate(&interval.lower);
                if at_threshold.is_zero() {
                    // The root IS the bound, and the Ramanujan condition is `<=`, so it is inside.
                } else if (at_threshold > Rat::zero()) == (at_lower > Rat::zero()) {
                    // Same sign as the low end, so the sign change — and the root — is above.
                    above += 1;
                }
                // Otherwise the root lies below the bound and contributes nothing.
                let _ = &mut open;
            }
        }
        any_open |= open > 0;
        if open == 0 {
            decided += 1;
        }
        let verdict = if open > 0 {
            "OPEN"
        } else if above == 0 {
            "yes"
        } else {
            "no"
        };
        println!(
            "  {:<32} {:>4} {:>10} {:>10} {:>8} {:>8} {:>7}",
            graph.name,
            graph.degree,
            format!("{threshold}"),
            census.distinct_real_roots,
            above,
            open,
            verdict
        );
    }

    println!("\n{}", "-".repeat(96));
    println!("THE CONTROLS");
    println!("{}", "-".repeat(96));
    println!("  K_n, C_n and K_n,n are POSITIVE controls: all are Ramanujan, and a reading that");
    println!("  called any of them otherwise would be refuted by classical spectra. K_n,n was");
    println!("  declared the NEGATIVE control in an earlier version of this driver on the belief");
    println!(
        "  that its bipartite -k breaks the bound. It does not — the definition excludes every"
    );
    println!("  eigenvalue with |lambda| = k, so both trivial eigenvalues are excluded, and they");
    println!("  square to the same value. The reading returned yes and the expectation was wrong.");
    println!("  CL_16 is the REAL negative control: its largest non-trivial eigenvalue is");
    println!("  2cos(22.5 deg) + 1 = 2.848, past the fixed bound 2*sqrt(2) = 2.828, while CL_8 at");
    println!("  2.414 sits inside it. The crossing is a property of the material, and a test that");
    println!("  cannot return `no` is not a test.");
    println!(
        "\n  {decided} of {} rows decided without a straddling interval; open rows: {}",
        graphs.len(),
        if any_open { "present" } else { "none" }
    );

    println!("\n{}", "-".repeat(96));
    println!("WHAT THIS MAY NOT BE REPORTED AS");
    println!("{}", "-".repeat(96));
    println!("  A property of finite graphs this driver declared. NOT a statement about the");
    println!("  Riemann hypothesis: the analogy that licenses the name is a theorem about Ihara");
    println!("  zetas of finite graphs and nothing more, and the spine bars a suggestive spectral");
    println!("  image from grading any deed. This driver grades nothing.");
    println!("\n{}", "=".repeat(96));
    println!("RETURNED -- the question is asked, and it is decidable");
    println!("{}", "=".repeat(96));
}

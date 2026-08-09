//! The depth of a bisection, read off the polynomial instead of chosen.
//!
//! Three authored levels bounded how deep an exact root isolation was allowed to descend before it
//! refused: `MAXIMUM_ISOLATION_DEPTH = 200` in `rational_polynomial`, and `REFINEMENT_APERTURE = 64`
//! and `ISOLATION_APERTURE = 64` in `winding_inertia`. None of the three was derived from anything.
//! `canon/THE_CONTAMINANT_PROTOCOL.md` §2.5: *"Refusing past a number you invented does not make the
//! number derived."*
//!
//! There is a theorem for it. For a squarefree `f` of degree `n >= 2`,
//!
//! ```text
//!   sep(f)  >  sqrt( 3 |disc(f)| / n^(n+2) ) * ||f||_2^(1-n)
//! ```
//!
//! (Mahler, *An inequality for the discriminant of a polynomial*, Michigan Math. J. **11** (1964)
//! 257-262; stated in this `||f||_2` form at Wolfram MathWorld, *Root Separation*). Squared, every
//! quantity is an exact rational read off `f`'s own coefficients:
//!
//! ```text
//!   sep(f)^2  >  3 |disc(f)| / ( n^(n+2) * (sum a_i^2)^(n-1) )  =:  S
//! ```
//!
//! This driver exhibits the orbit of lifting all three, in the form
//! `canon/THE_CONTAMINANT_PROTOCOL.md` §4 asks for: the separating material, and the return on
//! either side of it.
//!
//! ```text
//!   station 1   the bound against separations known exactly, and its scale invariance
//!   station 2   MAXIMUM_ISOLATION_DEPTH: Mignotte's family, which straddles two hundred
//!   station 3   REFINEMENT_APERTURE: Pell near-cancellations, which straddle sixty-four
//!   station 4   ISOLATION_APERTURE: the ceiling nothing can reach, and the extent that would
//! ```
//!
//! Run: `cargo run -p holonic-engine --release --example the_material_states_its_own_isolation_depth`

use holonic_engine::rational_polynomial::{
    BivariatePolynomial, RationalPolynomial, RootSeparation, integer_discriminant,
    interior_split_schedule, rational_root_census, resultant_in_eliminated_variable,
    root_separation, worst_retained_fraction,
};
use holonic_engine::winding_inertia::{StarTable, SymmetricCirculant, winding_inertia};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;

/// The three levels this construction excised. They appear here as history and are read by nothing
/// in the library; every refusal below is decided by a quantity computed from the material.
const EXCISED_MAXIMUM_ISOLATION_DEPTH: u64 = 200;
const EXCISED_REFINEMENT_APERTURE: usize = 64;
const EXCISED_ISOLATION_APERTURE: u64 = 64;

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn rule(title: &str) {
    println!("\n=== {title}");
}

/// `floor(log2 x)` for a positive rational, exactly, from bit lengths and one comparison.
fn floor_log2(value: &Rat) -> i64 {
    let numerator_bits = value.numer().magnitude().bits() as i64;
    let denominator_bits = value.denom().magnitude().bits() as i64;
    let estimate = numerator_bits - denominator_bits;
    let mut low = estimate - 1;
    while power_of_two(low + 1) <= *value {
        low += 1;
    }
    while power_of_two(low) > *value {
        low -= 1;
    }
    low
}

fn power_of_two(exponent: i64) -> Rat {
    let magnitude = BigInt::from(2).pow(exponent.unsigned_abs() as u32);
    if exponent >= 0 {
        Rat::from_integer(magnitude)
    } else {
        Rat::new(BigInt::one(), magnitude)
    }
}

fn describe(separation: &RootSeparation) -> String {
    match separation {
        RootSeparation::NothingToSeparate { degree } => {
            format!("degree {degree}: no pair of roots to separate")
        }
        RootSeparation::Bounded(bound) => format!(
            "n {:<3} disc {:<5} bits   ||f||_2^2 {:<5} bits   S ~ 2^{:<6} ({} Euclidean steps)",
            bound.degree,
            bound.discriminant.magnitude().bits(),
            bound.coefficient_norm_squared.magnitude().bits(),
            floor_log2(&bound.squared_lower_bound),
            bound.euclidean_steps
        ),
    }
}

// ===============================================================================================

/// Station 1. The bound, held against separations that are known exactly.
fn the_bound_against_what_is_known() {
    rule("station 1 — Mahler's bound against separations known exactly");
    println!("  f                          disc      ||f||_2^2   S                     sep^2   S < sep^2");
    let family: [(&str, Vec<i64>, Rat); 5] = [
        ("x^2 - 2", vec![-2, 0, 1], integer(8)),
        ("x^2 - x - 1", vec![-1, -1, 1], integer(5)),
        ("(x-1)(x-2)(x-3)", vec![-6, 11, -6, 1], integer(1)),
        ("4x^2 - 8x + 3", vec![3, -8, 4], integer(1)),
        ("x^2 + 1  (complex pair)", vec![1, 0, 1], integer(4)),
    ];
    for (name, coefficients, squared_separation) in family {
        let integral = RationalPolynomial::new(coefficients.iter().map(|v| integer(*v)).collect())
            .primitive_integer_form()
            .expect("nonzero");
        let RootSeparation::Bounded(bound) = root_separation(&integral).expect("squarefree") else {
            unreachable!("degree two and above is bounded")
        };
        println!(
            "  {name:<26} {:<9} {:<11} {:<21} {:<7} {}",
            bound.discriminant,
            bound.coefficient_norm_squared,
            bound.squared_lower_bound,
            squared_separation,
            bound.squared_lower_bound < squared_separation
        );
    }

    println!("\n  scale invariance — disc moves by c^(2n-2), the norm by c^2, the bound by nothing");
    let base = RationalPolynomial::new(vec![integer(-6), integer(11), integer(-6), integer(1)]);
    for factor in [1_i64, 2, 3, 5] {
        let scaled = holonic_engine::exact_value::IntegerPolynomial::new(
            base.coefficients()
                .iter()
                .map(|value| (value * integer(factor)).to_integer())
                .collect(),
        )
        .expect("nonzero");
        let RootSeparation::Bounded(bound) = root_separation(&scaled).expect("squarefree") else {
            unreachable!()
        };
        println!(
            "    c = {factor}   disc {:<10} ||f||_2^2 {:<8} S {}",
            bound.discriminant, bound.coefficient_norm_squared, bound.squared_lower_bound
        );
    }

    println!(
        "\n  two routes to the same discriminant, and both their costs (CLAUDE.md §8: where an"
    );
    println!("  independent implementation exists, state both costs — measured in work, never in time)");
    println!("  f                          disc            Euclidean steps   Sylvester/Bareiss");
    let cost_family: [(&str, Vec<i64>); 4] = [
        ("x^2 - 2", vec![-2, 0, 1]),
        ("(x-1)(x-2)(x-3)", vec![-6, 11, -6, 1]),
        ("x^4 + 1", vec![1, 0, 0, 0, 1]),
        ("x^5 - x - 1", vec![-1, -1, 0, 0, 0, 1]),
    ];
    for (name, coefficients) in cost_family {
        let rational = RationalPolynomial::new(coefficients.iter().map(|v| integer(*v)).collect());
        let integral = rational.primitive_integer_form().expect("nonzero");
        let (discriminant, euclidean_steps) =
            integer_discriminant(&integral).expect("degree two and above");
        let lift = |polynomial: &RationalPolynomial| {
            BivariatePolynomial::new(
                polynomial
                    .coefficients()
                    .iter()
                    .map(|value| RationalPolynomial::constant(value.clone()))
                    .collect(),
            )
        };
        let (sylvester, work) =
            resultant_in_eliminated_variable(&lift(&rational), &lift(&rational.derivative()))
                .expect("both have positive degree");
        let degree = integral.degree();
        let mut by_sylvester = sylvester.coefficient(0) / rational.leading().expect("leads").clone();
        if (degree * (degree - 1) / 2) % 2 == 1 {
            by_sylvester = -by_sylvester;
        }
        assert_eq!(by_sylvester, Rat::from_integer(discriminant.clone()));
        println!(
            "  {name:<26} {:<15} {euclidean_steps:<17} {}x{} matrix, {} exact divisions, {} multiplications",
            discriminant,
            work.matrix_extent,
            work.matrix_extent,
            work.exact_divisions,
            work.polynomial_multiplications
        );
    }

    println!("\n  and the refusals it carries, which are statements about the polynomial:");
    let repeated = RationalPolynomial::new(vec![integer(-8), integer(12), integer(-6), integer(1)])
        .primitive_integer_form()
        .expect("nonzero");
    println!("    (x-2)^3      -> {:?}", root_separation(&repeated));
    let linear = RationalPolynomial::new(vec![integer(-1), integer(2)])
        .primitive_integer_form()
        .expect("nonzero");
    println!("    2x - 1       -> {:?}", root_separation(&linear));
}

// ===============================================================================================

/// `x^n - 2(a x - 1)^2`: two roots about `sqrt2 * a^(-(n+2)/2)` apart.
fn mignotte(exponent: usize, scale: &BigInt) -> RationalPolynomial {
    let mut coefficients = vec![Rat::zero(); exponent + 1];
    coefficients[0] = integer(-2);
    coefficients[1] = Rat::from_integer(scale * BigInt::from(4));
    coefficients[2] = Rat::from_integer(-(scale * scale) * BigInt::from(2));
    coefficients[exponent] = Rat::one();
    RationalPolynomial::new(coefficients)
}

/// Station 2. `MAXIMUM_ISOLATION_DEPTH = 200`, and the material that straddles it.
fn the_census_orbit() {
    rule("station 2 — MAXIMUM_ISOLATION_DEPTH = 200, against Mignotte's family");
    println!(
        "  Mignotte x^6 - 2(a x - 1)^2. sep ~ sqrt2 * a^-4, so the depth demanded is set by `a`."
    );
    println!(
        "\n  a          depth reached   permitted by S   real roots   sturm counts   past the excised {EXCISED_MAXIMUM_ISOLATION_DEPTH}?"
    );
    for power in [6_u32, 12, 15, 16, 18, 24] {
        let scale = BigInt::from(10).pow(power);
        let polynomial = mignotte(6, &scale);
        match rational_root_census(&polynomial) {
            Ok(census) => println!(
                "  10^{power:<8} {:<15} {:<16} {:<12} {:<14} {}",
                census.work.isolation_depth_reached,
                census.isolation_depth_bound,
                census.distinct_real_roots,
                census.work.sturm_counts,
                if census.work.isolation_depth_reached >= EXCISED_MAXIMUM_ISOLATION_DEPTH {
                    "YES — the authored depth refused here"
                } else {
                    "no"
                }
            ),
            Err(error) => println!("  10^{power:<8} REFUSED {error}"),
        }
    }
    let census = rational_root_census(&mignotte(6, &BigInt::from(10).pow(18))).expect("returns");
    println!("\n  at a = 10^18 the separation bound reads:");
    println!("    {}", describe(&census.separation));
    println!(
        "    split schedule retains at most {} per step, so {} splits are permitted",
        census.split_schedule_retained, census.isolation_depth_bound
    );
    println!(
        "    the isolation asked for {} of them and returned {} certified real roots",
        census.work.isolation_depth_reached,
        census.roots.len()
    );
    for (index, root) in census.roots.iter().enumerate() {
        let interval = &root.isolating.isolating_interval;
        println!(
            "      root {index}: width 2^{:<6} sturm variations {} -> {}",
            floor_log2(&(&interval.upper - &interval.lower)),
            root.isolating.certificate.variations_at_lower,
            root.isolating.certificate.variations_at_upper
        );
    }
}

// ===============================================================================================

/// `(p_k, q_k)` with `p/q -> sqrt 2` and `p^2 - 2q^2 = (-1)^k`.
fn pell(index: usize) -> (BigInt, BigInt) {
    let (mut previous_p, mut p) = (BigInt::one(), BigInt::one());
    let (mut previous_q, mut q) = (BigInt::zero(), BigInt::one());
    for _ in 1..index {
        let next_p = BigInt::from(2) * &p + &previous_p;
        let next_q = BigInt::from(2) * &q + &previous_q;
        previous_p = p;
        previous_q = q;
        p = next_p;
        q = next_q;
    }
    (p, q)
}

/// `circ(-p, q, 0, 0, 0, 0, 0, q)`: eight characters, and `lambda_1 = q sqrt2 - p`.
fn near_cancelling(index: usize) -> SymmetricCirculant {
    let (p, q) = pell(index);
    let mut row = vec![Rat::zero(); 8];
    row[0] = Rat::from_integer(-p);
    row[1] = Rat::from_integer(q.clone());
    row[7] = Rat::from_integer(q);
    SymmetricCirculant::from_first_row(row).expect("reversal symmetric")
}

/// The excised aperture, replayed against the public star table: the refinements needed to put an
/// enclosure strictly on one side of zero, refusing at `cap` exactly as `REFINEMENT_APERTURE` did.
fn refinements_to_decide(
    form: &SymmetricCirculant,
    character: usize,
    cap: usize,
) -> Option<usize> {
    let (_, symbol) = form.integral_symbol();
    let mut table = StarTable::found(form.extent()).expect("the star table founds");
    for taken in 0..=cap {
        let enclosure = table.enclose(&symbol, character).expect("the symbol encloses");
        if enclosure.lower.is_positive() || enclosure.upper.is_negative() {
            return Some(taken);
        }
        if taken == cap {
            return None;
        }
        table.refine().expect("an inexact table refines");
    }
    None
}

/// Station 3. `REFINEMENT_APERTURE = 64`, and the material that straddles it.
fn the_winding_orbit() {
    rule("station 3 — REFINEMENT_APERTURE = 64, against Pell near-cancellations");
    println!(
        "  circ(-p, q, 0, 0, 0, 0, 0, q) on eight characters. lambda_1 = q sqrt2 - p, whose size is"
    );
    println!("  1/(p + q sqrt2) against coefficients of size q, so the refinements grow like log(q^2).");
    println!(
        "\n  index   q                      |lambda_1| ~   refinements   replay at the excised {EXCISED_REFINEMENT_APERTURE}"
    );
    for index in [4_usize, 8, 13, 16, 21, 24, 28, 32] {
        let (p, q) = pell(index);
        let form = near_cancelling(index);
        let reading = winding_inertia(&form).expect("the circulant reads");
        let enclosure = &reading.passage(1).expect("character one").scaled_enclosure;
        let magnitude = enclosure.lower.abs().min(enclosure.upper.abs());
        let replay = match refinements_to_decide(&form, 1, EXCISED_REFINEMENT_APERTURE) {
            Some(taken) => format!("decided after {taken}"),
            None => "UNDECIDED — the authored aperture refused here".to_owned(),
        };
        println!(
            "  {index:<7} {q:<22} 2^{:<12} {:<13} {replay}",
            floor_log2(&magnitude),
            reading.refinements
        );
        // Pell's identity decides the hand with no reference to this module.
        let expected_negative = &p * &p > BigInt::from(2) * &q * &q;
        assert_eq!(
            enclosure.upper.is_negative(),
            expected_negative,
            "index {index}: p^2 - 2q^2 and the enclosure disagree about the hand"
        );
    }

    let form = near_cancelling(28);
    let reading = winding_inertia(&form).expect("the circulant reads");
    println!("\n  at index 28 the determinant's own bound reads:");
    println!(
        "    {}",
        describe(&root_separation(&reading.characteristic_polynomial).expect("squarefree"))
    );
    println!(
        "    characteristic polynomial degree {}, {} refinements taken",
        reading.characteristic_polynomial.degree(),
        reading.refinements
    );
    println!("    passages, by winding rather than by count:");
    for passage in &reading.passages {
        println!(
            "      chi_{:<2} winding {:<6} star {:<8} returns {}",
            passage.character,
            passage.winding,
            passage.star_polygon.label(),
            passage.returns.name()
        );
    }
}

// ===============================================================================================

/// Station 4. `ISOLATION_APERTURE = 64` — the ceiling nothing reaches, and what would.
fn the_ceiling_nothing_reaches() {
    rule("station 4 — ISOLATION_APERTURE = 64, and the extent that would hit it");
    println!(
        "  `isolate_all_roots` is reached only from `StarTable::found`, so its material is fixed by"
    );
    println!("  the extent: the roots are 2cos(2*pi*m/n), whose smallest gap sits at m = 0.");
    println!(
        "\n  extent   star degree   retained per split   depth reached   permitted by S   past {EXCISED_ISOLATION_APERTURE}?"
    );
    for extent in [3_usize, 4, 6, 8, 12, 20, 36, 60, 120] {
        let table = StarTable::found(extent).expect("the star table founds");
        let polynomial = table.polynomial().clone();
        let separation = root_separation(&polynomial).expect("the star polynomial is squarefree");
        let retained = worst_retained_fraction(&interior_split_schedule(polynomial.degree()))
            .expect("the schedule is nonempty");
        let permitted_from_six = separation
            .splitting_depth(&integer(6), &retained)
            .expect("the bound is positive");
        let (reached, permitted) = table.isolation_depth();
        assert_eq!(permitted, permitted_from_six);
        println!(
            "  {extent:<8} {:<13} {retained:<20} {reached:<15} {permitted:<16} {}",
            polynomial.degree(),
            if reached >= EXCISED_ISOLATION_APERTURE {
                "YES"
            } else {
                "no"
            }
        );
    }
    println!(
        "\n  Nothing reaches it. The star values are 2cos(2*pi*m/n) and their smallest gap is"
    );
    println!("  4 sin^2(pi/n) ~ 4*pi^2/n^2, so a descent of {EXCISED_ISOLATION_APERTURE} splits from width 6 needs a gap under");
    println!("  6*2^-{EXCISED_ISOLATION_APERTURE}, hence an extent past about 10^10 — at which `StarTable::found` would first");
    println!("  have to allocate n/2 + 1 isolating intervals. That is the material that would hit");
    println!("  this level, and it is not reachable.");
    println!(
        "\n  The excision therefore moves no return here, and the reachable population is not even"
    );
    println!("  uniformly larger: the derived depth is TIGHTER than 64 at small extents (9 at C_3)");
    println!("  and looser at large ones. What changes is what the refusal means — from an");
    println!("  exhausted allowance to a contradiction between Sturm and the discriminant.");
}

fn main() {
    println!("THE MATERIAL STATES ITS OWN ISOLATION DEPTH");
    println!("Mahler 1964, via the discriminant. Three authored levels excised, orbit exhibited.");
    the_bound_against_what_is_known();
    the_census_orbit();
    the_winding_orbit();
    the_ceiling_nothing_reaches();
    println!("\nno float, no tolerance, no authored depth.");
}

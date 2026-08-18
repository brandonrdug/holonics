//! **Dividing one vector by another returns a scalar and an oriented area. An attention score is
//! the scalar. The area is computed nowhere and it is the hand of the crossing.**
//!
//! ```text
//! cargo run --release --example the_arrow_is_the_division_and_the_score_is_its_aim
//! ```
//!
//! **Station one of
//! [`blueprint/THE_CLIFFORD_LIFT_THE_PHASE_WIRE_AND_THE_FOUR_UNTAKEN_READINGS.md`](../../../blueprint/THE_CLIFFORD_LIFT_THE_PHASE_WIRE_AND_THE_FOUR_UNTAKEN_READINGS.md).**
//! It executed first against a struct local to this file; the carrier is now
//! [`holonic_engine::clifford`] in the library, and this driver reads it. The superseded plan is
//! `blueprint/THE_ARROW_IS_THE_DIVISION_AND_ATTENTION_KEEPS_ONLY_ITS_AIM.md`, whose station four —
//! *the cross is the hand, so a layer is a braid* — is merged into the same build, because the
//! algebra that carries a hand is the even Clifford algebra and there is only one of those.
//!
//! ## What moved when the local struct became a library organ
//!
//! Every figure below is unchanged. Two things are genuinely stronger:
//!
//! - **The reconstruction is now a product in the algebra.** It was a hand-rolled contraction of the
//!   blade against `b`; it is now `(a b⁻¹) b` with the geometric product doing the work, so the
//!   division law is a measurement on the algebra rather than a restatement of how the blade was
//!   built.
//! - **The signature is declared.** `qᵢ = eᵢ·eᵢ` is a caller's declaration, and `euclidean` is named
//!   rather than defaulted. An undeclared `G = I` is the smuggling this line exists to refuse.
//!
//! One presentational change: the blade is **sparse**, so it prints as its non-zero coordinates
//! `e_{i,j}` rather than as a dense `d(d−1)/2` vector. The coordinates are the same rationals.

use std::collections::BTreeMap;

use holonic_engine::clifford::{Aim, Arrow, Causal, Clifford, Signature, merge_blades};
use num_bigint::BigInt;
use num_traits::Zero;
use relational_geometry::Rat;

fn rational(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn whole(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn render(vector: &[Rat]) -> String {
    let parts: Vec<String> = vector.iter().map(std::string::ToString::to_string).collect();
    format!("({})", parts.join(", "))
}

fn render_blade(blade: &BTreeMap<(usize, usize), Rat>) -> String {
    if blade.is_empty() {
        return "0".to_string();
    }
    let parts: Vec<String> = blade
        .iter()
        .map(|((i, j), value)| format!("{value} e_{i}{j}"))
        .collect();
    parts.join("  +  ")
}

fn hand_name(hand: Aim) -> &'static str {
    match hand {
        Aim::Cohere => "COHERE",
        Aim::Anti => "ANTI",
        Aim::Ortho => "ORTHO",
    }
}

fn causal_name(causal: Causal) -> &'static str {
    match causal {
        Causal::TransportDominant => "TRANSPORT",
        Causal::Balanced => "BALANCED",
        Causal::StorageDominant => "STORAGE",
        Causal::Unread => "UNREAD",
    }
}

fn main() {
    println!("{}", "=".repeat(100));
    println!("THE ARROW IS THE DIVISION, AND AN ATTENTION SCORE IS ITS AIM");
    println!("{}", "=".repeat(100));
    println!();
    println!("  Dividing one vector by another returns a scalar and an oriented area:");
    println!();
    println!("      A B^-1  =  (A.B)/||B||^2   +   (A^B)/||B||^2");
    println!("                 the QUOTIENT        the REMAINDER");
    println!("                 a scalar            an oriented area");
    println!();
    println!("  `soma/body/src/arrow.rs` already carries this as Arrow{{reach, aim, cross}} in TWO");
    println!("  dimensions, with the note \"The whole arrow, never one scalar.\" The carrier read");
    println!("  below is that arrow at d dimensions over exact rationals, in the library, with the");
    println!("  algebra that carries its hand.");

    // ---------------------------------------------------------------- the algebra
    println!();
    println!("{}", "=".repeat(100));
    println!("[0]  THE ALGEBRA  --  and the one factor that separates it from the standing carrier");
    println!("{}", "=".repeat(100));
    println!();
    println!("    multiquadratic   e_S e_T  =              (prod_{{S^T}} k_i) . e_{{S x T}}");
    println!("    Clifford         e_S e_T  =  sigma(S,T) . (prod_{{S^T}} q_i) . e_{{S x T}}");
    println!();
    println!("  sigma(S,T) = (-1)^#{{(i,j) : i in S, j in T, i > j}} -- the exterior sign, the parity");
    println!("  of the transpositions that sort S concatenated with T.");
    println!();

    let euclidean3 = Signature::euclidean(3);
    let e0 = Clifford::vector(euclidean3.clone(), &[whole(1), whole(0), whole(0)]).expect("in");
    let e1 = Clifford::vector(euclidean3.clone(), &[whole(0), whole(1), whole(0)]).expect("in");
    let forward = e0.product(&e1).expect("same signature");
    let backward = e1.product(&e0).expect("same signature");
    println!(
        "    e0 e1 = {}        e1 e0 = {}",
        render_blade_of(&forward),
        render_blade_of(&backward)
    );
    assert_ne!(forward, backward, "the product must not commute");
    println!();
    println!("  THE FALSIFIER STATION ONE NAMES: if the product commuted, the sign was not installed");
    println!("  and the whole station is decoration. It does not commute.");
    println!();
    println!("  AND THE OBVIOUS REPAIR IS NOT AVAILABLE. mu(S) = (-1)^|S| is a CHARACTER of the");
    println!("  grading group -- mu(S)mu(T) = mu(S x T) -- hence a coboundary, so twisting by it is");
    println!("  an isomorphism and preserves commutativity. sigma is asymmetric in its arguments and");
    println!("  every character of an abelian group is symmetric, so sigma is not one:");
    let sigma_forward = merge_blades(&[0], &[1]);
    let sigma_backward = merge_blades(&[1], &[0]);
    println!(
        "    sigma({{0}},{{1}}) = {:+}      sigma({{1}},{{0}}) = {:+}      same surviving blade {:?}",
        sigma_forward.sign, sigma_backward.sign, sigma_forward.surviving
    );
    println!();
    println!("  So the crossing-word algebra that carries a hand IS the even Clifford algebra, and");
    println!("  `soul::FormedRotor {{aim, cross}}` is already its two-dimensional case.");

    // ---------------------------------------------------------------- station one
    println!();
    println!("{}", "=".repeat(100));
    println!("[1]  THE DIVISION LAW  --  and what dropping the cross costs");
    println!("{}", "=".repeat(100));
    println!();

    let material: Vec<(&str, Vec<Rat>, Vec<Rat>)> = vec![
        (
            "generic, non-collinear",
            vec![whole(4), whole(1), whole(-2)],
            vec![whole(2), whole(0), whole(0)],
        ),
        (
            "Brandon's 4/2, as collinear vectors",
            vec![whole(4), whole(0), whole(0)],
            vec![whole(2), whole(0), whole(0)],
        ),
        (
            "rational coordinates",
            vec![rational(7, 3), rational(-1, 2), whole(5)],
            vec![rational(1, 6), whole(2), rational(-3, 4)],
        ),
        (
            "orthogonal — the aim is null",
            vec![whole(0), whole(5), whole(0)],
            vec![whole(3), whole(0), whole(0)],
        ),
    ];

    let mut collinear = 0usize;
    let mut non_collinear = 0usize;
    for (name, left, right) in &material {
        let arrow = Arrow::between(&euclidean3, left, right).expect("same ambient");
        let area = arrow.area_squared();
        assert_eq!(
            area.frames_agree(),
            Some(true),
            "the blade and Lagrange must agree exactly"
        );
        if area.value.is_zero() {
            collinear += 1;
        } else {
            non_collinear += 1;
        }
        println!("  {name}");
        println!("    A = {}   B = {}", render(left), render(right));
        println!(
            "    aim {}   area^2 {}   hand {}   causal {}",
            arrow.aim(),
            area.value,
            hand_name(arrow.hand()),
            causal_name(arrow.causal_class())
        );
        println!("    blade  {}", render_blade(arrow.cross()));
        match arrow.quotient() {
            Ok(quotient) => println!("    quotient  A.B/||B||^2 = {quotient}"),
            Err(refusal) => {
                println!("    quotient  {refusal}");
                continue;
            }
        }

        let whole_back = arrow.reconstruct().expect("the divisor is not null");
        let aim_back = arrow
            .reconstruct_from_aim()
            .expect("the divisor is not null");
        assert_eq!(
            &whole_back, left,
            "the whole arrow must reconstruct the dividend exactly"
        );
        println!("    from the WHOLE arrow  {}   EXACT", render(&whole_back));
        let exact_from_aim = &aim_back == left;
        println!(
            "    from the AIM alone    {}   {}",
            render(&aim_back),
            if exact_from_aim {
                "exact -- this pair is COLLINEAR, so the remainder is zero"
            } else {
                "WRONG, and the error IS the remainder"
            }
        );
        if !exact_from_aim {
            println!(
                "      the dropped part      {}",
                render(&arrow.rejection().expect("the divisor is not null"))
            );
        }
        println!();
    }
    println!("  material: {non_collinear} non-collinear pairs, {collinear} collinear");
    println!("  THE ANTI-VACUITY ARM: on a collinear pair the remainder is genuinely zero and the");
    println!("  aim alone reconstructs. A run made only of collinear pairs would show the aim");
    println!("  sufficing and would prove nothing, which is why both are here.");
    assert!(
        non_collinear > 0 && collinear > 0,
        "the material must exhibit both, or the reading cannot fail"
    );
    println!();
    println!("  AND THE RECONSTRUCTION IS NOW A PRODUCT. `a = (a b^-1) b` is computed in the algebra");
    println!("  -- the actual quotient times the actual divisor -- not a contraction written to");
    println!("  invert the way the blade was built. That is what makes it a measurement.");

    // ---------------------------------------------------------------- station two
    println!();
    println!("{}", "=".repeat(100));
    println!("[2]  THE BLINDNESS  --  one score, two planes");
    println!("{}", "=".repeat(100));
    println!();
    println!("  A score is the aim. Two crossings with the SAME aim and DIFFERENT blades are");
    println!("  indistinguishable to it. In d >= 3 this is immediate: the same angle, another plane.");
    println!();

    let euclidean4 = Signature::euclidean(4);
    let q = vec![whole(1), whole(0), whole(0), whole(0)];
    let keys: Vec<(&str, Vec<Rat>)> = vec![
        ("k1 = (2,3,0,0)", vec![whole(2), whole(3), whole(0), whole(0)]),
        ("k2 = (2,0,3,0)", vec![whole(2), whole(0), whole(3), whole(0)]),
        ("k3 = (2,0,0,3)", vec![whole(2), whole(0), whole(0), whole(3)]),
    ];
    let arrows: Vec<(&str, Arrow)> = keys
        .iter()
        .map(|(name, key)| {
            (
                *name,
                Arrow::between(&euclidean4, &q, key).expect("same ambient"),
            )
        })
        .collect();
    println!("  q = {}", render(&q));
    println!();
    println!("  {:<18} {:>6} {:>10}   {}", "key", "aim", "area^2", "blade");
    for (name, arrow) in &arrows {
        println!(
            "  {name:<18} {:>6} {:>10}   {}",
            arrow.aim(),
            arrow.area_squared().value,
            render_blade(arrow.cross())
        );
    }
    for pair in arrows.windows(2) {
        assert_eq!(pair[0].1.aim(), pair[1].1.aim(), "the aims must be exactly equal");
        assert_eq!(
            pair[0].1.area_squared().value,
            pair[1].1.area_squared().value,
            "the areas must be exactly equal too, or the area alone would separate them"
        );
        assert_ne!(
            pair[0].1.cross(),
            pair[1].1.cross(),
            "the blades must differ, or there is nothing to see"
        );
    }
    println!();
    println!("  Every aim is EXACTLY equal.  Every area^2 is EXACTLY equal.  Every blade DIFFERS.");
    println!();
    println!("  THE FALSIFIER THE PLAN NAMED, AND IT RETURNS AGAINST THE WEAKER READING:");
    println!("  a scalar summary of the wedge does not suffice either. The area is the same in all");
    println!("  three; only the blade separates them. So the wedge must be carried WHOLE, and");
    println!("  reducing it to its magnitude would be a second float.");
    println!();
    println!("  This is the phase-object theorem at the attention score. A pure phase grating has");
    println!("  |t| = 1 everywhere and an intensity receiver measures nothing. The dot product is a");
    println!("  magnitude receiver; the plane of the crossing is a phase object.");

    // ---------------------------------------------------------------- the ortho population
    println!();
    println!("{}", "=".repeat(100));
    println!("[3]  THE ORTHO CASE  --  where the score reads nothing and the gyration is maximal");
    println!("{}", "=".repeat(100));
    println!();
    println!("  `soma/body/src/arrow.rs:32-34`, on Aim::Ortho:");
    println!();
    println!("    \"the cohere is null, but the CROSS/gyration is MAXIMAL: the pure orthogonal turn,");
    println!("     the FOUNDING hand, the magnitude looked-past. NOT 'no current' -- it is the most");
    println!("     turn there is, mis-read as nothing because the cohere face is null.\"");
    println!();
    let sweep: Vec<Vec<Rat>> = (0..6)
        .map(|at| {
            let mut vector = vec![Rat::zero(); 4];
            vector[at % 4] = whole(i64::try_from(at).expect("small") + 1);
            vector[(at + 1) % 4] = whole(2);
            vector
        })
        .collect();
    let mut census: BTreeMap<&str, usize> = BTreeMap::new();
    let mut causal_census: BTreeMap<&str, usize> = BTreeMap::new();
    let mut ortho_with_area = 0usize;
    for left in &sweep {
        for right in &sweep {
            let arrow = Arrow::between(&euclidean4, left, right).expect("same ambient");
            if arrow.right_span().is_zero() {
                continue;
            }
            *census.entry(hand_name(arrow.hand())).or_insert(0) += 1;
            *causal_census
                .entry(causal_name(arrow.causal_class()))
                .or_insert(0) += 1;
            if arrow.hand() == Aim::Ortho && !arrow.area_squared().value.is_zero() {
                ortho_with_area += 1;
            }
        }
    }
    println!("  a small exact sweep, {} pairs:", sweep.len() * sweep.len());
    for (hand, count) in &census {
        println!("    {hand:<8} {count}");
    }
    println!();
    println!("  of the ORTHO pairs, {ortho_with_area} carry a NON-ZERO area — the score reads zero");
    println!("  and the arrow carries a whole plane. Those are the pairs an attention head is told");
    println!("  are unrelated, and on which the law body says the turn is maximal.");
    assert!(
        ortho_with_area > 0,
        "the sweep must exhibit at least one ortho pair with a real blade"
    );

    println!();
    println!("  AND THE SHARPER READING, which the hand alone cannot give. `arrow.rs:159-161`:");
    println!("  squaring sends the whole wall to zero along with the origin, so only a reading of");
    println!("  the PAIR separates the honest point [0:1] from the non-point [0:0]:");
    for (class, count) in &causal_census {
        println!("    {class:<10} {count}");
    }
    println!();
    println!("  A zero score names two utterly different causal facts -- ORTHO, where the gyration");
    println!("  is maximal, and UNREAD, where the relating is behind the pole's own horizon and has");
    println!("  no causal character at all. The score returns the same number for both. Station six");
    println!("  takes this census to a real head for exactly that reason.");

    println!();
    println!("{}", "=".repeat(100));
    println!("WHAT THIS RUN DOES NOT CLAIM");
    println!("{}", "=".repeat(100));
    println!();
    println!("  It measures what a score CANNOT see. It does not claim a model would behave");
    println!("  differently with the blade carried -- that is a separate question needing a separate");
    println!("  falsifier, and station six of the plan puts the census to real weights rather than");
    println!("  to the small exact sweep above.");
    println!();
    println!("  Nothing here rests on the receiver family being orthogonal. The dot and the wedge are");
    println!("  bilinear forms on coordinates; they need no orthonormal basis and no projector, which");
    println!("  is why this line survives the refutation that removed the projector reading.");
}

/// The grade-two part of a Clifford element, printed as its blade coordinates.
fn render_blade_of(element: &Clifford) -> String {
    let grade_two = element.grade(2);
    if grade_two.is_zero() {
        return "0".to_string();
    }
    let parts: Vec<String> = grade_two
        .terms()
        .iter()
        .map(|(blade, value)| {
            let axes: String = blade.iter().map(std::string::ToString::to_string).collect();
            format!("{value} e_{axes}")
        })
        .collect();
    parts.join("  +  ")
}

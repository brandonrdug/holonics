//! `E = mc^2` is the relation at one angle, and the angle is computed here.
//!
//! ## What this drives
//!
//! `research/records/2026-08-09_THE_SHORTHAND_DELETED_THE_TURN_AND_THE_CAST_WAS_ERASED_EVERYWHERE.md`
//! §8 closes with *"the pi-group computation is exhibited by hand above and is not run by any
//! code."* This is the code. Nothing below is asserted from the record; every figure is a return
//! from `holonic_engine::quantity`.
//!
//! Six things are returned, in order:
//!
//! 1. **The Buckingham pi computation** on `(E, m, c, p)` over a caller-declared `(M, L, T)`:
//!    `rank` three independent ways, `n - rank` groups, and a basis of `ker M` verified to
//!    annihilate the matrix exactly.
//! 2. **The span, not the basis.** Two correct computations return different bases of one kernel,
//!    so the driver certifies that the physically named groups `E/mc^2` and `E/pc` lie in the
//!    returned span and prints their exact coordinates in it. Then it *moves the frame* — permuting
//!    the declared quantities and permuting the declared base units — and requires the rank, the
//!    count, and span membership to be unmoved while the basis words visibly move.
//! 3. **The left kernel**, which is what "set `c = 1`" actually is: a rescaling of the declared base
//!    units that no declared quantity can detect. It is computed, one-dimensional here, and its
//!    dimension is `k - rank`.
//! 4. **The refusals**, exhibited: adding a length to a time returns a typed refusal naming both
//!    dimensions; comparing them returns `Open` rather than unequal; a dimensionless cast is refused
//!    by name.
//! 5. **The controls that can fail.** A full-rank dimension matrix returns *zero* groups, and the
//!    count is swept `0 -> 1 -> 2` as material is added. A perturbed energy is carried through the
//!    same non-dimensionalisation and returns a nonzero residual, so the identity check has teeth.
//! 6. **The relation, exact over Q.** `E^2 = (mc^2)^2 + (pc)^2` at three rational values of `beta`,
//!    with no float and no square root anywhere: `1 = (mc^2/E)^2 + (pc/E)^2` is a Pythagorean
//!    triple, and the half-turn parameter `t = tan(theta/2) = sin/(1 + cos)` comes back an exact
//!    rational. At `beta = 0` it comes back **zero**: the shorthand is `theta = 0`.
//!
//! `M`, `L`, `T` occur only in this file's fixture and in the module's tests. The organ names no
//! unit.

use holonic_engine::exact_value::ExactOrdering;
use holonic_engine::quantity::{
    BaseUnits, Cast, Dimension, DimensionMatrix, PiGroup, PiGroups, Quantity, QuantityError,
};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::{Rat, format_rat};

fn whole(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn rational(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn word(values: &[i64]) -> Vec<Rat> {
    values.iter().map(|value| whole(*value)).collect()
}

fn render_word(values: &[Rat]) -> String {
    let rendered: Vec<String> = values.iter().map(format_rat).collect();
    format!("({})", rendered.join(", "))
}

// -----------------------------------------------------------------------------------------------
// the declared fixture

struct Mechanics {
    base: BaseUnits,
    energy: Dimension,
    mass: Dimension,
    speed: Dimension,
    momentum: Dimension,
}

impl Mechanics {
    fn declare(order: [&str; 3]) -> Self {
        let base = BaseUnits::declare(order).expect("the declared base is well formed");
        let by = |mass: i64, length: i64, time: i64| {
            base.dimension_of(&[("M", whole(mass)), ("L", whole(length)), ("T", whole(time))])
                .expect("every symbol is declared")
        };
        Self {
            energy: by(1, 2, -2),
            mass: by(1, 0, 0),
            speed: by(0, 1, -1),
            momentum: by(1, 1, -1),
            base,
        }
    }

    fn matrix(&self, order: [&str; 4]) -> DimensionMatrix {
        let columns = order
            .iter()
            .map(|name| {
                let dimension = match *name {
                    "E" => self.energy.clone(),
                    "m" => self.mass.clone(),
                    "c" => self.speed.clone(),
                    "p" => self.momentum.clone(),
                    other => panic!("undeclared quantity {other}"),
                };
                ((*name).to_owned(), dimension)
            })
            .collect();
        DimensionMatrix::declare(self.base.clone(), columns).expect("the declared matrix is sound")
    }

    fn cast(&self) -> Cast {
        // Units in which one length-unit per time-unit IS c. The MAGNITUDE is one; the DIMENSION is
        // not, and that is the whole distinction the carrier draws.
        Cast::declare("c", Quantity::new(Rat::one(), self.speed.clone()))
            .expect("a cast with a dimension is lawful")
    }
}

// -----------------------------------------------------------------------------------------------
// the returns

fn report(groups: &PiGroups) {
    println!(
        "    rank            {} (elimination)   {} (Smith normal form)   {} (transpose)",
        groups.rank, groups.rank_by_smith_normal_form, groups.rank_by_transpose
    );
    println!(
        "    n - rank        {} - {} = {} independent dimensionless groups",
        groups.quantities.len(),
        groups.rank,
        groups.independent_group_count
    );
    println!("    free positions  {:?}", groups.free_positions);
    println!("{}", groups.render_basis());
    let factors: Vec<String> = groups
        .invariant_factors
        .iter()
        .map(ToString::to_string)
        .collect();
    let scales: Vec<String> = groups
        .column_scales
        .iter()
        .map(ToString::to_string)
        .collect();
    println!(
        "    invariant factors [{}]   column scales [{}]   exact eliminations {}",
        factors.join(", "),
        scales.join(", "),
        groups.eliminations
    );
    println!(
        "    k - rank        {} undetectable base rescaling(s) over ({})",
        groups.undetectable_rescaling_count,
        groups.base_units.join(", ")
    );
    for rescaling in &groups.undetectable_base_rescalings {
        println!("                    {}", render_word(rescaling));
    }
}

fn membership(groups: &PiGroups, name: &str, candidate: &[Rat]) -> bool {
    match groups.coordinates_of(candidate) {
        Some(coordinates) => {
            println!(
                "    {name:<10} {:<24} IN THE SPAN, coordinates {}",
                render_word(candidate),
                render_word(&coordinates)
            );
            true
        }
        None => {
            println!(
                "    {name:<10} {:<24} NOT in the span",
                render_word(candidate)
            );
            false
        }
    }
}

// -----------------------------------------------------------------------------------------------

fn main() {
    let mut failures: Vec<String> = Vec::new();
    let mechanics = Mechanics::declare(["M", "L", "T"]);
    let matrix = mechanics.matrix(["E", "m", "c", "p"]);

    println!("\n=== 1. the dimension matrix, and Buckingham pi computed on it ===\n");
    println!("{}\n", matrix.render());
    let groups = matrix.buckingham().expect("the pi groups return");
    report(&groups);
    if groups.rank != 2 {
        failures.push(format!("expected rank 2, returned {}", groups.rank));
    }
    if groups.independent_group_count != 2 {
        failures.push(format!(
            "expected 2 pi-groups, returned {}",
            groups.independent_group_count
        ));
    }

    println!("\n    the annihilation certificate, computed by ExactRatMatrix::apply:");
    let exact = matrix.as_exact_matrix().expect("rectangular");
    for group in groups.basis.iter().chain(&groups.primitive_basis) {
        let image = exact.apply(&group.exponents).expect("shapes compose");
        let zero = image.iter().all(Zero::is_zero);
        println!(
            "      M · {:<28} = {}   {}",
            group.render(&groups.quantities),
            render_word(&image),
            if zero { "ANNIHILATES" } else { "RESIDUAL" }
        );
        if !zero {
            failures.push(format!(
                "the group {} left a residual",
                group.render(&groups.quantities)
            ));
        }
    }

    println!("\n=== 2. the basis is a receiver coordinate; the span is the invariant ===\n");
    println!("    the two groups the physics is stated in:");
    let over_rest = word(&[1, -1, -2, 0]); //  E / m c^2
    let over_momentum = word(&[1, 0, -1, -1]); //  E / p c
    if !membership(&groups, "E/mc^2", &over_rest) {
        failures.push("E/mc^2 is not in the returned span".to_owned());
    }
    if !membership(&groups, "E/pc", &over_momentum) {
        failures.push("E/pc is not in the returned span".to_owned());
    }
    println!("\n    and a word that is not dimensionless, which must NOT be in the span:");
    if membership(&groups, "E/m", &word(&[1, -1, 0, 0])) {
        failures.push("E/m was admitted into the span".to_owned());
    }

    println!("\n    second frame — the declared quantities permuted to (p, c, m, E):");
    let permuted = mechanics.matrix(["p", "c", "m", "E"]);
    let permuted_groups = permuted.buckingham().expect("returns");
    report(&permuted_groups);
    let moved = permuted_groups.basis[0].exponents != groups.basis[0].exponents;
    println!(
        "    the basis words {} under the permutation, and the rank and count do not",
        if moved { "MOVED" } else { "did not move" }
    );
    if !moved {
        failures.push("the permutation frame acted trivially, so it gauges nothing".to_owned());
    }
    if permuted_groups.rank != groups.rank
        || permuted_groups.independent_group_count != groups.independent_group_count
    {
        failures.push("the rank or the count moved under a relabelling".to_owned());
    }
    // (E, m, c, p) -> (p, c, m, E) sends the word (a,b,c,d) to (d,c,b,a).
    let permute = |values: &[Rat]| {
        vec![
            values[3].clone(),
            values[2].clone(),
            values[1].clone(),
            values[0].clone(),
        ]
    };
    if !membership(&permuted_groups, "E/mc^2", &permute(&over_rest)) {
        failures.push("E/mc^2 left the span under a relabelling".to_owned());
    }
    if !membership(&permuted_groups, "E/pc", &permute(&over_momentum)) {
        failures.push("E/pc left the span under a relabelling".to_owned());
    }

    println!("\n    third frame — the declared BASE UNITS permuted to (T, L, M):");
    let rebased = Mechanics::declare(["T", "L", "M"]);
    let rebased_groups = rebased
        .matrix(["E", "m", "c", "p"])
        .buckingham()
        .expect("returns");
    report(&rebased_groups);
    if rebased_groups.rank != groups.rank {
        failures.push("the rank moved when the base units were relabelled".to_owned());
    }
    if rebased_groups.basis != groups.basis {
        failures
            .push("the pi-group basis moved when only the base units were relabelled".to_owned());
    }
    // A gauge whose group acts trivially on the declared material is not a gauge. Permuting the
    // ROWS cannot move the kernel — that is the invariance being read — so the frame is only
    // evidence if it moves something. It moves the LEFT kernel, and that is required here.
    let left_moved =
        rebased_groups.undetectable_base_rescalings != groups.undetectable_base_rescalings;
    println!(
        "    the pi-group basis is UNMOVED by a row relabelling (row operations do not touch\n\
         \x20   ker M), and the left kernel {} — {} to {} — so the frame is not vacuous.",
        if left_moved { "MOVED" } else { "did not move" },
        render_word(&groups.undetectable_base_rescalings[0]),
        render_word(&rebased_groups.undetectable_base_rescalings[0])
    );
    if !left_moved {
        failures.push(
            "the base-unit frame acted trivially on everything, so it gauges nothing".to_owned(),
        );
    }

    println!("\n=== 3. the left kernel IS 'set c = 1', computed ===\n");
    println!(
        "    {} rescaling(s) of (M, L, T) that no declared quantity can detect:",
        groups.undetectable_rescaling_count
    );
    for rescaling in &groups.undetectable_base_rescalings {
        println!("      {}", render_word(rescaling));
    }
    println!(
        "\n    reading it: L -> lambda·L and T -> lambda·T together leaves every one of E, m, c, p\n\
         \x20   dimensionally unmoved, because each is M^a (L/T)^b. That is why c may be set to 1 —\n\
         \x20   and k - rank = {} is exactly how much of the declared base this material cannot see.\n\
         \x20   The check: each rescaling applied to every declared column must return zero.",
        groups.undetectable_rescaling_count
    );
    for rescaling in &groups.undetectable_base_rescalings {
        for (name, dimension) in groups.quantities.iter().zip(matrix.dimensions()) {
            let pairing = dimension
                .exponents()
                .iter()
                .zip(rescaling)
                .fold(Rat::zero(), |sum, (left, right)| sum + left * right);
            println!(
                "      <{}, [{}]> = {}",
                render_word(rescaling),
                name,
                format_rat(&pairing)
            );
            if !pairing.is_zero() {
                failures.push(format!("the rescaling is detected by {name}"));
            }
        }
    }

    println!("\n=== 4. the refusals ===\n");
    let length = Quantity::new(whole(3), mechanics.base.unit("L").expect("declared"));
    let time = Quantity::new(whole(3), mechanics.base.unit("T").expect("declared"));
    match length.sum(&time) {
        Ok(returned) => {
            failures.push(format!("a length plus a time returned {returned}"));
        }
        Err(refusal) => println!("    3 [L]  +  3 [T]        REFUSED: {refusal}"),
    }
    println!(
        "    3 [L] <=> 3 [T]        {:?}   (not unequal — the question has no answer here)",
        length.compare(&time)
    );
    if length.compare(&time) != ExactOrdering::Open {
        failures.push("mismatched dimensions did not return Open".to_owned());
    }
    let longer = Quantity::new(whole(4), mechanics.base.unit("L").expect("declared"));
    println!(
        "    3 [L] <=> 4 [L]        {:?}   (same dimension, so it answers)",
        length.compare(&longer)
    );
    let energy = Quantity::new(whole(5), mechanics.energy.clone());
    let momentum = Quantity::new(whole(3), mechanics.momentum.clone());
    match energy.sum(&momentum) {
        Ok(_) => failures.push("E + p was admitted".to_owned()),
        Err(refusal) => println!("    E  +  p                REFUSED: {refusal}"),
    }
    let erased = Quantity::new(Rat::one(), mechanics.base.dimensionless());
    match Cast::declare("c", erased) {
        Ok(_) => failures.push("a dimensionless cast was declared".to_owned()),
        Err(refusal) => println!("    declare c with no dimension   REFUSED: {refusal}"),
    }
    match Quantity::new(whole(7), mechanics.energy.clone()).rational() {
        Ok(_) => failures.push("a bare rational was read off a dimensioned quantity".to_owned()),
        Err(refusal) => println!("    read 7 [M L^2 T^-2] as a bare rational   REFUSED: {refusal}"),
    }

    println!("\n=== 5. the controls that can fail ===\n");
    let base = mechanics.base.clone();
    let mass_column = (
        "m".to_owned(),
        base.dimension_of(&[("M", whole(1))]).unwrap(),
    );
    let length_column = (
        "l".to_owned(),
        base.dimension_of(&[("L", whole(1))]).unwrap(),
    );
    let time_column = (
        "t".to_owned(),
        base.dimension_of(&[("T", whole(1))]).unwrap(),
    );
    let speed_column = ("c".to_owned(), mechanics.speed.clone());
    let energy_column = ("E".to_owned(), mechanics.energy.clone());
    let mut columns = vec![mass_column, length_column, time_column];
    let mut counts = Vec::new();
    for addition in [None, Some(speed_column), Some(energy_column)] {
        if let Some(column) = addition {
            columns.push(column);
        }
        let swept = DimensionMatrix::declare(base.clone(), columns.clone())
            .expect("declared")
            .buckingham()
            .expect("returns");
        let names: Vec<String> = swept.quantities.clone();
        println!(
            "    ({:<14})  n = {}  rank = {}  ->  {} group(s)   {}",
            names.join(", "),
            names.len(),
            swept.rank,
            swept.independent_group_count,
            if swept.basis.is_empty() {
                "(none)".to_owned()
            } else {
                swept
                    .primitive_basis
                    .iter()
                    .map(|group| group.render(&names))
                    .collect::<Vec<String>>()
                    .join("   ")
            }
        );
        counts.push(swept.independent_group_count);
    }
    if counts != vec![0, 1, 2] {
        failures.push(format!(
            "the count sweep returned {counts:?}, not [0, 1, 2]"
        ));
    }
    println!(
        "    the count moved {counts:?} with the material — a full-rank matrix returns ZERO groups."
    );

    println!("\n=== 6. the relation, exact over Q ===\n");
    let cast = mechanics.cast();
    println!(
        "    the cast, declared:  {}  with dimension [{}]",
        cast.quantity(),
        cast.dimension()
    );
    let mass_four = Quantity::new(whole(4), mechanics.mass.clone());
    let application = cast.apply(&mass_four, &whole(2)).expect("applies");
    println!("    {}\n", application.render());

    println!(
        "      beta      gamma     m    p    E    mc^2   pc    (mc^2/E)^2 + (pc/E)^2   t = tan(theta/2)"
    );
    for (mass, momentum_value, energy_value, beta) in [
        (4_i64, 3_i64, 5_i64, rational(3, 5)),
        (12, 5, 13, rational(5, 13)),
        (7, 0, 7, Rat::zero()),
        (4, 3, 6, rational(3, 5)), // the perturbed control: E is wrong on purpose
    ] {
        let perturbed =
            energy_value * energy_value != mass * mass + momentum_value * momentum_value;
        let rest = cast
            .apply(
                &Quantity::new(whole(mass), mechanics.mass.clone()),
                &whole(2),
            )
            .expect("applies")
            .returned;
        let carried = cast
            .apply(
                &Quantity::new(whole(momentum_value), mechanics.momentum.clone()),
                &whole(1),
            )
            .expect("applies")
            .returned;
        let total = Quantity::new(whole(energy_value), mechanics.energy.clone());
        assert_eq!(rest.dimension(), total.dimension(), "mc^2 is an energy");
        assert_eq!(carried.dimension(), total.dimension(), "pc is an energy");

        let cosine = rest
            .ratio(&total)
            .expect("lawful")
            .rational()
            .expect("dimensionless")
            .clone();
        let sine = carried
            .ratio(&total)
            .expect("lawful")
            .rational()
            .expect("dimensionless")
            .clone();
        let norm = &cosine * &cosine + &sine * &sine;
        let half_turn = &sine / (Rat::one() + &cosine);
        let gamma = Rat::one() / &cosine;
        println!(
            "      {:<8}  {:<8}  {:<3}  {:<3}  {:<3}  {:<5}  {:<4}  {:<22}  {}{}",
            format_rat(&beta),
            format_rat(&gamma),
            mass,
            momentum_value,
            energy_value,
            format_rat(rest.parts().0),
            format_rat(carried.parts().0),
            format_rat(&norm),
            format_rat(&half_turn),
            if perturbed {
                "   <- PERTURBED CONTROL"
            } else {
                ""
            }
        );
        if perturbed {
            if norm.is_one() {
                failures.push("the perturbed control still returned a unit norm".to_owned());
            }
            continue;
        }
        if !norm.is_one() {
            failures.push(format!(
                "the non-dimensionalisation returned {} rather than 1",
                format_rat(&norm)
            ));
        }
        if sine != beta {
            failures.push(format!(
                "pc/E returned {} rather than beta = {}",
                format_rat(&sine),
                format_rat(&beta)
            ));
        }
        // E^2 = (mc^2)^2 + (pc)^2, as quantities, with dimensions carried through.
        let left = total.powed(&whole(2)).expect("squares");
        let right = rest
            .powed(&whole(2))
            .expect("squares")
            .sum(&carried.powed(&whole(2)).expect("squares"))
            .expect("the three terms share one dimension, which is what makes the sum legal");
        if left != right {
            failures.push("E^2 = (mc^2)^2 + (pc)^2 did not return exactly".to_owned());
        }
    }

    println!(
        "\n    every figure above is an exact rational. No float, no sqrt, no tolerance: over Q the\n\
         \x20   relation is a PYTHAGOREAN TRIPLE, and (3,4,5) and (5,12,13) are the two taken here.\n\
         \x20   beta = 0 returns t = 0 exactly. E = mc^2 IS theta = 0."
    );

    println!(
        "\n    and the second group leaves the chart there, which is why the shorthand looks total:"
    );
    let at_rest = vec![
        Quantity::new(whole(7), mechanics.energy.clone()),
        Quantity::new(whole(7), mechanics.mass.clone()),
        Quantity::new(Rat::one(), mechanics.speed.clone()),
        Quantity::new(Rat::zero(), mechanics.momentum.clone()),
    ];
    let group_over_rest = PiGroup::new(over_rest.clone());
    let group_over_momentum = PiGroup::new(over_momentum.clone());
    println!(
        "      E/mc^2 at p = 0   ->  {}",
        format_rat(
            group_over_rest
                .evaluate(&at_rest)
                .expect("returns")
                .rational()
                .expect("dimensionless")
        )
    );
    match group_over_momentum.evaluate(&at_rest) {
        Ok(returned) => {
            failures.push(format!("E/pc returned {returned} at p = 0"));
        }
        Err(refusal) => println!("      E/pc   at p = 0   ->  REFUSED: {refusal}"),
    }
    println!(
        "      pc/E   at p = 0   ->  {}   (beta = 0; the group is there, its inverse is not)",
        format_rat(
            group_over_momentum
                .negated()
                .evaluate(&at_rest)
                .expect("returns")
                .rational()
                .expect("dimensionless")
        )
    );

    // The one refusal species the evaluator must still exhibit: a half-integer exponent word asks
    // for a root the magnitude does not have. This is why the PRIMITIVE basis is the evaluable one.
    println!("\n    the raw elimination basis is not evaluable over Q, and says so:");
    let values = vec![
        Quantity::new(whole(5), mechanics.energy.clone()),
        Quantity::new(whole(4), mechanics.mass.clone()),
        Quantity::new(Rat::one(), mechanics.speed.clone()),
        Quantity::new(whole(3), mechanics.momentum.clone()),
    ];
    match groups.basis[0].evaluate(&values) {
        Ok(returned) => println!(
            "      {} -> {returned}",
            groups.basis[0].render(&groups.quantities)
        ),
        Err(refusal) => println!(
            "      {:<28} REFUSED: {refusal}",
            groups.basis[0].render(&groups.quantities)
        ),
    }
    let primitive = &groups.primitive_basis[0];
    println!(
        "      {:<28} -> {}",
        primitive.render(&groups.quantities),
        format_rat(
            primitive
                .evaluate(&values)
                .expect("the primitive word evaluates")
                .rational()
                .expect("dimensionless")
        )
    );

    println!("\n=== SUMMARY ===\n");
    println!(
        "    (E, m, c, p) over (M, L, T): rank {} by three independent readings, {} pi-groups,\n\
         \x20   {} undetectable base rescaling, {} exact eliminations, zero floats.",
        groups.rank,
        groups.independent_group_count,
        groups.undetectable_rescaling_count,
        groups.eliminations
    );
    if failures.is_empty() {
        println!("    every declared check returned. 0 failures.");
    } else {
        println!("    {} FAILURE(S):", failures.len());
        for failure in &failures {
            println!("      - {failure}");
        }
        std::process::exit(1);
    }

    // Touch the error type so a reader can see the refusal species enumerated in one place.
    let _species: [&str; 4] = [
        stringify!(QuantityError::DimensionMismatch),
        stringify!(QuantityError::CastErasesTheDimension),
        stringify!(QuantityError::NoRationalRoot),
        stringify!(QuantityError::RankDisagreement),
    ];
    let _: fn() -> QuantityError = || QuantityError::DivisionByZero;
}

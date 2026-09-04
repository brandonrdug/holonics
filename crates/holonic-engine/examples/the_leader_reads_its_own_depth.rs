//! The witness depth and the grain, lifted off the organ and read off the material — and the
//! difference that excision makes, exhibited on material that separates before from after.
//!
//! ## What was authored, and why it was not hygiene
//!
//! `crates/holonic-engine/src/derivation_integral.rs` carried two levels until 2026-08-09:
//!
//! ```text
//!   pub const LEADER_GRAIN_RECIPROCAL: i64   = 3;
//!   pub const LEADER_WITNESS_DEPTH:    usize = 1;
//! ```
//!
//! `leader_quadrature`'s own header states the mechanism the second one contradicts: *"the material
//! boundary at a tip is its **local jet**, and every extension rebases it by an exact Taylor shift.
//! The jet the leader reads at extension `k+1` is literally not the jet it read at `k`"*. A witness
//! depth of one licenses a RIDE on the strength of a single agreement, which is a claim that the
//! jet has stopped moving made from one comparison.
//!
//! The same header's ruling 2 quotes the Brandon-ratified
//! `research/records/2026-07-17_THE_LEADER_GROWS_THE_CHANNEL_THE_RETURN_TRAVELS_THE_FOUND_PATH.md`
//! banning *"No random route chooser, target search, global path, standing-wave cause, or
//! **instantaneous return**"*, and `docs/canon/THE_AUTHORED_LEVEL.md` §5.1 names this excision on the
//! same reading: *"what the material stopped the leader at … **A leader whose witness depth is one
//! takes a single step; that is not a leader.**"*
//!
//! ## What replaces them
//!
//! The mechanism that transforms information during transport here is the exact Taylor rebase.
//! `LocalJet::rebase_movement_depth` is the order at which it can no longer contribute a
//! difference: the jet's **rank**, because coefficient `t` of `j.rebase(σ)` is a polynomial in `σ`
//! of degree `m−1−t`, and the `m`-th forward difference of a degree-`(m−1)` family vanishes while
//! the `(m−1)`-th does not. **One is right on a constant jet and wrong on every other**, which is
//! precisely the distinction a constant could not make.
//!
//! The grain follows from the same depth. A leader entering a germ of extent `E` at grain `g` and
//! effective depth `d` founds `d` extensions before the agreement lineage licenses a ride, so a
//! ride exists iff `E − d·g > g`, i.e. `g < E/(d+1)`, at scale `E/g − d`. **That bound is open**,
//! so the material names an interval and not a number; the coarsest grain whose scale is a whole
//! number of grains takes the least integer above one, and `MaterialBoundary::declared_grain` is
//! `finest_standing_extent / (jet_aperture + 2)`.
//!
//! ## What this driver returns
//!
//! Four sections, each a measurement with its own control:
//!
//! 1. **The theorem, computed.** The annihilating difference order of the rebased jet sequence,
//!    taken directly, against the rank. The control is that order `m−1` does *not* annihilate.
//! 2. **The orbit of the excision under `GermBounded` and `GrainOnly`.** The return holds; the
//!    lineage moves. Both are printed.
//! 3. **The orbit past the declared aperture, where the depth decides the answer.** On
//!    `reverting_material` under `UnclampedAncestry` the authored depth of one returns `49/2`
//!    against a true `23`. That is the pin deciding a return, and the refusal the excision installs
//!    names it.
//! 4. **`derivation_integral`'s own material**, where the derived levels reproduce `1/3` and `1`
//!    exactly — the outcome `docs/canon/THE_CONTAMINANT_PROTOCOL.md` §4 calls *the return holds, the
//!    reachable population grows* — together with the material that would move them.

use std::error::Error;

use holonic_engine::leader_quadrature::{
    LeaderError, LeaderLaw, LocalJet, MaterialBoundary, RationalGerm, RideDiscipline, WitnessDepth,
    germwise_oracle_area, integrate_by_leaders, path_disagreement,
};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::{Rat, format_rat, integer, rat};

// ---------------------------------------------------------------------------------------------
// declared material

fn jet(coefficients: &[(i64, i64)]) -> LocalJet {
    LocalJet::new(
        coefficients
            .iter()
            .map(|(numerator, denominator)| rat(*numerator, *denominator))
            .collect::<Vec<Rat>>(),
    )
    .expect("a jet carries at least one coefficient")
}

fn germ(extent: Rat, coefficients: &[(i64, i64)]) -> RationalGerm {
    RationalGerm::new(extent, jet(coefficients)).expect("a germ conducts over a positive extent")
}

fn boundary(germs: Vec<RationalGerm>) -> MaterialBoundary {
    MaterialBoundary::new(germs).expect("a non-empty material boundary")
}

/// `f = t` on `[0,3)`, `f = 2` on `[3,4)`, `f = t` on `[4,7)`. Hand figure `23`.
///
/// This is the separating material and it is separating for a stated reason: its jet at offset `0`
/// is `[0,1]` and at offset `1` it is `[1,1]`. **The jet moved between extension one and extension
/// two**, so an agreement lineage of length one has witnessed no limit.
fn reverting_material() -> (MaterialBoundary, Rat) {
    (
        boundary(vec![
            germ(integer(3), &[(0, 1), (1, 1)]),
            germ(integer(1), &[(2, 1)]),
            germ(integer(3), &[(4, 1), (1, 1)]),
        ]),
        integer(23),
    )
}

/// Three germs of ranks 2, 1, 2 with extents that are not grain multiples. Hand figure `799/72`.
fn unaligned_piecewise() -> (MaterialBoundary, Rat) {
    (
        boundary(vec![
            germ(rat(7, 3), &[(0, 1), (1, 1)]),
            germ(rat(4, 5), &[(5, 2)]),
            germ(rat(3, 2), &[(11, 4), (2, 1)]),
        ]),
        rat(799, 72),
    )
}

/// `f = x` on `[0,2)`, then `g(u) = 7 + 3u^2` on the next `4`. Ranks 2 and 3. Hand figure `94`.
fn abrupt_material() -> (MaterialBoundary, Rat) {
    (
        boundary(vec![
            germ(integer(2), &[(0, 1), (1, 1)]),
            germ(integer(4), &[(7, 1), (0, 1), (3, 1)]),
        ]),
        integer(94),
    )
}

/// The shape `derivation_integral::route_material` builds: one **unit** germ per path step, each
/// carrying that step's increment as a **constant** jet. Increments `4, 1, 5`, so area `10`.
fn route_shaped_material() -> (MaterialBoundary, Rat) {
    (
        boundary(vec![
            germ(integer(1), &[(4, 1)]),
            germ(integer(1), &[(1, 1)]),
            germ(integer(1), &[(5, 1)]),
        ]),
        integer(10),
    )
}

/// The same route shape with material the *route* cannot currently produce: germs of unequal
/// extent carrying jets of rank two. This is what would move `derivation_integral`'s derived
/// levels, and it is declared here so the third outcome of §4 is distinguishable from the second.
fn route_shaped_material_with_moving_jets() -> (MaterialBoundary, Rat) {
    // `f = 4 + t` over `[0,2)`  ->  8 + 2 = 10
    // `f = 1`     over `[2,3)`  ->  1
    // `f = 5 + 2t` over `[3,6)` ->  15 + 9 = 24
    (
        boundary(vec![
            germ(integer(2), &[(4, 1), (1, 1)]),
            germ(integer(1), &[(1, 1)]),
            germ(integer(3), &[(5, 1), (2, 1)]),
        ]),
        integer(35),
    )
}

fn every_material() -> Vec<(&'static str, MaterialBoundary, Rat)> {
    let mut declared = Vec::new();
    let (material, area) = reverting_material();
    declared.push(("reverting_material", material, area));
    let (material, area) = unaligned_piecewise();
    declared.push(("unaligned_piecewise", material, area));
    let (material, area) = abrupt_material();
    declared.push(("abrupt_material", material, area));
    let (material, area) = route_shaped_material();
    declared.push(("route_shaped (unit germs, rank 1)", material, area));
    let (material, area) = route_shaped_material_with_moving_jets();
    declared.push(("route_shaped (moving jets)", material, area));
    declared
}

// ---------------------------------------------------------------------------------------------
// controls

struct Controls {
    held: usize,
    failed: Vec<String>,
}

impl Controls {
    fn new() -> Self {
        Self {
            held: 0,
            failed: Vec::new(),
        }
    }

    fn check(&mut self, name: &str, holds: bool, saying: &str) {
        if holds {
            self.held += 1;
            println!("    HOLDS   {name}");
        } else {
            self.failed.push(name.to_owned());
            println!("    FAILED  {name}");
        }
        println!("            {saying}");
    }
}

// ---------------------------------------------------------------------------------------------
// 1. the theorem, computed rather than asserted

fn padded(jet: &LocalJet, rank: usize) -> Vec<Rat> {
    let mut coefficients = jet.coefficients().to_vec();
    coefficients.resize(rank, Rat::zero());
    coefficients
}

fn forward_difference(rows: &[Vec<Rat>]) -> Vec<Vec<Rat>> {
    rows.windows(2)
        .map(|pair| {
            pair[1]
                .iter()
                .zip(&pair[0])
                .map(|(next, here)| next - here)
                .collect()
        })
        .collect()
}

fn all_zero(rows: &[Vec<Rat>]) -> bool {
    rows.iter()
        .all(|row| row.iter().all(|value| value.is_zero()))
}

/// The order at which the forward difference of the rebased-jet sequence annihilates, taken
/// directly from the sequence. This is the quantity `rebase_movement_depth` claims to be.
fn measured_annihilating_order(source: &LocalJet, step: &Rat) -> usize {
    let rank = source.rank();
    let mut offset = Rat::zero();
    let mut rows: Vec<Vec<Rat>> = Vec::new();
    for _ in 0..rank + 3 {
        rows.push(padded(&source.rebase(&offset), rank));
        offset = &offset + step;
    }
    let mut order = 0usize;
    while !all_zero(&rows) {
        rows = forward_difference(&rows);
        order += 1;
    }
    order
}

fn the_theorem(controls: &mut Controls) {
    println!("\n  1. THE DEPTH IS THE ORDER AT WHICH THE REBASE STOPS CONTRIBUTING");
    println!(
        "\n     {:<34} {:>5} {:>7} {:>11} {:>13}",
        "jet", "rank", "step", "annihilates", "one order less"
    );

    let declared = [
        ("3 (constant)", jet(&[(3, 1)])),
        ("t - 1", jet(&[(-1, 1), (1, 1)])),
        ("t^2", jet(&[(0, 1), (0, 1), (1, 1)])),
        ("1 + t + t^2 + t^3", jet(&[(1, 1), (1, 1), (1, 1), (1, 1)])),
        (
            "2 - 3t + 4t^2 - 5t^3 + 6t^4",
            jet(&[(2, 1), (-3, 1), (4, 1), (-5, 1), (6, 1)]),
        ),
    ];

    let mut every_order_matches = true;
    let mut every_lower_order_survives = true;
    for (name, source) in &declared {
        for (numerator, denominator) in [(1, 1), (1, 3), (22, 7)] {
            let step = rat(numerator, denominator);
            let order = measured_annihilating_order(source, &step);
            let rank = source.rank();
            every_order_matches &= order == rank;
            every_order_matches &= source.rebase_movement_depth() == rank;
            // The control: the difference one order below must NOT annihilate, or `rank` would be
            // an over-estimate and the equality above would be free.
            let survives_below = order > rank - 1;
            every_lower_order_survives &= survives_below;
            println!(
                "     {name:<34} {rank:>5} {:>7} {order:>11} {:>13}",
                format_rat(&step),
                if survives_below {
                    "survives"
                } else {
                    "VANISHED"
                }
            );
        }
    }

    controls.check(
        "the measured annihilating order equals the jet rank on every declared jet and step",
        every_order_matches,
        "rebase_movement_depth is computed from the theorem; this takes the finite differences",
    );
    controls.check(
        "the difference one order below the rank does not annihilate",
        every_lower_order_survives,
        "without this the rank could be any over-estimate and the equality above would be free",
    );
}

// ---------------------------------------------------------------------------------------------
// 2. the orbit inside the declared aperture

fn the_orbit_inside_the_aperture(controls: &mut Controls) {
    println!("\n  2. INSIDE THE APERTURE: THE RETURN HOLDS, THE LINEAGE MOVES");
    println!(
        "\n     {:<34} {:>7} {:>6} {:>6} {:>6} {:>6} {:>10} {:>10}",
        "material / depth", "grain", "depth", "ext", "found", "ride", "area", "hand"
    );

    let mut every_area_holds = true;
    let mut some_lineage_moved = false;
    for (name, material, hand) in every_material() {
        let grain = rat(1, 4);
        let authored = integrate_by_leaders(
            &material,
            &LeaderLaw::new(
                grain.clone(),
                RideDiscipline::GermBounded,
                WitnessDepth::Declared(1),
            ),
        );
        let read_off = integrate_by_leaders(
            &material,
            &LeaderLaw::new(
                grain.clone(),
                RideDiscipline::GermBounded,
                WitnessDepth::ReadOffTheJet,
            ),
        )
        .expect("the material's own depth is always admissible");

        match &authored {
            Ok(authored) => {
                println!(
                    "     {:<34} {:>7} {:>6} {:>6} {:>6} {:>6} {:>10} {:>10}",
                    format!("{name}  authored depth 1"),
                    format_rat(&grain),
                    1,
                    authored.extension_count(),
                    authored.found_count(),
                    authored.ride_count(),
                    format_rat(&authored.area),
                    format_rat(&hand)
                );
                every_area_holds &= authored.area == hand;
                some_lineage_moved |= authored.extension_spans() != read_off.extension_spans();
            }
            Err(LeaderError::WitnessDepthBelowMaterial { required, .. }) => {
                println!(
                    "     {:<34} {:>7} {:>6} {:>6} {:>6} {:>6} {:>10} {:>10}",
                    format!("{name}  authored depth 1"),
                    format_rat(&grain),
                    1,
                    "REFUSED",
                    format!("needs {required}"),
                    "-",
                    "-",
                    format_rat(&hand)
                );
                some_lineage_moved = true;
            }
            Err(other) => panic!("unexpected refusal: {other}"),
        }

        println!(
            "     {:<34} {:>7} {:>6} {:>6} {:>6} {:>6} {:>10} {:>10}",
            format!("{name}  read off the jet"),
            format_rat(&grain),
            read_off.material_witness_depth,
            read_off.extension_count(),
            read_off.found_count(),
            read_off.ride_count(),
            format_rat(&read_off.area),
            format_rat(&hand)
        );
        every_area_holds &= read_off.area == hand;
        every_area_holds &= read_off.area == germwise_oracle_area(&material);
    }

    controls.check(
        "inside the aperture the excision does not move the returned rational",
        every_area_holds,
        "the self-similarity law says the depth declares the lineage; here it is measured",
    );
    controls.check(
        "the excision does move the lineage on at least one declared material",
        some_lineage_moved,
        "an excision whose orbit is empty on every material would be bookkeeping, and must say so",
    );
}

// ---------------------------------------------------------------------------------------------
// 3. past the aperture, where the depth decides the answer

fn where_the_depth_decides_the_answer(controls: &mut Controls) {
    println!("\n  3. PAST THE APERTURE: THE AUTHORED DEPTH WAS DECIDING THE RETURN");

    let (material, truth) = reverting_material();
    let at_zero = material.standing_at(&Rat::zero()).expect("inside").jet;
    let at_one = material.standing_at(&Rat::one()).expect("inside").jet;
    println!("\n     the separating material, exhibited:");
    println!(
        "       jet at extension 1 (offset 0)   {:?}",
        at_zero
            .coefficients()
            .iter()
            .map(format_rat)
            .collect::<Vec<_>>()
    );
    println!(
        "       jet at extension 2 (offset 1)   {:?}",
        at_one
            .coefficients()
            .iter()
            .map(format_rat)
            .collect::<Vec<_>>()
    );
    println!(
        "       they differ: {}     rebase_movement_depth: {}",
        at_zero != at_one,
        at_zero.rebase_movement_depth()
    );

    println!(
        "\n     {:<34} {:>8} {:>6} {:>6} {:>10} {:>10}",
        "declaration", "grain", "ext", "ride", "area", "truth"
    );
    let mut rows: Vec<(String, Option<Rat>)> = Vec::new();
    for declared in 1..=4usize {
        let attempt = integrate_by_leaders(
            &material,
            &LeaderLaw::new(
                Rat::one(),
                RideDiscipline::UnclampedAncestry,
                WitnessDepth::Declared(declared),
            ),
        );
        match attempt {
            Ok(quadrature) => {
                println!(
                    "     {:<34} {:>8} {:>6} {:>6} {:>10} {:>10}",
                    format!("Declared({declared})"),
                    format_rat(&quadrature.grain),
                    quadrature.extension_count(),
                    quadrature.ride_count(),
                    format_rat(&quadrature.area),
                    format_rat(&truth)
                );
                rows.push((format!("Declared({declared})"), Some(quadrature.area)));
            }
            Err(LeaderError::WitnessDepthBelowMaterial {
                offset,
                declared,
                required,
            }) => {
                println!(
                    "     {:<34} {:>8} {:>6} {:>6} {:>10} {:>10}",
                    format!("Declared({declared})"),
                    format_rat(&Rat::one()),
                    "REFUSED",
                    "-",
                    format!("needs {required}"),
                    format_rat(&truth)
                );
                println!(
                    "            at offset {}: the rebase is still contributing after {declared} \
                     agreement(s)",
                    format_rat(&offset)
                );
                rows.push((format!("Declared({declared})"), None));
            }
            Err(other) => panic!("unexpected refusal: {other}"),
        }
    }

    let read_off = integrate_by_leaders(
        &material,
        &LeaderLaw::new(
            Rat::one(),
            RideDiscipline::UnclampedAncestry,
            WitnessDepth::ReadOffTheJet,
        ),
    )
    .expect("the material's own depth is always admissible");
    println!(
        "     {:<34} {:>8} {:>6} {:>6} {:>10} {:>10}",
        "ReadOffTheJet",
        format_rat(&read_off.grain),
        read_off.extension_count(),
        read_off.ride_count(),
        format_rat(&read_off.area),
        format_rat(&truth)
    );

    let returned: Vec<&Rat> = rows.iter().filter_map(|(_, area)| area.as_ref()).collect();
    let distinct = returned
        .iter()
        .any(|area| **area != **returned.first().expect("at least one admitted depth"));

    controls.check(
        "the declared witness depth moves the returned rational past the aperture",
        distinct,
        "a level that changes the answer is deciding it; this is the orbit the excision is graded by",
    );
    controls.check(
        "the depth the pin authored is refused on the material that separates it",
        rows.iter()
            .any(|(name, area)| name == "Declared(1)" && area.is_none()),
        "one agreement on a rank-two jet is an instantaneous measurement and cannot be made",
    );

    let two = integrate_by_leaders(
        &material,
        &LeaderLaw::new(
            Rat::one(),
            RideDiscipline::UnclampedAncestry,
            WitnessDepth::Declared(2),
        ),
    )
    .expect("two is the material's requirement here");
    let three = integrate_by_leaders(
        &material,
        &LeaderLaw::new(
            Rat::one(),
            RideDiscipline::UnclampedAncestry,
            WitnessDepth::Declared(3),
        ),
    )
    .expect("three is above the material's requirement");
    println!(
        "\n     path_disagreement(Declared(2), Declared(3)) = {}   (truth {}, wrong return {})",
        format_rat(&path_disagreement(&two, &three)),
        format_rat(&truth),
        format_rat(&two.area)
    );
    controls.check(
        "the measured holonomy of the aperture violation is exhibited, not narrated",
        path_disagreement(&two, &three) == rat(3, 2) && three.area == truth,
        "the residual is returned by the organ's own path_disagreement over two declared depths",
    );
}

// ---------------------------------------------------------------------------------------------
// 4. derivation_integral's own material

fn the_route_material(controls: &mut Controls) {
    println!("\n  4. derivation_integral's ROUTE MATERIAL: THE DERIVED LEVELS REPRODUCE THE PIN");

    let (route, area) = route_shaped_material();
    let (moving, moving_area) = route_shaped_material_with_moving_jets();

    println!(
        "\n     {:<34} {:>12} {:>10} {:>8} {:>8} {:>10}",
        "material", "finest extent", "aperture", "grain", "depth", "area"
    );
    let mut rows = Vec::new();
    for (name, material, hand) in [
        ("route_shaped (unit germs, rank 1)", &route, &area),
        ("route_shaped (moving jets)", &moving, &moving_area),
    ] {
        let law = LeaderLaw::read_off(material, RideDiscipline::GermBounded);
        let quadrature = integrate_by_leaders(material, &law).expect("lawful");
        println!(
            "     {:<34} {:>12} {:>10} {:>8} {:>8} {:>10}",
            name,
            format_rat(material.finest_standing_extent()),
            material.jet_aperture(),
            format_rat(&law.grain),
            quadrature.material_witness_depth,
            format_rat(&quadrature.area)
        );
        assert_eq!(&quadrature.area, hand, "{name}: the hand figure moved");
        rows.push((law.grain.clone(), quadrature.material_witness_depth));
    }

    println!(
        "\n     the pin said grain 1/3 and depth 1. The route material returns {} and {}.",
        format_rat(&rows[0].0),
        rows[0].1
    );
    println!(
        "     Material whose jets move returns {} and {} from the same two rules.",
        format_rat(&rows[1].0),
        rows[1].1
    );

    controls.check(
        "the derived levels reproduce the excised pin exactly on the material it was written for",
        rows[0].0 == rat(1, 3) && rows[0].1 == 1,
        "a derivation that explains the old value as a special case is stronger than one that \
         replaces it",
    );
    controls.check(
        "and they move on material the same two rules admit",
        rows[1].0 != rows[0].0 && rows[1].1 != rows[0].1,
        "otherwise this is the third outcome — the level was inert — and would have to say so",
    );

    // The uniform half: at the material's own grain, EVERY ride carries at least one rank step.
    let one_rank_step = Rat::from_integer(BigInt::from(2));
    let mut every_ride_clears_a_rank_step = true;
    let mut smallest_scale: Option<Rat> = None;
    for (_, material, _) in every_material() {
        let law = LeaderLaw::read_off(&material, RideDiscipline::GermBounded);
        let quadrature = integrate_by_leaders(&material, &law).expect("lawful");
        for witness in &quadrature.scale_witnesses {
            every_ride_clears_a_rank_step &= witness.scale >= one_rank_step;
            smallest_scale = Some(match smallest_scale {
                None => witness.scale.clone(),
                Some(least) if witness.scale < least => witness.scale.clone(),
                Some(least) => least,
            });
        }
    }
    println!(
        "\n     smallest ride scale over every declared material at its own grain: {}",
        smallest_scale.as_ref().map(format_rat).unwrap_or_default()
    );
    controls.check(
        "at the grain the material declares, every ride carries at least one rank step",
        every_ride_clears_a_rank_step && smallest_scale.is_some(),
        "this is what closes the open bound g < E/(d+1): the least integer scale above one",
    );

    // The tight half: on a single standing form the bound is ATTAINED — scale exactly two — and
    // one step coarser, at the open bound E/(d+1), that form does not ride at all. Without both,
    // `+ 2` could be any amount of slack.
    let single_forms: Vec<(&str, MaterialBoundary)> = vec![
        ("f = 3 over 2", boundary(vec![germ(integer(2), &[(3, 1)])])),
        (
            "f = 5t over 3",
            boundary(vec![germ(integer(3), &[(0, 1), (5, 1)])]),
        ),
        (
            "f = t^2 over 2",
            boundary(vec![germ(integer(2), &[(0, 1), (0, 1), (1, 1)])]),
        ),
    ];
    println!(
        "\n     {:<24} {:>6} {:>8} {:>8} {:>14} {:>10}",
        "single standing form", "rank", "grain", "scale", "open bound", "rides there"
    );
    let mut bound_is_attained = true;
    let mut open_bound_does_not_ride = true;
    for (name, material) in &single_forms {
        let law = LeaderLaw::read_off(material, RideDiscipline::GermBounded);
        let quadrature = integrate_by_leaders(material, &law).expect("lawful");
        let scale = quadrature
            .scale_witnesses
            .first()
            .map(|witness| witness.scale.clone());
        let open_bound = material.finest_standing_extent().clone()
            / Rat::from_integer(BigInt::from(material.jet_aperture() + 1));
        let at_the_bound = integrate_by_leaders(
            material,
            &LeaderLaw::new(
                open_bound.clone(),
                RideDiscipline::GermBounded,
                WitnessDepth::ReadOffTheJet,
            ),
        )
        .expect("lawful");
        println!(
            "     {:<24} {:>6} {:>8} {:>8} {:>14} {:>10}",
            name,
            material.jet_aperture(),
            format_rat(&law.grain),
            scale.as_ref().map(format_rat).unwrap_or_else(|| "-".into()),
            format_rat(&open_bound),
            !at_the_bound.scale_witnesses.is_empty()
        );
        bound_is_attained &= scale == Some(one_rank_step.clone());
        open_bound_does_not_ride &= at_the_bound.scale_witnesses.is_empty();
    }
    controls.check(
        "on a single standing form the bound is attained: the scale is exactly one rank step",
        bound_is_attained,
        "otherwise the + 2 carries slack and some smaller divisor would have done",
    );
    controls.check(
        "and one step coarser — the open bound E/(d+1) — that form does not ride at all",
        open_bound_does_not_ride,
        "the bound is open, which is exactly why the material cannot name a coarsest grain",
    );
}

// ---------------------------------------------------------------------------------------------

fn main() -> Result<(), Box<dyn Error>> {
    println!("  THE LEADER READS ITS OWN DEPTH");
    println!(
        "  two levels excised from derivation_integral: LEADER_WITNESS_DEPTH = 1 and \
         LEADER_GRAIN_RECIPROCAL = 3"
    );

    let mut controls = Controls::new();
    the_theorem(&mut controls);
    the_orbit_inside_the_aperture(&mut controls);
    where_the_depth_decides_the_answer(&mut controls);
    the_route_material(&mut controls);

    println!("\n  {} controls held.", controls.held);
    if controls.failed.is_empty() {
        println!("  every declared control holds.");
        Ok(())
    } else {
        println!("  FAILED: {:?}", controls.failed);
        std::process::exit(1);
    }
}

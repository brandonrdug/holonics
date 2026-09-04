//! The swing is the invariant.
//!
//! ## What this is
//!
//! The cross-ratio is this project's most-used technical primitive, and `docs/canon/THE_QUOTE_NETWORK.md`
//! puts it in the foundations:
//!
//! > *"the fundamentals of mathematics are in counting, cross-ratios, factors, and offsets."*
//!
//! Its **defining** property is that it is the invariant of the projective group acting on a line.
//! Until 2026-08-08 that property was asserted nowhere in this workspace, and neither were the group
//! laws of the one genuine `PGL(2,ℚ)` carrier in the tree. The two halves sat one crate apart:
//!
//! - `crates/relational-geometry/src/receiver_atlas.rs` computed the cross-ratio in a **private**
//!   `fn`, exact over `Rat`, collinearity-checked;
//! - `crates/holonic-engine/src/simplicial.rs` carried `ProjectiveTurn` — `apply`, `followed_by`,
//!   `inverse`, `is_projective_identity`, singular matrices refused — and `holonic-engine` depends
//!   on `relational-geometry`, so neither side could see the other's half.
//!
//! Its three fixtures used `ProjectiveTurn::identity()` or the fixed translate `(1,1,0,1)`: **the
//! orbit was trivial by construction.** A third cross-ratio at `crates/holonic-body/src/soul.rs:159` does test
//! invariance, but only under translation and scaling — the **affine subgroup**, which is the weak
//! part of the group and the part that fixes the point at infinity.
//!
//! The seam was closed by publishing the reading rather than moving the group: `cross_ratio` is now
//! `pub` in `relational-geometry` with a typed refusal, and the invariance is asserted here, where
//! the group lives. No dependency was inverted and no second `PGL(2,ℚ)` carrier was grown — a second
//! implementation agreeing with the first is one computation compared with itself twice
//! (`CLAUDE.md` §8).
//!
//! ## The exactness route
//!
//! Everything below is `Rat = BigRational`. There is no float, no tolerance, no epsilon, no
//! threshold and no decimal comparison anywhere in this file. Every printed value is
//! `format_rat` of an exact rational, and every verdict is `==` between two of them.
//!
//! ## The declared controls
//!
//! Per `CLAUDE.md` §8 — *a check whose material cannot vary the property under test is the same
//! defect as a check that cannot fail; it just wears a passing result*:
//!
//! 1. **The orbit is exhibited and required.** Every mark is printed before and after every turn,
//!    every mark is required to move, and the five image quadruples are required to be five
//!    distinct quadruples with the source among none of them — the shape
//!    `crates/holonic-engine/src/rebase_invariants.rs:1220` sets for its three pivot walks.
//! 2. **Three of the five turns have `c ≠ 0`**, so the statement proved is projective and not the
//!    affine one `soul.rs` already covers. Each turn's pole is printed; an affine turn has none.
//! 3. **The invariance is exact** — `Rat == Rat`.
//! 4. **A control that can fail.** `t -> t²` and `t -> t³` reparameterise the *same* pencil through
//!    the *same* machinery and must **change** the cross-ratio. Coordinatewise squaring in the plane
//!    must be **refused** as leaving the pencil.
//! 5. **Degeneracy is refused by name**, never by panic: a singular turn, a collapsed pencil, a
//!    parameter at the turn's pole, and four species of degenerate quadruple.
//! 6. **The receiver atlas's own orbit.** Two receivers are not two projections until they are shown
//!    to have projected the marks differently, so their coordinates are exhibited before their
//!    agreement is read.

use std::collections::BTreeSet;

use holonic_engine::simplicial::{ProjectivePencil, ProjectiveTurn, SimplicialError};
use relational_geometry::{
    Construction, CrossRatioRefusal, GrainedReceiver, MarkedOccurrence, OccurrenceId,
    ProjectionLaw, Rat, RatMat3, RatVec2, RatVec3, Receiver, ReceiverGrain, ReceiverId,
    ReceiverOrientation, SwingCell, analyze_receiver_atlas, cross_ratio, format_rat, integer, rat,
};

fn mark(point: &RatVec2) -> String {
    format!("({},{})", format_rat(&point.x), format_rat(&point.y))
}

fn quadruple(points: &[RatVec2]) -> String {
    points.iter().map(mark).collect::<Vec<_>>().join(" ")
}

fn parameters_of(values: &[Rat]) -> String {
    values.iter().map(format_rat).collect::<Vec<_>>().join(", ")
}

/// Carry plane marks through a planar homography acting on `(x,y,1)` and dehomogenize.  A mark on
/// the map's vanishing line returns `None` rather than being repaired.
fn carry_through_plane(homography: &RatMat3, points: &[RatVec2]) -> Option<Vec<RatVec2>> {
    points
        .iter()
        .map(|point| {
            let image =
                homography.apply(&RatVec3::new(point.x.clone(), point.y.clone(), integer(1)));
            (image.z != integer(0)).then(|| RatVec2::new(&image.x / &image.z, &image.y / &image.z))
        })
        .collect()
}

/// Which coordinate `cross_ratio` reduces this quadruple on.
fn reduction_axis(points: &[RatVec2]) -> &'static str {
    if points[1].x != points[0].x { "x" } else { "y" }
}

fn coordinates(points: &[RatVec2]) -> Vec<(Rat, Rat)> {
    points
        .iter()
        .map(|point| (point.x.clone(), point.y.clone()))
        .collect()
}

/// The declared family of turns. Three have `c ≠ 0`.
fn declared_turns() -> Vec<(&'static str, ProjectiveTurn)> {
    vec![
        (
            "translate  t -> t+1",
            ProjectiveTurn::new(integer(1), integer(1), integer(0), integer(1)).unwrap(),
        ),
        (
            "dilate     t -> 3t",
            ProjectiveTurn::new(integer(3), integer(0), integer(0), integer(1)).unwrap(),
        ),
        (
            "invert     t -> 1/t",
            ProjectiveTurn::new(integer(0), integer(1), integer(1), integer(0)).unwrap(),
        ),
        (
            "general    t -> (2t+1)/(t+3)",
            ProjectiveTurn::new(integer(2), integer(1), integer(1), integer(3)).unwrap(),
        ),
        (
            "general    t -> (t-2)/(3t+1)",
            ProjectiveTurn::new(integer(1), integer(-2), integer(3), integer(1)).unwrap(),
        ),
    ]
}

/// Two pencils. `cross_ratio` reads the pencil's `x` when its direction has nonzero `x` and its
/// `y` otherwise, so a family of one pencil leaves half that branch unexercised.
fn declared_pencils() -> Vec<(&'static str, ProjectivePencil)> {
    vec![
        (
            "oblique  (1,-2) + t(3,5)   [reduced on x]",
            ProjectivePencil::new(
                RatVec2::new(integer(1), integer(-2)),
                RatVec2::new(integer(3), integer(5)),
            )
            .unwrap(),
        ),
        (
            "vertical (4,1) + t(0,7)    [reduced on y]",
            ProjectivePencil::new(
                RatVec2::new(integer(4), integer(1)),
                RatVec2::new(integer(0), integer(7)),
            )
            .unwrap(),
        ),
    ]
}

/// Neither a pole nor a fixed point of any declared turn, which is what lets the orbit demand
/// that **every** mark move.
fn declared_quadruples() -> Vec<Vec<Rat>> {
    vec![
        vec![integer(2), integer(3), integer(5), integer(8)],
        vec![rat(-3, 2), rat(1, 5), integer(2), integer(9)],
    ]
}

fn main() {
    let mut holds: Vec<(String, bool, String)> = Vec::new();
    let turns = declared_turns();

    println!("THE SWING IS THE INVARIANT");
    println!("==========================");
    println!(
        "\ncross_ratio(T.p) == cross_ratio(p) for T in PGL(2,Q), exact over Rat, with the orbit\n\
         exhibited first. `relational_geometry::cross_ratio` reads four plane marks in one pencil;\n\
         `holonic_engine::simplicial::ProjectiveTurn` moves one projective line coordinate; a\n\
         `ProjectivePencil` is what joins them."
    );

    // =============================================================================================
    println!("\n\nTHE DECLARED FAMILY");
    println!("-------------------");
    println!("  turns");
    let mut projective_turns = 0usize;
    for (name, turn) in &turns {
        let pole = match turn.pole() {
            Some(value) => format!("pole at t={}", format_rat(&value)),
            None => "no pole (fixes infinity)".to_owned(),
        };
        let kind = if turn.is_affine() {
            "AFFINE     c=0"
        } else {
            projective_turns += 1;
            "PROJECTIVE c!=0"
        };
        let determinant = &turn.a * &turn.d - &turn.b * &turn.c;
        println!(
            "    {name:<30}  [a b; c d] = [{} {}; {} {}]  det {}  {kind}  {pole}",
            format_rat(&turn.a),
            format_rat(&turn.b),
            format_rat(&turn.c),
            format_rat(&turn.d),
            format_rat(&determinant),
        );
    }
    println!("  pencils");
    for (name, _) in &declared_pencils() {
        println!("    {name}");
    }
    println!("  parameter quadruples");
    for values in &declared_quadruples() {
        println!("    [{}]", parameters_of(values));
    }
    holds.push((
        "a projective turn with c != 0 is included, so the statement is stronger than affine"
            .to_owned(),
        projective_turns >= 3,
        format!(
            "{projective_turns} of {} declared turns have c != 0",
            turns.len()
        ),
    ));

    // =============================================================================================
    println!("\n\nTHE ORBIT, AND THE INVARIANCE");
    println!("-----------------------------");
    let mut every_mark_moved = true;
    let mut every_orbit_full = true;
    let mut every_ratio_stood = true;
    let mut orbit_evidence = Vec::new();
    let mut invariance_evidence = Vec::new();

    for (pencil_name, pencil) in declared_pencils() {
        for parameters in declared_quadruples() {
            let source = pencil.place_all(&parameters);
            let source_ratio = cross_ratio(&source).unwrap();
            println!("\n  pencil    {pencil_name}");
            println!("  t         [{}]", parameters_of(&parameters));
            println!("  BEFORE    {}", quadruple(&source));
            println!("  X         {}", format_rat(&source_ratio));
            println!();

            let mut orbit: BTreeSet<Vec<(Rat, Rat)>> = BTreeSet::new();
            for (turn_name, turn) in &turns {
                let image = pencil.carry(turn, &parameters).unwrap();
                let moved = source
                    .iter()
                    .zip(image.iter())
                    .filter(|(before, after)| before != after)
                    .count();
                let image_ratio = cross_ratio(&image).unwrap();
                let stood = image_ratio == source_ratio;
                every_mark_moved &= moved == source.len();
                every_ratio_stood &= stood;
                orbit.insert(coordinates(&image));
                println!("    {turn_name}");
                println!("      AFTER   {}", quadruple(&image));
                println!("      moved   {moved} of {} marks", source.len());
                println!(
                    "      X       {}   {}",
                    format_rat(&image_ratio),
                    if stood { "== source" } else { "!= SOURCE" }
                );
            }

            let source_absent = !orbit.contains(&coordinates(&source));
            let full = orbit.len() == turns.len() && source_absent;
            every_orbit_full &= full;
            println!(
                "\n    ORBIT   {} distinct image quadruples over {} turns; the source is {}",
                orbit.len(),
                turns.len(),
                if source_absent {
                    "among none of them"
                } else {
                    "AMONG THEM"
                }
            );
            orbit_evidence.push(format!(
                "{pencil_name} / [{}]: {} images over {} turns",
                parameters_of(&parameters),
                orbit.len(),
                turns.len()
            ));
            invariance_evidence.push(format!(
                "{pencil_name} / [{}]: X = {}",
                parameters_of(&parameters),
                format_rat(&source_ratio)
            ));
        }
    }
    holds.push((
        "every declared turn moves every mark".to_owned(),
        every_mark_moved,
        "no turn returned a mark where it found it".to_owned(),
    ));
    holds.push((
        "the orbit is non-trivial: one distinct image quadruple per turn, source among none"
            .to_owned(),
        every_orbit_full,
        orbit_evidence.join(" | "),
    ));
    holds.push((
        "cross_ratio(T.p) == cross_ratio(p), exactly, over Rat".to_owned(),
        every_ratio_stood,
        invariance_evidence.join(" | "),
    ));

    // =============================================================================================
    println!("\n\nTHE PLANE ITSELF MOVES");
    println!("----------------------");
    println!(
        "  The turns above move marks ALONG one fixed pencil. A PGL(3,Q) homography of the receiver\n\
         plane moves the pencil: the source line goes to a DIFFERENT line. On the vertical pencil it\n\
         also flips which coordinate `cross_ratio` reduces on, from y to x -- the implementation's own\n\
         internal branch changes across the transformation and the returned value does not."
    );
    let homography = RatMat3::from_i64([[2, 1, 0], [1, 3, 1], [0, 1, 2]]);
    println!(
        "\n  H = [2 1 0; 1 3 1; 0 1 2]   det {}   bottom row (0,1,2) so w = y+2 is not constant",
        format_rat(&homography.determinant())
    );
    let mut every_line_moved = true;
    let mut every_planar_ratio_stood = true;
    let mut axis_flips = 0usize;
    for (pencil_name, pencil) in declared_pencils() {
        for parameters in declared_quadruples() {
            let source = pencil.place_all(&parameters);
            let source_ratio = cross_ratio(&source).unwrap();
            let image = carry_through_plane(&homography, &source).unwrap();
            let direction = source[1].subtract(&source[0]);
            let line_moved = image
                .iter()
                .any(|point| direction.cross(&point.subtract(&source[0])) != integer(0));
            let image_ratio = cross_ratio(&image).unwrap();
            let stood = image_ratio == source_ratio;
            every_line_moved &= line_moved;
            every_planar_ratio_stood &= stood;
            let source_axis = reduction_axis(&source);
            let image_axis = reduction_axis(&image);
            if source_axis != image_axis {
                axis_flips += 1;
            }
            println!("\n  pencil    {pencil_name}");
            println!("  t         [{}]", parameters_of(&parameters));
            println!(
                "  BEFORE    {}   reduced on {source_axis}   X {}",
                quadruple(&source),
                format_rat(&source_ratio)
            );
            println!(
                "  AFTER  H  {}   reduced on {image_axis}   X {}   {}",
                quadruple(&image),
                format_rat(&image_ratio),
                if stood { "== source" } else { "!= SOURCE" }
            );
            println!(
                "  the line  {}",
                if line_moved {
                    "moved: image marks are off the source pencil"
                } else {
                    "DID NOT MOVE"
                }
            );
        }
    }
    holds.push((
        "a planar homography moves the line off itself and the cross-ratio still stands".to_owned(),
        every_line_moved && every_planar_ratio_stood,
        "four (pencil, quadruple) pairs, every image line distinct from its source".to_owned(),
    ));
    holds.push((
        "the homography flips which coordinate cross_ratio reduces on, so the branch is read in \
         two frames"
            .to_owned(),
        axis_flips > 0,
        format!("{axis_flips} of 4 (pencil, quadruple) pairs changed reduction axis"),
    ));

    // =============================================================================================
    println!("\n\nTHE CONTROL THAT CAN FAIL");
    println!("-------------------------");
    println!(
        "  A non-projective reparameterisation of the SAME pencil, through the SAME machinery,\n\
         landing on the SAME line. If the cross-ratio survived this, the invariance above would be\n\
         a property of the fixture and not of the group."
    );
    let mut every_bend_moved_it = true;
    for (pencil_name, pencil) in declared_pencils() {
        for parameters in declared_quadruples() {
            let source_ratio = cross_ratio(&pencil.place_all(&parameters)).unwrap();
            println!("\n  pencil    {pencil_name}");
            println!(
                "  t         [{}]   X {}",
                parameters_of(&parameters),
                format_rat(&source_ratio)
            );
            for (name, exponent) in [("square  t -> t^2", 2i32), ("cube    t -> t^3", 3)] {
                let bent = parameters
                    .iter()
                    .map(|parameter| parameter.pow(exponent))
                    .collect::<Vec<_>>();
                let bent_ratio = cross_ratio(&pencil.place_all(&bent)).unwrap();
                let changed = bent_ratio != source_ratio;
                every_bend_moved_it &= changed;
                println!(
                    "    {name}   [{}]   X {}   {}",
                    parameters_of(&bent),
                    format_rat(&bent_ratio),
                    if changed { "CHANGED" } else { "SURVIVED" }
                );
            }
        }
    }
    holds.push((
        "a non-projective reparameterisation changes the cross-ratio".to_owned(),
        every_bend_moved_it,
        "t -> t^2 and t -> t^3 moved it on both pencils and both quadruples".to_owned(),
    ));

    let (_, first_pencil) = declared_pencils().into_iter().next().unwrap();
    let planar_square = first_pencil
        .place_all(&declared_quadruples()[0])
        .iter()
        .map(|point| RatVec2::new(&point.x * &point.x, &point.y * &point.y))
        .collect::<Vec<_>>();
    let planar_refusal = cross_ratio(&planar_square);
    println!(
        "\n  coordinatewise square in the plane (x,y) -> (x^2,y^2)\n    {}\n    -> {:?}",
        quadruple(&planar_square),
        planar_refusal
    );
    holds.push((
        "a nonlinear map of the plane leaves the pencil and is refused, not answered".to_owned(),
        planar_refusal == Err(CrossRatioRefusal::MarksOutsideOnePencil),
        format!("{planar_refusal:?}"),
    ));

    // =============================================================================================
    println!("\n\nTHE GROUP LAWS");
    println!("--------------");
    let probes = [rat(-3, 2), rat(1, 5), integer(2), integer(9), integer(4)];
    let mut inverses_close = true;
    for (name, turn) in &turns {
        let forward = turn.followed_by(&turn.inverse()).is_projective_identity();
        let backward = turn.inverse().followed_by(turn).is_projective_identity();
        inverses_close &= forward && backward;
        println!(
            "  {name:<30}  T then T^-1 -> identity: {forward}   T^-1 then T -> identity: {backward}"
        );
    }
    holds.push((
        "T followed_by T.inverse() is the projective identity, both hands".to_owned(),
        inverses_close,
        format!("{} declared turns", turns.len()),
    ));

    let mut associates = true;
    let mut composite_pairs = 0usize;
    for (_, first) in &turns {
        for (_, second) in &turns {
            for (_, third) in &turns {
                associates &= first.followed_by(second).followed_by(third)
                    == first.followed_by(&second.followed_by(third));
                composite_pairs += 1;
            }
        }
    }
    println!("  associativity over {composite_pairs} ordered triples: {associates}");
    holds.push((
        "(A then B) then C == A then (B then C), on the nose".to_owned(),
        associates,
        format!("{composite_pairs} ordered triples of declared turns"),
    ));

    let mut apply_respects_composition = true;
    let mut checked = 0usize;
    for (_, first) in &turns {
        for (_, second) in &turns {
            let composite = first.followed_by(second);
            for probe in &probes {
                let staged = first.apply(probe).and_then(|middle| second.apply(&middle));
                apply_respects_composition &= composite.apply(probe) == staged;
                checked += 1;
            }
        }
    }
    println!("  apply respects followed_by over {checked} probes: {apply_respects_composition}");
    holds.push((
        "composite.apply(t) == second.apply(first.apply(t))".to_owned(),
        apply_respects_composition,
        format!(
            "{checked} probes over {}x{} ordered pairs",
            turns.len(),
            turns.len()
        ),
    ));

    // The group's own orbit: if the declared family commuted, associativity on it would be nearly
    // vacuous.
    let (left_name, left) = &turns[2];
    let (right_name, right) = &turns[3];
    let commutator = left
        .followed_by(right)
        .followed_by(&right.followed_by(left).inverse());
    let noncommuting = !commutator.is_projective_identity();
    println!(
        "  the family does not commute: [{left_name}] then [{right_name}] differs from the \
         reverse: {noncommuting}"
    );
    holds.push((
        "the declared turns do not commute, so the composition law was actually exercised"
            .to_owned(),
        noncommuting,
        format!(
            "commutator [a b; c d] = [{} {}; {} {}]",
            format_rat(&commutator.a),
            format_rat(&commutator.b),
            format_rat(&commutator.c),
            format_rat(&commutator.d)
        ),
    ));

    let scaled_identity =
        ProjectiveTurn::new(integer(2), integer(0), integer(0), integer(2)).unwrap();
    let (_, general) = &turns[3];
    let scaled = ProjectiveTurn::new(
        &general.a * integer(5),
        &general.b * integer(5),
        &general.c * integer(5),
        &general.d * integer(5),
    )
    .unwrap();
    let gauge = scaled_identity.is_projective_identity()
        && scaled != *general
        && probes
            .iter()
            .all(|probe| scaled.apply(probe) == general.apply(probe));
    println!("  a common nonzero scale is gauge, not a different map: {gauge}");
    holds.push((
        "a common nonzero scale is gauge: 2I is the identity turn and 5M is M's map".to_owned(),
        gauge,
        "the matrices differ and every probe agrees".to_owned(),
    ));

    // =============================================================================================
    println!("\n\nDEGENERACY, REFUSED BY NAME");
    println!("---------------------------");
    let singular = ProjectiveTurn::new(integer(2), integer(4), integer(1), integer(2));
    let collapsed = ProjectivePencil::new(RatVec2::new(integer(1), integer(2)), RatVec2::zero());
    let (_, invert) = &turns[2];
    let at_pole = first_pencil.carry(invert, &[integer(1), integer(0)]);
    println!("  ProjectiveTurn::new(2,4,1,2)          det 0        -> {singular:?}");
    println!("  ProjectivePencil::new(origin, zero)                -> {collapsed:?}");
    match &at_pole {
        Err(refusal) => println!(
            "  carry(t -> 1/t, [1, 0])               pole at 0    -> Err(TurnSendsParameterToInfinity)\n\
             {:<53}   \"{refusal}\"",
            ""
        ),
        Ok(points) => println!(
            "  carry(t -> 1/t, [1, 0])               pole at 0    -> Ok({})",
            quadruple(points)
        ),
    }

    let a = RatVec2::new(integer(0), integer(0));
    let b = RatVec2::new(integer(1), integer(2));
    let c = RatVec2::new(integer(3), integer(6));
    let three = cross_ratio(&[a.clone(), b.clone(), c.clone()]);
    let coincident = cross_ratio(&[a.clone(), a.clone(), b.clone(), c.clone()]);
    let repeated = cross_ratio(&[
        a.clone(),
        b.clone(),
        b.clone(),
        RatVec2::new(integer(5), integer(10)),
    ]);
    let scattered = cross_ratio(&[a, b, c, RatVec2::new(integer(1), integer(0))]);
    println!("  cross_ratio of three marks                         -> {three:?}");
    println!("  cross_ratio with the first two coincident          -> {coincident:?}");
    println!("  cross_ratio with a repeated projective member      -> {repeated:?}");
    println!("  cross_ratio of four marks off one pencil           -> {scattered:?}");
    let refusals_named = matches!(singular, Err(SimplicialError::SingularTurn))
        && matches!(collapsed, Err(SimplicialError::CollapsedPencil))
        && at_pole == Err(SimplicialError::TurnSendsParameterToInfinity(integer(0)))
        && three == Err(CrossRatioRefusal::NotFourMarks(3))
        && coincident == Err(CrossRatioRefusal::CoincidentPivotMarks)
        && repeated == Err(CrossRatioRefusal::RepeatedProjectiveMember)
        && scattered == Err(CrossRatioRefusal::MarksOutsideOnePencil);
    holds.push((
        "every degeneracy is refused by a named variant, and nothing panicked".to_owned(),
        refusals_named,
        "singular turn, collapsed pencil, parameter at the pole, and four quadruple species"
            .to_owned(),
    ));

    // =============================================================================================
    println!("\n\nTHE RECEIVER ATLAS'S OWN ORBIT");
    println!("------------------------------");
    println!(
        "  `four_marks_carry_one_cross_ratio_through_distinct_receivers` asserted\n\
         `receiver_values.len() == 2` and nothing else. That is a BTreeMap keyed by ReceiverId, so\n\
         the length counts RECEIVERS and is fixed before any geometry runs. Here is what the two\n\
         receivers actually put on their faces."
    );
    let (construction, frame) = Construction::new("source");
    let occurrences = [-1i64, 0, 1, 3]
        .into_iter()
        .enumerate()
        .map(|(index, parameter)| {
            let parameter = integer(parameter);
            MarkedOccurrence::new(
                OccurrenceId(index as u64 + 1),
                format!("m{index}"),
                frame,
                RatVec3::new(
                    &parameter + integer(1),
                    integer(2) * &parameter - integer(1),
                    &parameter / integer(2) + integer(1),
                ),
            )
        })
        .collect::<Vec<_>>();
    let mut perspective = Receiver::new(
        ReceiverId(2),
        "fine perspective",
        frame,
        ProjectionLaw::PerspectiveRay {
            focal_distance: integer(7),
        },
    );
    perspective.orientation =
        ReceiverOrientation::from_cayley_xyz(rat(1, 5), rat(-1, 4), rat(1, 3));
    let receivers = vec![
        GrainedReceiver {
            receiver: Receiver::new(
                ReceiverId(1),
                "coarse orthographic",
                frame,
                ProjectionLaw::Orthographic,
            ),
            grain: ReceiverGrain::new(5, 5),
        },
        GrainedReceiver {
            receiver: perspective,
            grain: ReceiverGrain::new(31, 17),
        },
    ];
    let atlas = analyze_receiver_atlas(
        &construction,
        &receivers,
        &occurrences,
        &[SwingCell {
            id: 1,
            name: "one swing".to_owned(),
            pivot: [OccurrenceId(1), OccurrenceId(2), OccurrenceId(3)],
            witness: OccurrenceId(4),
        }],
    )
    .unwrap();

    let mut faces: BTreeSet<Vec<(Rat, Rat)>> = BTreeSet::new();
    for face in &atlas.faces {
        let points = face
            .occurrences
            .iter()
            .map(|occurrence| occurrence.projected.rational.clone().unwrap())
            .collect::<Vec<_>>();
        println!("    {:<22} {}", face.receiver_name, quadruple(&points));
        faces.insert(coordinates(&points));
    }
    let pointwise_distinct = atlas.occurrences.iter().all(|joint| {
        joint.faces[&ReceiverId(1)].projected.rational
            != joint.faces[&ReceiverId(2)].projected.rational
    });
    let swing = atlas.swing(1).unwrap();
    println!(
        "    distinct received quadruples: {} over {} receivers; every mark moved: {pointwise_distinct}",
        faces.len(),
        atlas.faces.len()
    );
    for (receiver, value) in &swing.receiver_values {
        println!("    {receiver:?} X = {}", format_rat(value));
    }
    println!(
        "    invariant: {}",
        swing
            .invariant
            .as_ref()
            .map(format_rat)
            .unwrap_or_else(|| "NONE".to_owned())
    );
    holds.push((
        "the two receivers project the four marks to two distinct quadruples, at every mark"
            .to_owned(),
        faces.len() == 2 && pointwise_distinct,
        format!(
            "{} distinct quadruples over {} receivers, pointwise distinct: {pointwise_distinct}",
            faces.len(),
            atlas.faces.len()
        ),
    ));
    holds.push((
        "an orthographic face and a rotated perspective face return one cross-ratio".to_owned(),
        swing.invariant.is_some(),
        match &swing.invariant {
            Some(value) => format!("X = {}", format_rat(value)),
            None => format!("{:?}", swing.receiver_values),
        },
    ));

    // THE FALSIFICATION.  Material on which the old assertion still passes and the repaired one
    // does not: two orthographic receivers differing only in grain. A grain changes the aperture
    // address and never the exact projected point, so both faces carry the SAME four coordinates
    // while `receiver_values.len()` is still 2.
    println!(
        "\n  Falsification -- two receivers differing only in grain. `receiver_values.len() == 2`\n\
         still passes here; the repaired assertion does not, which is what makes it a check."
    );
    let twin_atlas = analyze_receiver_atlas(
        &construction,
        &[
            GrainedReceiver {
                receiver: Receiver::new(
                    ReceiverId(1),
                    "orthographic, coarse grain",
                    frame,
                    ProjectionLaw::Orthographic,
                ),
                grain: ReceiverGrain::new(5, 5),
            },
            GrainedReceiver {
                receiver: Receiver::new(
                    ReceiverId(3),
                    "orthographic, fine grain",
                    frame,
                    ProjectionLaw::Orthographic,
                ),
                grain: ReceiverGrain::new(31, 17),
            },
        ],
        &occurrences,
        &[SwingCell {
            id: 1,
            name: "one swing".to_owned(),
            pivot: [OccurrenceId(1), OccurrenceId(2), OccurrenceId(3)],
            witness: OccurrenceId(4),
        }],
    )
    .unwrap();
    let mut twin_faces: BTreeSet<Vec<(Rat, Rat)>> = BTreeSet::new();
    for face in &twin_atlas.faces {
        let points = face
            .occurrences
            .iter()
            .map(|occurrence| occurrence.projected.rational.clone().unwrap())
            .collect::<Vec<_>>();
        println!("    {:<28} {}", face.receiver_name, quadruple(&points));
        twin_faces.insert(coordinates(&points));
    }
    let twin_swing = twin_atlas.swing(1).unwrap();
    println!(
        "    receiver_values.len() = {}  (the old assertion: PASSES)",
        twin_swing.receiver_values.len()
    );
    println!(
        "    distinct received quadruples = {}  (the repaired assertion: FAILS, as it must)",
        twin_faces.len()
    );
    holds.push((
        "the repaired assertion can fail: two receivers with one projection collapse to one \
         quadruple while receiver_values.len() is still 2"
            .to_owned(),
        twin_swing.receiver_values.len() == 2 && twin_faces.len() == 1,
        format!(
            "receiver_values.len() = {}, distinct quadruples = {}",
            twin_swing.receiver_values.len(),
            twin_faces.len()
        ),
    ));

    // =============================================================================================
    println!("\n\nDECLARED CONTROLS");
    println!("-----------------");
    let mut failed = 0;
    for (claim, held, evidence) in &holds {
        if *held {
            println!("  [holds] {claim}\n            {evidence}");
        } else {
            failed += 1;
            println!("  [FAILS] {claim}\n            {evidence}");
        }
    }
    println!();
    if failed == 0 {
        println!("HELD -- {} declared controls, 0 failed", holds.len());
    } else {
        println!(
            "FAILED -- {failed} of {} declared controls did not hold",
            holds.len()
        );
        std::process::exit(1);
    }

    classify_mechanisms(&declared_pencils());
}

/// **Material that DOES meet a pole, which the declared quadruples deliberately avoid.**
///
/// `declared_quadruples` is chosen so that no mark is a pole of any declared turn — that is what
/// lets the orbit demand every mark move. It also means no turn can ever fail, so a classification
/// over that material alone would return one block and carry nothing. These quadruples each contain
/// the pole of one projective turn: `t = 0` is the pole of the swap `(0,1,1,0)`, and `t = -3` is the
/// pole of `(2,1,1,3)`.
fn quadruples_meeting_a_pole() -> Vec<(&'static str, Vec<Rat>)> {
    vec![
        (
            "contains t=0  (the swap's pole)",
            vec![integer(0), integer(1), integer(2), integer(4)],
        ),
        (
            "contains t=-3 (the pole of 2,1;1,3)",
            vec![integer(-3), integer(1), integer(2), integer(4)],
        ),
    ]
}

/// **The admission law over transport mechanisms, computed by this body and nothing else.**
///
/// A mechanism is CONFIRMED on a material when the cross-ratio it carries is exactly unmoved, and
/// REFUTED when the carry refuses or the value moves. Both sides are exact rational arithmetic in
/// this process — **no external checker is consulted, and none is needed.** A proof assistant is a
/// medium for communicating and re-running a proof; it is not where the mathematics is decided.
///
/// The verdict is the same four-state law the conditioning fibers use:
///
/// ```text
///     Admitted     preserved the invariant on every material it met
///     Conflicted   preserved on some and not others — its applicability has a CONDITION,
///                  and here that condition is nameable: no mark at the turn's pole
///     Refuted      never preserved it
/// ```
fn classify_mechanisms(pencils: &[(&'static str, ProjectivePencil)]) {
    let turns = declared_turns();
    let mut materials: Vec<(String, Vec<Rat>)> = declared_quadruples()
        .into_iter()
        .enumerate()
        .map(|(at, parameters)| (format!("pole-free {at}"), parameters))
        .collect();
    materials.extend(
        quadruples_meeting_a_pole()
            .into_iter()
            .map(|(name, parameters)| (name.to_owned(), parameters)),
    );

    // Each mechanism is a map on the pencil parameter. The projective turns are the declared
    // family; the two reparameterisations are the controls that must fail, because squaring and
    // cubing are not projective and leave the pencil.
    let mut mechanisms: Vec<(String, Box<dyn Fn(&Rat) -> Option<Rat>>)> = Vec::new();
    for (name, turn) in turns {
        let carried = turn.clone();
        mechanisms.push((
            format!("turn {name}"),
            Box::new(move |value: &Rat| carried.apply(value)),
        ));
    }
    mechanisms.push((
        "reparameterise t -> t^2".to_owned(),
        Box::new(|value: &Rat| Some(value * value)),
    ));
    mechanisms.push((
        "reparameterise t -> t^3".to_owned(),
        Box::new(|value: &Rat| Some(value * value * value)),
    ));

    println!("\n\nTHE MECHANISMS, ADMITTED BY WHAT THEY PRESERVE");
    println!("----------------------------------------------");
    println!(
        "  Both sides of the evidence are computed here, exactly over Rat. No external checker is\n\
         \x20 consulted: a mechanism either leaves the cross-ratio exactly where it was or it does not."
    );
    println!(
        "\n  {:<34} {:>9} {:>9}   verdict",
        "mechanism", "preserved", "moved"
    );

    let mut conflicted_conditions: Vec<String> = Vec::new();
    for (name, mechanism) in &mechanisms {
        let mut preserved = 0u64;
        let mut moved = 0u64;
        let mut failing: Vec<String> = Vec::new();
        for (pencil_name, pencil) in pencils {
            for (material_name, parameters) in &materials {
                let before = match cross_ratio(&pencil.place_all(parameters)) {
                    Ok(value) => value,
                    Err(_) => continue,
                };
                let carried: Option<Vec<Rat>> =
                    parameters.iter().map(|value| mechanism(value)).collect();
                let holds = match carried {
                    // The carry refused — a mark left the pencil. That is a refutation and it is
                    // reported rather than skipped, because refusing IS the mechanism's behaviour
                    // on this material.
                    None => false,
                    Some(images) => match cross_ratio(&pencil.place_all(&images)) {
                        Ok(after) => after == before,
                        Err(_) => false,
                    },
                };
                if holds {
                    preserved += 1;
                } else {
                    moved += 1;
                    failing.push(format!(
                        "{material_name} on {}",
                        &pencil_name[..7.min(pencil_name.len())]
                    ));
                }
            }
        }
        let verdict = match (preserved, moved) {
            (0, 0) => "OPEN",
            (_, 0) => "ADMITTED",
            (0, _) => "REFUTED",
            _ => "CONFLICTED",
        };
        println!("  {name:<34} {preserved:>9} {moved:>9}   {verdict}");
        if verdict == "CONFLICTED" {
            conflicted_conditions.push(format!("    {name} fails on: {}", failing.join(", ")));
        }
    }

    if conflicted_conditions.is_empty() {
        println!(
            "\n  NOTHING CONFLICTED. Every mechanism either preserved the invariant everywhere or\n\
             \x20 nowhere, so this material carries no recognition condition to find."
        );
    } else {
        println!("\n  The conflicted mechanisms, and where they fail:");
        for line in &conflicted_conditions {
            println!("{line}");
        }
        println!(
            "\n  A CONFLICTED mechanism is not a broken one. It preserves the cross-ratio wherever\n\
             \x20 it is defined, and refuses where a mark sits at its pole — so its applicability\n\
             \x20 carries a condition its name does not: NO MARK AT THE POLE. That condition is what\n\
             \x20 an atlas edge owes, and the classification found it without being told."
        );
    }
}

//! The matroid hands its Hodge–Riemann form to the organ that names windings.
//!
//! `canon/THE_HOLOBROCHOS_SPINE.md` recorded the cut: *"`matroid_chow::generator_pairing` (the
//! Hodge–Riemann pairing) → `winding_inertia::from_symmetric_form`: no join at all, in library or
//! driver. Nothing has handed a matroid's form to the organ that names windings."* This driver is
//! the join, and `ChowRing::cyclic_generator_receiver` is the library edge it runs on.
//!
//! `CLAUDE.md` §2b: *"A count of signs is a state reading. Name the windings instead."* The two
//! organs were built for exactly that sentence and had never met. `inertia` returns `(p, z, q)`;
//! `winding_inertia` returns one named passage per character — its winding `k/n`, the star polygon
//! `{n/k}` it traces, and whether traversing it returns with the turn, against it, or nothing.
//!
//! ## What the material says, and it is mostly a refusal
//!
//! A circulant carries `c_0` at every diagonal entry, so a cyclic reading of a form needs every
//! direction to self-pair to the same value. On a simple rank-three matroid `deg(x_L²) = −1` on a
//! rank-two flat and `deg(x_p²) = 1 − |{lines through p}|` on a point, so a constant diagonal forces
//! every point onto exactly two lines — and that forces `|E| = 3`. The derivation is on
//! `ChowRing::cyclic_generator_receiver`. **`U(3,3)` is the only simple rank-three matroid whose
//! generator pairing a character group can see**, and this sweep exhibits the refusal by name on
//! every other fixture rather than reporting a silent absence.
//!
//! A wave that reports movement everywhere and a wave that reports it nowhere carry the same
//! evidence, which is none. This one is required to do both: at least one fixture must conduct and
//! at least one must refuse, and the run fails if either side of that is empty.

use std::process::ExitCode;

use holonic_engine::inertia::{Inertia, SymmetricForm, inertia};
use holonic_engine::matroid_chow::{ChowError, ChowRing, Matroid};
use holonic_engine::winding_inertia::{
    CyclicReading, Hand, PassageReturn, SymmetricCirculant, WindingError, winding_inertia,
};
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;

/// Declared by this caller, not by the library: how many placements the cyclic-reading walk may
/// touch before it reports an exhausted allowance rather than an absence.
const WALK_APERTURE: u64 = 1_000_000;

fn main() -> ExitCode {
    let mut failures: Vec<String> = Vec::new();

    println!("the matroid names its windings");
    println!("matroid_chow::generator_pairing  ->  winding_inertia");
    println!();
    println!(
        "the cut this closes, from canon/THE_HOLOBROCHOS_SPINE.md: \"no join at all, in library or"
    );
    println!("driver. Nothing has handed a matroid's form to the organ that names windings.\"");
    println!();
    println!("walk aperture declared by this driver: {WALK_APERTURE} placements.");

    let mut conducted = 0_usize;
    let mut refused = 0_usize;

    for (matroid, note) in fixtures() {
        match report_matroid(matroid, note, &mut failures) {
            Verdict::Conducted => conducted += 1,
            Verdict::Refused => refused += 1,
            Verdict::NotThisGrade => {}
        }
    }

    println!();
    println!("================================================================================");
    println!("the orbit of the join over the declared material");
    println!("  fixtures whose pairing a character group can see: {conducted}");
    println!("  fixtures refused by name:                          {refused}");
    if conducted == 0 {
        failures.push(
            "no fixture conducted: a sweep that refuses everywhere cannot distinguish a working \
             join from a broken one"
                .into(),
        );
    }
    if refused == 0 {
        failures.push(
            "no fixture refused: a sweep that admits everywhere cannot distinguish a gate from an \
             absent gate"
                .into(),
        );
    }

    report_reading_refusals(&mut failures);

    println!();
    println!("================================================================================");
    if failures.is_empty() {
        println!("every declared control returned as stated.");
        ExitCode::SUCCESS
    } else {
        println!("{} declared control(s) failed:", failures.len());
        for failure in &failures {
            println!("  - {failure}");
        }
        ExitCode::FAILURE
    }
}

enum Verdict {
    Conducted,
    Refused,
    NotThisGrade,
}

// -------------------------------------------------------------------------------------------
// the declared material — the same fixture family `matroid_hodge_riemann` sweeps

fn fixtures() -> Vec<(Matroid, &'static str)> {
    vec![
        (
            Matroid::uniform(2, 3).expect("U(2,3)"),
            "rank two: the pairing is stated for a top grade of two, so this one is refused before \
             any winding question is asked",
        ),
        (
            Matroid::uniform(3, 3).expect("U(3,3)"),
            "the Boolean matroid B3: three general lines in P^2, wonderful model Bl_3 P^2",
        ),
        (
            Matroid::uniform(3, 4).expect("U(3,4)"),
            "four general lines in P^2",
        ),
        (
            Matroid::graphic(
                "M(K4)",
                4,
                &[(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)],
            )
            .expect("M(K4)"),
            "the graphic matroid of K_4",
        ),
        (
            Matroid::rank_three_from_lines(
                "Fano F7",
                7,
                &[
                    &[0, 1, 2],
                    &[0, 3, 4],
                    &[0, 5, 6],
                    &[1, 3, 5],
                    &[1, 4, 6],
                    &[2, 3, 6],
                    &[2, 4, 5],
                ],
            )
            .expect("F7"),
            "the Fano plane: representable only in characteristic two",
        ),
        (
            Matroid::rank_three_from_lines(
                "non-Pappus",
                9,
                &[
                    &[0, 1, 2],
                    &[3, 4, 5],
                    &[0, 4, 8],
                    &[0, 5, 7],
                    &[1, 3, 8],
                    &[1, 5, 6],
                    &[2, 3, 7],
                    &[2, 4, 6],
                ],
            )
            .expect("non-Pappus"),
            "representable over no field at all",
        ),
        (
            Matroid::uniform(4, 4).expect("U(4,4)"),
            "the Boolean matroid B4: rank four, so its top grade is three",
        ),
    ]
}

// -------------------------------------------------------------------------------------------

fn report_matroid(matroid: Matroid, note: &str, failures: &mut Vec<String>) -> Verdict {
    println!();
    println!("================================================================================");
    println!(
        "{}   |E| = {}, rank {}",
        matroid.name(),
        matroid.ground(),
        matroid.rank()
    );
    println!("  {note}.");

    let name = matroid.name().to_string();
    let ground = matroid.ground();
    let ring = match ChowRing::new(matroid) {
        Ok(ring) => ring,
        Err(error) => {
            println!("  the ring itself is refused: {error}");
            return Verdict::NotThisGrade;
        }
    };
    let pairing = match ring.generator_pairing() {
        Ok(pairing) => pairing,
        Err(error) => {
            println!("  generator_pairing refuses: {error}");
            return Verdict::NotThisGrade;
        }
    };

    let extent = pairing.extent();
    let elimination = inertia(&pairing);
    println!(
        "  {extent} generators, one per proper nonempty flat; degree-one dimension {}",
        ring.dimension(1)
    );
    println!(
        "  elimination on the ring's own flat order: {}",
        show_split(&elimination)
    );

    // ---- control: the null cone of the pairing is the ring's own relation ideal ----
    //
    // The pairing factors through A^1, so its kernel contains J_1; Poincare duality in degree one
    // makes the induced form nondegenerate, so the kernel is exactly J_1 and its dimension is
    // |E| - 1. `ring.dimension(1)` is an exact row reduction of the relation ideal and never
    // touches the pairing. This can fail: a bug in either route, or a ring for which duality does
    // not hold, separates the two numbers.
    let relations = ground - 1;
    println!(
        "  null directions {} against |E| - 1 = {relations} independent relations, and extent - \
         dim A^1 = {}",
        elimination.zero,
        extent - ring.dimension(1)
    );
    if elimination.zero != relations || extent - ring.dimension(1) != relations {
        failures.push(format!(
            "{name}: the pairing's null cone is {} directions, the relation ideal is {relations}, \
             and the ring's own degree-one dimension leaves {}",
            elimination.zero,
            extent - ring.dimension(1)
        ));
    }

    match ring.cyclic_generator_receiver(WALK_APERTURE) {
        Err(error) => {
            println!("  the winding organ REFUSES this pairing:");
            println!("    {error}");
            let text = format!("{error}");
            if !text.contains("circulant under no reading")
                && !text.contains("no cyclic reading makes this form circulant")
            {
                failures.push(format!(
                    "{name}: the refusal is not one of the two the walk is supposed to return: \
                     {text}"
                ));
            }
            if text.contains("exhausted allowance") {
                failures.push(format!(
                    "{name}: the walk ran out of its declared allowance, which is not an absence \
                     and may not be reported as one"
                ));
            }
            Verdict::Refused
        }
        Ok(receiver) => {
            println!(
                "  a cyclic reading EXISTS: {:?}   (walk touched {} placements)",
                receiver.reading.order(),
                receiver.walked
            );

            // ---- control: the receiver moved, and the split did not ----
            match &receiver.native_refusal {
                None => failures.push(format!(
                    "{name}: the pairing was already circulant in the ring's own flat order, so \
                     the two-frame claim is vacuous here and the driver must say so rather than \
                     present one frame as two"
                )),
                Some(refusal) => {
                    println!("  the ring's own flat order is blind to it:");
                    println!("    {refusal}");
                }
            }

            let read = SymmetricCirculant::read_cyclically(&pairing, &receiver.reading)
                .expect("the receiver's own reading re-reads");
            let transported = read
                .as_symmetric_form()
                .expect("a circulant is a symmetric form");
            let after = inertia(&transported);
            println!(
                "  first row under the reading: [{}]",
                receiver
                    .circulant
                    .first_row()
                    .iter()
                    .map(show_rat)
                    .collect::<Vec<String>>()
                    .join(", ")
            );

            let reading = match winding_inertia(&receiver.circulant) {
                Ok(reading) => reading,
                Err(error) => {
                    failures.push(format!("{name}: winding_inertia refused: {error}"));
                    return Verdict::Conducted;
                }
            };

            println!();
            println!("  the passages, named by their windings rather than counted by their signs:");
            for passage in &reading.passages {
                println!(
                    "    character {:>2}   winding {:>4}   star {:>6}   {}",
                    passage.character,
                    show_rat(&passage.winding),
                    passage.star_polygon.label(),
                    passage.returns.name()
                );
            }
            println!();
            println!(
                "    against the turn: {}",
                show_windings(&reading.windings_past_the_hand())
            );
            println!(
                "    on the null cone:  {}",
                show_windings(&reading.null_windings())
            );
            println!(
                "    with the turn:     {}",
                show_windings(&reading.windings_of(Hand::WithTheTurn))
            );

            // ---- control: three routes, one split ----
            //
            // Elimination on the ring's flat order, elimination on the cyclic reading, and the
            // character route (cyclotomic null test plus Sturm enclosures against a
            // Faddeev-LeVerrier determinant) are three independent computations. This can fail:
            // any disagreement between exact elimination and exact character theory shows up here.
            let characters = reading.split();
            println!();
            println!(
                "    elimination, flat order:    {}",
                show_split(&elimination)
            );
            println!("    elimination, cyclic reading: {}", show_split(&after));
            println!(
                "    character route:             {}",
                show_split(&characters)
            );
            if elimination != after || after != characters {
                failures.push(format!(
                    "{name}: three routes to one split disagree: {} / {} / {}",
                    show_split(&elimination),
                    show_split(&after),
                    show_split(&characters)
                ));
            }

            // ---- control: the hand is a convention, the split is not ----
            //
            // Negating the form swaps the two hands and moves no null. This can fail: a hand read
            // off anything other than the form's own sign would not swap, and a null decided by an
            // enclosure rather than by the cyclotomic divisor could move.
            let negated = match winding_inertia(&receiver.circulant.negated()) {
                Ok(negated) => negated,
                Err(error) => {
                    failures.push(format!("{name}: the negated circulant refused: {error}"));
                    return Verdict::Conducted;
                }
            };
            let swapped = negated.split();
            println!(
                "    negated form:                {}   nulls {}",
                show_split(&swapped),
                show_windings(&negated.null_windings())
            );
            if swapped.positive != characters.negative
                || swapped.negative != characters.positive
                || swapped.zero != characters.zero
                || negated.null_windings() != reading.null_windings()
            {
                failures.push(format!(
                    "{name}: negation did not swap the two hands while leaving the null cone where \
                     it was"
                ));
            }

            // ---- control: the single returning direction is a named passage ----
            //
            // The Hodge index theorem gives one positive direction. The character route names which
            // one, and the ring's own multiplication and degree map are asked the same question
            // through a third route: deg(c^2) for c the class the character-zero passage is.
            let ones: Vec<Rat> = vec![Rat::one(); extent];
            let constant = ring
                .class_from_coefficients(&ones)
                .expect("one coefficient per flat");
            let self_intersection = ring
                .top_self_intersection(&constant)
                .expect("degree two is the top grade here");
            let zero_frequency = reading
                .passage(0)
                .expect("character zero is always present")
                .returns;
            println!();
            println!(
                "    character 0 is the constant vector sum_F x_F; the ring returns deg((sum_F \
                 x_F)^2) = {}, and the character route calls that passage \"{}\"",
                show_rat(&self_intersection),
                zero_frequency.name()
            );
            let agrees = match zero_frequency {
                PassageReturn::Handed(Hand::WithTheTurn) => self_intersection.is_positive(),
                PassageReturn::Handed(Hand::AgainstTheTurn) => self_intersection.is_negative(),
                PassageReturn::OnTheNullCone => self_intersection.is_zero(),
            };
            if !agrees {
                failures.push(format!(
                    "{name}: the ring's own deg((sum_F x_F)^2) = {} disagrees with what the \
                     character route says character zero returns",
                    show_rat(&self_intersection)
                ));
            }

            // ---- control: an exhausted allowance is not an absence ----
            //
            // The same fixture, with an allowance too small to close the walk, must return the
            // exhaustion refusal and not the absence refusal. This can fail: a search that
            // conflates the two would return `NoCyclicReceiver` here and the two refusals would be
            // indistinguishable to every caller.
            match ring.cyclic_generator_receiver(1) {
                Err(ChowError::Winding(WindingError::CyclicWalkPastItsAperture { walked })) => {
                    println!(
                        "    with an allowance of one placement the walk reports exhaustion at \
                         {walked}, not absence"
                    );
                }
                other => failures.push(format!(
                    "{name}: an allowance of one placement should report an exhausted allowance; \
                     it returned {}",
                    match other {
                        Ok(_) => "a receiver".to_string(),
                        Err(error) => format!("{error}"),
                    }
                )),
            }

            Verdict::Conducted
        }
    }
}

// -------------------------------------------------------------------------------------------

/// The reading machinery's own refusals, exhibited rather than assumed.
fn report_reading_refusals(failures: &mut Vec<String>) {
    println!();
    println!("================================================================================");
    println!("the reading is a receiver and it is validated as one");

    // A reading that repeats a direction is not a change of basis, so Sylvester's law would not
    // apply to it. This can fail: a `declare` that admitted it would let a caller transport a form
    // by a singular matrix and read the resulting split as the form's.
    match CyclicReading::declare(vec![0, 1, 1]) {
        Err(WindingError::ReadingIsNotAPermutation { position }) => {
            println!("  a reading repeating a direction is refused at position {position}.");
        }
        other => failures.push(format!(
            "a reading that repeats a direction should be refused; it returned {other:?}"
        )),
    }

    // The native reading must return exactly what the un-read form returns. This can fail: a
    // reading path that symmetrized, wrapped or averaged would admit a form the direct gate
    // refuses, and the whole two-frame claim would collapse into a repair.
    let cycle = SymmetricForm::from_integers(&[
        vec![0, 1, 0, 1],
        vec![1, 0, 1, 0],
        vec![0, 1, 0, 1],
        vec![1, 0, 1, 0],
    ])
    .expect("C_4 adjacency is symmetric");
    let scrambled = SymmetricForm::from_integers(&[
        vec![0, 1, 0, 1],
        vec![1, 0, 1, 1],
        vec![0, 1, 0, 1],
        vec![1, 1, 1, 0],
    ])
    .expect("symmetric, and deliberately not circulant");
    for (form, label) in [
        (&cycle, "the C_4 adjacency"),
        (&scrambled, "one entry moved"),
    ] {
        let native = CyclicReading::native(form.extent()).expect("extent four");
        let direct = SymmetricCirculant::from_symmetric_form(form).err();
        let read = SymmetricCirculant::read_cyclically(form, &native).err();
        println!(
            "  {label}: direct gate {}, native reading {}",
            direct.as_ref().map_or("admits".into(), |e| format!("{e}")),
            read.as_ref().map_or("admits".into(), |e| format!("{e}"))
        );
        if direct != read {
            failures.push(format!(
                "{label}: the native reading and the direct gate returned different verdicts"
            ));
        }
    }
    if SymmetricCirculant::from_symmetric_form(&scrambled).is_ok() {
        failures.push(
            "the deliberately non-circulant form was admitted, so the gate this driver leans on \
             does not gate"
                .into(),
        );
    }
}

// -------------------------------------------------------------------------------------------

fn show_split(split: &Inertia) -> String {
    format!(
        "({} with, {} null, {} against)",
        split.positive, split.zero, split.negative
    )
}

fn show_rat(value: &Rat) -> String {
    if value.is_integer() {
        value.numer().to_string()
    } else {
        format!("{}/{}", value.numer(), value.denom())
    }
}

fn show_windings(windings: &[Rat]) -> String {
    if windings.is_empty() {
        "none".into()
    } else {
        windings
            .iter()
            .map(show_rat)
            .collect::<Vec<String>>()
            .join(", ")
    }
}

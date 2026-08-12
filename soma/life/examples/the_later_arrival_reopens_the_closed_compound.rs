//! **The later arrival reopens the closed compound.**
//!
//! `the_vertex_emits_where_the_tape_only_walked` built one direction: a completed compound closes
//! and hands up one successor at grain `k+1` with its residual. Integration. Nothing came back
//! down, and nothing responded to later material — so the machine could integrate and could not
//! differentiate, and a body that only integrates has no cycle at all.
//!
//! This driver builds the other direction and closes the loop.
//!
//! ```text
//!   closure          complete_{F,Q,k}(C_k) → (n_{k+1}, ρ_k)      the internal boundary departs
//!   differentiation  differentiate_k(n_{k+1}) → (∂Σ, r_Σ, supp)  it is handed back
//!
//!   and the two are ADJOINT:      ⟨w, ∂Σ⟩  =  ⟨dw, Σ⟩
//! ```
//!
//! The right-hand side is `holonic_engine::running_integral::coboundary` on the engine's own
//! carrier. That organ was chosen over the two other candidates on the merits, and the reasons are
//! printed by the run itself.
//!
//! **The law this driver states and then tries to break:**
//!
//! ```text
//!   Σ REOPENS  ⟺  a later arrival founds a passage incident to a constituent of supp_Σ
//!                 AND  r_Σ ≠ 0  in the declared coefficient group
//! ```
//!
//! Four falsifiers, each of which can fail, each with a declared control:
//!
//! ```text
//!   A  a later arrival must change a NAMED earlier compound
//!   B  withdrawing that arrival must restore the original successor BIT-EXACTLY
//!   C  where the residual vanishes the arrival must reach the compound and cause NOTHING
//!   D  the law's prediction must match the complete re-derivation, compound by compound
//! ```
//!
//! **The run corrects that law and the correction is the finding. Read falsifier D's verdict.**
//! Stated as one gate the law conflates two questions with two different predictors:
//!
//! ```text
//!   reaching  gates the VALENCE      Γ moves  ⟺  a passage that did not exist lands on a
//!                                                 constituent of ∂Σ that is not already `Both`
//!   the residual gates the TRANSPORT r(Σ' − Σ) = r(Σ') − r(Σ), so a standing compound hands
//!                                                 its whole obstruction into every cycle the
//!                                                 arrival founds through it — and a saturated
//!                                                 one hands forward exactly nothing
//! ```
//!
//! and the closed boundary itself moves **never**, because adding cells to a graph cannot destroy
//! a cycle. That is a theorem, it is measured on every run, and it is what CLOSED means.
//!
//! ```text
//! cargo run --release -p life --example the_later_arrival_reopens_the_closed_compound
//! ```

use std::collections::BTreeSet;

use num_bigint::BigInt;

use life::incidence_production::{
    ArrivalResponse, DeclaredOccurrence, Differentiation, Emission, IncidenceComplex, PhaseChart,
};

use holonic_engine::{
    gluing::{read_cover, Cover},
    rebase_invariants::PivotRule,
    running_integral::CoefficientGroup,
};

/// The declared aperture on inscription patches per occurrence. Returns its outside.
const DECLARED_EXTENT: usize = 40;

/// How many closed boundaries to print in full.
const PRINTED: usize = 6;

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let chart = PhaseChart::WindingAdjacent;
    let group = CoefficientGroup::Integers;

    println!("WHY `running_integral` AND NOT THE OTHER TWO");
    println!(
        "  differentiation must be the FORMAL PARTNER of closure, and `⟨w, ∂Σ⟩ = ⟨dw, Σ⟩` is that\n\
         \x20 partnership written as an identity that can be checked from both sides. \
         `running_integral`\n\
         \x20 owns `coboundary`, the Stokes pairing and `ChordObstruction{{declared, implied, \
         residual}}` —\n\
         \x20 which is the residual this complex already computes on closed paths, in additive form \
         and\n\
         \x20 with a caller-declared coefficient group."
    );
    println!(
        "  `gluing.rs`'s Mayer–Vietoris δ was NOT chosen for the DIFFERENTIATION, because \
         `read_cover`\n\
         \x20 is keyed to a cover of ONE FIXED complex and a later arrival adds cells that were in \
         no\n\
         \x20 piece of it, so the union it computes over is not the object that changed. It is the \
         right\n\
         \x20 organ for a different question on the SAME run and it is used for it below: on the \
         ADMITTED\n\
         \x20 complex the cover {{standing body, arrival}} is genuine, and δ returns exactly the \
         classes\n\
         \x20 the union carries that NEITHER piece does — §V's *composition can create paths that no\n\
         \x20 isolated cell affords*, computed."
    );
    println!(
        "  `reopening.rs` was NOT chosen because its material is a TRUNCATION: it adjoins the \
         channel a\n\
         \x20 discarded numeric tail deleted, entering through `ExactFace::from_binary_float`. \
         Nothing\n\
         \x20 here truncates a value. The deletion closure performs is STRUCTURAL — cells depart — \
         and\n\
         \x20 the channel that recovers them is the boundary operator, not a series tail."
    );
    println!();

    // ---------------------------------------------------------------------------------------
    let material = declared_material();
    let complex = IncidenceComplex::found(&material, DECLARED_EXTENT)
        .map_err(|error| format!("found: {error:?}"))?;
    println!("THE DECLARED MATERIAL");
    for occurrence in &material {
        println!(
            "  storage {:>4}  caused_by {:?}  {:?}",
            occurrence.storage_ordinal,
            occurrence.caused_by.iter().collect::<Vec<_>>(),
            occurrence.text
        );
    }
    for (identity, ordinal, rank) in complex.causal_ranks() {
        println!("  ⪯ rank {rank}   storage {ordinal:>4}   {identity}");
    }
    println!(
        "  {} constituents · {} contacts · {} closed boundaries · {} ⪯ edges · {} patches outside \
         the declared extent",
        complex.sites().len(),
        complex.bonds().len(),
        complex.compounds().len(),
        complex.dependencies().len(),
        complex.patches_outside_extent()
    );
    println!();

    // ---------------------------------------------------------------------------------------
    println!("∂∂ = 0 — THREE FRAMES, NO NEW VALIDATOR");
    complex
        .validate_with_body(true)
        .map_err(|error| format!("body refused: {error:?}"))?;
    println!("  body::incidence::EventComplex               ADMITS");
    let view = complex
        .engine_view()
        .map_err(|error| format!("engine refused: {error:?}"))?;
    println!(
        "  holonic_engine::GradedCausalComplex         ADMITS — {} cells, f-vector {:?}",
        view.complex().cells().len(),
        view.complex().f_vector()
    );
    println!("  this module                                 builds no validator of its own");
    println!();

    // ---------------------------------------------------------------------------------------
    println!("DIFFERENTIATION — WHAT CLOSURE SUPPRESSED, HANDED BACK");
    let differentiated = complex
        .differentiate_all(chart)
        .map_err(|error| format!("differentiate: {error:?}"))?;
    let emissions = complex
        .hand_up(chart)
        .map_err(|error| format!("hand up: {error:?}"))?;
    println!(
        "  {} closed boundaries. `w(e) = sheet(e) · contact_winding(e)`, exact in ℤ — the ADDITIVE \
         reading",
        differentiated.len()
    );
    println!(
        "  of the same two material numbers the multiplicative transport uses. The two are not the \
         same"
    );
    println!(
        "  map: `PhaseChart::rotation` is not a homomorphism out of (ℤ,+), so their agreement is a \
         measurement."
    );
    println!();
    let mut stokes_held = 0usize;
    for (at, differentiation) in differentiated.iter().enumerate() {
        if differentiation.stokes_holds() {
            stokes_held += 1;
        }
        if at >= PRINTED {
            continue;
        }
        print_differentiation(differentiation, &emissions[at]);
    }
    if differentiated.len() > PRINTED {
        println!("  … {} further closed boundaries", differentiated.len() - PRINTED);
    }
    println!();
    println!(
        "  STOKES  ⟨w, ∂Σ⟩ = ⟨dw, Σ⟩ on {stokes_held} of {} closed boundaries",
        differentiated.len()
    );
    println!(
        "    the left side is this module walking the boundary in traversal order; the right is the\n\
         \x20   engine summing over its own unordered boundary chain. Its bound: it separates a \
         traversal\n\
         \x20   from a chain, not two theories."
    );
    let (flat_additively, flat_multiplicatively) = (
        differentiated
            .iter()
            .filter(|one| one.residual_vanishes(&group))
            .count(),
        differentiated.iter().filter(|one| one.holonomy_is_flat()).count(),
    );
    let both = differentiated
        .iter()
        .filter(|one| one.residual_vanishes(&group) == one.holonomy_is_flat())
        .count();
    println!(
        "  TWO FRAMES ON FLATNESS   additive r_Σ = 0 on {flat_additively}   multiplicative H = 1 on \
         {flat_multiplicatively}   agree on {both} of {}",
        differentiated.len()
    );
    println!(
        "    where they disagree the material carries a turn one reading deletes. Neither is the \
         defect."
    );
    println!();

    // ---------------------------------------------------------------------------------------
    println!("THE CYCLE SPACE, READ FROM TWO INDEPENDENTLY BUILT SPANNING FORESTS");
    let chords = complex
        .chord_population(&group)
        .map_err(|error| format!("chords: {error:?}"))?;
    let module_image = complex
        .holonomy_image(chart)
        .map_err(|error| format!("image: {error:?}"))?;
    println!(
        "  this module's fundamental-cycle basis : {} chords",
        differentiated.len()
    );
    println!(
        "  the engine's `found_potential_in`     : {} chords over {} components ({} agreeing, {} \
         retained)",
        chords.cycle_rank, chords.components, chords.agreeing, chords.retained.len()
    );
    println!(
        "  β₁ = E − V + C = {} − {} + {} = {}",
        complex.bonds().len(),
        complex.sites().len(),
        chords.components,
        complex.bonds().len() as i64 - complex.sites().len() as i64 + chords.components as i64
    );
    println!("  the retained chord obstructions, verbatim — `residual = declared − implied`:");
    for chord in chords.retained.iter().take(PRINTED) {
        println!(
            "    declared {:>4}   implied {:>4}   residual {:>4}",
            chord.declared, chord.implied, chord.residual
        );
    }
    if chords.retained.len() > PRINTED {
        println!("    … {} further", chords.retained.len() - PRINTED);
    }
    println!(
        "  IMAGE OF H₁ → ℤ   module basis {module_image}   engine basis {}   {}",
        chords.image,
        if module_image == chords.image {
            "IDENTICAL — the invariant survives the change of basis"
        } else {
            "DIFFER — a basis is leaking into the invariant, or one basis is incomplete"
        }
    );
    println!(
        "    a basis is a receiver-visible coordinate; the subgroup it generates is not. This is \
         the\n\
         \x20   two-frame check `CLAUDE.md` §0's fourth lesson asks for and it can fail."
    );
    println!();

    // ---------------------------------------------------------------------------------------
    println!("═══ FALSIFIER A — A LATER ARRIVAL CHANGES A NAMED EARLIER COMPOUND ═══");
    println!();
    let arrival = co_present_arrival();
    let response = complex
        .admit_later(&arrival, chart, &group)
        .map_err(|error| format!("admit: {error:?}"))?;
    report_arrival(&response, &differentiated);
    println!();
    print_artifact(&response);
    println!();

    // -- A3: the higher-grain successor the earlier compound composes into -------------------
    println!("  ═══ A3 — THE EARLIER COMPOUND COMPOSES INTO A DIFFERENT HIGHER-GRAIN SUCCESSOR ═══");
    println!(
        "  the closed boundary is permanent; what a later arrival changes is what it composes \
         WITH. So"
    );
    println!(
        "  the different successor with the different residual is one grain up, and that is where \
         the"
    );
    println!("  conditioning is: a pathway changed, and the next current rides the changed pathway.");
    let before_tower = tower(&complex, chart);
    let after_tower = tower(&response.complex, chart);
    println!();
    println!("    {:>7} {:>26} {:>26}", "grain", "before the arrival", "after the arrival");
    for grain in 0..before_tower.len().max(after_tower.len()) {
        println!(
            "    {:>7} {:>26} {:>26}",
            grain + 1,
            before_tower
                .get(grain)
                .map_or("—".to_owned(), |emissions| format!(
                    "{} successors",
                    emissions.len()
                )),
            after_tower
                .get(grain)
                .map_or("—".to_owned(), |emissions| format!(
                    "{} successors",
                    emissions.len()
                ))
        );
    }
    for grain in 1..before_tower.len().max(after_tower.len()) {
        let empty = Vec::new();
        let before_at = before_tower.get(grain).unwrap_or(&empty);
        let after_at = after_tower.get(grain).unwrap_or(&empty);
        if before_at.is_empty() && after_at.is_empty() {
            continue;
        }
        println!();
        println!("    ── GRAIN {} SUCCESSORS, VERBATIM ──", grain + 1);
        println!("    BEFORE:");
        for emission in before_at.iter().take(PRINTED) {
            println!(
                "      holonomy {:<30} {:?}",
                emission.holonomy_text(),
                elide(&emission.surface, 90)
            );
        }
        if before_at.is_empty() {
            println!("      (none)");
        }
        println!("    AFTER:");
        for emission in after_at.iter().take(PRINTED) {
            println!(
                "      holonomy {:<30} {:?}",
                emission.holonomy_text(),
                elide(&emission.surface, 90)
            );
        }
        if after_at.is_empty() {
            println!("      (none)");
        }
        let bit_exact = before_at
            .iter()
            .filter(|emission| after_at.contains(emission))
            .count();
        let boundary_held = before_at
            .iter()
            .filter(|left| {
                after_at
                    .iter()
                    .any(|right| right.closed_boundary_reading() == left.closed_boundary_reading())
            })
            .count();
        println!(
            "    of {} grain-{} successors: {} survived BIT-EXACTLY, {} survived with their closed \
             boundary intact",
            before_at.len(),
            grain + 1,
            bit_exact,
            boundary_held
        );
        for left in before_at {
            let Some(right) = after_at
                .iter()
                .find(|right| right.surface == left.surface && right.holonomy == left.holonomy)
            else {
                continue;
            };
            if right == left {
                continue;
            }
            println!(
                "      A NAMED GRAIN-{} SUCCESSOR MOVED WHILE ITS SURFACE AND HOLONOMY HELD:",
                grain + 1
            );
            println!("        {:?}", left.surface);
            println!(
                "        BEFORE  multiplicity {}  ·  {} internal contacts  ·  Γ {}",
                left.residual.carried_multiplicity,
                left.residual.internal_contacts,
                port_text(left.frame_reading().1)
            );
            println!(
                "        AFTER   multiplicity {}  ·  {} internal contacts  ·  Γ {}",
                right.residual.carried_multiplicity,
                right.residual.internal_contacts,
                port_text(right.frame_reading().1)
            );
        }
    }
    println!();

    exhibit_transport(&response, chart)?;
    println!();

    // -- A5: what the union carries that neither piece does ---------------------------------
    exhibit_gluing(&complex, &response)?;
    println!();

    // ---------------------------------------------------------------------------------------
    println!("═══ FALSIFIER B — WITHDRAWING THE ARRIVAL RESTORES THE ORIGINAL BIT-EXACTLY ═══");
    println!();
    let withdrawn = response
        .complex
        .withdraw(&response.trace)
        .map_err(|error| format!("withdraw: {error:?}"))?;
    let restored = withdrawn
        .hand_up(chart)
        .map_err(|error| format!("hand up: {error:?}"))?;
    println!(
        "  the withdrawal is the inverse of the admission ON THE ADMITTED COMPLEX, not a \
         re-founding from"
    );
    println!(
        "  the original material. It therefore tests what a re-founding cannot: that nothing \
         accumulated."
    );
    println!(
        "    {} constituent occurrence counts and {} contact multiplicities were raised by the \
         arrival and are taken back down",
        response.trace.site_occurrence_delta.len(),
        response.trace.bond_multiplicity_delta.len()
    );
    println!(
        "    {} constituents · {} contacts · {} closed boundaries after withdrawal (base: {} · {} · \
         {})",
        withdrawn.sites().len(),
        withdrawn.bonds().len(),
        withdrawn.compounds().len(),
        complex.sites().len(),
        complex.bonds().len(),
        complex.compounds().len()
    );
    println!(
        "  {} successors restored against {} before; BIT-EXACT: {}",
        restored.len(),
        response.before.len(),
        if restored == response.before {
            "YES"
        } else {
            "NO — THE FALSIFIER FIRED"
        }
    );
    if restored != response.before {
        for (left, right) in response.before.iter().zip(restored.iter()) {
            if left != right {
                println!("    before {:?}", left.surface);
                println!("    after  {:?}", right.surface);
            }
        }
    }
    println!();

    // ---------------------------------------------------------------------------------------
    println!("═══ FALSIFIER C — WHERE THE RESIDUAL VANISHES, NOTHING IS CAUSED ═══");
    println!();
    let flat = IncidenceComplex::found(&saturated_material(), DECLARED_EXTENT)
        .map_err(|error| format!("flat: {error:?}"))?;
    let flat_differentiated = flat
        .differentiate_all(chart)
        .map_err(|error| format!("flat differentiate: {error:?}"))?;
    println!(
        "  the declared saturated material: {:?}",
        saturated_material()[0].text
    );
    println!(
        "    `popcount('b'⊕'c') = popcount('c'⊕'a') = 1` — the two contacts cross ONE bit each — \
         and they"
    );
    println!(
        "    land on opposed sheets, `popcount('c')` even against `popcount('a')` odd. So \
         `w = +1` and"
    );
    println!("    `w = −1`, the closed boundary sums to zero, and neither contact is itself flat.");
    for differentiation in &flat_differentiated {
        print_differentiation_head(differentiation);
    }
    let flat_arrival = saturated_arrival();
    let flat_response = flat
        .admit_later(&flat_arrival, chart, &group)
        .map_err(|error| format!("flat admit: {error:?}"))?;
    println!(
        "  the arrival {:?} at ⪯ rank {} — co-present: {}",
        flat_arrival.text, flat_response.arrival_rank, flat_response.arrival_is_co_present
    );
    println!(
        "    reached {} · reopened {} · saturated {} · untouched {}",
        flat_response.reached.len(),
        flat_response.reopened.len(),
        flat_response.saturated.len(),
        flat_response.untouched.len()
    );
    println!(
        "    the arrival RE-TRODE {} contact(s) and founded {} new one(s), so it DID reach the \
         compound",
        flat_response.trace.bond_multiplicity_delta.len(),
        flat_response.new_contacts
    );
    println!(
        "  NO CLOSED BOUNDARY MOVED: {}   ·   any compound REOPENED: {}   ·   closed boundaries \
         founded beside it: {}",
        if flat_response.no_closed_boundary_moved() { "YES" } else { "NO" },
        if flat_response.reopened.is_empty() { "no" } else { "YES — the residual gate is wrong" },
        flat_response.founded.len()
    );
    for verdict in &flat_response.verdicts {
        let after = verdict.after.as_ref();
        println!(
            "    {:?}  Π {} → {}  Γ {} → {}  closed boundary {}",
            verdict.surface,
            verdict.before.frame_reading().0,
            after.map_or(0, |emission| emission.frame_reading().0),
            verdict.before.frame_reading().1.len(),
            after.map_or(0, |emission| emission.frame_reading().1.len()),
            if verdict.moved { "MOVED" } else { "HELD" }
        );
    }
    println!(
        "    `Π` — the lived construction — rose, and that is correct: frequency is the machine's \
         own"
    );
    println!(
        "    mechanics and not this law's to gate. `Γ` moved because a passage that did not exist \
         now"
    );
    println!(
        "    lands on the compound: that is valence, receiver-relative by §IV, and not closure's to"
    );
    println!("    fix either. What did not move is the closed boundary. And what was NOT caused is");
    println!("    any transport out of it:");
    println!();
    exhibit_transport(&flat_response, chart)?;
    println!();

    // ---------------------------------------------------------------------------------------
    let later = causally_later_arrival();
    let later_response = complex
        .admit_later(&later, chart, &group)
        .map_err(|error| format!("later admit: {error:?}"))?;

    println!("═══ FALSIFIER D — THE LAW'S PREDICTION AGAINST THE COMPLETE RE-DERIVATION ═══");
    println!();
    println!(
        "  every run re-derives every closed boundary and checks the law's prediction against it. A"
    );
    println!(
        "  differential update whose prediction is never checked is a claim about code rather than \
         a"
    );
    println!("  measurement of it (`CLAUDE.md` §8).");
    println!();
    println!(
        "  THE LAW SPLIT IN TWO WHEN IT WAS RUN, AND THE SPLIT IS THE FINDING. REACHING gates the"
    );
    println!(
        "  VALENCE; the RESIDUAL gates the TRANSPORT. They are different questions with different"
    );
    println!("  predictors, and the single-gate statement at the top of this file conflated them.");
    for (name, response) in [
        ("co-present arrival", &response),
        ("saturated control", &flat_response),
        ("causally-later arrival", &later_response),
    ] {
        println!();
        println!("  [{name}]");
        println!(
            "    {:>28} {:>10} {:>10} {:>10} {:>10}",
            "", "Γ predict", "Γ actual", "r predict", "∂Σ actual"
        );
        for verdict in response.verdicts.iter().take(PRINTED + 6) {
            println!(
                "    {:>28} {:>10} {:>10} {:>10} {:>10}",
                elide(&verdict.surface, 28),
                if verdict.predicted_valence_move { "Γ MOVE" } else { "Γ hold" },
                if verdict.valence_moved { "MOVED" } else { "held" },
                if verdict.predicted_to_transport { "r CARRY" } else { "r none" },
                if verdict.moved { "∂Σ MOVED" } else { "∂Σ held" }
            );
        }
        let (right, wrong) = response.valence_law_agreement();
        let held = response.verdicts.iter().filter(|verdict| !verdict.moved).count();
        println!(
            "    valence law right {right}, wrong {wrong}, of {}   ·   closed boundaries that held: \
             {held} of {}",
            response.verdicts.len(),
            response.verdicts.len()
        );
    }
    println!();
    println!("  THE READING, AND IT CORRECTS THE LAW AS STATED AT THE TOP OF THIS FILE.");
    println!(
        "    1. `∂Σ actual` is a CONSTANT `held`. Adding cells to a graph never destroys a cycle, \
         so no"
    );
    println!(
        "       later arrival can move a closed boundary at all — which is what CLOSED means, and \
         it is"
    );
    println!(
        "       the honest content of `complete_(F,Q,k)` being a completion rather than a stage. \
         The"
    );
    println!(
        "       brief this driver was built to satisfy asked for a compound that RE-CLOSES \
         DIFFERENTLY;"
    );
    println!("       the material returned a theorem instead, and the theorem governs.");
    println!(
        "    2. What a later arrival changes about a standing compound is its VALENCE and what it"
    );
    println!(
        "       COMPOSES INTO. Both are measured above, on named compounds, verbatim, and both moved."
    );
    println!(
        "    3. The RESIDUAL gates neither of those. It gates TRANSPORT — what the compound hands"
    );
    println!(
        "       forward into the cycles the arrival founds through it — and that is exact and is a"
    );
    println!("       theorem, with the saturated control handing forward exactly zero.");
    println!();

    println!("═══ THE SECOND SPECIES — AN ARRIVAL AT A NEW RANK REACHES BACK ONLY ALONG ⪯ ═══");
    println!();
    println!(
        "  `⪯` is derived from the corpus's own `caused_by`, so an arrival's rank is derived and \
         never"
    );
    println!(
        "  chosen. Constituents are keyed by (rank, surface): two occurrences at the SAME rank are \
         not"
    );
    println!(
        "  causally ordered relative to each other, so they share constituents; an occurrence at a \
         NEW"
    );
    println!(
        "  rank does not, and reaches back only along `⪯`. Those are two species of later material \
         and"
    );
    println!("  they can move different things.");
    println!();
    println!(
        "  arrival {:?} caused_by {:?} → ⪯ rank {} — co-present: {}",
        later.text,
        later.caused_by.iter().collect::<Vec<_>>(),
        later_response.arrival_rank,
        later_response.arrival_is_co_present
    );
    println!(
        "    new constituents {} · new contacts {} · new ⪯ edges {}",
        later_response.new_constituents, later_response.new_contacts, later_response.new_dependencies
    );
    println!(
        "    reached {} · reopened {} · saturated {} · untouched {}",
        later_response.reached.len(),
        later_response.reopened.len(),
        later_response.saturated.len(),
        later_response.untouched.len()
    );
    let moved_boundary = later_response.moved().len();
    println!(
        "    closed boundaries that moved: {moved_boundary}   founded {}   dissolved {}",
        later_response.founded.len(),
        later_response.dissolved.len()
    );
    let frame_moved = later_response
        .verdicts
        .iter()
        .filter(|verdict| {
            verdict.after.as_ref().is_some_and(|after| {
                let (before_pi, before_ports) = verdict.before.frame_reading();
                let (after_pi, after_ports) = after.frame_reading();
                before_pi != after_pi || before_ports != after_ports
            })
        })
        .count();
    println!("    closed boundaries whose PRESENT-FRAME reading (Π, Γ) moved: {frame_moved}");
    for verdict in later_response.verdicts.iter() {
        let Some(after) = verdict.after.as_ref() else {
            continue;
        };
        if after.frame_reading().1 == verdict.before.frame_reading().1 {
            continue;
        }
        println!("      {:?}", verdict.surface);
        println!(
            "        Γ before  {}",
            port_text(verdict.before.frame_reading().1)
        );
        println!("        Γ after   {}", port_text(after.frame_reading().1));
    }
    println!();
    println!(
        "  READ IT AS THE FINDING IT IS. A causally-later arrival changes an earlier compound's \
         VALENCE"
    );
    println!(
        "  — which ports it exposes, and in which polarity — and cannot change its closed boundary, \
         because"
    );
    println!(
        "  `⪯` is not `∂` and the cycle basis is built from `∂` alone. A co-present arrival can \
         change both."
    );
    println!(
        "  §IV names valence as *receiver-relative, not a permanent integer*, so this is the law \
         behaving,"
    );
    println!("  not a wall.");

    Ok(())
}

/// `r(Σ' − Σ) = r(Σ') − r(Σ)`, exhibited on every founded cycle sharing a contact with a standing
/// one.
///
/// This is what makes the residual **causal** rather than reported. The pairing is linear on the
/// cycle space, so a standing compound hands its whole obstruction into every cycle the arrival
/// founds through it, and a **saturated** one — `r_Σ = 0` — hands forward exactly nothing. Both
/// halves are theorems and neither is authored here. The left-hand side is evaluated by
/// `holonic_engine::running_integral::Cochain::evaluate` on a chain this module never sums; the
/// right by this module walking two boundaries.
fn exhibit_transport(response: &ArrivalResponse, chart: PhaseChart) -> Result<(), String> {
    println!("  ═══ THE RESIDUAL IS WHAT THE NEXT CONSTRUCTION IS BUILT FROM ═══");
    println!(
        "  `⟨w, ·⟩` is linear on the cycle space, so `r(Σ' − Σ) = r(Σ') − r(Σ)`: a standing compound"
    );
    println!(
        "  hands its WHOLE obstruction into every cycle the arrival founds through it, and a \
         saturated"
    );
    println!(
        "  one hands forward EXACTLY NOTHING. The left side is evaluated by the engine on a chain \
         this"
    );
    println!("  module never sums; the right by this module walking two boundaries.");
    let differentiated = response
        .complex
        .differentiate_all(chart)
        .map_err(|error| format!("admitted differentiate: {error:?}"))?;
    let view = response
        .complex
        .engine_view()
        .map_err(|error| format!("engine view: {error:?}"))?;
    let founded_surfaces = response
        .founded
        .iter()
        .map(|emission| emission.surface.clone())
        .collect::<BTreeSet<_>>();
    println!();
    println!(
        "    {:>26} {:>26} {:>7} {:>7} {:>10} {:>11}",
        "founded Σ'", "standing Σ", "r(Σ')", "r(Σ)", "r(Σ'−Σ)", "r(Σ')−r(Σ)"
    );
    let zero = BigInt::from(0);
    let mut held = 0usize;
    let mut taken = 0usize;
    let mut through_saturated = 0usize;
    for founded in &differentiated {
        if !founded_surfaces.contains(&founded.surface) {
            continue;
        }
        for standing in &differentiated {
            if standing.compound == founded.compound || founded_surfaces.contains(&standing.surface)
            {
                continue;
            }
            let shared = founded
                .reexposed
                .iter()
                .any(|left| standing.reexposed.iter().any(|right| left.bond == right.bond));
            if !shared {
                continue;
            }
            let difference = response
                .complex
                .residual_of_combination_in(
                    &[(founded.compound, 1), (standing.compound, -1)],
                    &view,
                )
                .map_err(|error| format!("combination: {error:?}"))?;
            let expected = &founded.residual - &standing.residual;
            taken += 1;
            if difference == expected {
                held += 1;
            }
            let saturated = standing.residual == zero;
            if saturated {
                through_saturated += 1;
            }
            println!(
                "    {:>26} {:>26} {:>7} {:>7} {:>10} {:>11}{}",
                elide(&founded.surface, 26),
                elide(&standing.surface, 26),
                founded.residual,
                standing.residual,
                difference,
                expected,
                if saturated {
                    "   ← SATURATED: r(Σ'−Σ) = r(Σ'). It handed forward nothing."
                } else {
                    ""
                }
            );
        }
    }
    if taken == 0 {
        println!("    (the arrival founded no cycle through a standing closed boundary)");
    }
    println!(
        "    linearity held on {held} of {taken} exhibited pairs; {through_saturated} of those run \
         through a compound whose residual is zero"
    );
    Ok(())
}

/// Mayer–Vietoris on the ADMITTED complex, with the cover `{standing body, arrival}`.
///
/// This is the question `gluing.rs` is actually for, and it is not the differentiation: given one
/// complex and two receivers on it, `δ_n: H_n(A∪B) → H_{n−1}(A∩B)` returns the classes the union
/// carries that neither piece does. Here the two receivers are *the body as it stood* and *what
/// arrived*, so the obstruction is exactly what the composition afforded and neither side had —
/// §V's *composition can create paths that no isolated cell affords*, computed rather than asserted.
fn exhibit_gluing(base: &IncidenceComplex, response: &ArrivalResponse) -> Result<(), String> {
    println!("  ═══ A5 — WHAT THE UNION CARRIES THAT NEITHER PIECE DOES ═══");
    let view = response
        .complex
        .engine_view()
        .map_err(|error| format!("engine view: {error:?}"))?;
    let complex = view.complex();
    let admitted = &response.complex;

    let mut standing_skeleton = BTreeSet::new();
    for at in 0..response.trace.base_bonds {
        standing_skeleton.extend(view.bond(at));
    }
    let mut arrived_skeleton = BTreeSet::new();
    for at in response.trace.base_bonds..admitted.bonds().len() {
        arrived_skeleton.extend(view.bond(at));
    }
    // A closed boundary belongs to the piece whose contacts it is built from; one built from both
    // goes to the arrival's piece, since it did not exist before.
    let mut standing_full = standing_skeleton.clone();
    let mut arrived_full = arrived_skeleton.clone();
    for at in 0..admitted.compounds().len() {
        let Some(cell) = view.compound(at) else {
            continue;
        };
        if admitted.compounds()[at]
            .bonds
            .iter()
            .any(|bond| *bond >= response.trace.base_bonds)
        {
            arrived_full.insert(cell);
        } else {
            standing_full.insert(cell);
        }
    }
    println!(
        "    the base complex carried {} constituents and {} contacts; the admitted one carries {} \
         and {}.",
        base.sites().len(),
        base.bonds().len(),
        admitted.sites().len(),
        admitted.bonds().len()
    );

    for (name, left, right, note) in [
        (
            "the 1-SKELETON cover",
            standing_skeleton,
            arrived_skeleton,
            "the standing contacts against the arrival's contacts, with every closed boundary left \
             out. This is the cover that can SEE a composed cycle, because a cycle running through \
             both pieces belongs to neither.",
        ),
        (
            "the FULL cover",
            standing_full,
            arrived_full,
            "the same split with the closed boundaries assigned. It is reported second and read \
             carefully: `closed_hull` drags every contact a 2-cell needs into that 2-cell's own \
             piece, so a founded cycle is handed WHOLE to the arrival and δ is structurally unable \
             to see it. A zero here is a property of the cover, not of the composition.",
        ),
    ] {
        let cover = Cover {
            left: complex
                .closed_hull(left)
                .map_err(|error| format!("standing hull: {error}"))?,
            right: complex
                .closed_hull(right)
                .map_err(|error| format!("arrival hull: {error}"))?,
        };
        println!();
        println!("    [{name}]  {note}");
        println!(
            "      standing {} cells · arrival {} cells · overlap {} · union {}",
            cover.left.len(),
            cover.right.len(),
            cover.overlap().len(),
            cover.union().len()
        );
        // Three pivot rules, because one is not a frame (`CLAUDE.md` §8).
        for rule in PivotRule::ALL {
            let reading = read_cover(complex, &cover, rule)
                .map_err(|error| format!("read cover: {error}"))?;
            println!(
                "      [{:>17}] δ rank per grade {:?}   torsion {:?}   Euler defect {}   rank \
                 bound {}",
                format!("{rule:?}"),
                reading.obstruction,
                reading.torsion_obstruction,
                reading.euler_defect,
                reading.rank_bound_holds
            );
            if reading.exhibits_obstruction() {
                for (grade, rank) in reading.obstructed_grades() {
                    println!(
                        "        grade {grade}: rank {rank} — {rank} class(es) the union carries \
                         that NEITHER the standing body NOR the arrival carries alone. §V: \
                         composition creates paths that no isolated cell affords."
                    );
                    if grade == 1 {
                        println!(
                            "        CROSS-CHECK: this module founded {} closed boundaries; \
                             Mayer–Vietoris returns rank {rank} — {}",
                            response.founded.len(),
                            if rank == response.founded.len() as i64 {
                                "the two frames agree, and they share no code path"
                            } else {
                                "THE TWO FRAMES DISAGREE"
                            }
                        );
                    }
                }
            } else {
                println!("        no class lives only in the union at this rule.");
            }
        }
    }
    Ok(())
}

/// Iterate the hand-up to its stopping point, collecting the successors at each grain above zero.
///
/// The iteration is cut where the successor population stops contracting, and the cut is declared
/// rather than run to exhaustion: a non-contracting hand-up is not converging on the event's one
/// atomic successor and iterating it further measures nothing.
fn tower(complex: &IncidenceComplex, chart: PhaseChart) -> Vec<Vec<Emission>> {
    let mut grains = Vec::new();
    let mut carried = complex.clone();
    let mut population = usize::MAX;
    loop {
        let Ok((emitted, next)) = carried.next_grain(chart) else {
            if let Ok(emitted) = carried.hand_up(chart) {
                grains.push(emitted);
            }
            break;
        };
        if emitted.len() >= population {
            grains.push(emitted);
            break;
        }
        population = emitted.len();
        grains.push(emitted);
        if next.compounds().is_empty() || population <= 1 {
            break;
        }
        carried = next;
    }
    grains
}

fn port_text(ports: &[(String, life::incidence_production::ExposedPolarity)]) -> String {
    ports
        .iter()
        .map(|(surface, polarity)| format!("{surface}:{}", polarity.name()))
        .collect::<Vec<_>>()
        .join("  ")
}

fn print_differentiation_head(differentiation: &Differentiation) {
    println!(
        "    [{:>2}] {:?}   r_Σ = {}   ⟨dw,Σ⟩ = {}   H = ({}, {})   Stokes {}",
        differentiation.compound,
        differentiation.surface,
        differentiation.residual,
        differentiation.coboundary_reading,
        differentiation.holonomy.cosine,
        differentiation.holonomy.sine,
        if differentiation.stokes_holds() { "✓" } else { "✗" }
    );
}

fn print_differentiation(differentiation: &Differentiation, emission: &Emission) {
    println!(
        "  [{:>2}] grain {} ← the successor {:?} at ⪯ rank {}",
        differentiation.compound, emission.grain, emission.surface, differentiation.causal_rank
    );
    println!("       ∂Σ — the contacts closure suppressed, handed back in traversal order:");
    for contact in &differentiation.reexposed {
        println!("         {}", contact.text());
    }
    println!(
        "       r_Σ = ⟨w, ∂Σ⟩ = {}      ⟨dw, Σ⟩ = {}      {}",
        differentiation.residual,
        differentiation.coboundary_reading,
        if differentiation.stokes_holds() {
            "STOKES HOLDS"
        } else {
            "STOKES FAILED — a defect in this module"
        }
    );
    println!(
        "       H = ({}, {})   chain gauge {:+}   supp_Σ = {} constituents over {} contacts",
        differentiation.holonomy.cosine,
        differentiation.holonomy.sine,
        differentiation.chain_gauge,
        differentiation.support.len(),
        differentiation.support_contacts.len()
    );
    // The closure this differentiation inverts named exactly these as departed.
    let departed = emission
        .residual
        .departed_contacts
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>();
    let restored = differentiation
        .reexposed
        .iter()
        .map(|contact| format!("{} ⟶ {}", contact.from, contact.to))
        .collect::<BTreeSet<_>>();
    println!(
        "       differentiation returns exactly what closure departed: {}",
        if departed == restored { "YES" } else { "NO" }
    );
}

fn report_arrival(response: &ArrivalResponse, differentiated: &[Differentiation]) {
    println!(
        "  the arrival: {:?}",
        response.arrival
    );
    println!(
        "    ⪯ rank {} (derived from `caused_by`, never chosen) — co-present with a standing rank: \
         {}",
        response.arrival_rank, response.arrival_is_co_present
    );
    println!(
        "    it founded {} new constituents, {} new contacts, {} new ⪯ edges, and re-trod {} \
         standing contacts",
        response.new_constituents,
        response.new_contacts,
        response.new_dependencies,
        response.trace.bond_multiplicity_delta.len()
    );
    println!();
    println!("  THE REOPENING LAW APPLIED, COMPOUND BY COMPOUND");
    println!(
        "    {:>3} {:>30} {:>8} {:>9} {:>10}",
        "Σ", "surface", "r_Σ", "reached", "verdict"
    );
    for differentiation in differentiated {
        let at = differentiation.compound;
        let verdict = if response.reopened.contains(&at) {
            "REOPENS"
        } else if response.saturated.contains(&at) {
            "saturated"
        } else {
            "untouched"
        };
        println!(
            "    {:>3} {:>30} {:>8} {:>9} {:>10}",
            at,
            elide(&differentiation.surface, 30),
            differentiation.residual,
            if response.reached.contains(&at) { "yes" } else { "no" },
            verdict
        );
    }
    println!(
        "    {} reached · {} reopened · {} saturated · {} untouched, of {} closed boundaries",
        response.reached.len(),
        response.reopened.len(),
        response.saturated.len(),
        response.untouched.len(),
        differentiated.len()
    );
}

fn print_artifact(response: &ArrivalResponse) {
    println!("  ═══ THE ARTIFACT — THE SUCCESSORS BEFORE AND AFTER, VERBATIM ═══");
    let moved = response.moved();
    println!(
        "  {} of {} closed boundaries moved. {} were founded that did not exist before; {} \
         dissolved.",
        moved.len(),
        response.verdicts.len(),
        response.founded.len(),
        response.dissolved.len()
    );
    let mut shown = 0usize;
    for verdict in &response.verdicts {
        if !verdict.moved {
            continue;
        }
        shown += 1;
        if shown > PRINTED {
            break;
        }
        println!();
        println!("  ── compound {} ──", verdict.compound);
        println!("     BEFORE  surface   {:?}", verdict.before.surface);
        println!(
            "             holonomy  {}   chain gauge {:+}",
            verdict.before.holonomy_text(),
            verdict.before.chain_gauge
        );
        println!(
            "             residual  {} internal contacts, multiplicity {}, {} constituents departed",
            verdict.before.residual.internal_contacts,
            verdict.before.residual.carried_multiplicity,
            verdict.before.residual.sites_departed
        );
        for contact in &verdict.before.residual.departed_contacts {
            println!("                       departed: {contact}");
        }
        println!(
            "             exposed   {}",
            port_text(verdict.before.frame_reading().1)
        );
        match verdict.after.as_ref() {
            None => {
                println!(
                    "     AFTER   this closed boundary NO LONGER EXISTS. The arrival's contact \
                     split it;"
                );
                println!(
                    "             the constituents are still there and the cycle they bounded is \
                     not."
                );
            }
            Some(after) => {
                println!("     AFTER   surface   {:?}", after.surface);
                println!(
                    "             holonomy  {}   chain gauge {:+}",
                    after.holonomy_text(),
                    after.chain_gauge
                );
                println!(
                    "             residual  {} internal contacts, multiplicity {}, {} constituents \
                     departed",
                    after.residual.internal_contacts,
                    after.residual.carried_multiplicity,
                    after.residual.sites_departed
                );
                for contact in &after.residual.departed_contacts {
                    println!("                       departed: {contact}");
                }
                println!("             exposed   {}", port_text(after.frame_reading().1));
            }
        }
    }
    if moved.len() > PRINTED {
        println!();
        println!("  … {} further moved closed boundaries", moved.len() - PRINTED);
    }
    println!();
    println!("  THE CLOSED BOUNDARIES THE ARRIVAL FOUNDED, WHICH DID NOT EXIST BEFORE:");
    for emission in response.founded.iter().take(PRINTED) {
        println!(
            "    {:?}   holonomy {}   {} internal contacts",
            emission.surface,
            emission.holonomy_text(),
            emission.residual.internal_contacts
        );
    }
    if response.founded.len() > PRINTED {
        println!("    … {} further", response.founded.len() - PRINTED);
    }
}

fn elide(text: &str, extent: usize) -> String {
    if text.chars().count() <= extent {
        return text.to_owned();
    }
    format!("{}…", text.chars().take(extent - 1).collect::<String>())
}

/// The declared material: a causal chain of three whose storage ordinals do not ascend with it.
fn declared_material() -> Vec<DeclaredOccurrence> {
    vec![
        DeclaredOccurrence {
            identity: "declared:b".to_owned(),
            storage_ordinal: 90,
            caused_by: BTreeSet::from(["declared:a".to_owned()]),
            text: "the arc bends the channel and the bends carry the return".to_owned(),
        },
        DeclaredOccurrence {
            identity: "declared:a".to_owned(),
            storage_ordinal: 91,
            caused_by: BTreeSet::new(),
            text: "the leader founds the channel and the channel carries the leader".to_owned(),
        },
        DeclaredOccurrence {
            identity: "declared:c".to_owned(),
            storage_ordinal: 12,
            caused_by: BTreeSet::from(["declared:b".to_owned()]),
            text: "the channel returns the leader and the leader founds the arc".to_owned(),
        },
    ]
}

/// A later arrival whose derived rank coincides with `declared:b`'s, because it shares its cause.
///
/// It therefore composes with the SAME constituents: it re-treads standing contacts and founds new
/// ones between constituents that are already on closed boundaries.
fn co_present_arrival() -> DeclaredOccurrence {
    DeclaredOccurrence {
        identity: "arrival:co-present".to_owned(),
        storage_ordinal: 7,
        caused_by: BTreeSet::from(["declared:a".to_owned()]),
        text: "the bends carry arc the".to_owned(),
    }
}

/// A later arrival caused by the last occurrence of the chain, so its rank is new.
fn causally_later_arrival() -> DeclaredOccurrence {
    DeclaredOccurrence {
        identity: "arrival:causally-later".to_owned(),
        storage_ordinal: 400,
        caused_by: BTreeSet::from(["declared:c".to_owned()]),
        text: "the channel returns the arc".to_owned(),
    }
}

/// The declared saturated material: a closed boundary whose residual is exactly zero.
fn saturated_material() -> Vec<DeclaredOccurrence> {
    vec![DeclaredOccurrence {
        identity: "saturated:a".to_owned(),
        storage_ordinal: 0,
        caused_by: BTreeSet::new(),
        text: "ab cc ab".to_owned(),
    }]
}

/// An arrival that reaches the saturated compound with genuinely new structure.
///
/// `ab ee cc` founds two contacts through **both** constituents the saturated compound's residual is
/// supported on, so the arrival genuinely reaches it with new cells rather than with a raised count.
/// The cycle it founds carries a **non-zero** residual of its own, so `r(Σ'−Σ) = r(Σ')` is a visible
/// statement rather than `0 = 0`. The only thing standing between the arrival and a transport out of
/// the compound is `r_Σ = 0`, which is exactly what the control is for.
fn saturated_arrival() -> DeclaredOccurrence {
    DeclaredOccurrence {
        identity: "saturated:arrival".to_owned(),
        storage_ordinal: 1,
        caused_by: BTreeSet::new(),
        text: "ab ee cc ab".to_owned(),
    }
}

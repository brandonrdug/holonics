use super::*;
use crate::lean_development::{DeclarationGrain, read_development};

/// Declarations whose bodies are causally different while their tactics are spelled alike, and
/// whose tactics differ while their causal situation is identical. A fixture that can only fail one
/// way proves nothing, so both directions of the spelling comparison have material here.
///
/// **`joined` is why the refinement test can pass and it earns its place.** `chained`'s `first`
/// feeds one later step, and so does `joined`'s `uno` — so an ascription-only reading cannot tell
/// them apart at horizon one: both have exactly one downstream slot and both downstreams carry a
/// statement. They differ only in what that downstream *is*: `second` is arrived at by one earlier
/// step, `tres` by two. That difference lives on [`MoveAxis::ArrivalsIn`] and nowhere else, which
/// is exactly a pair the causal panel must depart and the coarse panel must hold.
///
/// The binders are multi-character deliberately. [`crate::lean_development::BinderGrain`] defaults
/// to `MultiCharacter`, so `have u : …` founds no step at all at the inherited grain — measured
/// here first, which is how that aperture came to be declared rather than hidden.
///
/// Without it the coarse family already separates everything by **terminus** — whether a successor
/// exists at all — and the refinement departs nothing. That was measured before this declaration
/// was added, and it is the honest reason the fixture has four bodies rather than three.
const MATERIAL: &str = r#"
namespace Fixture

theorem chained (a b : Nat) : a + b = b + a := by
  have first : a + b = b + a := Nat.add_comm a b
  have second : a + b = b + a := first
  exact second

theorem flat (a b : Nat) : a + b = b + a := by
  have alpha : a + b = b + a := Nat.add_comm a b
  have beta : b + a = a + b := Nat.add_comm b a
  exact alpha

theorem obtained (a b : Nat) : a + b = b + a := by
  obtain third : a + b = b + a := Nat.add_comm a b
  obtain fourth : a + b = b + a := third
  exact fourth

theorem joined (a b : Nat) : a + b = b + a := by
  have uno : a + b = b + a := Nat.add_comm a b
  have dos : b + a = a + b := Nat.add_comm b a
  have tres : a + b = b + a := Eq.trans uno (Eq.symm dos)
  exact tres

end Fixture
"#;

fn complex() -> MoveComplex {
    let reading = read_development(MATERIAL, DeclarationGrain::EveryTopLevelDeclaration);
    MoveComplex::found(&reading.declarations)
}

fn cover(complex: &MoveComplex, declaration: &MoveDeclaration) -> MoveWorkCover {
    MoveWorkCover::exactly(&move_demand(complex, declaration))
}

fn every_move(complex: &MoveComplex) -> Vec<MoveOccurrence> {
    complex.occurrences().collect()
}

#[test]
fn the_material_founds_moves_and_their_arrivals() {
    let complex = complex();
    assert_eq!(
        complex.moves(),
        9,
        "three bodies of two binding steps and one of three"
    );
    assert!(
        complex.arrivals() > 0,
        "`second := first` is an arrival and the reading must see it"
    );
    assert!(
        complex.branch_aperture() > 0,
        "an aperture of zero would mean conduct reaches nothing"
    );
    assert_eq!(
        complex.formers(),
        2,
        "the fixture founds with `have` and `obtain` and nothing else"
    );
}

#[test]
fn an_empty_family_is_refused_rather_than_returning_one_block() {
    let complex = complex();
    let declaration = MoveDeclaration {
        candidates: every_move(&complex),
        family: MoveFamily::EMPTY,
        horizon: 1,
    };
    let focus = declaration.candidates[0];
    let cover = MoveWorkCover {
        items: usize::MAX,
        pair_chart: usize::MAX,
    };
    assert_eq!(
        species_fiber(&complex, focus, &declaration, &cover),
        Err(MoveSpeciesError::EmptyFamily)
    );
}

#[test]
fn a_single_candidate_is_refused_because_its_fiber_restates_the_declaration() {
    let complex = complex();
    let candidates = vec![every_move(&complex)[0]];
    let declaration = MoveDeclaration {
        candidates: candidates.clone(),
        family: MoveFamily::CAUSAL,
        horizon: 1,
    };
    let cover = MoveWorkCover {
        items: usize::MAX,
        pair_chart: usize::MAX,
    };
    assert_eq!(
        species_fiber(&complex, candidates[0], &declaration, &cover),
        Err(MoveSpeciesError::CandidatesTooFew(1))
    );
}

#[test]
fn the_work_cover_refuses_before_execution() {
    let complex = complex();
    let declaration = MoveDeclaration {
        candidates: every_move(&complex),
        family: MoveFamily::CAUSAL,
        horizon: 1,
    };
    let focus = declaration.candidates[0];
    let demand = move_demand(&complex, &declaration);
    let cover = MoveWorkCover {
        items: demand.items.saturating_sub(1),
        pair_chart: demand.pair_chart,
    };
    assert_eq!(
        species_fiber(&complex, focus, &declaration, &cover),
        Err(MoveSpeciesError::WorkCoverInsufficient { demand, cover })
    );
}

#[test]
fn the_focus_must_be_in_the_declared_population() {
    let complex = complex();
    let every = every_move(&complex);
    let declaration = MoveDeclaration {
        candidates: every[1..].to_vec(),
        family: MoveFamily::CAUSAL,
        horizon: 1,
    };
    let cover = cover(&complex, &declaration);
    assert_eq!(
        species_fiber(&complex, every[0], &declaration, &cover),
        Err(MoveSpeciesError::FocusNotDeclared)
    );
}

#[test]
fn the_species_is_plural_and_contains_its_focus() {
    let complex = complex();
    let declaration = MoveDeclaration {
        candidates: every_move(&complex),
        family: MoveFamily::of([MoveAxis::Ascribed]),
        horizon: 1,
    };
    let focus = declaration.candidates[0];
    let cover = cover(&complex, &declaration);
    let fiber = species_fiber(&complex, focus, &declaration, &cover).expect("the fiber returns");
    assert!(fiber.fiber.contains(&focus));
    assert!(
        fiber.is_plural(),
        "one ascription axis cannot separate this material: {:?}",
        fiber.fiber
    );
}

/// The refinement discipline of the token experiment, transposed: the richer family's fiber must be
/// a subset of the coarse one, and what departed is deposited by name.
#[test]
fn the_richer_family_refines_the_coarse_one_and_departures_are_named() {
    let complex = complex();
    let candidates = every_move(&complex);
    let focus = candidates[0];
    let coarse = MoveDeclaration {
        candidates: candidates.clone(),
        family: MoveFamily::of([MoveAxis::Ascribed]),
        horizon: 1,
    };
    let richer = MoveDeclaration {
        candidates,
        family: MoveFamily::CAUSAL,
        horizon: 1,
    };
    let cover = cover(&complex, &richer);
    let refinement =
        refine_species(&complex, focus, &coarse, &richer, &cover).expect("the refinement returns");
    for member in &refinement.richer.fiber {
        assert!(
            refinement.coarse.fiber.contains(member),
            "{member:?} appeared under the richer family and was absent under the coarse one, \
             which is not a refinement"
        );
    }
    assert!(
        refinement.moved(),
        "the causal axes departed nothing from an ascription-only reading, so on this material \
         they see nothing"
    );
    for departed in &refinement.departed {
        assert!(!refinement.retained.contains(departed));
    }
}

/// `MoveFamily::refines` is what makes a refinement a refinement. A sideways family is not one.
#[test]
fn a_sideways_family_does_not_refine() {
    assert!(MoveFamily::FULL.refines(MoveFamily::CAUSAL));
    assert!(MoveFamily::FULL.refines(MoveFamily::SPELLING));
    assert!(!MoveFamily::CAUSAL.refines(MoveFamily::SPELLING));
    assert!(!MoveFamily::SPELLING.refines(MoveFamily::CAUSAL));
    assert!(MoveFamily::CAUSAL.refines(MoveFamily::CAUSAL));
}

/// The relabelling control. It cannot fail, and the module says why: observations enter the
/// quotient by equality, so renaming every tactic moves no block. It is run because the centrifuge
/// failed exactly this control at 11 of 13 boundaries when its transport read bytes.
#[test]
fn renaming_every_founding_tactic_moves_no_block() {
    let complex = complex();
    let renamed = complex.with_renamed_formers(|former| format!("zzz-{former}-zzz"));
    let candidates = every_move(&complex);
    let focus = candidates[0];
    let declaration = MoveDeclaration {
        candidates,
        family: MoveFamily::FULL,
        horizon: 1,
    };
    let cover = cover(&complex, &declaration);
    let before = species_fiber(&complex, focus, &declaration, &cover).expect("before");
    let after = species_fiber(&renamed, focus, &declaration, &cover).expect("after");
    assert_eq!(before.fiber, after.fiber);
    assert_eq!(before.conduct_blocks, after.conduct_blocks);
    assert_eq!(before.memory_order, after.memory_order);
}

/// The check that CAN fail: if the causal panel returns the former-only panel's reading, the causal
/// axes added nothing and the species is the tactic's name in other clothes.
#[test]
fn the_causal_panel_is_not_the_spelling_panel() {
    let complex = complex();
    let candidates = every_move(&complex);
    let focus = candidates[0];
    let spelling = MoveDeclaration {
        candidates: candidates.clone(),
        family: MoveFamily::SPELLING,
        horizon: 1,
    };
    let causal = MoveDeclaration {
        candidates,
        family: MoveFamily::CAUSAL,
        horizon: 1,
    };
    let cover = cover(&complex, &causal);
    let by_spelling = species_fiber(&complex, focus, &spelling, &cover).expect("spelling");
    let by_cause = species_fiber(&complex, focus, &causal, &cover).expect("causal");
    assert_ne!(
        by_spelling.fiber, by_cause.fiber,
        "the two panels returned the same species, so the causal axes are reading the tactic name"
    );
}

/// A horizon is a declared receiver coordinate and a gauge. If widening it moves nothing on this
/// material, it is a vacuous gauge here and the reading must say so rather than imply depth.
#[test]
fn the_horizon_is_a_gauge_whose_orbit_is_exhibited() {
    let complex = complex();
    let candidates = every_move(&complex);
    let focus = candidates[0];
    let mut readings = Vec::new();
    for horizon in [0usize, 1, 2] {
        let declaration = MoveDeclaration {
            candidates: candidates.clone(),
            family: MoveFamily::CAUSAL,
            horizon,
        };
        let cover = cover(&complex, &declaration);
        readings.push(
            species_fiber(&complex, focus, &declaration, &cover)
                .expect("every horizon returns")
                .fiber,
        );
    }
    assert_ne!(
        readings[0], readings[1],
        "conduct at horizon 1 saw nothing horizon 0 did not, so the arrival graph is inert here"
    );
}

/// At horizon zero nothing but the common exposed face is presented, so every candidate is
/// identical and the fiber is the whole declared population. This is the anti-tautology floor: a
/// reading that returned a split here would be reading something it was not handed.
#[test]
fn the_common_exposed_face_collapses_everything_at_horizon_zero() {
    let complex = complex();
    let candidates = every_move(&complex);
    let focus = candidates[0];
    let declaration = MoveDeclaration {
        candidates: candidates.clone(),
        family: MoveFamily::FULL,
        horizon: 0,
    };
    let cover = cover(&complex, &declaration);
    let fiber = species_fiber(&complex, focus, &declaration, &cover).expect("the fiber returns");
    assert_eq!(fiber.fiber.len(), candidates.len());
    assert_eq!(fiber.conduct_blocks, 1);
}

/// Slot indexing must be a bijection between words and slots, or `successor` walks to the wrong
/// site and every fiber past horizon one is quietly wrong.
#[test]
fn every_word_round_trips_through_its_slot() {
    let complex = complex();
    let system = MoveSystem {
        complex: &complex,
        roots: vec![0],
        horizon: 2,
        axes: MoveFamily::FULL.axes(),
    };
    let stride = system.stride();
    let mut seen = BTreeSet::new();
    for slot in 0..stride {
        let word = system.word(slot).expect("every slot below the stride is a word");
        assert!(word.len() <= 2);
        assert_eq!(system.slot_of(&word), Some(slot));
        assert!(seen.insert(word), "two slots decoded to one word");
    }
    assert_eq!(seen.len() as u64, stride);
}

#[test]
fn the_declared_demand_is_what_the_system_presents() {
    let complex = complex();
    let candidates = every_move(&complex);
    let declaration = MoveDeclaration {
        candidates: candidates.clone(),
        family: MoveFamily::FULL,
        horizon: 1,
    };
    let demand = move_demand(&complex, &declaration);
    assert_eq!(demand.roots, candidates.len());
    assert_eq!(demand.items, demand.roots * demand.slots);
    let system = MoveSystem {
        complex: &complex,
        roots: (0..candidates.len()).collect(),
        horizon: 1,
        axes: MoveFamily::FULL.axes(),
    };
    assert!(
        system.items().len() <= demand.items,
        "the demand must bound what is presented, never undercount it"
    );
}

#[test]
fn an_absent_occurrence_is_named_rather_than_skipped() {
    let complex = complex();
    let absent = MoveOccurrence {
        declaration: 999,
        step: 999,
    };
    let declaration = MoveDeclaration {
        candidates: vec![absent, every_move(&complex)[0]],
        family: MoveFamily::CAUSAL,
        horizon: 1,
    };
    let cover = MoveWorkCover {
        items: usize::MAX,
        pair_chart: usize::MAX,
    };
    assert_eq!(
        species_fiber(&complex, absent, &declaration, &cover),
        Err(MoveSpeciesError::OccurrenceAbsent(absent))
    );
}

/// `isolated` and `unconsumed` are different populations, and conflating them is the error an
/// independent instrument caught. In the fixture `flat`'s `alpha` is named by the closing `exact`
/// and `beta` is named nowhere again: both are isolated, only one is unconsumed.
#[test]
fn the_isolated_population_is_not_the_unconsumed_one() {
    let complex = complex();
    let isolated: BTreeSet<MoveOccurrence> = complex.isolated().into_iter().collect();
    let unconsumed: BTreeSet<MoveOccurrence> = complex.unconsumed().into_iter().collect();
    for member in &unconsumed {
        assert!(
            isolated.contains(member),
            "an unconsumed move must also be isolated: nothing arrives from it either"
        );
    }
    assert!(
        unconsumed.len() < isolated.len(),
        "the fixture must contain an isolated move the closing term consumes, or this comparison \
         cannot fail: isolated {} unconsumed {}",
        isolated.len(),
        unconsumed.len()
    );
    for member in isolated.difference(&unconsumed) {
        assert_eq!(
            complex.terminally_consumed(*member),
            Some(true),
            "the difference between the two populations is exactly terminal consumption"
        );
    }
}

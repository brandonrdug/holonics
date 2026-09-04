//! THE TRAVERSAL COMPOSES AND THE HOP DOES NOT — the two-component link on real material.
//!
//! ## Why this driver exists
//!
//! `LaboratorySourceAtlas::enact` crosses every site a leader meets **as an independent junction**.
//! Each crossing is judged against the leader alone and then discarded into `Crosses` / `Defers`.
//! That is a **star** reading: `n` separate one-hop questions sharing one centre.
//!
//! A leader that reaches site B *through* site A has traversed a **path**, and a path has a
//! composite transport that no hop reports. Until 2026-08-15 the module could not have computed one
//! — its carrier was the scalar transmission, which **does not compose**:
//!
//! ```text
//!    tau_ij tau_jk − tau_ik  =  2Y_i(Y_i−Y_j)(Y_j−Y_k) / [(Y_i+Y_j)(Y_j+Y_k)(Y_i+Y_k)]
//! ```
//!
//! zero only when two admittances coincide. The transfer matrix `M(rho)` composes exactly and
//! **carries the reflected amplitude through the composition instead of beside it**, which is what
//! makes a composite `Gamma` sayable at all.
//!
//! ## What is measured, and the two readings are kept apart
//!
//! ```text
//!    STAR   what enact computes    each site against the leader, n independent junctions
//!    PATH   what the chain adds    the traversal composed, one transport and one composite Gamma
//! ```
//!
//! **Neither is the correct one.** They answer different questions, and the return exhibits both so
//! the difference is visible rather than assumed. What the driver claims is narrower and checkable:
//! *the composite is not recoverable from the hops*, which is the whole content of the matrix.
//!
//! ## The declared falsifiers
//!
//! 1. **The composite must not equal the product of the hop transmissions.** If it does on this
//!    material, the scalar carrier was sufficient and the matrix bought nothing here.
//! 2. **A traversal that reflects at every link must be able to compose to a rebase.** `1 -> 3 -> 1`
//!    reflects twice and returns the identity, because with no phase between two interfaces the
//!    returns cancel exactly — a zero-thickness layer is invisible. If no real sub-traversal shows
//!    this, the reading *"a reflecting chain cannot be a rebase"* would stand and the correction
//!    deposited on 2026-08-15 would be withdrawn.
//! 3. **The rescaling gauge must act.** Every invariance below is read through `DeclaredGauge`,
//!    which cannot be constructed from material its transformation left alone.
//!
//! ## Bars
//!
//! No count here is a cost. Every admittance is a population of the material — what the leader
//! carries and what a site shares — and no threshold selects anything: a junction that dilates past
//! the leader's chronology **defers**, retained by name with its exact reflection.

use std::collections::BTreeSet;
use std::path::PathBuf;

use holonic_engine::traversible_chain::{
    found, Admittance, Crossing, InteractionChain, Standing, TransferMatrix,
};
use holonic_structure::{DeclaredGauge, Disposition, Face};
use life::laboratory_language::{
    text_features, LaboratoryResearchLeader, LaboratorySourceAtlas, LaboratoryWorldReturn,
};
use relational_geometry::Rat;

fn repository_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn admittance(population: u64) -> Option<Admittance> {
    Admittance::declared(Rat::from_integer(population.into())).ok()
}

/// The admittance profile of one traversal, read off the material and nothing else.
///
/// The leader enters carrying its whole region; each site it reaches admits what it **shares**. The
/// profile is therefore `[|region|, M_1, M_2, ...]` in the atlas's own returned order — no ordering
/// is authored here and no site is selected.
///
/// **Each admittance is a `Face`, and that is not decoration.** A population is a scalar taken from
/// a relation — *this leader against this section* — and a bare `u64` deletes the relation and keeps
/// the magnitude, which is the float argument one grain down. `Face` carries both, so the traversal
/// below can name which site a link crossed instead of reporting that link 4,187 had admittance 2.
/// `holonic_structure::Face` has no constructor that yields a scalar without its relation.
fn profile_of(
    leader: &LaboratoryResearchLeader,
    returned: &LaboratoryWorldReturn,
) -> Vec<Face<u64, String>> {
    let mut profile = vec![Face::taken(
        leader.region.len() as u64,
        format!("leader:{}", leader.identity),
    )];
    for section in &returned.sections {
        profile.push(Face::taken(
            section.matched_features.len() as u64,
            section.source_identity.clone(),
        ));
    }
    profile
}

/// The scalar faces alone, for the arithmetic that genuinely only needs them.
fn scalars(profile: &[Face<u64, String>]) -> Vec<u64> {
    profile.iter().map(|face| *face.descend()).collect()
}

fn chain_over(profile: &[u64]) -> Option<InteractionChain<u64>> {
    let source = admittance(profile[0])?;
    let mut chain = found(profile[0], &source, Standing::NoTravelingSection);
    for pair in profile.windows(2) {
        let (incident, transmitted) = (admittance(pair[0])?, admittance(pair[1])?);
        let crossing = Crossing::meet(&incident, &transmitted).ok()?;
        chain.carry(
            crossing,
            pair[1],
            Standing::Carrying(Rat::from_integer(pair[1].into())),
        );
    }
    Some(chain)
}

fn pair(value: &Rat) -> String {
    format!("{} : {}", value.numer(), value.denom())
}

fn main() {
    let root = repository_root();
    println!("THE TRAVERSAL COMPOSES AND THE HOP DOES NOT");
    println!("  material  {}", root.display());

    let atlas = LaboratorySourceAtlas::mount_repository(&root).expect("the repository mounts");
    let receipt = atlas.receipt();
    println!(
        "  atlas     source_files {}   theory {}   rust {}   features {}",
        receipt.source_files,
        receipt.theory_sections,
        receipt.rust_source_sections,
        receipt.indexed_features
    );
    assert!(
        receipt.theory_sections > 0 && receipt.rust_source_sections > 0,
        "a blind atlas returning a large number reads exactly like a working one"
    );

    // ── the leader, whose region is derived from a real question and never authored ────────────
    let question = "what carries the reflected amplitude through a composed junction";
    let region: BTreeSet<String> = text_features(question);
    let leader = LaboratoryResearchLeader {
        identity: "the-composing-leader".to_owned(),
        question: question.to_owned(),
        region: region.clone(),
        // The horizon is the caller's declared chronology, not a count of sections. `MAX` here so
        // nothing defers on the chronology and the whole met population enters the profile — the
        // deferral law is exercised by its own owner's tests and is not the subject.
        horizon: u64::MAX,
        generation: 0,
        caused_by_clauses: BTreeSet::new(),
    };

    let returned = atlas.enact(&leader).expect("the leader returns");
    println!(
        "\n  STAR      region {}   complete {}   crossed {}   omitted {}   deferred {}",
        region.len(),
        returned.complete_population,
        returned.sections.len(),
        returned.omitted_population,
        returned.deferred.len()
    );
    assert!(
        !returned.sections.is_empty(),
        "the traversal reached nothing, so there is no path to compose"
    );

    let faced = profile_of(&leader, &returned);
    let profile = scalars(&faced);
    let chain = chain_over(&profile).expect("every admittance is a positive population");

    // ── what the star reading returns, per hop, against the leader ─────────────────────────────
    let mut hop_transmissions: Vec<Rat> = Vec::new();
    let mut reflecting_links = 0usize;
    for pair_of in profile.windows(2) {
        let crossing = Crossing::meet(
            &admittance(pair_of[0]).expect("positive"),
            &admittance(pair_of[1]).expect("positive"),
        )
        .expect("admits");
        if !crossing.is_matched() {
            reflecting_links += 1;
        }
        hop_transmissions.push(crossing.transmission());
    }
    let scalar_product = hop_transmissions
        .iter()
        .fold(Rat::from_integer(1.into()), |carried, hop| carried * hop);

    // ── what the PATH reading returns, which no hop can ────────────────────────────────────────
    let composite: TransferMatrix = chain.compose();
    let composite_transmission = composite.transmission().expect("a through entry");
    let composite_reflection = composite.reflection().expect("a through entry");

    println!(
        "  PATH      hops {}   reflecting links {}",
        chain.hops(),
        reflecting_links
    );
    println!(
        "            composite tau      {}",
        pair(&composite_transmission)
    );
    println!(
        "            composite Gamma    {}",
        pair(&composite_reflection)
    );
    println!("            product of hop tau {}", pair(&scalar_product));
    println!(
        "            disposition {:?}   is_rebase {}",
        chain.disposition(),
        chain.is_rebase()
    );

    // ── FALSIFIER 1 · the composite is not the product of the hops ─────────────────────────────
    assert!(
        reflecting_links > 0,
        "every link matched, so the composition question is vacuous on this material"
    );
    assert_ne!(
        composite_transmission, scalar_product,
        "FALSIFIED: the scalar product reproduced the composite, so the matrix bought nothing here"
    );
    println!(
        "\n  falsifier 1  the composite differs from the hop product   HELD  ({} against {})",
        pair(&composite_transmission),
        pair(&scalar_product)
    );

    // ── FALSIFIER 2 · a reflecting traversal that composes to a rebase ─────────────────────────
    //
    // Searched over the REAL profile's own sub-traversals rather than authored. An out-and-back —
    // any window whose two ends carry the same admittance — reflects at every link and must
    // compose to the identity, because with no phase between interfaces the returns cancel exactly.
    let mut out_and_back: Option<(usize, usize, Vec<u64>)> = None;
    'search: for start in 0..profile.len() {
        for end in (start + 2)..profile.len() {
            if profile[start] != profile[end] {
                continue;
            }
            let window = &profile[start..=end];
            if window.windows(2).all(|hop| hop[0] == hop[1]) {
                // Every link already matched — a rebase for the trivial reason. Not the case.
                continue;
            }
            out_and_back = Some((start, end, window.to_vec()));
            break 'search;
        }
    }
    match out_and_back {
        Some((start, end, window)) => {
            // THE FACE EARNS ITS KEEP HERE. The window is a stretch of the profile; without the
            // relation this could only report indices, and `0..=9697` names nothing. With it the
            // two ends are addressable, which is what makes an out-and-back a claim about the
            // MATERIAL rather than about the array.
            println!(
                "               ends addressed   {}  ->  {}",
                faced[start].reopen(),
                faced[end].reopen()
            );
            let sub = chain_over(&window).expect("positive populations");
            let sub_composite = sub.compose();
            let reflected_links = window.windows(2).filter(|hop| hop[0] != hop[1]).count();
            let distinct: BTreeSet<u64> = window.iter().copied().collect();
            println!(
                "  falsifier 2  out-and-back {start}..={end}   links {}   reflecting {reflected_links}   \
                 ends {} = {}   distinct populations {:?}",
                window.len() - 1,
                window[0],
                window[window.len() - 1],
                distinct
            );
            println!(
                "               composite Gamma {}   is_rebase {}",
                pair(&sub_composite.reflection().expect("a through entry")),
                sub.is_rebase()
            );
            assert!(
                reflected_links > 0,
                "a window with no reflecting link cannot test the cancellation"
            );
            assert!(
                num_traits::Zero::is_zero(&sub_composite.reflection().expect("a through entry")),
                "FALSIFIED: an out-and-back left a reflected component, so the returns did not cancel"
            );
            println!("               the returns cancel exactly                HELD");
        }
        None => {
            println!(
                "  falsifier 2  no out-and-back window in this profile — UNDETERMINED, and reported \
                 rather than passed. The material carries no variation in the property under test."
            );
        }
    }

    // ── FALSIFIER 3 · the rescaling gauge, and it must act ─────────────────────────────────────
    //
    // The horizon law on the traversal itself: scaling every population by a common factor is a
    // change of the frame the counts are taken in. Every RATIO must survive it and every MAGNITUDE
    // must move. `DeclaredGauge` refuses to exist unless the transformation acted, so the survival
    // below is evidence rather than a statement about an orbit that never happened.
    let scaled: Vec<u64> = profile.iter().map(|population| population * 3).collect();
    let gauge = DeclaredGauge::of(profile.clone(), scaled.clone())
        .expect("a threefold rescaling acts on every positive population");
    println!(
        "\n  gauge     threefold rescaling moved {} of {} members",
        gauge.witness().len(),
        profile.len()
    );

    let scaled_chain = chain_over(&scaled).expect("positive populations");
    let scaled_composite = scaled_chain.compose();
    assert_eq!(
        composite, scaled_composite,
        "the composed transport depends only on the ratios and must cross the frame boundary"
    );
    // The anti-vacuity arm: the populations themselves are magnitudes and move at every member.
    assert_eq!(
        gauge.projection_moved(|population: &u64| *population),
        (0..profile.len()).collect::<Vec<_>>(),
        "every population moved, so the invariance above is not vacuous"
    );
    println!("            composite transport UNMOVED · every population MOVED   HELD");

    // ── what the star reading structurally cannot say ──────────────────────────────────────────
    //
    // Reported as the driver's actual return: the composite is a property of the ORDER, and the
    // star has no order. Reversing the traversal is a relabelling for the star and a different
    // path for the chain — and on an abelian interface family it is the same transport, which is
    // itself the measurement rather than an assumption.
    let mut reversed = profile.clone();
    reversed.reverse();
    let reversed_composite = chain_over(&reversed)
        .expect("positive populations")
        .compose();
    let reversed_reflection = reversed_composite.reflection().expect("a through entry");
    println!(
        "\n  order     forward Gamma {}   reversed Gamma {}",
        pair(&composite_reflection),
        pair(&reversed_reflection)
    );

    // AND THE HAND IS WHAT MOVED. Reversing exchanges incident and transmitted, so `rho -> 1/rho`
    // and `Gamma -> −Gamma`. The MAGNITUDE of the composite is a function of the two ends alone —
    // the family is abelian, so the route between them contributes nothing — while the HAND is a
    // function of the direction of travel. A magnitude reader calls these two traversals identical.
    // That is the phase-object theorem on this carrier, and it is measured here rather than cited.
    assert_eq!(
        &(-composite_reflection.clone()),
        &reversed_reflection,
        "reversal must negate the composite reflection exactly"
    );
    assert!(
        !num_traits::Zero::is_zero(&composite_reflection),
        "a zero reflection would make the negation above vacuous"
    );
    println!(
        "            the magnitude is a function of the two ENDS — the family is abelian, so the route\n\
         \x20           between them contributes nothing. THE HAND IS NOT: reversal negates Gamma exactly,\n\
         \x20           and a magnitude reader calls these two traversals identical. It is also why no\n\
         \x20           holonomy lives here — a closed traversal returns the identity BY CONSTRUCTION,\n\
         \x20           which is a receipt that could not have come out otherwise."
    );

    println!("\n  DISPOSITION  {:?}", chain.disposition());
    assert_eq!(
        chain.disposition(),
        Disposition::Reached,
        "the traversal crossed at least one junction, so the chain reached"
    );
    println!("  the traversal composes; the hop does not.");
}

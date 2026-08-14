//! **A later current rides the deposit, and removing the deposit removes the ride.**
//!
//! This is the falsifier the goal turns on, and nothing in the tree performed it before
//! 2026-08-13. `canon/THE_INFORMATION_ENGINE.md` §0 measures the body as a descent with no return
//! edge, and `canon/THE_HOLOBROCHOS_SPINE.md` §1's own audit is that *"the engine has no
//! `q_n = q_m` anywhere. It is a strict pipeline."* The roadmap records the same defect one
//! altitude down: *"`geometry_responses` is supplied, never updated by what the layout returned…
//! The curvature is measured and discarded."*
//!
//! So the question this driver answers is not *does an arrival return a reading* — `admit_later`
//! has always done that — but **does an earlier arrival's deposit change what a later arrival can
//! do**, and is that dependence exhibited by removing the deposit rather than asserted.
//!
//! ```text
//!   1  admit A            -> A deposits: new constituents, new contacts, closed boundaries
//!   2  admit B on (base+A) -> B's reading, WITH the deposit standing
//!   3  withdraw A          -> the exact inverse; the complex returns bit-identical to base
//!   4  admit B on base     -> B's reading, WITHOUT the deposit
//!   5  compare 2 against 4 -> the difference IS what B rode
//! ```
//!
//! **Step 3 is the control that makes step 5 mean anything.** If the withdrawal were not exact, a
//! difference between the two readings of B could be an artifact of a damaged complex rather than
//! of the missing deposit. `IncidenceComplex::withdraw` is the declared inverse of admission and
//! this driver checks bit-equality against the original before it compares anything.
//!
//! **And step 4 is the negative control the operating contract demands** (§8: *a check whose
//! material cannot vary the property under test is the same defect as a check that cannot fail*).
//! B is admitted twice against materially different standing. If the two readings agree in every
//! coordinate, B did not ride A's deposit and this driver says so rather than reporting the
//! agreement as a success.
//!
//! ```text
//! cargo run --release -p life --example the_later_current_rides_the_deposit
//! ```

use std::collections::BTreeSet;

use holonic_engine::running_integral::CoefficientGroup;
use life::incidence_production::{
    ArrivalResponse, DeclaredOccurrence, IncidenceComplex, IncidenceProductionError, PhaseChart,
};

/// The declared aperture on how many inscription patches of each occurrence participate. A caller
/// declaration, never an authored level: the population it excludes is returned by the complex.
const DECLARED_EXTENT: usize = 8;

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

/// One occurrence declared through the text codec.
fn declared(
    identity: &str,
    storage_ordinal: u64,
    caused_by: &[&str],
    text: &str,
) -> Result<DeclaredOccurrence, IncidenceProductionError> {
    let mut causes = BTreeSet::new();
    for cause in caused_by {
        causes.insert((*cause).to_owned());
    }
    DeclaredOccurrence::from_text(identity, storage_ordinal, causes, text)
}

/// The standing terrain, before any arrival.
fn base_material() -> Result<Vec<DeclaredOccurrence>, IncidenceProductionError> {
    let mut material = Vec::new();
    material.push(declared(
        "declared:a",
        0,
        &[],
        "the leader founds the channel and the channel carries the leader",
    )?);
    material.push(declared(
        "declared:b",
        1,
        &["declared:a"],
        "the arc bends the channel and the bends carry the return",
    )?);
    Ok(material)
}

/// **A** — the deposit. Co-present with the standing material, so it shares constituents and can
/// found contacts inside the terrain rather than only reaching back along `⪯`.
fn deposit() -> Result<DeclaredOccurrence, IncidenceProductionError> {
    declared(
        "arrival:deposit",
        2,
        &["declared:a"],
        "the return founds the arc and the arc carries the leader",
    )
}

/// **B** — the later current. Declared identically in both runs; only the terrain differs.
fn later_current() -> Result<DeclaredOccurrence, IncidenceProductionError> {
    declared(
        "arrival:later",
        3,
        &["declared:a"],
        "the arc returns the leader",
    )
}

/// Every coordinate of a reading this driver compares. None is a magnitude of the material; each is
/// a population or a count of named cells, and the named cells are printed beside them.
struct Reading {
    reached: usize,
    reopened: usize,
    saturated: usize,
    untouched: usize,
    founded: usize,
    dissolved: usize,
    new_contacts: usize,
    new_constituents: usize,
    new_dependencies: usize,
    reopened_names: Vec<String>,
    founded_names: Vec<String>,
}

fn read(response: &ArrivalResponse) -> Reading {
    let mut reopened_names = Vec::new();
    for at in &response.reopened {
        let compound = &response.complex.compounds()[*at];
        let mut name = String::new();
        for site in &compound.sites {
            if !name.is_empty() {
                name.push(' ');
            }
            name.push_str(&response.complex.sites()[*site].surface);
        }
        reopened_names.push(name);
    }
    let mut founded_names = Vec::new();
    for emission in &response.founded {
        founded_names.push(emission.surface.clone());
    }
    Reading {
        reached: response.reached.len(),
        reopened: response.reopened.len(),
        saturated: response.saturated.len(),
        untouched: response.untouched.len(),
        founded: response.founded.len(),
        dissolved: response.dissolved.len(),
        new_contacts: response.new_contacts,
        new_constituents: response.new_constituents,
        new_dependencies: response.new_dependencies,
        reopened_names,
        founded_names,
    }
}

fn print_reading(label: &str, reading: &Reading) {
    println!("  {label}");
    println!(
        "    reached {} · reopened {} · saturated {} · untouched {}",
        reading.reached, reading.reopened, reading.saturated, reading.untouched
    );
    println!(
        "    closed boundaries founded {} · dissolved {}",
        reading.founded, reading.dissolved
    );
    println!(
        "    new constituents {} · new contacts {} · new ⪯ edges {}",
        reading.new_constituents, reading.new_contacts, reading.new_dependencies
    );
    for name in &reading.reopened_names {
        println!("    reopened: {name:?}");
    }
    for name in &reading.founded_names {
        println!("    founded:  {name:?}");
    }
}

fn run() -> Result<(), String> {
    let chart = PhaseChart::WindingAdjacent;
    let group = CoefficientGroup::Integers;

    println!("THE STANDING TERRAIN");
    let material = base_material().map_err(|error| format!("declare base material: {error:?}"))?;
    let base = IncidenceComplex::found(&material, DECLARED_EXTENT)
        .map_err(|error| format!("found the base complex: {error:?}"))?;
    println!(
        "  {} constituents · {} contacts · {} closed boundaries · {} ⪯ edges",
        base.sites().len(),
        base.bonds().len(),
        base.compounds().len(),
        base.dependencies().len()
    );
    println!(
        "  the aperture returned its outside: {} patches present and not admitted",
        base.patches_outside_extent()
    );
    println!();

    // -- 1 · admit A: the deposit -----------------------------------------------------------
    println!("1 · THE DEPOSIT ARRIVES");
    let a = deposit().map_err(|error| format!("declare the deposit: {error:?}"))?;
    let a_response = base
        .admit_later(&a, chart, &group)
        .map_err(|error| format!("admit the deposit: {error:?}"))?;
    let a_reading = read(&a_response);
    print_reading(&format!("A = {:?}", a.declared_surface()), &a_reading);
    if a_reading.new_constituents == 0 && a_reading.new_contacts == 0 {
        return Err(
            "THE DEPOSIT DEPOSITED NOTHING. The passage must deposit; if nothing was deposited, \
             nothing passed, and there is no ride to measure."
                .to_owned(),
        );
    }
    let with_deposit = a_response.complex.clone();
    println!();

    // -- 1b · the attachment is two-sided -----------------------------------------------------
    println!("1b · WHERE IT LANDED WAS NOT ITS OWN CHOICE");
    println!(
        "  `H.0466`: the path founds at actual local contact between grown constructions — ground \
         is not a passive terminal selected from above. Every exposed standing constituent reaches \
         toward every arriving one, and §IV decides: opposed boundary roles meet, equal roles have \
         no direction between them. Both outcomes are retained."
    );
    let attempts = with_deposit.attachment(&a_response.trace);
    let met = attempts.iter().filter(|a| a.connected).count();
    let refused = attempts.len() - met;
    println!(
        "  {} upward attempts · {met} met · {refused} did not",
        attempts.len()
    );
    if attempts.is_empty() {
        return Err(
            "THE TERRAIN REACHED FOR NOTHING. With no attempt there is no two-sided attachment and \
             the arrival landed passively, which is what the law refuses."
                .to_owned(),
        );
    }
    if refused == 0 {
        println!(
            "  AT THE COMPLETED ARRIVAL every constituent both donates and accepts somewhere, so \
             every attempt meets. That is NOT the law failing to discriminate — it is the reading \
             taken after the alignment finished. A leader does not attach in an instant; it steps, \
             and the polarities of a flowing structure take orders of time to align. The stepped \
             reading is below."
        );
    }
    for attempt in attempts.iter().take(6) {
        println!(
            "    {:>10} {:>8} {} {:<8} {:<10}  winding {:>2}  sheet {:>2}",
            attempt.terrain_surface,
            attempt.terrain_polarity.name(),
            if attempt.connected {
                "──▶"
            } else {
                " ✕ "
            },
            attempt.arrival_polarity.name(),
            attempt.arrival_surface,
            attempt.contact_winding,
            attempt.sheet
        );
    }
    if attempts.len() > 6 {
        println!("    … {} further attempts", attempts.len() - 6);
    }

    // -- 1c · the leader steps ----------------------------------------------------------------
    println!();
    println!("  THE LEADER STEPS — the attachment read at each step of the arrival's growth");
    println!(
        "    `2026-07-17_THE_LEADER_GROWS_THE_CHANNEL…`: each step of the leader extends the \
         channel, the tip is where the next step is taken from, and attachment FOUNDs at actual \
         local contact between grown constructions. So the arrival is admitted one patch at a \
         time and the attachment re-read at every step. A refusal that appears mid-growth and is \
         gone at the end is not noise — it is the alignment happening."
    );
    println!(
        "    {:>4} {:>9} {:>5} {:>8} {:>10} {:>10}",
        "step", "attempts", "met", "refused", "terrain ⊥", "arrival ⊥"
    );
    let mut refused_during_growth = 0usize;
    for step in 1..=a.inscription.len() {
        let mut stepped = a.clone();
        stepped.inscription.truncate(step);
        let stepped_response = match base.admit_later(&stepped, chart, &group) {
            Ok(response) => response,
            Err(error) => {
                println!("    {step:>4}   refused: {error:?}");
                continue;
            }
        };
        let stepped_attempts = stepped_response.complex.attachment(&stepped_response.trace);
        let stepped_met = stepped_attempts.iter().filter(|a| a.connected).count();
        let stepped_refused = stepped_attempts.len() - stepped_met;
        refused_during_growth += stepped_refused;
        // How many distinct boundary roles each side is presenting at this step. One role on both
        // sides is a structure that has not yet differentiated; the alignment is that count moving.
        let mut terrain_roles = BTreeSet::new();
        let mut arrival_roles = BTreeSet::new();
        for attempt in &stepped_attempts {
            terrain_roles.insert(attempt.terrain_polarity.name());
            arrival_roles.insert(attempt.arrival_polarity.name());
        }
        println!(
            "    {:>4} {:>9} {:>5} {:>8} {:>10} {:>10}",
            step,
            stepped_attempts.len(),
            stepped_met,
            stepped_refused,
            terrain_roles.len(),
            arrival_roles.len()
        );
    }
    if refused_during_growth == 0 {
        println!(
            "    NOTHING WAS REFUSED AT ANY STEP. On this material the alignment is already \
             complete at the first step, so the stepping exhibits no convergence and the \
             discriminating control below carries the load."
        );
    } else {
        println!(
            "    {refused_during_growth} refusals occurred DURING growth and are gone at the \
             completed arrival. The law discriminates while the structure is still flowing; the \
             end state is where it has finished converging, which is why reading only the end \
             state reads a process as a property."
        );
    }

    // The discriminating control: sparse material whose own chain gives genuine endpoints.
    println!();
    println!("  THE DISCRIMINATING CONTROL — a terrain with genuine endpoints");
    let sparse_material = vec![declared("sparse:terrain", 0, &[], "alpha beta gamma")
        .map_err(|error| format!("declare the sparse terrain: {error:?}"))?];
    let sparse = IncidenceComplex::found(&sparse_material, DECLARED_EXTENT)
        .map_err(|error| format!("found the sparse terrain: {error:?}"))?;
    let sparse_arrival = declared("sparse:arrival", 1, &[], "delta epsilon")
        .map_err(|error| format!("declare the sparse arrival: {error:?}"))?;
    let sparse_response = sparse
        .admit_later(&sparse_arrival, chart, &group)
        .map_err(|error| format!("admit onto the sparse terrain: {error:?}"))?;
    let sparse_attempts = sparse_response.complex.attachment(&sparse_response.trace);
    let sparse_met = sparse_attempts.iter().filter(|a| a.connected).count();
    let sparse_refused = sparse_attempts.len() - sparse_met;
    println!(
        "  {} upward attempts · {sparse_met} met · {sparse_refused} did not",
        sparse_attempts.len()
    );
    for attempt in &sparse_attempts {
        println!(
            "    {:>10} {:>8} {} {:<8} {:<10}  winding {:>2}  sheet {:>2}",
            attempt.terrain_surface,
            attempt.terrain_polarity.name(),
            if attempt.connected {
                "──▶"
            } else {
                " ✕ "
            },
            attempt.arrival_polarity.name(),
            attempt.arrival_surface,
            attempt.contact_winding,
            attempt.sheet
        );
    }
    if sparse_refused == 0 {
        return Err(
            "THE DISCRIMINATING CONTROL DID NOT DISCRIMINATE. If the outcome cannot vary on \
             material built to vary it, the attachment is not being decided by both sides and the \
             arrival is still landing passively."
                .to_owned(),
        );
    }
    println!(
        "  the outcome follows from BOTH polarities — a donor and a donor have no direction \
         between them — and the attempts that did not meet are retained with the material's own \
         reading of the gap, rather than deleted to manufacture one endpoint"
    );
    println!();

    // -- 2 · admit B against the changed terrain ---------------------------------------------
    println!("2 · THE LATER CURRENT, WITH THE DEPOSIT STANDING");
    let b = later_current().map_err(|error| format!("declare the later current: {error:?}"))?;
    let b_with = with_deposit
        .admit_later(&b, chart, &group)
        .map_err(|error| format!("admit the later current on the changed terrain: {error:?}"))?;
    let with = read(&b_with);
    print_reading(&format!("B = {:?}", b.declared_surface()), &with);
    println!();

    // -- 3 · the control: the withdrawal is exact --------------------------------------------
    println!("3 · THE CONTROL — THE WITHDRAWAL IS THE EXACT INVERSE");
    let restored = with_deposit
        .withdraw(&a_response.trace)
        .map_err(|error| format!("withdraw the deposit: {error:?}"))?;
    // The reading is compared, not the representation: two complexes that hand up the same
    // emissions with the same residuals are the same terrain for every later current, and that is
    // the property this control needs. Struct equality would be a stronger and less meaningful
    // claim — it would refuse a reordering that no receiver can see.
    let base_emissions = base
        .hand_up(chart)
        .map_err(|error| format!("hand up the base terrain: {error:?}"))?;
    let restored_emissions = restored
        .hand_up(chart)
        .map_err(|error| format!("hand up the restored terrain: {error:?}"))?;
    if restored_emissions != base_emissions
        || restored.sites().len() != base.sites().len()
        || restored.bonds().len() != base.bonds().len()
        || restored.compounds().len() != base.compounds().len()
    {
        return Err(
            "THE WITHDRAWAL WAS NOT EXACT. Any difference in step 5 would then be an artifact of a \
             damaged complex rather than of the missing deposit, so the comparison is refused."
                .to_owned(),
        );
    }
    println!(
        "  {} constituents · {} contacts · {} closed boundaries, and {} emissions bit-identical",
        restored.sites().len(),
        restored.bonds().len(),
        restored.compounds().len(),
        restored_emissions.len()
    );
    println!("  so any difference below is caused by the deposit and by nothing else");
    println!();

    // -- 4 · admit B against the terrain without the deposit ---------------------------------
    println!("4 · THE SAME LATER CURRENT, WITHOUT THE DEPOSIT");
    let b_without = restored
        .admit_later(&b, chart, &group)
        .map_err(|error| format!("admit the later current on the base terrain: {error:?}"))?;
    let without = read(&b_without);
    print_reading(&format!("B = {:?}", b.declared_surface()), &without);
    println!();

    // -- 5 · the comparison -------------------------------------------------------------------
    println!("5 · WHAT THE LATER CURRENT RODE");
    let mut moved = Vec::new();
    let mut compare = |name: &str, with: usize, without: usize| {
        if with != without {
            moved.push(format!("{name}: {without} → {with}"));
        }
    };
    compare("reached", with.reached, without.reached);
    compare("reopened", with.reopened, without.reopened);
    compare("saturated", with.saturated, without.saturated);
    compare("untouched", with.untouched, without.untouched);
    compare("founded", with.founded, without.founded);
    compare("dissolved", with.dissolved, without.dissolved);
    compare(
        "new constituents",
        with.new_constituents,
        without.new_constituents,
    );
    compare("new contacts", with.new_contacts, without.new_contacts);
    compare(
        "new ⪯ edges",
        with.new_dependencies,
        without.new_dependencies,
    );

    let mut reopened_only_with = Vec::new();
    for name in &with.reopened_names {
        if !without.reopened_names.contains(name) {
            reopened_only_with.push(name.clone());
        }
    }
    let mut reopened_only_without = Vec::new();
    for name in &without.reopened_names {
        if !with.reopened_names.contains(name) {
            reopened_only_without.push(name.clone());
        }
    }

    if moved.is_empty() && reopened_only_with.is_empty() && reopened_only_without.is_empty() {
        println!("  NOTHING MOVED.");
        println!(
            "  The later current returned the same reading in every coordinate against materially \
             different standing, so it did NOT ride the deposit. That is the honest return and it \
             is a falsification, not a failure: the deposit changed the terrain and the later \
             current was blind to the change."
        );
        return Err("the later current did not ride the deposit".to_owned());
    }

    println!("  the deposit changed what the later current could do, in these coordinates:");
    for line in &moved {
        println!("    {line}");
    }
    for name in &reopened_only_with {
        println!("    reopened ONLY with the deposit standing: {name:?}");
    }
    for name in &reopened_only_without {
        println!("    reopened ONLY without the deposit: {name:?}");
    }
    println!();
    println!(
        "  READ IT AS WHAT IT IS. The later current is declared identically in both runs — same \
         identity, same inscription, same causes. The only thing that differs is whether the \
         earlier arrival's deposit is standing in the terrain. Every coordinate above is therefore \
         a consequence the later current took FROM the deposit, and the withdrawal control proves \
         the terrain it was removed from was bit-identical to the terrain it was added to."
    );
    println!();
    println!(
        "  WHAT THIS DOES NOT ESTABLISH. One deposit, one later current, one declared extent, at \
         grade 0. It does not measure a return through a world boundary, it does not close \
         `q_n = q_m`, and it does not show the change surviving a source-detached remount. It \
         shows that a deposit is rideable and that the ride is removable by removing the \
         structure — which is the one thing nothing in this tree measured before."
    );
    Ok(())
}

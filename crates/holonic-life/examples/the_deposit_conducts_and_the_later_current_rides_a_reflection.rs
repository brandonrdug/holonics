//! **The mouth deposits, the deposit founds a conducting profile, the current crosses reflecting
//! junctions, and a later arrival rides what the first one left — with the withdrawal control that
//! makes the difference attributable.**
//!
//! ```text
//! cargo run --release -p life --example the_deposit_conducts_and_the_later_current_rides_a_reflection
//! ```
//!
//! **Stations three and seven of
//! [`archive/plans/THE_CLIFFORD_LIFT_THE_PHASE_WIRE_AND_THE_FOUR_UNTAKEN_READINGS.md`](../../../archive/plans/THE_CLIFFORD_LIFT_THE_PHASE_WIRE_AND_THE_FOUR_UNTAKEN_READINGS.md)** —
//! one driver, because the plan makes station seven station three's falsifier by name: *"Without it
//! this station has moved bytes and proved nothing."*
//!
//! # The join, and what it is a join OF
//!
//! Two standing organs that had never touched:
//!
//! - `life::incidence_production::IncidenceComplex::admit_later` — the mouth. It deposits material
//!   at a site and returns `reached / reopened / saturated / untouched`, which is the reading
//!   `docs/canon/THE_INFORMATION_ENGINE.md` §5 calls the two distinct ways to float: *saturated* (it
//!   arrived and nothing was caused) and *untouched* (it reached nothing).
//! - `holonic_engine::traversible_chain` — the conduction. Junctions with exact reflection, and
//!   since 2026-08-17 a declared propagation phase between them, so a chain has a genuine round
//!   trip and its holonomy is no longer forced to the identity.
//!
//! # The admittance is READ OFF THE ARRIVAL, never declared per junction
//!
//! This is the plan's second falsifier and it decides whether the reading is evidence at all:
//!
//! > *"if the founded classes trace back to admittances this driver declared per junction, the class
//! > is the preimage of an authored field however exact the arithmetic between them."*
//!
//! `traversible_chain.rs` states the law it must obey: an admittance is *"how much of an arriving
//! current a site can take… the transmitted admittance is what the site shares with it."* So every
//! admittance below is `shared : arriving` read off the arrival's own response, and nothing in this
//! file chooses a number. A place that shared nothing has admittance zero, which
//! `Admittance::declared` refuses **by type**: there is no traveling section to fabricate there, and
//! the chain terminates at the material rather than at a count.
//!
//! **The grain is the finding, and the first one this driver tried was blind.** Read at the
//! CONSTITUENT grain — `ArrivalTrace::site_occurrence_delta`, what the arrival added to standing
//! constituents — every conduction coordinate came back bit-identical with and without the deposit,
//! while the arrival's own reading moved `reached 5 → 7`. The cause is exact: the later current uses
//! none of the deposit's new constituents, so its distribution over standing ones cannot move. What
//! the deposit changed is the **closed-boundary structure**. Read at the BOUNDARY grain — one
//! junction per closed boundary the arrival reached, admitting `(its constituents the arrival
//! touched) : (its constituents)` — the conduction moves, and the band class itself moves.
//!
//! Both are printed. The blind one is retained precisely because it does not move: a profile read at
//! the wrong grain is invisible to a change that is really there, which is the phase-object theorem
//! arriving on a third subject.
//!
//! # The surface
//!
//! Serial path, and declared as such. The material below is a handful of occurrences over a text
//! codec and the deed is one exact rational chain composition per arrival — there is no front to
//! distribute, and a launch would be pure overhead. `CLAUDE.md`'s diagnosis rule applies in the
//! other direction too: *"no GPU activity"* on material this small is an aperture statement, not a
//! surface defect. Stations five and six are where this plan's current genuinely needs the card.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::dimensional_wave::ExactWavePhaseTransport;
use holonic_engine::running_integral::CoefficientGroup;
use holonic_engine::traversible_chain::{
    found_phased, Admittance, BandClass, BlochReading, Crossing, PhasedLink, PhasedTransfer,
    Standing, StandingWaveReading,
};
use holonic_structure::Composes;
use life::incidence_production::{
    ArrivalResponse, DeclaredOccurrence, IncidenceComplex, IncidenceProductionError, PhaseChart,
};
use num_traits::Zero;
use relational_geometry::Rat;

/// The declared aperture on how many inscription patches of each occurrence participate. A caller
/// declaration, never an authored level: the population it excludes is returned by the complex.
const DECLARED_EXTENT: usize = 8;

/// The trial-division bound `multiquadratic` uses to certify a squarefree kernel. Declared by this
/// caller, refused past rather than guessed.
const KERNEL_BOUND: u64 = 1 << 20;

fn main() {
    if let Err(error) = run() {
        eprintln!("REFUSED: {error}");
        std::process::exit(1);
    }
}

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

fn base_material() -> Result<Vec<DeclaredOccurrence>, IncidenceProductionError> {
    Ok(vec![
        declared(
            "declared:a",
            0,
            &[],
            "the leader founds the channel and the channel carries the leader",
        )?,
        declared(
            "declared:b",
            1,
            &["declared:a"],
            "the arc bends the channel and the bends carry the return",
        )?,
        declared(
            "declared:c",
            2,
            &["declared:b"],
            "the return meets the leader and the meeting founds a junction",
        )?,
    ])
}

/// **A** — the deposit.
fn deposit() -> Result<DeclaredOccurrence, IncidenceProductionError> {
    declared(
        "arrival:deposit",
        3,
        &["declared:a"],
        "the return founds the arc and the arc carries the leader",
    )
}

/// **B** — the later current. Declared identically in both runs; only the terrain differs.
fn later_current() -> Result<DeclaredOccurrence, IncidenceProductionError> {
    declared(
        "arrival:later",
        4,
        &["declared:a"],
        "the arc returns the leader and the junction bends the return",
    )
}

/// **The conduction profile an arrival founds.** Nothing here is chosen: the entries are what the
/// arrival actually reached, in the complex's own order, and each admittance is `shared : arriving`
/// at that place.
struct ConductionProfile {
    /// `(name, shared, arriving)` per place the arrival landed on.
    sites: Vec<(String, u64, u64)>,
    admittances: Vec<Admittance>,
    /// Places whose share was zero: refused by type, retained by name.
    refused: Vec<String>,
}

/// **The constituent grain** — the arrival's deposit distribution across standing constituents.
///
/// This was the first profile this driver derived, and **it was blind**: measured 2026-08-17, B's
/// reading moved (`reached 5 → 7`) while every conduction coordinate read off this profile was
/// bit-identical with and without the deposit. The cause is exact and is a fact about the grain,
/// not a defect in the machine: `site_occurrence_delta` records what the arrival added to
/// **standing constituents**, and what the deposit changed was the **closed-boundary structure**.
/// B uses none of A's two new constituents, so its constituent distribution cannot move.
///
/// It is retained and printed precisely because it does not move. A profile read at the wrong grain
/// is blind to a change that is really there — which is `CLAUDE.md`'s phase-object theorem arriving
/// a third time, on a third subject.
fn constituent_profile(response: &ArrivalResponse) -> ConductionProfile {
    let arriving: u64 = response.trace.site_occurrence_delta.values().sum();
    let mut sites = Vec::new();
    let mut admittances = Vec::new();
    let mut refused = Vec::new();
    for (at, shared) in &response.trace.site_occurrence_delta {
        let surface = response.complex.sites()[*at].surface.clone();
        match Admittance::from_shared(*shared, arriving.max(1)) {
            Ok(admittance) => {
                sites.push((surface, *shared, arriving));
                admittances.push(admittance);
            }
            Err(_) => refused.push(surface),
        }
    }
    ConductionProfile {
        sites,
        admittances,
        refused,
    }
}

/// **The boundary grain, which is where the change lives** — one junction per closed boundary the
/// arrival reached, admitting `(its constituents the arrival touched) : (its constituents)`.
///
/// Still `shared : arriving`, still read entirely off the response, and now taken at the grain the
/// deposit actually moves: `reached` is the population that changes when earlier material stands.
fn boundary_profile(response: &ArrivalResponse) -> ConductionProfile {
    let touched: BTreeSet<usize> = response
        .trace
        .site_occurrence_delta
        .keys()
        .copied()
        .collect();
    let mut sites = Vec::new();
    let mut admittances = Vec::new();
    let mut refused = Vec::new();
    for at in &response.reached {
        let compound = &response.complex.compounds()[*at];
        let arriving = compound.sites.len() as u64;
        let shared = compound
            .sites
            .iter()
            .filter(|site| touched.contains(site))
            .count() as u64;
        let mut name = String::new();
        for site in &compound.sites {
            if !name.is_empty() {
                name.push('·');
            }
            name.push_str(&response.complex.sites()[*site].surface);
        }
        match Admittance::from_shared(shared, arriving.max(1)) {
            Ok(admittance) => {
                sites.push((name, shared, arriving));
                admittances.push(admittance);
            }
            Err(_) => refused.push(name),
        }
    }
    ConductionProfile {
        sites,
        admittances,
        refused,
    }
}

/// **What the conduction returned**: the junctions, the reflections, the composite, and the bands.
struct ConductionReading {
    junction_reflections: Vec<Rat>,
    twists: Vec<&'static str>,
    composite_reflection: Rat,
    composite_transmission: Rat,
    standing_wave: StandingWaveReading,
    band: BandClass,
    half_trace: Rat,
    holonomy_is_identity: Option<bool>,
    is_rebase: bool,
}

/// Conduct a declared profile as a closed phased chain: cross every junction, propagate between
/// them, and close back onto the first admittance so the loop has a holonomy to read.
fn conduct(
    profile: &ConductionProfile,
    phase: &ExactWavePhaseTransport,
) -> Result<ConductionReading, String> {
    if profile.admittances.len() < 2 {
        return Err("a chain needs at least two admittances to have a junction".to_owned());
    }
    let source = profile.admittances[0].clone();
    let mut chain = found_phased(0usize, &source, Standing::NoTravelingSection);
    let mut junction_reflections = Vec::new();
    let mut twists = Vec::new();
    // Close the loop: the last junction returns to the first admittance.
    let ring: Vec<&Admittance> = profile
        .admittances
        .iter()
        .chain(std::iter::once(&profile.admittances[0]))
        .collect();
    for (at, pair) in ring.windows(2).enumerate() {
        let crossing =
            Crossing::meet(pair[0], pair[1]).map_err(|error| format!("junction {at}: {error}"))?;
        let reflection = crossing.reflection();
        twists.push(if reflection.is_zero() {
            "MATCHED"
        } else if reflection > Rat::zero() {
            "PRESERVING"
        } else {
            "INVERTING"
        });
        junction_reflections.push(reflection);
        let carrying = pair[1].clone();
        let closing = at + 2 == ring.len();
        chain.carry(
            PhasedLink::interface(crossing),
            at + 1,
            if closing {
                Standing::LoopClosed
            } else {
                Standing::Carrying(carrying.value().clone())
            },
        );
        if !closing {
            chain.carry(
                PhasedLink::propagation(phase.clone(), pair[1]),
                at + 1,
                Standing::Carrying(pair[1].value().clone()),
            );
        }
    }
    let composed = chain.compose();
    let reflection = composed
        .reflection()
        .ok_or_else(|| "the composite forward diagonal vanished".to_owned())?;
    let transmission = composed
        .transmission()
        .ok_or_else(|| "the composite forward diagonal vanished".to_owned())?;
    let band = BlochReading::of_cell(&composed);
    Ok(ConductionReading {
        junction_reflections,
        twists,
        composite_reflection: reflection.real.clone(),
        composite_transmission: transmission.real.clone(),
        standing_wave: StandingWaveReading::of_reflection(&reflection, KERNEL_BOUND),
        band: band.class,
        half_trace: band.half_trace,
        holonomy_is_identity: chain
            .holonomy()
            .map(|defect| defect == PhasedTransfer::identity()),
        is_rebase: chain.is_rebase(),
    })
}

fn print_arrival(label: &str, response: &ArrivalResponse) {
    println!("  {label}");
    println!(
        "    reached {} · reopened {} · saturated {} · untouched {}",
        response.reached.len(),
        response.reopened.len(),
        response.saturated.len(),
        response.untouched.len()
    );
    println!(
        "    new constituents {} · new contacts {} · new ⪯ edges {}",
        response.new_constituents, response.new_contacts, response.new_dependencies
    );
    println!(
        "    closed boundaries founded {} · dissolved {}",
        response.founded.len(),
        response.dissolved.len()
    );
}

fn print_profile(profile: &ConductionProfile) {
    println!(
        "    {:<16} {:>8} {:>10} {:>12}",
        "constituent", "took", "arriving", "admittance"
    );
    for ((surface, shared, arriving), admittance) in profile.sites.iter().zip(&profile.admittances)
    {
        println!(
            "    {:<16} {:>8} {:>10} {:>12}",
            surface,
            shared,
            arriving,
            admittance.value()
        );
    }
    for surface in &profile.refused {
        println!("    {surface:<16} refused by type: a site sharing nothing has no admittance");
    }
}

fn print_conduction(label: &str, reading: &ConductionReading) {
    println!("  {label}");
    print!("    per-junction Γ  ");
    for (reflection, twist) in reading.junction_reflections.iter().zip(&reading.twists) {
        print!("{reflection} [{twist}]   ");
    }
    println!();
    println!(
        "    composite Γ {} · τ {} · |Γ|² {} · SWR {}",
        reading.composite_reflection,
        reading.composite_transmission,
        reading.standing_wave.reflected_share,
        match &reading.standing_wave.standing_wave_ratio {
            Some(value) => format!("{value}"),
            None => "REFUSED (the root leaves ℚ)".to_string(),
        }
    );
    println!(
        "    band {:?} at half-trace {} · holonomy is identity: {:?} · rebase {}",
        reading.band, reading.half_trace, reading.holonomy_is_identity, reading.is_rebase
    );
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let chart = PhaseChart::WindingAdjacent;
    let group = CoefficientGroup::Integers;
    // A declared phase on the exact unit conic. (3/5, 4/5) is the smallest rational point that is
    // neither a whole nor a quarter turn, so it is the honest witness rather than a degenerate one.
    let phase =
        ExactWavePhaseTransport::new(Rat::new(3.into(), 5.into()), Rat::new(4.into(), 5.into()))
            .map_err(|error| format!("the declared phase is off the unit conic: {error:?}"))?;

    println!("{}", "=".repeat(100));
    println!("THE DEPOSIT CONDUCTS, AND THE LATER CURRENT RIDES A REFLECTION");
    println!("{}", "=".repeat(100));
    println!();
    println!(
        "  Two standing organs that had never touched: the mouth, which deposits material at a"
    );
    println!(
        "  site and returns reached/reopened/saturated/untouched; and the chain, which crosses"
    );
    println!(
        "  junctions with exact reflection and — since the phase wire — carries a round trip."
    );
    println!();

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

    // -- station three: the mouth onto the conducting carrier ---------------------------------
    println!();
    println!("{}", "=".repeat(100));
    println!("[3]  THE MOUTH ONTO THE CONDUCTING CARRIER");
    println!("{}", "=".repeat(100));
    println!();
    let arrival_a = deposit().map_err(|error| format!("declare A: {error:?}"))?;
    let response_a = base
        .admit_later(&arrival_a, chart, &group)
        .map_err(|error| format!("admit A: {error:?}"))?;
    print_arrival("A · the deposit arrives", &response_a);
    println!();
    println!(
        "  THE ADMITTANCE PROFILE THE ARRIVAL FOUNDED. Nothing below is declared per junction:"
    );
    println!("  each site is one the arrival actually raised, and its admittance is that site's");
    println!("  share of the arrival's own total deposit. `traversible_chain`'s law verbatim —");
    println!(
        "  \"how much of an arriving current a site can take… what the site shares with it.\""
    );
    println!();
    let constituents_a = constituent_profile(&response_a);
    println!("  at the CONSTITUENT grain — what A added to standing constituents:");
    print_profile(&constituents_a);
    println!();
    println!("  at the BOUNDARY grain — one junction per closed boundary A reached:");
    let profile_a = boundary_profile(&response_a);
    print_profile(&profile_a);
    println!();
    let conduction_a = conduct(&profile_a, &phase)?;
    print_conduction("A · conducted as a closed phased ring", &conduction_a);
    println!();
    println!(
        "  The current crossed {} junctions and came back. Every junction that did not match",
        conduction_a.junction_reflections.len()
    );
    println!(
        "  retained what did not cross — reflection is not loss, it is the fiber of a junction"
    );
    println!("  that did not match — and the composite carries the whole return.");

    // -- station seven: deposit, then ride, across a reflecting junction -----------------------
    println!();
    println!("{}", "=".repeat(100));
    println!("[7]  DEPOSIT, THEN RIDE, ACROSS A REFLECTING JUNCTION");
    println!("{}", "=".repeat(100));
    println!();
    println!("    1  admit A                 -> A deposits, and founds a conducting profile");
    println!("    2  admit B on (base + A)    -> B's reading and conduction, WITH A standing");
    println!("    3  withdraw A               -> bit-identical to base, or this run is void");
    println!("    4  admit B on base          -> B's reading and conduction, WITHOUT the deposit");
    println!("    5  compare                  -> the difference IS what B rode");
    println!();

    let with_a = &response_a.complex;
    let arrival_b = later_current().map_err(|error| format!("declare B: {error:?}"))?;
    let response_b_with = with_a
        .admit_later(&arrival_b, chart, &group)
        .map_err(|error| format!("admit B on base+A: {error:?}"))?;

    // 3 · the withdrawal control, before anything is compared.
    let restored = with_a
        .withdraw(&response_a.trace)
        .map_err(|error| format!("withdraw A: {error:?}"))?;
    let base_emissions = base
        .hand_up(chart)
        .map_err(|error| format!("hand up the base terrain: {error:?}"))?;
    let restored_emissions = restored
        .hand_up(chart)
        .map_err(|error| format!("hand up the restored terrain: {error:?}"))?;
    let withdrawal_is_exact = restored_emissions == base_emissions
        && restored.sites().len() == base.sites().len()
        && restored.bonds().len() == base.bonds().len()
        && restored.compounds().len() == base.compounds().len()
        && restored
            .sites()
            .iter()
            .zip(base.sites())
            .all(|(here, there)| here.occurrences == there.occurrences)
        && restored
            .bonds()
            .iter()
            .zip(base.bonds())
            .all(|(here, there)| here.multiplicity == there.multiplicity);
    println!("  3 · THE WITHDRAWAL CONTROL");
    println!(
        "      {} emissions, {} constituents, {} contacts, {} closed boundaries",
        restored_emissions.len(),
        restored.sites().len(),
        restored.bonds().len(),
        restored.compounds().len()
    );
    println!("      the complex returned bit-identical to base: {withdrawal_is_exact}");
    if !withdrawal_is_exact {
        return Err("the withdrawal was not exact; no comparison below would mean anything".into());
    }

    let response_b_without = base
        .admit_later(&arrival_b, chart, &group)
        .map_err(|error| format!("admit B on base: {error:?}"))?;

    println!();
    print_arrival("B · WITH the deposit standing", &response_b_with);
    println!();
    print_arrival("B · WITHOUT the deposit", &response_b_without);

    let constituents_with = constituent_profile(&response_b_with);
    let constituents_without = constituent_profile(&response_b_without);
    let profile_b_with = boundary_profile(&response_b_with);
    let profile_b_without = boundary_profile(&response_b_without);
    println!();
    println!("  B's CONSTITUENT-grain profile, with the deposit standing:");
    print_profile(&constituents_with);
    println!();
    println!("  B's CONSTITUENT-grain profile, without it:");
    print_profile(&constituents_without);
    let constituent_grain_moved = constituents_with
        .sites
        .iter()
        .map(|(name, shared, arriving)| (name.clone(), *shared, *arriving))
        .collect::<Vec<_>>()
        != constituents_without
            .sites
            .iter()
            .map(|(name, shared, arriving)| (name.clone(), *shared, *arriving))
            .collect::<Vec<_>>();
    println!();
    println!(
        "  >> THE CONSTITUENT GRAIN MOVED: {constituent_grain_moved}. It does not, and that is a"
    );
    println!(
        "  >> measurement rather than a disappointment. B uses none of A's two new constituents,"
    );
    println!("  >> so its deposit onto STANDING constituents cannot move. What A changed is the");
    println!(
        "  >> CLOSED-BOUNDARY structure, and a profile read at the constituent grain is blind to"
    );
    println!("  >> it -- the phase-object theorem on a third subject.");
    println!();
    println!("  B's BOUNDARY-grain profile, with the deposit standing:");
    print_profile(&profile_b_with);
    println!();
    println!("  B's BOUNDARY-grain profile, without it:");
    print_profile(&profile_b_without);

    let conduction_b_with = conduct(&profile_b_with, &phase)?;
    let conduction_b_without = conduct(&profile_b_without, &phase)?;
    println!();
    print_conduction(
        "B · conducted WITH the deposit standing",
        &conduction_b_with,
    );
    println!();
    print_conduction("B · conducted WITHOUT it", &conduction_b_without);

    // -- 5 · the comparison, coordinate by coordinate ------------------------------------------
    println!();
    println!("{}", "=".repeat(100));
    println!("[5]  WHAT B RODE  --  and the falsifier that decides whether it rode anything");
    println!("{}", "=".repeat(100));
    println!();
    let mut moved: Vec<(&str, String, String)> = Vec::new();
    let mut unmoved: Vec<&str> = Vec::new();
    let mut note = |name: &'static str, with: String, without: String| {
        if with == without {
            unmoved.push(name);
        } else {
            moved.push((name, with, without));
        }
    };
    note(
        "reached",
        response_b_with.reached.len().to_string(),
        response_b_without.reached.len().to_string(),
    );
    note(
        "reopened",
        response_b_with.reopened.len().to_string(),
        response_b_without.reopened.len().to_string(),
    );
    note(
        "saturated",
        response_b_with.saturated.len().to_string(),
        response_b_without.saturated.len().to_string(),
    );
    note(
        "untouched",
        response_b_with.untouched.len().to_string(),
        response_b_without.untouched.len().to_string(),
    );
    note(
        "new constituents",
        response_b_with.new_constituents.to_string(),
        response_b_without.new_constituents.to_string(),
    );
    note(
        "new contacts",
        response_b_with.new_contacts.to_string(),
        response_b_without.new_contacts.to_string(),
    );
    note(
        "closed boundaries founded",
        response_b_with.founded.len().to_string(),
        response_b_without.founded.len().to_string(),
    );
    note(
        "conduction: junctions",
        conduction_b_with.junction_reflections.len().to_string(),
        conduction_b_without.junction_reflections.len().to_string(),
    );
    note(
        "conduction: composite Γ",
        conduction_b_with.composite_reflection.to_string(),
        conduction_b_without.composite_reflection.to_string(),
    );
    note(
        "conduction: |Γ|²",
        conduction_b_with.standing_wave.reflected_share.to_string(),
        conduction_b_without
            .standing_wave
            .reflected_share
            .to_string(),
    );
    note(
        "conduction: half-trace",
        conduction_b_with.half_trace.to_string(),
        conduction_b_without.half_trace.to_string(),
    );
    note(
        "conduction: band",
        format!("{:?}", conduction_b_with.band),
        format!("{:?}", conduction_b_without.band),
    );
    note(
        "conduction: rebase",
        conduction_b_with.is_rebase.to_string(),
        conduction_b_without.is_rebase.to_string(),
    );

    println!(
        "  {:<30} {:>22} {:>22}",
        "coordinate", "WITH the deposit", "WITHOUT it"
    );
    for (name, with, without) in &moved {
        println!("  {name:<30} {with:>22} {without:>22}   MOVED");
    }
    for name in &unmoved {
        println!("  {name:<30} {:>22}", "unmoved");
    }
    println!();
    println!(
        "  {} coordinates moved, {} did not.",
        moved.len(),
        unmoved.len()
    );

    if moved.is_empty() {
        println!();
        println!("  >> THE FALSIFIER FIRED. B's reading and conduction are bit-identical with and");
        println!("  >> without A. The deposit was decorative: a contact that changes no pathway");
        println!("  >> taught the body nothing, whatever it returned.");
        return Err("the deposit changed nothing B could ride".into());
    }

    println!();
    println!(
        "  >> B RODE THE DEPOSIT. The difference is attributable by construction: the two runs"
    );
    println!("  >> declare B identically and differ only in whether A stands, and the withdrawal");
    println!("  >> returned the complex bit-identical to base before the second run was taken.");

    // -- the authored-partition arm ------------------------------------------------------------
    println!();
    println!("{}", "=".repeat(100));
    println!(
        "THE SECOND FALSIFIER  --  is the conduction the preimage of a field this driver wrote?"
    );
    println!("{}", "=".repeat(100));
    println!();
    println!("  The plan's own test: \"which declared input, if varied across two members of one");
    println!(
        "  returned class, would move them apart? If the answer is a field this driver wrote,"
    );
    println!("  the partition is authored.\"");
    println!();
    println!("  This driver declares THREE things and none of them is an admittance: the base");
    println!("  material, the two arrivals, and one propagation phase. Every admittance above is");
    println!(
        "  `shared : arriving` read off the arrival's own response — which closed boundaries it"
    );
    println!(
        "  reached and which of their constituents it touched — so varying the MATERIAL moves"
    );
    println!("  the profile and there is no field to vary that would move it otherwise.");
    println!();
    println!(
        "  And the arm that shows it: the two boundary profiles above differ, and they differ"
    );
    println!("  because the terrain differed. B's declaration is byte-identical in both runs.");
    let with_shares: BTreeMap<&str, u64> = profile_b_with
        .sites
        .iter()
        .map(|(surface, shared, _)| (surface.as_str(), *shared))
        .collect();
    let without_shares: BTreeMap<&str, u64> = profile_b_without
        .sites
        .iter()
        .map(|(surface, shared, _)| (surface.as_str(), *shared))
        .collect();
    let profiles_differ = with_shares != without_shares;
    println!("    B's deposit distribution differs between the two terrains: {profiles_differ}");
    println!();

    // -- the phase control ---------------------------------------------------------------------
    println!("{}", "=".repeat(100));
    println!("THE PHASE CONTROL  --  a whole turn is invisible, and that is how we know it is in the loop");
    println!("{}", "=".repeat(100));
    println!();
    let unphased = conduct(&profile_a, &ExactWavePhaseTransport::identity())?;
    let _ = &constituents_a;
    println!("  A's ring conducted with a WHOLE TURN between junctions:");
    print_conduction("A · unphased", &unphased);
    println!();
    println!("  and with the declared phase (3/5, 4/5), from above:");
    print_conduction("A · phased", &conduction_a);
    println!();
    let phase_moved = unphased.half_trace != conduction_a.half_trace
        || unphased.holonomy_is_identity != conduction_a.holonomy_is_identity
        || unphased.composite_reflection != conduction_a.composite_reflection;
    println!("  the phase moved the conduction: {phase_moved}");
    println!();
    println!(
        "  A closed ring of interfaces alone returns the identity BY CONSTRUCTION — the composed"
    );
    println!("  admittance ratio is Y_source/Y_source — so that receipt could not have come out");
    println!(
        "  otherwise and carries no evidence. With a phase in the loop it can, and does, differ."
    );
    if !phase_moved {
        return Err("the phase changed nothing; it is not in the loop".into());
    }

    println!();
    println!("{}", "=".repeat(100));
    println!("WHAT THIS RUN DOES NOT CLAIM");
    println!("{}", "=".repeat(100));
    println!();
    println!(
        "  The conduction is a reading of the profile the arrival founded. It does not claim the"
    );
    println!(
        "  complex itself conducts — `IncidenceComplex` is a deposit carrier and `diffusion` is"
    );
    println!(
        "  immutable after `new`; joining them at the level of state is a separate deed with its"
    );
    println!("  own falsifier.");
    println!();
    println!("  Nothing here quotes `energy_residual`, which `traversible_chain` records as");
    println!("  identically zero for its convention, algebraically.");
    println!();
    println!(
        "  The material is small and declared, and the surface is the serial path deliberately:"
    );
    println!("  a handful of occurrences and one exact rational chain per arrival has no front to");
    println!("  distribute. Stations five and six are where this plan's current needs the card.");
    Ok(())
}

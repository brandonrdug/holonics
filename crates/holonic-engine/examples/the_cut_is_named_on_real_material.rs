//! **Name the spine's cut on a real chain from this body.**
//!
//! ```text
//! cargo run --release --example the_cut_is_named_on_real_material -- standing/output
//! ```
//!
//! [`holonic_engine::spine_cut`] classifies which of the spine's five cuts a chain reading is at —
//! leak, rest, accumulation, short circuit, circulation. Until this driver was written its only
//! material was a hand-made theta graph in `#[cfg(test)]`, so the cut it names had never been read
//! off a live chain. An organ that reaches nothing has not been graded.
//!
//! ## The chain, and where every part of it comes from
//!
//! The material is the deposited Lean production at `standing/output`, read by
//! [`holonic_engine::conditioned_derivation`] and founded as a graded complex by
//! [`holonic_engine::derivation_atlas`]. Nothing below is constructed for this driver.
//!
//! ```text
//!   B    the incidence     every grade-1 cell of the founded complex, its tail and head read
//!                          off the cell's own boundary -- the -1 face and the +1 face
//!   j    the current       the CHAIN of a real traversal: chain(left) - chain(right) for a
//!                          compared route pair, or chain(route) for a single route
//!   r    the residual      B j, computed by `ChainReading::divergence` from the incidence and
//!                          the current. It is never invented: it is what the reading itself
//!                          says entered or left each vertex at unchanged storage
//!   q_n - q_m              the line integral of the accumulation cochain along the traversal --
//!                          for a pair, exactly `running_integral`'s standing residual
//!   the declared load      `circuit.reaches()`: the cells that deliver a declaration to the
//!                          statement it reached. That is what the production exists to cross,
//!                          and it is read off the founded incidence, not chosen here
//! ```
//!
//! ## Why the same two routes give two different cuts
//!
//! A [`holonic_engine::derivation_integral::Route`] is a chain of recruitments between two
//! declarations. Read **singly** it is an open path: it departs one declaration and arrives at
//! another and never comes back, so `B j` is `-1` at the departure and `+1` at the arrival and the
//! cut is **leak** — the spine's *"an emission with no return edge"*, with the source and the sink
//! exhibited by name. Read **as a pair** against the other route joining the same two declarations,
//! the composite is a cycle, `B j` vanishes at every vertex, and the cut is one of the closed three.
//! The loop closing is the whole point, and it is visible here as a change of cut on the same cells.
//!
//! ## Four loop families, and the rule is a live gauge over them
//!
//! ```text
//!   statement lineage      reach S from D against reach it from E    crosses the load
//!   recruited declaration  reach E as a resource against a shared    misses the load
//!                          identifier
//!   shared identifier      D -[s1]-> E against D -[s2]-> E           misses the load
//!   the backtrack          leave D across s and return across the    the chain is zero
//!                          SAME cell
//! ```
//!
//! The backtrack is two passages whose chain cancels: `CausalChain` retains the opposed terms, the
//! current's difference is zero on every carrier, and the cut is **rest**. Two things happened and
//! nothing flowed, which is exactly what rest is and exactly what a passage count cannot say.
//!
//! Under [`AccumulationRule::RouteLoad`] the cochain is head-determined, so two routes across two
//! shared identifiers accumulate `-Lambda(D) + Lambda(E)` either way and the loop is exact.
//! [`AccumulationRule::RecruitmentLoad`] is not head-determined and the same loop stores. **The same
//! cells change cut when the rule changes**, which is the gauge orbit `CLAUDE.md` §8 requires a
//! declared schedule family to exhibit before its agreement may be read as evidence.
//!
//! ## The controls, and what would make each fail
//!
//! Eight, each printed with its verdict and with the material that would break it. Six are
//! properties of the returned population and can fail on material; two are refusals the organ owes.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use num_bigint::BigInt;
use num_traits::Zero;
use relational_geometry::Rat;

use holonic_engine::VertexId;
use holonic_engine::algebraic::CausalChain;
use holonic_engine::conditioned_derivation::{
    ConditionedBody, ConditionedCircuit, found_conditioned_circuit,
};
use holonic_engine::derivation_atlas::CircuitAperture;
use holonic_engine::derivation_integral::{
    AccumulationRule, RouteDisagreement, accumulation, circuit_loads, compare_routes,
    recruited_declaration_family, recruited_declarations, route_via_recruitment,
    shared_recruitments, statement_lineage, without_declarations,
};
use holonic_engine::running_integral::{Cochain, Path as Walk, PathStep, running_sum};
use holonic_engine::spine_cut::{
    ChainReading, EdgeId, SpineCut, SpineCutError, name_the_cut, read_the_chain,
};

// -------------------------------------------------------------------------------------------------
// the material
// -------------------------------------------------------------------------------------------------

fn artifacts(root: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let Ok(entries) = std::fs::read_dir(root) else {
        return found;
    };
    let mut here: Vec<PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
    here.sort();
    for path in here {
        if path.is_dir() {
            found.extend(artifacts(&path));
        } else if path.extension().is_some_and(|carried| carried == "lean") {
            found.push(path);
        }
    }
    found
}

fn read_deposit(root: &Path) -> Vec<(String, String)> {
    artifacts(root)
        .into_iter()
        .filter_map(|path| {
            std::fs::read_to_string(&path)
                .ok()
                .map(|text| (path.display().to_string(), text))
        })
        .collect()
}

// -------------------------------------------------------------------------------------------------
// the incidence, read off the founded complex
// -------------------------------------------------------------------------------------------------

/// The names to print `B` with, and what the mouth says about this complex.
///
/// The reading itself is built by [`holonic_engine::spine_cut::read_the_chain`]; nothing here
/// reconstructs an incidence. This carries only what a printout needs.
struct Names {
    edge_name: BTreeMap<EdgeId, String>,
    vertex_name: BTreeMap<VertexId, String>,
    one_cells: usize,
    /// A grade-0 address, kept so a vertex can be offered where a load edge is expected.
    a_vertex_address: Option<u64>,
    /// What the mouth returns when handed this complex and an empty current: `Ok(n)` means every
    /// one of the `n` one-cells is joinable, and a refusal names the first that is not.
    mouth: Result<usize, String>,
}

fn read_names(circuit: &ConditionedCircuit) -> Names {
    let complex = circuit.circuit.complex();
    let mut edge_name = BTreeMap::new();
    let mut vertex_name = BTreeMap::new();
    let mut one_cells = 0usize;
    let mut a_vertex_address = None;

    for cell in complex.cells().values() {
        match cell.grade {
            0 => {
                vertex_name.insert(VertexId(cell.id.0), cell.name.clone());
                a_vertex_address.get_or_insert(cell.id.0);
            }
            1 => {
                one_cells += 1;
                edge_name.insert(EdgeId(cell.id.0), cell.name.clone());
            }
            _ => {}
        }
    }

    let mouth = read_the_chain(complex, &CausalChain::default(), Rat::zero())
        .map(|reading| reading.edges.len())
        .map_err(|refusal| refusal.to_string());

    Names {
        edge_name,
        vertex_name,
        one_cells,
        a_vertex_address,
        mouth,
    }
}

impl Names {
    fn edge(&self, id: EdgeId) -> String {
        self.edge_name
            .get(&id)
            .cloned()
            .unwrap_or_else(|| format!("{id:?}"))
    }

    fn vertex(&self, id: VertexId) -> String {
        self.vertex_name
            .get(&id)
            .cloned()
            .unwrap_or_else(|| format!("{id:?}"))
    }
}

/// **The declared load, read off the material.** The reach cells `D |- S` are what the production
/// exists to cross: they are where a declaration is delivered to the statement it reached. Nothing
/// is chosen here — the set is exactly the founded reach incidence, which is empty under
/// `StatementIncidence::Withheld` and non-empty exactly when the aperture founds statements.
fn declared_load(circuit: &ConditionedCircuit) -> BTreeSet<EdgeId> {
    circuit
        .circuit
        .reaches()
        .values()
        .map(|cell| EdgeId(cell.0))
        .collect()
}

// -------------------------------------------------------------------------------------------------
// a reading
// -------------------------------------------------------------------------------------------------

/// One chain reading, with what it is in words.
struct Reading {
    family: &'static str,
    named: String,
    chain: CausalChain,
    /// The line integral of the accumulation cochain along the traversal.
    potential_change: BigInt,
}

/// Build the reading through the organ's own mouth. **The residual is not passed**: `read_the_chain`
/// computes `r = B j` from the incidence and the current, so a reading this driver could not
/// support cannot be declared into existence here.
fn chain_reading(
    circuit: &ConditionedCircuit,
    reading: &Reading,
) -> Result<ChainReading, SpineCutError> {
    read_the_chain(
        circuit.circuit.complex(),
        &reading.chain,
        Rat::from_integer(reading.potential_change.clone()),
    )
}

/// Every vertex a carrying edge touches: the support of the reading on the incidence.
fn touched(reading: &ChainReading) -> BTreeSet<VertexId> {
    let carrying = reading.carrying();
    reading
        .edges
        .iter()
        .filter(|edge| carrying.contains(&edge.id))
        .flat_map(|edge| [edge.tail, edge.head])
        .collect()
}

// -------------------------------------------------------------------------------------------------
// the loop families
// -------------------------------------------------------------------------------------------------

/// A compared pair, as a closed reading: the cycle is `chain(left) - chain(right)` and the potential
/// change around it is `running_integral`'s standing residual.
fn from_pair(family: &'static str, pair: &RouteDisagreement) -> Reading {
    Reading {
        family,
        named: pair.named(),
        chain: pair.disagreement.cycle.clone(),
        potential_change: pair.residual().clone(),
    }
}

/// The shared-identifier family, built from the module's own route constructor: two declarations
/// joined across two different identifiers both recruit.
fn shared_identifier_family(
    circuit: &ConditionedCircuit,
    cochain: &Cochain,
    rule: AccumulationRule,
) -> Vec<RouteDisagreement> {
    let loads = circuit_loads(circuit);
    let declarations: Vec<String> = loads
        .declarations()
        .into_iter()
        .map(str::to_owned)
        .collect();
    let mut compared = Vec::new();
    for (index, from) in declarations.iter().enumerate() {
        for to in declarations.iter().skip(index + 1) {
            let shared: Vec<String> = shared_recruitments(&loads, from, to).into_iter().collect();
            for (first, left_symbol) in shared.iter().enumerate() {
                for right_symbol in shared.iter().skip(first + 1) {
                    let (Some(left), Some(right)) = (
                        route_via_recruitment(circuit, from, to, left_symbol),
                        route_via_recruitment(circuit, from, to, right_symbol),
                    ) else {
                        continue;
                    };
                    if let Ok(pair) = compare_routes(circuit, cochain, rule, &left, &right) {
                        compared.push(pair);
                    }
                }
            }
        }
    }
    compared
}

/// **The backtrack.** Leave a declaration across one of its own recruitment cells and return across
/// the same cell. Two passages, opposed, and `CausalChain` retains both — so the current's
/// difference is zero on every carrier and nothing flowed.
fn backtrack_family(circuit: &ConditionedCircuit, cochain: &Cochain) -> Vec<Reading> {
    let mut readings = Vec::new();
    for ((declaration, symbol), cell) in circuit.circuit.recruitments() {
        let walk = Walk::new([PathStep::against(*cell), PathStep::along(*cell)]);
        let Ok(integral) = running_sum(circuit.circuit.complex(), cochain, &walk) else {
            continue;
        };
        readings.push(Reading {
            family: "backtrack",
            named: format!("{declaration} -[{symbol}]-> and back across the same cell"),
            chain: walk.chain(),
            potential_change: integral.total.clone(),
        });
        // One is enough to name the cut; the population is reported, not enumerated.
        break;
    }
    readings
}

// -------------------------------------------------------------------------------------------------
// controls
// -------------------------------------------------------------------------------------------------

struct Controls {
    failed: Vec<String>,
    checked: usize,
}

impl Controls {
    fn new() -> Self {
        Self {
            failed: Vec::new(),
            checked: 0,
        }
    }

    fn check(&mut self, name: &str, holds: bool, would_fail_on: &str) {
        self.checked += 1;
        println!(
            "  [{}] {name}\n        would FAIL on: {would_fail_on}",
            if holds { "holds" } else { "FAILS" }
        );
        if !holds {
            self.failed.push(name.to_owned());
        }
    }
}

fn rule(title: &str) {
    println!("\n{}", "=".repeat(98));
    println!("{title}");
    println!("{}", "=".repeat(98));
}

// -------------------------------------------------------------------------------------------------
// the run
// -------------------------------------------------------------------------------------------------

/// Everything one declared material returned.
struct Classified {
    material: String,
    rule: AccumulationRule,
    /// cut name -> how many readings landed there.
    population: BTreeMap<String, usize>,
    /// cut name -> one named reading that landed there, kept for exhibition.
    witness: BTreeMap<String, String>,
    /// Every reading, so a later comparison can find the same loop under the other rule.
    by_name: BTreeMap<String, String>,
    /// How many readings **returned** what they emitted. Only circulation does, and the count is
    /// taken from `SpineCut::returns` rather than from the name.
    returning: usize,
    refusals: Vec<String>,
}

fn classify(
    material: &str,
    circuit: &ConditionedCircuit,
    names: &Names,
    load: &BTreeSet<EdgeId>,
    accumulation_rule: AccumulationRule,
    readings: &[Reading],
    exhibit: &mut Vec<Exhibit>,
) -> Classified {
    let mut population: BTreeMap<String, usize> = BTreeMap::new();
    let mut witness: BTreeMap<String, String> = BTreeMap::new();
    let mut by_name: BTreeMap<String, String> = BTreeMap::new();
    let mut returning = 0usize;
    let mut refusals = Vec::new();

    for reading in readings {
        let built = match chain_reading(circuit, reading) {
            Ok(built) => built,
            Err(refusal) => {
                refusals.push(format!("{} -> {refusal}", reading.named));
                continue;
            }
        };
        match name_the_cut(&built, load) {
            Ok(cut) => {
                let name = cut.name().to_owned();
                if cut.returns() {
                    returning += 1;
                }
                *population.entry(name.clone()).or_insert(0) += 1;
                by_name.insert(
                    format!("{}::{}", reading.family, reading.named),
                    name.clone(),
                );
                if !witness.contains_key(&name) {
                    witness.insert(name.clone(), reading.named.clone());
                    exhibit.push(Exhibit {
                        cut_name: name.clone(),
                        rendered: render_reading(
                            names,
                            &format!("{material}  rule {}", accumulation_rule.named()),
                            &format!("[{}]  {}", reading.family, reading.named),
                            &built,
                            &cut,
                        ),
                    });
                }
            }
            Err(refusal) => refusals.push(format!("{} -> {refusal}", reading.named)),
        }
    }

    Classified {
        material: material.to_owned(),
        rule: accumulation_rule,
        population,
        witness,
        by_name,
        returning,
        refusals,
    }
}

fn report(classified: &Classified) {
    println!(
        "\n  {}   rule {}",
        classified.material,
        classified.rule.named()
    );
    if classified.population.is_empty() {
        println!("    no reading was classified on this material.");
    }
    for (cut, count) in &classified.population {
        println!(
            "    {cut:<20} {count:>4} readings   first: {}",
            classified
                .witness
                .get(cut)
                .cloned()
                .unwrap_or_else(|| "-".to_owned())
        );
    }
    println!(
        "    returned what it emitted: {} of {} readings   (only circulation returns)",
        classified.returning,
        classified.population.values().sum::<usize>()
    );
    for refusal in &classified.refusals {
        println!("    REFUSED  {refusal}");
    }
}

/// One reading of one cut, rendered against the incidence it was read on. The rendering happens at
/// classification time because each declared material founds its own cell addresses; a name resolved
/// against the wrong complex would be a fabricated label.
struct Exhibit {
    cut_name: String,
    rendered: String,
}

fn render_reading(
    names: &Names,
    frame: &str,
    named: &str,
    reading: &ChainReading,
    cut: &SpineCut,
) -> String {
    use std::fmt::Write as _;
    let mut out = String::new();
    let _ = writeln!(out, "\n  {frame}");
    let _ = writeln!(out, "  {named}");
    let _ = writeln!(
        out,
        "    the cut: {}      returns: {}",
        cut.name(),
        cut.returns()
    );
    let _ = writeln!(out, "    the current, cell by cell:");
    for (id, flow) in &reading.current {
        let _ = writeln!(out, "      j = {flow:>3}  on  {}", names.edge(*id));
    }
    let _ = writeln!(out, "    q_n - q_m = {}", reading.potential_change);
    let support = touched(reading);
    let _ = writeln!(
        out,
        "    the divergence B j, exhibited at every vertex the current touches ({} of them):",
        support.len()
    );
    let divergence = reading.divergence();
    for vertex in &support {
        let _ = writeln!(
            out,
            "      (B j)[{}] = {}",
            names.vertex(*vertex),
            divergence.get(vertex).cloned().unwrap_or_else(Rat::zero)
        );
    }
    match cut {
        SpineCut::Leak { at } => {
            let _ = writeln!(out, "    the leak, by name -- what entered and what left:");
            for (vertex, value) in at {
                let _ = writeln!(out, "      r[{}] = {value}", names.vertex(*vertex));
            }
        }
        SpineCut::Rest => {
            let _ = writeln!(
                out,
                "    two passages were retained and every carrier's difference is zero: nothing \
                 flowed."
            );
        }
        SpineCut::Accumulation { stored } => {
            let _ = writeln!(
                out,
                "    the loop closed and did NOT return {stored}: it was stored."
            );
        }
        SpineCut::ShortCircuit {
            bypass,
            declared_load,
        } => {
            let _ = writeln!(
                out,
                "    the loop returned across {} cells, none of them a load cell:",
                bypass.len()
            );
            for id in bypass {
                let _ = writeln!(out, "      bypass  {}", names.edge(*id));
            }
            let _ = writeln!(
                out,
                "    the declared load it never crossed carries {} cells, the first being {}",
                declared_load.len(),
                declared_load
                    .iter()
                    .next()
                    .map(|id| names.edge(*id))
                    .unwrap_or_else(|| "-".to_owned())
            );
        }
        SpineCut::Circulation {
            crossed,
            divergence,
        } => {
            let _ = writeln!(out, "    the loop crossed the declared load at:");
            for id in crossed {
                let _ = writeln!(out, "      load    {}", names.edge(*id));
            }
            // Counted, not asserted: the variant carries `B j` and this reads it.
            let standing = divergence.values().filter(|value| !value.is_zero()).count();
            let _ = writeln!(
                out,
                "    the retained divergence carries {} vertices, of which {standing} are \
                 non-zero",
                divergence.len()
            );
        }
    }
    out
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let root = PathBuf::from(
        arguments
            .first()
            .cloned()
            .unwrap_or_else(|| "standing/output".to_owned()),
    );

    let deposit = read_deposit(&root);
    if deposit.is_empty() {
        eprintln!("no .lean artifact under {}", root.display());
        std::process::exit(2);
    }
    let body = match ConditionedBody::mount(deposit.clone()) {
        Ok(body) => body,
        Err(refusal) => {
            eprintln!("the deposit was refused: {refusal}");
            std::process::exit(2);
        }
    };

    let found =
        |aperture: CircuitAperture| found_conditioned_circuit(body.standing().to_vec(), aperture);
    let whole = match found(CircuitAperture::STATEMENT_INCIDENT) {
        Ok(circuit) => circuit,
        Err(refusal) => {
            eprintln!("the circuit was refused: {refusal}");
            std::process::exit(2);
        }
    };
    let withheld = match found(CircuitAperture::DEPOSITED_READER) {
        Ok(circuit) => circuit,
        Err(refusal) => {
            eprintln!("the statement-withheld circuit was refused: {refusal}");
            std::process::exit(2);
        }
    };
    let recruited = recruited_declarations(&whole);
    let ablated = without_declarations(&whole, &recruited);

    rule("THE CUT IS NAMED ON REAL MATERIAL -- spine_cut over a conditioned derivation circuit");

    println!("\nmaterial");
    println!(
        "  deposit        {:<58} {} artifacts",
        root.display(),
        deposit.len()
    );
    let mut controls = Controls::new();

    // -------------------------------------------------------------------------------------------
    rule("[1]  THE INCIDENCE -- B, read off the founded complex");

    let names = read_names(&whole);
    let load = declared_load(&whole);
    println!("\n  aperture {:?}", CircuitAperture::STATEMENT_INCIDENT);
    println!(
        "  vertices {}   one-cells {}",
        names.vertex_name.len(),
        names.one_cells
    );
    match &names.mouth {
        Ok(read) => println!(
            "  `spine_cut::read_the_chain` read {read} of those {} one-cells as joinable edges",
            names.one_cells
        ),
        Err(refusal) => println!("  the mouth REFUSED this complex: {refusal}"),
    }
    println!(
        "  the load is {} of those {} one-cells -- a loop crosses it or it does not, and both \
         happen below",
        load.len(),
        names.one_cells
    );
    println!(
        "\n  the declared load, read off `circuit.reaches()` -- what the production exists to cross:"
    );
    for id in &load {
        println!("    load cell  {}", names.edge(*id));
    }
    println!(
        "\n  every declaration some OTHER declaration recruited (the ablation target): {:?}",
        recruited
    );

    // -------------------------------------------------------------------------------------------
    rule("[2]  THE READINGS -- four loop families and the open routes they are built from");

    let mut all: Vec<Classified> = Vec::new();
    let mut exhibits: Vec<Exhibit> = Vec::new();
    let mut open_route_leaks = 0usize;

    let materials: Vec<(String, &ConditionedCircuit)> = match &ablated {
        Ok(circuit) => vec![
            ("the whole production".to_owned(), &whole),
            (
                format!("the production with {recruited:?} ablated"),
                circuit,
            ),
        ],
        Err(refusal) => {
            println!("\n  the ablated circuit was refused: {refusal}");
            vec![("the whole production".to_owned(), &whole)]
        }
    };

    for (material, circuit) in &materials {
        let material_names = read_names(circuit);
        let material_load = declared_load(circuit);
        for accumulation_rule in [
            AccumulationRule::RouteLoad,
            AccumulationRule::RecruitmentLoad,
        ] {
            let cochain = accumulation(circuit, accumulation_rule);
            let mut readings: Vec<Reading> = Vec::new();

            // -- the statement lineage: routes that cross the load ----------------------------
            let statements: Vec<String> = circuit
                .circuit
                .statements()
                .into_iter()
                .map(str::to_owned)
                .collect();
            for statement in &statements {
                let Ok(population) =
                    statement_lineage(circuit, &cochain, accumulation_rule, statement)
                else {
                    continue;
                };
                for pair in &population.compared {
                    readings.push(from_pair("statement lineage", pair));
                }
            }

            // -- the recruited-declaration family ---------------------------------------------
            if let Ok(population) =
                recruited_declaration_family(circuit, &cochain, accumulation_rule)
            {
                for pair in &population.compared {
                    readings.push(from_pair("recruited declaration", pair));
                }
            }

            // -- two shared identifiers -------------------------------------------------------
            for pair in &shared_identifier_family(circuit, &cochain, accumulation_rule) {
                readings.push(from_pair("shared identifier", pair));
            }

            // -- the open routes each of those pairs is built from -----------------------------
            let closed = readings.len();
            let mut singles: Vec<Reading> = Vec::new();
            for statement in &statements {
                let Ok(population) =
                    statement_lineage(circuit, &cochain, accumulation_rule, statement)
                else {
                    continue;
                };
                for pair in &population.compared {
                    for (side, route, integral) in [
                        ("left", &pair.left, &pair.disagreement.left),
                        ("right", &pair.right, &pair.disagreement.right),
                    ] {
                        singles.push(Reading {
                            family: "open route",
                            named: format!("{side}: {}", route.named()),
                            chain: route.path.chain(),
                            potential_change: integral.total.clone(),
                        });
                    }
                }
            }
            let open = singles.len();
            open_route_leaks += open;
            readings.extend(singles);

            // -- the backtrack -----------------------------------------------------------------
            let backtracks = backtrack_family(circuit, &cochain);
            let backtracked = backtracks.len();
            readings.extend(backtracks);

            println!(
                "\n  {material}   rule {}   {closed} closed-pair readings, {open} open routes, \
                 {backtracked} backtracks, {} total",
                accumulation_rule.named(),
                readings.len()
            );

            all.push(classify(
                material,
                circuit,
                &material_names,
                &material_load,
                accumulation_rule,
                &readings,
                &mut exhibits,
            ));
        }
    }

    // -------------------------------------------------------------------------------------------
    rule("[3]  THE CUT POPULATION -- what the classifier returned, by material and rule");

    for classified in &all {
        report(classified);
    }

    let reached: BTreeSet<String> = all
        .iter()
        .flat_map(|classified| classified.population.keys().cloned())
        .collect();
    println!("\n  the distinct cuts reached across every declared material: {reached:?}");

    // -------------------------------------------------------------------------------------------
    rule("[4]  ONE READING OF EACH CUT, WHOLE -- the current, the divergence, the evidence");

    let mut shown: BTreeSet<String> = BTreeSet::new();
    for exhibit in &exhibits {
        if shown.insert(exhibit.cut_name.clone()) {
            print!("{}", exhibit.rendered);
        }
    }

    // -------------------------------------------------------------------------------------------
    rule("[5]  THE REFUSALS -- what the organ will not answer");

    // The statement-withheld aperture is a real material whose load is EMPTY: it founds no reach
    // cells at all, so there is nothing for a current to cross and the cut would be a property of
    // the declaration. The refusal fires on the material, not on a synthetic empty set.
    let withheld_names = read_names(&withheld);
    let withheld_load = declared_load(&withheld);
    let withheld_cochain = accumulation(&withheld, AccumulationRule::RouteLoad);
    let withheld_readings =
        shared_identifier_family(&withheld, &withheld_cochain, AccumulationRule::RouteLoad);
    println!("\n  aperture {:?}", CircuitAperture::DEPOSITED_READER);
    println!(
        "  vertices {}   one-cells {}   reach cells founded: {}",
        withheld_names.vertex_name.len(),
        withheld_names.one_cells,
        withheld_load.len()
    );
    let withheld_reading = withheld_readings.first().map(|pair| {
        (
            pair.named(),
            chain_reading(&withheld, &from_pair("shared identifier", pair)),
        )
    });
    let empty_load_refused = match withheld_reading {
        Some((named, Ok(built))) => match name_the_cut(&built, &withheld_load) {
            Ok(cut) => {
                println!(
                    "  the organ ANSWERED an empty load with {}, which it must not",
                    cut.name()
                );
                false
            }
            Err(refusal) => {
                println!("  a real loop on this material, offered its own empty load:");
                println!("    {named}");
                println!("    REFUSED: {refusal}");
                true
            }
        },
        Some((named, Err(refusal))) => {
            println!("  the mouth refused this complex on {named}: {refusal}");
            false
        }
        None => {
            println!("  the statement-withheld material returned no loop to offer.");
            false
        }
    };

    // A grade-0 address offered where a load edge is expected: a real address from the SAME complex
    // as the reading, which that complex does not carry as an edge. Built fresh on the whole
    // production so the address and the reading are certainly one incidence.
    let whole_cochain = accumulation(&whole, AccumulationRule::RouteLoad);
    let whole_loop = shared_identifier_family(&whole, &whole_cochain, AccumulationRule::RouteLoad)
        .first()
        .and_then(|pair| chain_reading(&whole, &from_pair("shared identifier", pair)).ok());
    let vertex_as_load_refused = match (names.a_vertex_address, whole_loop) {
        (Some(address), Some(built)) => {
            let offered = BTreeSet::from([EdgeId(address)]);
            match name_the_cut(&built, &offered) {
                Ok(cut) => {
                    println!(
                        "\n  a VERTEX address offered as the load was ANSWERED with {}, which it \
                         must not",
                        cut.name()
                    );
                    false
                }
                Err(refusal) => {
                    println!(
                        "\n  the grade-0 address {} offered where a load EDGE is expected:",
                        names.vertex(VertexId(address))
                    );
                    println!("    REFUSED: {refusal}");
                    true
                }
            }
        }
        _ => false,
    };

    // -------------------------------------------------------------------------------------------
    rule("[6]  THE GAUGE -- does the accumulation rule move a cut?");

    let mut moved: Vec<(String, String, String)> = Vec::new();
    for material in materials.iter().map(|(name, _)| name.clone()) {
        let route_load = all
            .iter()
            .find(|c| c.material == material && c.rule == AccumulationRule::RouteLoad);
        let recruitment_load = all
            .iter()
            .find(|c| c.material == material && c.rule == AccumulationRule::RecruitmentLoad);
        let (Some(left), Some(right)) = (route_load, recruitment_load) else {
            continue;
        };
        for (named, cut) in &left.by_name {
            if let Some(other) = right.by_name.get(named) {
                if other != cut {
                    moved.push((named.clone(), cut.clone(), other.clone()));
                }
            }
        }
    }
    println!(
        "\n  loops whose cut CHANGED when the accumulation rule changed: {}",
        moved.len()
    );
    for (named, left, right) in moved.iter().take(6) {
        println!("    {named}");
        println!("      route-load -> {left}          recruitment-load -> {right}");
    }
    if moved.len() > 6 {
        println!("    ... and {} more", moved.len() - 6);
    }

    let ablation_moved = match (
        all.iter().find(|c| {
            c.material == "the whole production" && c.rule == AccumulationRule::RouteLoad
        }),
        all.iter().find(|c| {
            c.material != "the whole production" && c.rule == AccumulationRule::RouteLoad
        }),
    ) {
        (Some(left), Some(right)) => {
            println!("\n  the structural ablation:");
            println!("    whole      {:?}", left.population);
            println!("    ablated    {:?}", right.population);
            left.population != right.population
        }
        _ => false,
    };

    // -------------------------------------------------------------------------------------------
    rule("[7]  CONTROLS");

    let crossed_the_load = reached.contains("circulation j != 0");
    let missed_the_load = reached.contains("short circuit");

    controls.check(
        "the declared load is read off the material and is non-empty",
        !load.is_empty(),
        "an aperture that founds no reach cells -- and that material is run below, where the \
         organ refuses instead of answering",
    );
    controls.check(
        "at least two DIFFERENT cuts are reached across the declared materials",
        reached.len() >= 2,
        "a classifier that returns one name whatever it is handed, or a material carrying only \
         one species of chain",
    );
    controls.check(
        "the declared load SEPARATES: some closed loop crosses it and some closed loop does not",
        crossed_the_load && missed_the_load,
        "a load every closed loop crosses -- the short-circuit branch would then be unreachable \
         and the declaration would be doing no work",
    );
    controls.check(
        "an open route leaks and its closure does not: the same cells, two cuts",
        open_route_leaks > 0 && reached.contains("leak") && crossed_the_load,
        "a body whose routes already return -- there would be no emission without a return edge \
         to name",
    );
    controls.check(
        "the empty-load refusal fires on real material",
        empty_load_refused,
        "an organ that answered `short circuit` for every closed current when no load was \
         declared, making the cut a property of the declaration",
    );
    controls.check(
        "a grade-0 address offered as a load edge is refused by name",
        vertex_as_load_refused,
        "an organ that accepted any u64 as a load address",
    );
    controls.check(
        "the accumulation rule is a LIVE gauge: at least one loop changes cut under it",
        !moved.is_empty(),
        "two rules that land in one block of the cut partition on this material -- then their \
         agreement is vacuous and this run is bookkeeping",
    );
    controls.check(
        "the structural ablation MOVES the cut population",
        ablation_moved,
        "an ablation that removes no cell any reading crosses",
    );

    println!(
        "\n  {} controls checked, {} failed{}",
        controls.checked,
        controls.failed.len(),
        if controls.failed.is_empty() {
            String::new()
        } else {
            format!(": {:?}", controls.failed)
        }
    );

    if !controls.failed.is_empty() {
        std::process::exit(1);
    }
}

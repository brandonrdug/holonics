//! **The release read on the known-truth terrains, and the terrains' own counts** (THE_REBUILD U6,
//! step 1; #73, #148, #63): the reading half of step 1's harness, beside lane B's key location and
//! lane C's pair release (`hnn_keys_loop.rs`).
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_prediction -- executed evaluate <terrain> <seed> <count> <out> <label[=state]>…
//! cargo run --release -p holonics --example hnn_prediction -- executed counts <terrain> <training seed> <count> <validation seed> <count> <out>
//! ```
//!
//! - **`executed evaluate`**: every constitution generates every request of a known-truth terrain
//!   by `hnn::prediction::generate_by_bank` from the open section (`lossless` the declared opening,
//!   `opening` the founded transport, `<label>=<state>` a complete continuing state mounted whole);
//!   the counts are printed with constant and nonconstant requests apart and the success rule
//!   (every nonconstant section whole), and every section is written to `<out>`.
//! - **`executed counts`** (U6 step 1, loop 1a; the
//!   [pin](../../records/2026-09-30_THE_TWO_COUNTS_PINNED_BEFORE_ITS_RUNS.md)): the declared
//!   reference family (lag `ℓ ∈ [1, 40]`, a map of `ℤ/4`; the line in the hierarchical family too)
//!   read along the training passage, its survivors at every observation, `n*_terrain` at the
//!   stopping object and its certificate: read-only instrumentation, never passed to the machine,
//!   and the yardstick lane B's readings to lock are measured against.
//!
//! The certified descent's modes (`move`, `train`, `spread`, `slopes`, `witness`, `causal`,
//! `segment`, `instants`, `direction`, `rho-slopes`, `witness-plane`, `move-once`, `margins`,
//! `agreement`, `span`, `route-plane`, `kinetic`, `joined`, `run`, `pairs`, `step-state`, `expose`,
//! `word-read`, `locks`, `spectrum`) and loop 1c's (`restore`, `replay`, `coupling`,
//! `resume-coupling`, `represent`, in `hnn_loop_1c.rs`) retired with `hnn::executed`'s comparison
//! and move on October 5 (the library spine's S2; the
//! [retirement record](../../records/2026-10-05_S2_THE_CERTIFIED_DESCENT_RETIRES_AND_KEY_LOCATION_THEN_DEPOSITION_REPLACES_IT.md));
//! their source is at
//! [`9078f103`](https://github.com/brandonrdug/holonics/blob/9078f103/research/notebook/hnn_design/hnn_executed_loop.rs).

use super::*;
use holonics::hnn::constitution::ContinuingState;
use holonics::hnn::Encoded;
use holonics::holarchy::terrain::{CyclicLaw, KnownTruth};
use num_bigint::{BigInt, BigUint};
use num_traits::One;
use std::collections::BTreeSet;

/// An enclosure read at the grain `1/g`: the cells `[⌊g·lower⌋/g, (⌊g·upper⌋ + 1)/g)` it lies in.
pub(super) fn cell(interval: &ExactInterval, grain: i64) -> String {
    let g = Rat::from_integer(grain.into());
    let low = (&interval.lower * &g).floor().to_integer();
    let high = (&interval.upper * &g).floor().to_integer() + BigInt::from(1);
    format!("[{low}/{grain}, {high}/{grain})")
}

/// **A known-truth terrain** (only the terrain computes truth; the generation law is the library's,
/// `holarchy::terrain::KnownTruth::cyclic`, moved there on October 5 for THE_MACHINE guard 9 with its
/// draws in the same order): `order2`, `x_t = x_(t−2) + 1 (mod 4)` after the request's drawn cells;
/// `alternation`, two drawn classes alternating, `x_t = x_(t−2)`; `line`, a drawn start and step,
/// `x_t = x_0 + s t (mod 4)`; each passage a request and its stations.
pub(super) fn terrain_truth(terrain: &str, declared: &Declared, seed: u64, count: usize) -> KnownTruth {
    let symbols = declared.alphabet - 1;
    let (n, m) = (declared.request, declared.stations);
    let law = match terrain {
        "order2" => CyclicLaw::OrderTwo { opening: n },
        "alternation" => CyclicLaw::Alternation,
        "line" => CyclicLaw::Line,
        _ => panic!("a terrain: order2 | alternation | line"),
    };
    KnownTruth::cyclic(law, symbols, seed, count, n + m).expect("a declared cyclic terrain")
}

/// **A known-truth terrain's pairs**, read to declare a request's length and to score (the truth's
/// own classes): each passage cut into its request and its stations.
pub(super) fn terrain_pairs(
    terrain: &str,
    declared: &Declared,
    seed: u64,
    count: usize,
) -> Vec<(Vec<usize>, Vec<usize>)> {
    terrain_truth(terrain, declared, seed, count)
        .passages()
        .iter()
        .map(|passage| {
            let (request, target) = passage.split_at(declared.request);
            (request.to_vec(), target.to_vec())
        })
        .collect()
}

/// **The terrain's passages as the field reads them** (THE_MACHINE guard 9): its declared identity
/// (`Encoded::identity`), each passage a request and its stations, in the pairs' order.
pub(super) fn terrain_encoded(
    terrain: &str,
    declared: &Declared,
    field: &Field,
    seed: u64,
    count: usize,
) -> Vec<Encoded> {
    Encoded::identity(&terrain_truth(terrain, declared, seed, count), field)
        .expect("the terrain's classes inject into the field's source ports")
}

/// [definition; agent-inferred, step 1b's pin §13.6] **A checkpoint: the complete continuing state**
/// (`Constitution::continuing_state`): `E rows cols`, its rows and `rho ρ` first, then the normal
/// law's carried Gram and chart, its carried remainders, the locus's clock, the commit and the
/// storage product.
pub(super) fn write_state(theta: &Constitution, ring: usize) -> String {
    theta
        .continuing_state(ring)
        .expect("a deposit moves the source port alone")
        .to_text()
}

/// [definition; agent-inferred, October 3; October 5] **A state mounted from a file** onto the
/// declared opening: the file is a complete continuing state (`ContinuingState::from_text`, which
/// checks its text and its material identity) restored whole by `Constitution::continued`; refused
/// where the file is damaged, carries no check, holds `E` and `ρ` alone, or continues another
/// opening's material. The partial remount of `E` and `ρ` and the manifest of states written before
/// the identity served the retired descent's states only (at `9078f103`).
pub(super) fn mount(opening: &Constitution, path: &str) -> Constitution {
    #[allow(clippy::disallowed_methods)]
    let text = std::fs::read_to_string(path).expect("read the state");
    let state = ContinuingState::from_text(&text)
        .unwrap_or_else(|error| panic!("{path}: not a complete continuing state ({error})"));
    opening.clone().continued(&state).expect("the state continues the declared opening")
}


/// **The founded opening**: the declared constitution with the source ring's transport founded off the lossless boundary
/// (`Constitution::founded_transport`).
pub(super) fn founded_opening(engine: &Engine) -> Constitution {
    engine
        .theta
        .clone()
        .founded_transport(&engine.field, engine.refinement.ring())
        .expect("the founded transport")
}

/// **The release read on a terrain** (`executed evaluate <terrain> <seed> <count> <out> <label=E>…`, a
/// label `opening` reading the declared opening): every constitution generates every confirmation
/// request by `generate_by_bank` from the open section; the complete sections are written to `out`
/// and the counts printed: released and held, whole sections equal to their targets, stations
/// right by station, sections reaching the termination, incorrect releases, the first lock's
/// station and correctness, and the refused certificates.
pub(super) fn evaluate(terrain: &str, seed: u64, count: usize, out: &str, arms: &[String]) {
    use rayon::prelude::*;
    use std::fmt::Write as _;
    let clock = Instant::now();
    let declared = order_declared();
    let engine = Engine::new(declared);
    let bank = bank_of(declared.period, &bank_strength());
    let ring = engine.refinement.ring();
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let requests: Vec<Encoded> = terrain_encoded(terrain, &declared, &engine.field, seed, count)
        .into_iter()
        .map(|passage| passage.part(0..declared.request).expect("a request within its passage"))
        .collect();
    let mut listing = String::new();
    for arm in arms {
        let (label, path) = arm.split_once('=').unwrap_or((arm.as_str(), ""));
        let theta = match (label, path.is_empty()) {
            ("lossless", true) => engine.theta.clone(),
            (_, true) => founded_opening(&engine),
            // A complete continuing state, mounted whole.
            (_, false) => mount(&engine.theta, path),
        };
        // The constitution's own clock: its requests' generation (run in parallel on the host's
        // cores) and their tally, read before the listing is written.
        let started = Instant::now();
        let generated: Vec<_> = requests
            .par_iter()
            .map(|request| {
                let (current, moment) = ingest(&engine.field, request);
                generate_by_bank(
                    &engine.field,
                    &theta,
                    &current,
                    &moment,
                    &engine.refinement,
                    &bank,
                    BANK_GRAIN,
                )
            })
            .collect();
        let (mut released, mut held, mut whole, mut incorrect, mut terminated) = (0, 0, 0, 0, 0);
        let (mut refused, mut uncertified) = (0, 0);
        let mut by_station = vec![0usize; declared.stations];
        let (mut first_request, mut first_right) = (0, 0);
        // The two counts' split (the pin §4): nonconstant and constant requests apart, and the
        // success rule, every nonconstant request's section released whole.
        let (mut nonconstant, mut whole_nonconstant, mut whole_constant) = (0, 0, 0);
        writeln!(listing, "== {label} on {terrain}, seed {seed}").unwrap();
        for ((request, target), generation) in pairs.iter().zip(&generated) {
            let is_constant = constant_request(request);
            nonconstant += usize::from(!is_constant);
            let Ok(generation) = generation else {
                refused += 1;
                writeln!(listing, "{request:?} → refused").unwrap();
                continue;
            };
            let classes = &generation.release.classes;
            uncertified += usize::from(generation.uncertified.is_some());
            let right: Vec<bool> = classes.iter().zip(target).map(|(a, b)| a == b).collect();
            for (j, r) in right.iter().enumerate() {
                by_station[j] += usize::from(*r);
            }
            terminated += usize::from(generation.release.terminated.is_some());
            if let Some(first) = generation.locks.first().and_then(|lock| lock.first()) {
                first_request += usize::from(*first < 2);
                first_right += usize::from(classes[*first] == target[*first]);
            }
            if generation.release.released() {
                released += 1;
                if right.iter().all(|r| *r) {
                    whole += 1;
                    if is_constant {
                        whole_constant += 1;
                    } else {
                        whole_nonconstant += 1;
                    }
                } else {
                    incorrect += 1;
                }
            } else {
                held += 1;
            }
            writeln!(
                listing,
                "{} | target {:?} | {} {:?} | locks {:?}{}",
                request.iter().map(ToString::to_string).collect::<String>(),
                target,
                if generation.release.released() { "released" } else { "held" },
                classes,
                generation.locks,
                if is_constant { " | constant request" } else { "" }
            )
            .unwrap();
        }
        // The pair contacts the material holds closed, as the release read them (lane C).
        let contacts = generated
            .iter()
            .find_map(|generation| generation.as_ref().ok().map(|g| g.contacts.clone()))
            .unwrap_or_default();
        println!(
            "  {label} (transport modulus {}; closed pair contacts at {contacts:?}): released {released}, held {held}, refused {refused}, refused certificates {uncertified}; whole sections {whole} of {count} (nonconstant {whole_nonconstant} of {nonconstant}, constant {whole_constant} of {}); the success rule (every nonconstant section whole): {}; incorrect releases {incorrect}; reaching the termination {terminated}; stations right {} by station {by_station:?}; first lock at a request-reading station (0 or 1) {first_request}, first lock right {first_right}; {} ms",
            theta.transport(ring),
            count - nonconstant,
            if whole_nonconstant == nonconstant { "holds" } else { "does not hold" },
            by_station.iter().sum::<usize>(),
            started.elapsed().as_millis()
        );
        // Written after each constitution, so a run stopped by its guard keeps what it read.
        #[allow(clippy::disallowed_methods)]
        std::fs::write(out, &listing).expect("write the sections");
    }
    #[allow(clippy::disallowed_methods)]
    std::fs::write(out, listing).expect("write the sections");
    println!(
        "executed evaluate: {} ms; resident {}",
        clock.elapsed().as_millis(),
        resident()
    );
}

// -------------------------------------------------------------------------------------------
// The two counts (THE_REBUILD U6, step 1, loop 1a; the
// [pin](../../records/2026-09-30_THE_TWO_COUNTS_PINNED_BEFORE_ITS_RUNS.md)). Read-only
// instrumentation: the declared reference family is computed from the terrain's pairs alone and is
// printed; nothing of it (keys, survivors, lags, continuations) reaches the machine.

/// [definition; the pin §1] **The declared reference family's lags** `ℓ ∈ [1, LAGS]` over the
/// terrain's residue ring `ℤ/RESIDUES` (the alphabet less the termination).
const LAGS: usize = 40;
const RESIDUES: usize = 4;

/// **An observation's argument** under lag `ℓ` (the pin §1, the emitter): station `j`'s cell
/// `x_(n + j − ℓ)`, read from the request (the initial history) or from the same request's earlier
/// stations; never across a request boundary.
fn argument(request: &[usize], section: &[usize], station: usize, lag: usize) -> usize {
    let at = request.len() + station - lag;
    if at < request.len() {
        request[at]
    } else {
        section[at - request.len()]
    }
}

/// [definition; the pin §1] **A constant request**: its 40 cells one class, so every lag reads its
/// one symbol and it separates no lag.
fn constant_request(request: &[usize]) -> bool {
    request.iter().all(|&x| x == request[0])
}

/// An observation count in both units (the pin §4): `q` requests plus `j` stations.
fn both_units(observations: usize, stations: usize) -> String {
    format!(
        "{observations} observations ({} requests plus {} stations)",
        observations / stations,
        observations % stations
    )
}

/// [definition; the pin §1] **One lag's fibre in the global family**: whether it lives, and its
/// map's value at each residue (`None` unobserved: every value survives there).
#[derive(Clone, Debug, PartialEq, Eq)]
struct LagFibre {
    alive: bool,
    map: [Option<usize>; RESIDUES],
}

/// [definition; the pin §1] **One lag's fibre in the hierarchical family `H`**: whether it lives,
/// the finished requests' translation counts multiplied, and the current request's consistent
/// translations (reset to all of `ℤ/4` at each request boundary: the translation never carries
/// across requests, the lag and its death do).
#[derive(Clone, Debug)]
struct TranslationFibre {
    alive: bool,
    past: BigUint,
    current: [bool; RESIDUES],
}

/// [definition; the pin §1] **A declared reference family's survivors**, read along a passage in
/// its order: the global family (one key for every request) or `H` (a global lag, a per-request
/// translation, over a passage of `requests` requests, `begun` of them begun).
#[derive(Clone, Debug)]
enum ReferenceFamily {
    Global(Vec<LagFibre>),
    Hierarchical {
        lags: Vec<TranslationFibre>,
        requests: usize,
        begun: usize,
    },
}

impl ReferenceFamily {
    fn global() -> Self {
        Self::Global(vec![
            LagFibre {
                alive: true,
                map: [None; RESIDUES],
            };
            LAGS
        ])
    }

    fn hierarchical(requests: usize) -> Self {
        Self::Hierarchical {
            lags: vec![
                TranslationFibre {
                    alive: true,
                    past: BigUint::from(1u32),
                    current: [true; RESIDUES],
                };
                LAGS
            ],
            requests,
            begun: 0,
        }
    }

    fn name(&self) -> &'static str {
        match self {
            Self::Global(_) => "the global family",
            Self::Hierarchical { .. } => "the hierarchical family H",
        }
    }

    /// The family's size under its prior: `40 · 4⁴` keys, or `40 · 4^R` for `H`.
    fn size(&self) -> BigUint {
        let four = BigUint::from(RESIDUES as u32);
        match self {
            Self::Global(_) => BigUint::from(LAGS as u32) * four.pow(RESIDUES as u32),
            Self::Hierarchical { requests, .. } => {
                BigUint::from(LAGS as u32) * four.pow(*requests as u32)
            }
        }
    }

    /// **The survivors' count** `#S_k` (the pin §1): `Σ_(ℓ alive) 4^(u_ℓ)`, or for `H`
    /// `Σ_(ℓ alive) Π_r #C_(ℓ,r)`, every unbegun request with its four translations.
    fn count(&self) -> BigUint {
        let four = BigUint::from(RESIDUES as u32);
        match self {
            Self::Global(lags) => lags
                .iter()
                .filter(|lag| lag.alive)
                .map(|lag| four.pow(lag.map.iter().filter(|v| v.is_none()).count() as u32))
                .sum(),
            Self::Hierarchical {
                lags,
                requests,
                begun,
            } => lags
                .iter()
                .filter(|lag| lag.alive)
                .map(|lag| {
                    if *begun == 0 {
                        four.pow(*requests as u32)
                    } else {
                        let current =
                            BigUint::from(lag.current.iter().filter(|c| **c).count() as u32);
                        &lag.past * current * four.pow((*requests - *begun) as u32)
                    }
                })
                .sum(),
        }
    }

    /// **A request boundary**: `H`'s translation fibre resets to all of `ℤ/4`, the finished
    /// request's count joining the product (the pin §1, the reset convention).
    fn begin(&mut self) {
        if let Self::Hierarchical { lags, begun, .. } = self {
            if *begun > 0 {
                for lag in lags.iter_mut().filter(|lag| lag.alive) {
                    let kept = lag.current.iter().filter(|c| **c).count();
                    lag.past *= BigUint::from(kept as u32);
                }
            }
            for lag in lags.iter_mut() {
                lag.current = [true; RESIDUES];
            }
            *begun += 1;
        }
    }

    /// **One observation**: station `j` of a request, its true value `section[j]` against every
    /// alive key's emission (the pin §1).
    fn observe(&mut self, request: &[usize], section: &[usize], station: usize) {
        let value = section[station];
        match self {
            Self::Global(lags) => {
                for (index, lag) in lags.iter_mut().enumerate().filter(|(_, lag)| lag.alive) {
                    let a = argument(request, section, station, index + 1);
                    match lag.map[a] {
                        None => lag.map[a] = Some(value),
                        Some(v) if v != value => lag.alive = false,
                        Some(_) => {}
                    }
                }
            }
            Self::Hierarchical { lags, .. } => {
                for (index, lag) in lags.iter_mut().enumerate().filter(|(_, lag)| lag.alive) {
                    let a = argument(request, section, station, index + 1);
                    let c = (value + RESIDUES - a) % RESIDUES;
                    for (t, kept) in lag.current.iter_mut().enumerate() {
                        *kept &= t == c;
                    }
                    if lag.current.iter().all(|kept| !kept) {
                        lag.alive = false;
                    }
                }
            }
        }
    }

    /// The alive lags.
    fn alive(&self) -> Vec<usize> {
        match self {
            Self::Global(lags) => (1..=LAGS).filter(|l| lags[l - 1].alive).collect(),
            Self::Hierarchical { lags, .. } => (1..=LAGS).filter(|l| lags[l - 1].alive).collect(),
        }
    }

    /// **The continuations the survivors emit on a fresh request** (the pin §4): each key run
    /// freely over the request's `stations` (its own emissions its later arguments; an unobserved
    /// argument emits every value; `H`'s fresh translation every value), stopping once `bound`
    /// distinct continuations are found. With `given`, `H` reads the request's own first station
    /// (its translation's one reading) and every continuation starts with it.
    fn continuations(
        &self,
        request: &[usize],
        stations: usize,
        bound: usize,
        given: Option<usize>,
    ) -> BTreeSet<Vec<usize>> {
        fn emit(
            request: &[usize],
            lag: usize,
            map: [Option<usize>; RESIDUES],
            section: &mut Vec<usize>,
            stations: usize,
            out: &mut BTreeSet<Vec<usize>>,
            bound: usize,
        ) {
            if out.len() >= bound {
                return;
            }
            if section.len() == stations {
                out.insert(section.clone());
                return;
            }
            let a = argument(request, section, section.len(), lag);
            let values: Vec<usize> = match map[a] {
                Some(y) => vec![y],
                None => (0..RESIDUES).collect(),
            };
            for y in values {
                let mut next = map;
                next[a] = Some(y);
                section.push(y);
                emit(request, lag, next, section, stations, out, bound);
                section.pop();
            }
        }
        let mut out = BTreeSet::new();
        for lag in self.alive() {
            match self {
                Self::Global(lags) => emit(
                    request,
                    lag,
                    lags[lag - 1].map,
                    &mut Vec::new(),
                    stations,
                    &mut out,
                    bound,
                ),
                Self::Hierarchical { .. } => {
                    let translations: Vec<usize> = match given {
                        Some(first) => {
                            vec![(first + RESIDUES - argument(request, &[], 0, lag)) % RESIDUES]
                        }
                        None => (0..RESIDUES).collect(),
                    };
                    for c in translations {
                        let map: [Option<usize>; RESIDUES] =
                            std::array::from_fn(|a| Some((a + c) % RESIDUES));
                        emit(request, lag, map, &mut Vec::new(), stations, &mut out, bound);
                    }
                }
            }
            if out.len() >= bound {
                break;
            }
        }
        out
    }

    /// The survivor list, the certificate (the pin §4): every alive lag with its map (`·` an
    /// unobserved argument, its fibre all of `ℤ/4`), or for `H` the lag and its current
    /// translations; a key is marked an alias when it is not the terrain's generating key.
    fn certificate(&self, generating: Option<(usize, [usize; RESIDUES])>) -> String {
        match self {
            Self::Global(lags) => self
                .alive()
                .iter()
                .map(|&l| {
                    let map = lags[l - 1].map;
                    let shown: Vec<String> = map
                        .iter()
                        .map(|v| v.map_or_else(|| "·".to_string(), |y| y.to_string()))
                        .collect();
                    let alias = match generating {
                        Some((lag, f))
                            if lag == l && map.iter().zip(f).all(|(v, y)| *v == Some(y)) =>
                        {
                            ""
                        }
                        _ => " alias",
                    };
                    format!("ℓ {l} f [{}]{alias}", shown.join(" "))
                })
                .collect::<Vec<_>>()
                .join("; "),
            Self::Hierarchical { lags, .. } => self
                .alive()
                .iter()
                .map(|&l| {
                    let kept: Vec<usize> =
                        (0..RESIDUES).filter(|&c| lags[l - 1].current[c]).collect();
                    format!("ℓ {l} (current translations {kept:?})")
                })
                .collect::<Vec<_>>()
                .join("; "),
        }
    }

    /// Every alive lag's unobserved arguments (the global family).
    fn unobserved(&self) -> String {
        match self {
            Self::Global(lags) => self
                .alive()
                .iter()
                .filter_map(|&l| {
                    let free: Vec<usize> =
                        (0..RESIDUES).filter(|&a| lags[l - 1].map[a].is_none()).collect();
                    (!free.is_empty()).then(|| format!("ℓ {l}: {free:?}"))
                })
                .collect::<Vec<_>>()
                .join("; "),
            Self::Hierarchical { .. } => String::new(),
        }
    }
}

/// The terrain's generating key in the global family, where it is one (the pin §2): order-2
/// `(2, a ↦ a + 1)`, the alternation `(2, id)`; the line's law is no global key.
fn generating_key(terrain: &str) -> Option<(usize, [usize; RESIDUES])> {
    match terrain {
        "order2" => Some((2, [1, 2, 3, 0])),
        "alternation" => Some((2, [0, 1, 2, 3])),
        _ => None,
    }
}

/// `log₂` of an exact ratio of counts, enclosed on the declared grid.
fn bits(ratio: &Rat) -> ExactInterval {
    holonics::ratio::algebraic::log2_enclosure(ratio).expect("a positive ratio")
}

/// A ratio of two counts, exact.
fn count_ratio(numerator: &BigUint, denominator: &BigUint) -> Rat {
    Rat::new(BigInt::from(numerator.clone()), BigInt::from(denominator.clone()))
}

/// [definition; the pin §1, §4] **A family's reading along a passage**: the survivors' count
/// before every observation and after the last (`counts[k] = #S_k`), and the family after the
/// passage.
struct PassageReading {
    counts: Vec<BigUint>,
    family: ReferenceFamily,
}

/// Read a family along the passage, observation by observation, in the passage's order; `at`
/// sees the family after each observation `k` (its count `counts[k]` already pushed).
fn read_passage(
    mut family: ReferenceFamily,
    pairs: &[(Vec<usize>, Vec<usize>)],
    mut at: impl FnMut(usize, &ReferenceFamily, &[BigUint]),
) -> PassageReading {
    let mut counts = vec![family.count()];
    for (request, section) in pairs {
        family.begin();
        for station in 0..section.len() {
            family.observe(request, section, station);
            counts.push(family.count());
            at(counts.len() - 1, &family, &counts);
        }
    }
    PassageReading { counts, family }
}

/// **The ideal listener's information on each batch of the passage** (D1; the pin §5): each
/// move's exact ratio `#S_(64m)/#S_(64(m+1))` and its `log₂` enclosed, in bits.
fn batch_information(counts: &[BigUint], per_batch: usize) -> Vec<(Rat, ExactInterval)> {
    (0..(counts.len() - 1) / per_batch)
        .map(|m| {
            let ratio = count_ratio(&counts[m * per_batch], &counts[(m + 1) * per_batch]);
            let b = bits(&ratio);
            (ratio, b)
        })
        .collect()
}

/// The families the pin reads on a terrain (§1): the global family, and on the line `H` too.
fn families_of(terrain: &str, requests: usize) -> Vec<ReferenceFamily> {
    if terrain == "line" {
        vec![ReferenceFamily::global(), ReferenceFamily::hierarchical(requests)]
    } else {
        vec![ReferenceFamily::global()]
    }
}

/// **The terrain's counts** (`executed counts <terrain> <training seed> <requests> <validation
/// seed> <validation count> <out>`; the pin §1, §2, §4): the declared reference family read along
/// the machine's own training passage (the training requests in their order, station by station),
/// every observation's survivors and ratio written to `out`; `n*_terrain` at the stopping object
/// (the nonconstant validation requests, and all of them), the syntactic class, the certificate,
/// the unobserved arguments and lag aliases, the constant requests' bits apart, each batch's
/// information, and the training/validation content overlap. The line is read in `H` too.
pub(super) fn counts(
    terrain: &str,
    seed: u64,
    count: usize,
    validation_seed: u64,
    validation_count: usize,
    out: &str,
) {
    use std::fmt::Write as _;
    let clock = Instant::now();
    let declared = order_declared();
    let stations = declared.stations;
    let pairs = terrain_pairs(terrain, &declared, seed, count);
    let validation = terrain_pairs(terrain, &declared, validation_seed, validation_count);
    let batch = 8;
    let constant: Vec<usize> =
        (0..pairs.len()).filter(|&r| constant_request(&pairs[r].0)).collect();
    let validation_constant = validation.iter().filter(|(r, _)| constant_request(r)).count();
    let shared = validation
        .iter()
        .filter(|(v, _)| pairs.iter().any(|(t, _)| t == v))
        .count();
    let distinct_training: BTreeSet<&Vec<usize>> = pairs.iter().map(|(r, _)| r).collect();
    let distinct_validation: BTreeSet<&Vec<usize>> = validation.iter().map(|(r, _)| r).collect();
    println!(
        "executed counts: {terrain}, the training passage at seed {seed} ({count} requests, {} observations), validation at seed {validation_seed} ({validation_count} requests); the family: lag in [1, {LAGS}], a map of Z/{RESIDUES}",
        count * stations
    );
    println!(
        "  constant requests: training {} of {count} (requests {constant:?}), validation {validation_constant} of {validation_count}; distinct requests: training {}, validation {}; validation requests whose 40 cells equal a training request's: {shared} of {validation_count}",
        constant.len(),
        distinct_training.len(),
        distinct_validation.len()
    );
    let mut listing = String::new();
    for family in families_of(terrain, count) {
        let name = family.name();
        let size = family.size();
        let hierarchical = matches!(family, ReferenceFamily::Hierarchical { .. });
        // The stopping object, read where the survivors change (they only shrink, so the
        // continuations only shrink: the first count at which it holds is n*).
        let unique = |f: &ReferenceFamily, v: &(Vec<usize>, Vec<usize>), given: bool| {
            f.continuations(&v.0, stations, 2, given.then(|| v.1[0])).len() == 1
        };
        let holds = |f: &ReferenceFamily, all: bool, given: bool| {
            validation
                .iter()
                .filter(|v| all || !constant_request(&v.0))
                .all(|v| unique(f, v, given))
        };
        let (mut star, mut star_all, mut star_given) = (None, None, None);
        let mut star_family = None;
        let mut last_change = 0;
        if hierarchical && holds(&family, false, true) {
            star_given = Some(0);
        }
        let reading = read_passage(family, &pairs, |k, f, counts| {
            if counts[k] != counts[k - 1] {
                last_change = k;
                if star.is_none() && holds(f, false, false) {
                    star = Some(k);
                    star_family = Some(f.clone());
                }
                if star_all.is_none() && holds(f, true, false) {
                    star_all = Some(k);
                }
                if hierarchical && star_given.is_none() && holds(f, false, true) {
                    star_given = Some(k);
                }
            }
        });
        let counts = &reading.counts;
        writeln!(
            listing,
            "== {name} on {terrain}, seed {seed}: observation, request, station, value, #S, ratio #S_(k-1)/#S_k, its bits (2^-8 cells), the code log2(|K|/#S) (2^-8 cells)"
        )
        .unwrap();
        writeln!(listing, "0 - - - {} - - [0/256, 0/256]", counts[0]).unwrap();
        let mut constant_ratio = Rat::one();
        let mut nonconstant_ratio = Rat::one();
        for k in 1..counts.len() {
            let request = (k - 1) / stations;
            let station = (k - 1) % stations;
            let ratio = count_ratio(&counts[k - 1], &counts[k]);
            if constant.contains(&request) {
                constant_ratio *= &ratio;
            } else {
                nonconstant_ratio *= &ratio;
            }
            let code = count_ratio(&size, &counts[k]);
            writeln!(
                listing,
                "{k} {request} {station} {} {} {} {} {}",
                pairs[request].1[station],
                counts[k],
                ratio,
                cell(&bits(&ratio), 1 << 8),
                cell(&bits(&code), 1 << 8)
            )
            .unwrap();
        }
        let end = counts.last().expect("a count");
        println!(
            "  {name}: |K| = {size}; after the passage #S = {end}, the code log2(|K|/#S) ∈ {} bits; the alphabet's lower bound clog4 10240 = 7 observations",
            cell(&bits(&count_ratio(&size, end)), 1 << 8)
        );
        // The head of the ideal listener's curve (every observation in the receipts).
        let head = star
            .unwrap_or(0)
            .max(last_change.min(4 * stations))
            .min(counts.len() - 1);
        let curve: Vec<String> = (1..=head)
            .map(|k| format!("{k}:{}", count_ratio(&counts[k - 1], &counts[k])))
            .collect();
        println!(
            "  {name}: the curve's head, observation:ratio #S_(k-1)/#S_k, through observation {head}: {}",
            curve.join(" ")
        );
        println!(
            "  {name}: #S at the request boundaries 0 to 8: {}",
            (0..=8usize.min(count))
                .map(|r| counts[r * stations].to_string())
                .collect::<Vec<_>>()
                .join(" ")
        );
        match (star, &star_family) {
            (Some(k), Some(f)) => println!(
                "  {name}: n*_terrain (every nonconstant validation request's continuation unique) at {}; #S = {}; the code ∈ {} bits; survivors: {}; unobserved arguments: {}",
                both_units(k, stations),
                counts[k],
                cell(&bits(&count_ratio(&size, &counts[k])), 1 << 8),
                f.certificate(generating_key(terrain)),
                f.unobserved()
            ),
            _ => println!(
                "  {name}: n*_terrain not reached in the passage's {}: the stopping object does not hold",
                both_units(counts.len() - 1, stations)
            ),
        }
        match star_all {
            Some(k) => println!(
                "  {name}: with the constant validation requests included, the stopping object at {}",
                both_units(k, stations)
            ),
            None => println!(
                "  {name}: with the constant validation requests included, not reached"
            ),
        }
        if hierarchical {
            match star_given {
                Some(k) => println!(
                    "  {name}: given each validation request's own first station (its translation's reading), stations 1 to 7 unique at {}",
                    both_units(k, stations)
                ),
                None => println!(
                    "  {name}: given each validation request's own first station, not unique in the passage"
                ),
            }
        }
        println!(
            "  {name}: the syntactic class: the survivors last changed at {}; {end} survivors at the passage's end ({}); alive lags {:?}; survivors: {}; unobserved arguments: {}",
            both_units(last_change, stations),
            if *end == BigUint::from(1u32) { "one key" } else { "not one key" },
            reading.family.alive(),
            reading.family.certificate(generating_key(terrain)),
            reading.family.unobserved()
        );
        let final_distinct: Vec<usize> = validation
            .iter()
            .map(|v| reading.family.continuations(&v.0, stations, 1 << 12, None).len())
            .collect();
        let unique_nonconstant = validation
            .iter()
            .zip(&final_distinct)
            .filter(|(v, n)| !constant_request(&v.0) && **n == 1)
            .count();
        let unique_constant = validation
            .iter()
            .zip(&final_distinct)
            .filter(|(v, n)| constant_request(&v.0) && **n == 1)
            .count();
        println!(
            "  {name}: at the passage's end, validation requests with one admitted continuation: nonconstant {unique_nonconstant} of {}, constant {unique_constant} of {validation_constant}; distinct continuations per validation request (at most 4096 counted) {final_distinct:?}",
            validation_count - validation_constant
        );
        println!(
            "  {name}: the bits the constant training requests' observations carry: log2({constant_ratio}) ∈ {}; the nonconstant requests': log2({nonconstant_ratio}) ∈ {}",
            cell(&bits(&constant_ratio), 1 << 8),
            cell(&bits(&nonconstant_ratio), 1 << 8)
        );
        let per_batch = batch_information(counts, batch * stations);
        println!(
            "  {name}: each move's batch (8 requests, 64 observations), the ideal listener's ratio and bits: {}",
            per_batch
                .iter()
                .enumerate()
                .map(|(m, (ratio, b))| format!("move {m}: {ratio}, {}", cell(b, 1 << 8)))
                .collect::<Vec<_>>()
                .join("; ")
        );
    }
    #[allow(clippy::disallowed_methods)]
    std::fs::write(out, listing).expect("write the curve");
    println!(
        "executed counts: {} ms; resident {}",
        clock.elapsed().as_millis(),
        resident()
    );
}

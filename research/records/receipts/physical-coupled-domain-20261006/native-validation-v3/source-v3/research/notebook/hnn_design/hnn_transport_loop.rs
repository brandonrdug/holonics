//! **The located transport: each occurrence steps the rings by its located advance** (THE_REBUILD
//! U6, lanes E and B; the
//! [record](../../records/2026-10-05_THE_LOCATED_TRANSPORT_EACH_OCCURRENCE_STEPS_THE_RINGS_BY_ITS_LOCATED_ADVANCE.md),
//! whose §0 pins every declaration below; #73, #148, #63).
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_prediction -- executed transport <seed> <read keys> <length> <out> [locate]
//! ```
//!
//! [definition; agent-inferred, the record's §0] **`executed transport`** draws the terrain on the
//! helix `(3, 4, 5)` (`compression::keys::transport::SteppedTerrain::draw`), then the order of the
//! helix's 60 keys; the first `<read keys>` open the read set's passages of `<length>` cells, and
//! the keys left open the repair passages. From here the machine reads only the emitted classes:
//! 1. **Locate** (`TransportLocation::locate`): the fibre, its members, the survivors' curve
//!    (`<out>.curve`), `n*_machine` against the unicity count.
//! 2. **Relabel**: every fifth of the 120 permutations of the classes (24, the identity first), the
//!    location and the code length on each, and the residue chart's code length on each.
//! 3. **Found** (`hnn::encoding`, read-only): the helix chart on the representative member's
//!    transports, its squares, reached span and dimension.
//! 4. **Code**: the located navigator's code, read back, against the literal and the residue chart.
//! 5. **Repair**: the held-out keys' passages of 60 cells under the record's damage, restricted
//!    through the fibre (`restrict_fibre`), released or held; the residual, read back.
//!
//! Only then is the truth read, to score. Four repaired passages are written to `<out>.sections`.

use super::*;
use holonics::compression::keys::repair::CellRelease;
use holonics::compression::keys::transport::{
    CarryHelix, LocatedTransport, SteppedTerrain, TransportFibre, TransportLocation,
    gauge_representative, lift_reopen, lift_residual, located_code, read_located, read_residual,
    residual_code, restrict_fibre, unicity_count,
};
use holonics::hnn::encoding::{Encoding, PassageChart};

/// The helix's rings, ring 0 least significant; the last receives.
const PERIODS: [u64; 3] = [3, 4, 5];
/// `|A|`, the receiving ring's cells.
const CLASSES: usize = 5;
/// The repair passages' length: one turn of the joint clock.
const REPAIR_LENGTH: usize = 60;

/// **The declared damage** (the record's §0.3): 23 erased cells of 60, the tail included.
fn damage() -> Vec<usize> {
    std::iter::once(3)
        .chain(6..10)
        .chain(20..25)
        .chain(33..37)
        .chain(44..48)
        .chain(55..60)
        .collect()
}

/// Every permutation of `ℤ/m`, lexicographic.
fn permutations(m: usize) -> Vec<Vec<usize>> {
    if m == 0 {
        return vec![Vec::new()];
    }
    let mut all = Vec::new();
    for rest in permutations(m - 1) {
        for at in 0..m {
            let mut p = rest.clone();
            p.insert(at, m - 1);
            all.push(p);
        }
    }
    all.sort();
    all
}

/// The residue chart's transport (the refused chart, read only as the comparison):
/// `A_res(u) = Σ_g [u mod d_g ∈ {0}] ∏_(h<g) d_h`, the field's single notch.
fn residue_advances() -> Vec<u64> {
    (0..CLASSES as u64)
        .map(|u| {
            let mut weight = 1;
            PERIODS
                .iter()
                .map(|&d| {
                    let term = if u % d == 0 { weight } else { 0 };
                    weight *= d;
                    term
                })
                .sum()
        })
        .collect()
}

/// The residue chart's code length: its lock sets (`Σ d_g` bits) and the least residual over every
/// label bijection, each passage at its key of fewest patches.
fn residue_code(helix: &CarryHelix, passages: &[Vec<usize>]) -> usize {
    let advances = residue_advances();
    let description: u64 = PERIODS.iter().sum();
    let best = permutations(CLASSES)
        .into_iter()
        .map(|labels| {
            let labels: Vec<Option<usize>> = labels.into_iter().map(Some).collect();
            let located = LocatedTransport::new(helix.clone(), advances.clone(), labels.clone())
                .expect("a residue navigator");
            let keys: Vec<u64> = passages
                .iter()
                .map(|passage| {
                    (0..helix.period())
                        .min_by_key(|&key| located.patches(passage, key))
                        .expect("a key")
                })
                .collect();
            let code = residual_code(helix, &advances, &labels, &keys, passages).expect("a code");
            let lengths: Vec<usize> = passages.iter().map(Vec::len).collect();
            let read = read_residual(helix, &advances, &mut code.iter().copied(), &lengths)
                .expect("the residue code reads back");
            assert_eq!(read, passages, "the residue chart's code reopens its passages");
            code.len()
        })
        .min()
        .expect("a labelling");
    best + description as usize
}

fn outcome(fibre: &TransportFibre) -> String {
    match fibre {
        TransportFibre::Empty => "empty".to_string(),
        TransportFibre::One(_) => "one".to_string(),
        TransportFibre::Plural { classes } => format!("plural ({classes} gauge classes)"),
    }
}

fn row(cells: &[Option<usize>]) -> String {
    cells
        .iter()
        .map(|cell| cell.map_or('·', |c| char::from(b'0' + c as u8)))
        .collect()
}

pub(super) fn transport(seed: u64, read_keys: usize, length: usize, out: &str, locate_only: bool) {
    let clock = Instant::now();
    let helix = CarryHelix::new(PERIODS.to_vec()).expect("the declared helix");
    let period = helix.period() as usize;
    let mut draw = Draw::new(seed);
    let terrain = SteppedTerrain::draw(helix.clone(), &mut draw);
    let mut left: Vec<u64> = (0..helix.period()).collect();
    let order: Vec<u64> = (0..period).map(|_| left.remove(draw.below(left.len()))).collect();
    assert!(read_keys <= period, "at most every key is read");
    let (read, held_out) = order.split_at(read_keys);
    let passages: Vec<Vec<usize>> = read.iter().map(|&k| terrain.passage(k, length)).collect();
    let n: usize = passages.iter().map(Vec::len).sum();
    println!(
        "executed transport: helix {PERIODS:?} (D = {}, grain {}), {CLASSES} classes, seed {seed}; read set {read_keys} keys × {length} cells = {n} observations; held-out keys {}",
        helix.period(),
        helix.grain(),
        held_out.len()
    );

    // 1. Locate.
    let locate = Instant::now();
    let location = TransportLocation::locate(helix.clone(), CLASSES, &passages).expect("location");
    let locate_ms = locate.elapsed().as_millis();
    let fibre = location.fibre();
    let members = location.members();
    let peak = location.curve().iter().map(|c| c.survivors).max().unwrap_or(0);
    let nodes: u64 = location.curve().iter().map(|c| c.survivors).sum();
    let mut curve = String::from("observation\tsurvivors\tlifts\tcomplete\n");
    for (k, count) in location.curve().iter().enumerate() {
        curve.push_str(&format!(
            "{}\t{}\t{}\t{}\n",
            k + 1,
            count.survivors,
            count.lifts,
            count.complete
        ));
    }
    #[allow(clippy::disallowed_methods)]
    std::fs::write(format!("{out}.curve"), &curve).expect("write the curve");
    println!(
        "  locate: {} ms; fibre {}; members {}; survivors at the end {}; peak survivors {peak}; nodes explored {nodes}",
        locate_ms,
        outcome(&fibre),
        members.len(),
        location.curve().last().map_or(0, |c| c.survivors),
    );
    println!(
        "  n*_machine {:?}; unicity count n_U {}; first-occurrence order {:?}",
        location.located_from(),
        unicity_count(&helix, CLASSES),
        location.order()
    );
    // The truth, read only now: carried to the rotation gauge and to its representative.
    let truth = LocatedTransport::of_terrain(&terrain);
    let turn = truth.cell_of(passages[0][0]).expect("a labelled cell") as usize;
    let gauged = LocatedTransport::new(
        helix.clone(),
        truth.advances().to_vec(),
        (0..CLASSES).map(|c| truth.labels()[(c + turn) % CLASSES]).collect(),
    )
    .expect("the gauged truth");
    let representative = gauge_representative(&location, &gauged);
    let truth_member = members.contains(&representative);
    println!(
        "  truth: A {:?} (digits {:?}; CRT {:?}); the generator's representative is a member: {truth_member}",
        truth.advances(),
        (0..CLASSES).map(|u| truth.digits(u)).collect::<Vec<_>>(),
        (0..CLASSES).map(|u| truth.residues(u)).collect::<Vec<_>>(),
    );
    for member in members.iter().take(6) {
        let differs: Vec<usize> = (0..CLASSES)
            .filter(|&u| member.advances()[u] != representative.advances()[u])
            .collect();
        println!(
            "    member A {:?} labels {:?}; differs from the generator at classes {differs:?}",
            member.advances(),
            member.labels()
        );
    }
    let regenerates = members
        .iter()
        .all(|member| passages.iter().all(|passage| !member.keys(passage).is_empty()));
    println!("  every member regenerates every passage from some key: {regenerates}");
    if locate_only {
        println!("executed transport (location only): {} ms; resident {}", clock.elapsed().as_millis(), resident());
        return;
    }

    // 2. Relabel.
    let relabel = Instant::now();
    let Some(located) = members.first().cloned() else {
        println!("  no member: the relabelling, founding, code and repair are not read");
        println!("executed transport: {} ms; resident {}", clock.elapsed().as_millis(), resident());
        return;
    };
    let length_bits = located_code(&located, &passages).expect("the code").len();
    let residue_bits = residue_code(&helix, &passages);
    let (mut carried_all, mut n_star_equal, mut code_equal) = (0usize, 0usize, 0usize);
    let mut residue_lengths = std::collections::BTreeMap::<usize, usize>::new();
    // Every fifth permutation in lexicographic order, the identity first (the record's §0
    // amendment: 24 of 120, each a whole location).
    let perms: Vec<Vec<usize>> = permutations(CLASSES).into_iter().step_by(5).collect();
    for pi in &perms {
        let relabelled: Vec<Vec<usize>> = passages
            .iter()
            .map(|p| p.iter().map(|&u| pi[u]).collect())
            .collect();
        let moved = TransportLocation::locate(helix.clone(), CLASSES, &relabelled).expect("location");
        let moved_members = moved.members();
        let carry = |member: &LocatedTransport| {
            let mut advances = vec![0; CLASSES];
            for u in 0..CLASSES {
                advances[pi[u]] = member.advances()[u];
            }
            LocatedTransport::new(
                helix.clone(),
                advances,
                member.labels().iter().map(|label| label.map(|u| pi[u])).collect(),
            )
            .expect("a carried member")
        };
        if moved_members.len() == members.len()
            && members.iter().all(|m| moved_members.contains(&carry(m)))
        {
            carried_all += 1;
        }
        if moved.located_from() == location.located_from() {
            n_star_equal += 1;
        }
        if located_code(&carry(&located), &relabelled).expect("the code").len() == length_bits {
            code_equal += 1;
        }
        *residue_lengths.entry(residue_code(&helix, &relabelled)).or_default() += 1;
    }
    println!(
        "  relabel: {} ms; of {} permutations, fibre carried {carried_all}, n* equal {n_star_equal}, located code length equal {code_equal} ({length_bits} bits); the residue chart's code lengths (bits: permutations) {residue_lengths:?}",
        relabel.elapsed().as_millis(),
        perms.len()
    );

    // 3. Found.
    let found = Instant::now();
    let keys: Vec<u64> = passages
        .iter()
        .map(|passage| located.keys(passage).first().copied().expect("a key"))
        .collect();
    let (chart_n, transports, coupling, openings) = located.chart(&keys).expect("the chart");
    let chart = PassageChart::new(chart_n, transports, Vec::new(), coupling, openings)
        .expect("the passage chart");
    let encoding = Encoding::found(&chart).expect("the founding");
    let squares = encoding.squares(&chart).expect("the squares");
    let generated = located
        .advances()
        .iter()
        .fold(helix.period(), |g, &a| {
            let (mut x, mut y) = (g, a);
            while y != 0 {
                (x, y) = (y, x % y);
            }
            x
        });
    println!(
        "  found: {} ms; chart {chart_n}, reached {}, founded dimension {}; squares held on {} states × {} transports; gcd of the advances with D {generated}",
        found.elapsed().as_millis(),
        encoding.reached(),
        encoding.dimension(),
        squares.states,
        squares.transports
    );

    // 4. Code.
    let code = located_code(&located, &passages).expect("the code");
    let lengths: Vec<usize> = passages.iter().map(Vec::len).collect();
    let reopened = read_located(&helix, CLASSES, &code, &lengths).expect("the code reads back");
    let literal = 3 * n;
    println!(
        "  code: located {} bits (reopens the read set: {}); literal {literal} bits; the residue chart {residue_bits} bits",
        code.len(),
        reopened == passages
    );

    // 5. Repair.
    let repair = Instant::now();
    let erased = damage();
    let repair_keys: Vec<u64> = if held_out.is_empty() {
        read.to_vec()
    } else {
        held_out.to_vec()
    };
    let (mut released, mut correct, mut held, mut residual_bits, mut reopened_all) =
        (0usize, 0usize, 0usize, 0usize, 0usize);
    let mut families: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
    let (mut kept_members, mut refused_members) = (0usize, 0usize);
    let mut sections = String::new();
    for (index, &key) in repair_keys.iter().enumerate() {
        let truth_passage = terrain.passage(key, REPAIR_LENGTH);
        let damaged: Vec<Option<usize>> = truth_passage
            .iter()
            .enumerate()
            .map(|(t, &u)| (!erased.contains(&t)).then_some(u))
            .collect();
        let restriction = restrict_fibre(&members, &damaged).expect("the fibre fits the passage");
        let (kept, refused) = restriction.members();
        kept_members += kept;
        refused_members += refused;
        let releases = restriction.release().expect("the release");
        let mut repaired = Vec::with_capacity(REPAIR_LENGTH);
        for (t, release) in releases.iter().enumerate() {
            match release {
                CellRelease::Released(class) => {
                    released += 1;
                    correct += usize::from(*class == truth_passage[t]);
                    repaired.push(Some(*class));
                }
                CellRelease::Held(family) => {
                    held += 1;
                    *families.entry(family.len()).or_default() += 1;
                    repaired.push(None);
                }
                CellRelease::Intact(class) => repaired.push(Some(*class)),
            }
        }
        let residual = lift_residual(&members, &damaged, &truth_passage).expect("the residual");
        residual_bits += residual.len();
        if lift_reopen(&members, &damaged, &residual).expect("the reopening") == truth_passage {
            reopened_all += 1;
        }
        if index < 4 {
            sections.push_str(&format!(
                "passage {index} (key {key})\n  damaged  {}\n  repaired {}\n  truth    {}\n",
                row(&damaged),
                row(&repaired),
                row(&truth_passage.iter().map(|&u| Some(u)).collect::<Vec<_>>())
            ));
        }
    }
    #[allow(clippy::disallowed_methods)]
    std::fs::write(format!("{out}.sections"), &sections).expect("write the sections");
    let erased_total = erased.len() * repair_keys.len();
    println!(
        "  repair: {} ms; {} passages from {} keys; erased {erased_total}: released {released} (equal to the truth {correct}), held {held} (families by size {families:?}); members kept {kept_members}, refused {refused_members}; residual {residual_bits} bits against the literal {}; reopened {reopened_all} of {}",
        repair.elapsed().as_millis(),
        repair_keys.len(),
        if held_out.is_empty() { "the read" } else { "the held-out" },
        3 * erased_total,
        repair_keys.len()
    );
    println!("executed transport: {} ms; resident {}", clock.elapsed().as_millis(), resident());
}

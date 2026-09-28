//! **The ring-search experiment: the rings as the search for keys, not as predictors** (THE_REBUILD
//! §4, "The ring-search experiment", wave C; #28, #73, #63). A short loop whose claim is fixed
//! before it measures: the learner record's §2 ("The rings as the search") and §14.1 ("The decisive
//! ring experiment"). Its pin and receipt:
//! `research/records/2026-09-28_THE_RINGS_AS_A_SEARCH_FOR_KEYS_PINNED_BEFORE_THE_RUN.md`.
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_ring_search -- bank
//! cargo run --release -p holonics --example hnn_ring_search -- preflight
//! cargo run --release -p holonics --example hnn_ring_search -- run
//! ```
//!
//! `bank` prints the bank's declaration; `preflight` runs every arm on the development seeds and
//! times (2)'s passages; `diagnose <seed>` prints a development seed's matched rings' sheets; `run`
//! is the pinned measurement, run once.
//!
//! [definition; agent-inferred] **The two hypotheses**, measured and reported separately:
//! - **(1) Search.** A bank of coupled rings locks onto a future-equivalent key in less work than
//!   enumerating keys and than menu propagation, all work charged, on the blind moiré, the parity
//!   moiré and the rotor crib.
//! - **(2) Prior.** The fraction of the bank's initial configurations landing on each lock, over a
//!   certified finite partition, tracks the mass law `2^(−ℓ)`, `ℓ` the key's description length.
//!
//! What survives Astra's counterexamples (tongue width, basin measure and a description prior are
//! three quantities; `K^q` tongue scaling is not universal; a raw Stern–Brocot path is not a prefix
//! code without its length) is narrower: a lock proposes a key, exact receiver constraints certify
//! it, and the certification is charged to the arm that proposed.
//!
//! [definition; agent-inferred] **The bank** is the HNN's own ring law: `hnn::ring::PumpedRing` over
//! `ResonatorOperands`, in the word lattice's executed chart `(L_c, D_c, L_w) = (32, 16, 16)`, hop
//! `h = 1`, port admittance `Y = 1`, storage `C = I`, dissipation `D = 0` (the port carries the
//! loss), the pump standing on the real axis.
//! - **Its rings.** On the moiré, one ring per rate `p/q` of the family (`2 ≤ q ≤ 8`, `0 < p < q`,
//!   `gcd(p, q) = 1`: 21 rings). A ring's nodes are its rotor's `q` ports, each a realified complex
//!   node (in-phase `x`, quadrature `y`).
//! - **Its contacts** are the ring's own geometry, the same on both coordinates. Each port is joined
//!   to its two neighbours at `−1` (the cycle incidence, for `q ≥ 4`) and to its half-turn partner
//!   `j + q/2` at `+2`, or, for odd `q`, to its two nearest half-turn partners `j ± (q − 1)/2` at
//!   `+1` each. The ring's first Fourier pair, whose sign pattern is a grating's half-turn sheet, is
//!   then its softest mode. The stiffness is `K = c₀I + A`, with `c₀` the least point of
//!   `2^(−10)ℤ` making `K ⪰ 0` (certified by the inertia owner). Rings of different rates exchange no
//!   power, as the terrain's gratings do not.
//! - **Its drive** is the terrain's phase-carried moment. At tick `t` ring `p/q`'s rotor stands at
//!   port `t·p mod q`, and the cell's encoding enters that node's in-phase storage port: the blind
//!   sheet tuple as `Σ_i (1 − 2s_i)` (the layers superposed; no ring is told which layer is which),
//!   the parity color as `1 − 2·cell`.
//! - **Its pump.** `σ = 0` for `T_A = 2^8` ticks, while the first Fourier pair integrates the
//!   moment, then `σ = 1/4` for `T_B = 2^5` ticks, past the bifurcation of that pair alone (certified:
//!   the pumped in-phase block's negative directions are exactly the pair's).
//! - **Its lock readout** is the sheets of the in-phase coordinates after the last tick. A ring's
//!   proposals are the gratings `(p, q, c)` whose half-turn sheets `[2((c + j) mod q) ≥ q]` lie
//!   nearest its sheets (the least number of ports `j` that differ; every nearest `c` ascending),
//!   each followed by its two adjacent classes `c − 1`, `c + 1`: the lock's reading at the port grain
//!   with its unresolved fibre. A lock whose sheets are exactly a grating's decodes to that grating.
//! - **On the rotor crib** the bank is the Bombe's diagonal board as parametrons: one node per wire
//!   `(menu port a, image i)`, `7·7` wires. Each menu edge `a — b` with stage `W` under the key joins
//!   wire `(a, i)` to `(b, W i)` at `−1`, so `K` is the wire graph's Laplacian. A seed hypothesis
//!   `S(p₀) = s` at the least menu port enters as a kick `−1` at its wire on tick 0; `σ = 0` for 1
//!   tick, then `σ = 1/4` for `2^3` ticks drives each lit component's softest mode (its constant)
//!   past the bifurcation. The lit wires (the half-turn sheet) propose the board when each menu port
//!   holds exactly one and their images are distinct (the Bombe's stop); a port outside the menu takes
//!   the unused images in ascending order. Keys in order `0, …, 6`, seeds `s = 0, …, 6`.
//!
//! [definition; agent-inferred] **The nonlocking control** is the same bank with the pump at zero
//! throughout. The rotors still carry the cells rigidly and the resonators still integrate them, but
//! no bifurcation selects a sheet. Its readout and decoding are the bank's.
//!
//! [definition; agent-inferred] **The work unit** is one exact elementary operation (an integer or
//! rational addition, subtraction, multiplication, division, remainder, comparison, table lookup or
//! carry), common to all arms and counted as integers:
//! - enumeration and certification: a grating's sheet at the next tick 5 (advance, compare,
//!   subtract, double, compare), a channel cell 6, a parity cell 18 (three sheets, two exclusive-ors,
//!   a comparison), a crib cell 6 (board, position sum and remainder, stage, inverse board,
//!   comparison), a candidate's generation 3, a board's successor 3 and its inverse 7;
//! - menu propagation (`hnn::keys::crib_menu`, `Menu::propagate` one key at a time): each menu edge 2,
//!   per key each edge's stage `5·7` and involution check `2·7`, and each edge traversal the owner
//!   counts 3;
//! - the bank: `hnn::ring::{tick_work, read_work}` for a tick and a sheet read (`6n² + 15n` and `2n`
//!   at realified width `n`), `PumpedRing::solve_work` for the solves' preparation, decoding 5 a port
//!   compared, the crib board's `K` 4 a wire contact plus each edge's stage `5·7`, the stop test one a
//!   wire;
//! - the stage table a crib arm reads, `5·7` a stage, charged once per crib to each arm.
//!
//! The executed balance each tick also forms is the law's receipt, not the motion, and is not
//! charged; every passage's balance is checked (`PumpedPassage::closes`) and the count printed. The
//! moiré rings are data-free, so their preparation is charged once per terrain (the bank's
//! declaration), not per seed; the crib board's `K` is the menu's, so its preparation is charged per
//! key. Wall time is printed beside the counts.
//!
//! [definition; agent-inferred] **Certification.** A proposal counts only when the receiver
//! certifies it future-equivalent against the terrain's passage, and that work is charged to the arm:
//! - a moiré key's emission has a period dividing `T_c`, the lcm of its denominators, and the
//!   terrain's has a period `T ≤ T_max`, the family's longest joint period (`8` for one channel,
//!   `280 = 2^3·5·7` for three gratings). Agreement on the passage's first `T_max + T_c − 1` cells makes
//!   the two periodic words equal forever (Fine and Wilf, 1965, the two-word form) [proved-standard];
//! - a crib key `(k, S)` is future-equivalent when it reproduces the passage and the passage
//!   revisits a joint state `(ring 0's phase, ring 1's position, cell)`: under every key the next
//!   cell and the next state are functions of the state (ring 0 moves on the cells alone, ring 1 by
//!   its lock and ring 0's carry), so a key that reproduces a closed cycle repeats it forever. There
//!   are `5·7·7 = 245` joint states, so a passage of `2^9` cells always revisits one
//!   [proved-derived: pigeonhole]; the revisit is printed per crib;
//! - the harness checks each certified key against the truth after the fact, uncharged.
//!
//! [definition; agent-inferred] **The arms**, each stopping at its first certified key:
//! - **enumeration**: the blind moiré channel by channel over the family's gratings in the owner's
//!   order (`MoireFamily::grating`: `q`, then `p`, then `c` ascending); the parity moiré over joint
//!   keys in lexicographic order of the three gratings' indices; the crib over keys `0, …, 6` and
//!   boards in lexicographic order;
//! - **menu propagation** on the crib only: `hnn::keys` reads a stage menu, and the moiré carries no
//!   stage or plugboard, so no menu is declared there. Each survivor of a key is certified in the
//!   owner's order;
//! - **the bank** and **the nonlocking control**: every ring's passage over the same cells, then the
//!   proposals certified in ring order (`q`, then `p`, then each ring's own order), channel by
//!   channel on the blind moiré, as triples of distinct proposals in lexicographic order on the parity
//!   moiré; on the crib key by key, seed by seed.
//!
//! [definition; agent-inferred] **The pins.** Fresh seeds, disjoint from every seed used before (the
//! terrain notebook's `20260927`, the chase's `20261001` to `20261364`, the tests' small seeds):
//! - blind moiré: the sheet tuple, `k = 3` gratings with `q ≤ 8` (`N_8 = 122 = 2·61` gratings,
//!   `122³ = 2^3·61^3` joint keys), `2^10` cells, seeds `20262801 + s`, `s < 8`;
//! - parity moiré: the same family, the parity color, seeds `20262811 + s`, `s < 8`;
//! - rotor crib: campaign 1's field (population `2^16`) with ring 1 (7 ports) locked at every port,
//!   the other rings at configuration 0, a drawn key and plugboard (`7·7! = 35280 = 2^4·3^2·5·7^2`
//!   keys), `2^9` cells, menu offset 1, seeds `20262821 + s`, `s < 8`;
//! - development (the preflight only, never a measurement): `20262701`, `20262711`, `20262721`.
//!
//! [definition; agent-inferred] **(2)'s partition and mass law.** The bank is undriven: a prior
//! precedes the passage it weighs, and a driven basin is a posterior, (1)'s subject. Each ring's
//! initial in-phase displacement is a sign pattern in `{−1, +1}^q` (velocities and quadratures zero);
//! the bank's configurations are the product over its 21 rings, `2^122`, a certified finite
//! partition read exactly. A ring's lock time `τ` is the first tick of `T_B` from which its sheets
//! stay equal to its last read, when that read decodes to a grating (`∞` otherwise). The bank lands
//! on the ring that locks first; a tie is a plural lock, and no lock at all is none. The rings are
//! independent, so ring `r`'s basin is `Σ_t P(τ_r = t) ∏_(s ≠ r) P(τ_s > t)`, exact from each ring's
//! own `2^q` patterns. Undriven, a ring's motion depends on `q` alone, and each ring is read on its
//! patterns' rotation orbits (its forms are circulant; the equivariance is checked on every pattern
//! for `q ≤ 4`). The mass law over the bank's rates is `π(p/q) = 2^(−ℓ)/Z` with
//! `ℓ = n + 2⌊log₂ n⌋ + 1`: `n` the Stern–Brocot path length of `p/q` (the sum of its partial
//! quotients less one) and its Elias gamma length, so the code is self-delimiting.
//!
//! [definition; agent-inferred] **The criteria**, fixed before the run:
//! - **(1)** holds on a terrain when the bank certifies a key on every seed and its work summed over
//!   the seeds, with its declaration, is strictly below each control's (enumeration, the nonlocking
//!   control, and menu propagation on the crib; a control that misses a seed has no finite sum).
//!   (1) holds when it holds on all three terrains.
//! - **(2)** holds when the total variation between the basins (the plural and no-lock masses
//!   included, against zero mass) and `π` is at most `1/4`, and no rate with a strictly shorter
//!   description has a strictly smaller basin.
//! - **The falsifier**: if neither holds, the reading "rings as proposal dynamics" is refuted for the
//!   HNN's ring law, and the record says so plainly.
//! - **Adoption**: if (1) holds, the rings are declared the key search's proposal dynamics beside
//!   menu propagation (`hnn::keys`). Otherwise they are recorded as not a search.
//!
//! [definition] **Projection** (the preflight on the development seeds, one seed a terrain, before
//! the pin, 24 cores). Each moiré seed's bank or control arm ran in under `1` s and its enumeration
//! in under `10` ms; each crib seed's board bank in under `200` ms; three `q = 8` passages of (2) in
//! `140` ms, so (2)'s 89 rotation orbits and the 28 patterns of the equivariance check run in under
//! `10` s; the preflight's peak resident set was `33532` kB. The run is projected under one minute and
//! under `64` MB. It stops at `10` minutes of wall time or `20` GB resident, and a run that passes
//! either is reported as incomplete.
//!
//! [disclosure] Two declarations were fixed on the development seeds, before the pin: the preflight
//! found the full-coverage crib certificate unmet (a crib's cells do not visit every transition), and
//! the blind bank's exact decoding off by one class where two layers share a denominator (each
//! ring of that denominator reads both layers, one of them permuted, and the mixed first Fourier pair
//! lands on a class boundary). The revisit certificate and the lock's unresolved fibre replaced them.
//! No parameter of the bank's dynamics was changed.
//!
//! Printed exactly: integers, ratios reduced (`n/d`) with their quotient and remainder where they
//! compare works, basins as exact ratios with an enclosure on `2^(−10)ℤ`. No decimal is printed.

use std::time::Instant;

use holonics::hnn::WordLattice;
use holonics::hnn::field::{Field, FieldDeclaration};
use holonics::hnn::keys::{candidate_keys, crib_menu, ring_steps};
use holonics::hnn::ring::{PumpDeclaration, PumpStage, PumpStep, PumpedRing, ResonatorMaterial};
use holonics::holarchy::terrain::{Draw, Moire, MoireClass, MoireFamily, RotorCrib, rotor_crib};
use holonics::holon::contact::menu::PortPermutation;
use holonics::holon::parametron::Carrier;
use holonics::navigator::Clock;
use holonics::navigator::address::LockAddress;
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::linear::inertia::{SymmetricForm, inertia};
use holonics::ratio::{Rat, integer, rat};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};
use rayon::prelude::*;

// -------------------------------------------------------------------------------------------
// the pins

/// Seeds a terrain.
const SEEDS: u64 = 8;
const BLIND_SEED: u64 = 20_262_801;
const PARITY_SEED: u64 = 20_262_811;
const CRIB_SEED: u64 = 20_262_821;
/// The preflight's development seeds: blind `+0`, parity `+10`, crib `+20`.
const DEVELOPMENT_SEED: u64 = 20_262_701;

/// The moiré family: `k = 3` gratings, denominators up to `8`, and the passage.
const RINGS: usize = 3;
const DENOMINATOR: u64 = 8;
const MOIRE_CELLS: usize = 1 << 10;

/// The rotor crib: campaign 1's ring 1 locked at every port.
const CRIB_RING: usize = 1;
const CRIB_POPULATION: u64 = 1 << 16;
const CRIB_CELLS: usize = 1 << 9;
const CRIB_OFFSET: usize = 1;

/// The bank's schedule: `T_A` unpumped, `T_B` pumped; the crib board's.
const INTEGRATION: usize = 1 << 8;
const LOCKING: usize = 1 << 5;
const CRIB_INTEGRATION: usize = 1;
const CRIB_LOCKING: usize = 1 << 3;

/// The contacts: the neighbours' weight and the half-turn partner's.
const NEIGHBOUR: i64 = 1;
const HALF_TURN: i64 = 2;
/// `c₀` lies on `2^(−OFFSET_GRAIN)ℤ`.
const OFFSET_GRAIN: u32 = 10;

/// The pump past the bifurcation.
fn pump() -> Rat {
    rat(1, 4)
}

/// The word lattice's executed chart `(L_c, D_c, L_w)`.
fn word_lattice() -> WordLattice {
    WordLattice::new(32, 16, 16)
}

/// (2)'s tolerance on the total variation.
fn tolerance() -> Rat {
    rat(1, 4)
}

/// The enclosure grain for printed basins, `2^(−10)`.
const PRINT_GRAIN: u32 = 10;

// -------------------------------------------------------------------------------------------
// the work unit

const SHEET: u64 = 5;
const CHANNEL_CELL: u64 = SHEET + 1;
const JOINT_CELL: u64 = 3 * SHEET + 3;
const CRIB_CELL: u64 = 6;
const GENERATE: u64 = 3;
const BOARD: u64 = 3;
const STAGE: u64 = 5;
const INVOLUTION: u64 = 2;
const TRAVERSAL: u64 = 3;
const EDGE: u64 = 2;
const WIRE: u64 = 4;
const DECODE: u64 = 5;

// -------------------------------------------------------------------------------------------
// exact presentation

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

fn lcm(a: u64, b: u64) -> u64 {
    a / gcd(a, b) * b
}

/// An integer with its prime factorization.
fn factored(value: u64) -> String {
    if value < 2 {
        return value.to_string();
    }
    let (mut rest, mut factors, mut d) = (value, Vec::new(), 2u64);
    while d * d <= rest {
        let mut e = 0;
        while rest.is_multiple_of(d) {
            rest /= d;
            e += 1;
        }
        if e == 1 {
            factors.push(d.to_string());
        } else if e > 1 {
            factors.push(format!("{d}^{e}"));
        }
        d += 1;
    }
    if rest > 1 {
        factors.push(rest.to_string());
    }
    format!("{value} = {}", factors.join("·"))
}

/// `a/b` as its quotient and remainder.
fn quotient(a: u64, b: u64) -> String {
    format!("{} rem {} over {b}", a / b, a % b)
}

/// A ratio reduced, `n/d`.
fn ratio(value: &Rat) -> String {
    if value.denom().is_one() {
        value.numer().to_string()
    } else {
        format!("{}/{}", value.numer(), value.denom())
    }
}

/// The enclosure `[a/2^g, (a + 1)/2^g)` of a nonnegative ratio.
fn enclosure(value: &Rat) -> String {
    let scale = BigInt::one() << PRINT_GRAIN as usize;
    let floor = (value.numer() * &scale) / value.denom();
    format!("[{floor}/2^{PRINT_GRAIN}, {}/2^{PRINT_GRAIN})", &floor + 1)
}

/// A work sum, or none when an arm missed a seed.
fn sum_text(work: Option<u64>) -> String {
    work.map_or_else(|| "none (a seed missed)".to_string(), |w| w.to_string())
}

/// The peak resident set, from the kernel's status, in kB (the exterior boundary).
#[allow(clippy::disallowed_methods)]
fn peak_kb() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    status
        .lines()
        .find(|line| line.starts_with("VmHWM:"))?
        .split_whitespace()
        .nth(1)?
        .parse()
        .ok()
}

// -------------------------------------------------------------------------------------------
// the moiré family and its emission

fn family() -> MoireFamily {
    MoireFamily {
        rings: RINGS,
        denominator: DENOMINATOR,
    }
}

/// A grating `(p, q, c)`.
type Key = (u64, u64, u64);

/// The family's gratings in the owner's order.
fn gratings() -> Vec<Key> {
    let family = family();
    (0..family.gratings())
        .map(|index| {
            let g = family.grating(index).expect("an index of the family");
            (g.numerator(), g.denominator(), g.phase())
        })
        .collect()
}

/// The family's rates `(p, q)` in the bank's order: `q`, then `p`, ascending.
fn rates() -> Vec<(u64, u64)> {
    (2..=DENOMINATOR)
        .flat_map(|q| (1..q).filter(move |p| gcd(*p, q) == 1).map(move |p| (p, q)))
        .collect()
}

/// A grating's sheet stepped tick by tick: its port advances `p` a tick.
struct Sheet {
    p: u64,
    q: u64,
    port: u64,
}

impl Sheet {
    fn of((p, q, c): Key) -> Self {
        Self { p, q, port: c }
    }

    fn read(&self) -> bool {
        2 * self.port >= self.q
    }

    fn advance(&mut self) {
        self.port += self.p;
        if self.port >= self.q {
            self.port -= self.q;
        }
    }
}

/// The half-turn sheet of grating `(·, q, c)` at the ring's port `j`: `[2((c + j) mod q) ≥ q]`.
fn port_sheet(q: u64, c: u64, j: u64) -> bool {
    2 * ((c + j) % q) >= q
}

/// The longest joint period of `k` gratings of the family.
fn longest_period(k: usize) -> u64 {
    let denominators: Vec<u64> = (2..=DENOMINATOR).collect();
    let mut best = 1;
    let mut stack = vec![(0usize, 1u64)];
    while let Some((depth, period)) = stack.pop() {
        if depth == k {
            best = best.max(period);
            continue;
        }
        for &q in &denominators {
            stack.push((depth + 1, lcm(period, q)));
        }
    }
    best
}

/// **Certify one channel's grating**: agreement on the first `T_max + q − 1` cells.
fn channel_agrees(key: Key, bits: &[bool], ops: &mut u64) -> bool {
    let window = (DENOMINATOR + key.1 - 1) as usize;
    let mut sheet = Sheet::of(key);
    for bit in bits.iter().take(window) {
        *ops += CHANNEL_CELL;
        if sheet.read() != *bit {
            return false;
        }
        sheet.advance();
    }
    true
}

/// **Certify a joint parity key**: agreement on the first `T_max + T_c − 1` cells.
fn joint_agrees(keys: [Key; 3], cells: &[usize], longest: u64, ops: &mut u64) -> bool {
    let period = keys.iter().fold(1, |t, key| lcm(t, key.1));
    let window = (longest + period - 1) as usize;
    let mut sheets = keys.map(Sheet::of);
    for cell in cells.iter().take(window) {
        *ops += JOINT_CELL;
        let parity = sheets.iter().fold(false, |x, s| x ^ s.read());
        if usize::from(parity) != *cell {
            return false;
        }
        for sheet in &mut sheets {
            sheet.advance();
        }
    }
    true
}

/// The truth's check after the fact (uncharged): a key's emission equals the truth's over the lcm
/// of both periods.
fn equals_forever(a: &[Key], b: &[Key]) -> bool {
    let period = a.iter().chain(b).fold(1, |t, key| lcm(t, key.1));
    let (mut left, mut right): (Vec<Sheet>, Vec<Sheet>) = (
        a.iter().copied().map(Sheet::of).collect(),
        b.iter().copied().map(Sheet::of).collect(),
    );
    for _ in 0..period {
        let read = |s: &[Sheet]| s.iter().fold(false, |x, s| x ^ s.read());
        if read(&left) != read(&right) {
            return false;
        }
        left.iter_mut().for_each(Sheet::advance);
        right.iter_mut().for_each(Sheet::advance);
    }
    true
}

// -------------------------------------------------------------------------------------------
// the bank's declaration

/// The ring's contacts on its in-phase block (module header), without `c₀`.
fn contacts(q: u64) -> Vec<Vec<Rat>> {
    let n = q as usize;
    let mut a = vec![vec![Rat::zero(); n]; n];
    for j in 0..n {
        if q.is_multiple_of(2) {
            a[j][(j + n / 2) % n] += integer(HALF_TURN);
        } else {
            let half = (n - 1) / 2;
            a[j][(j + half) % n] += integer(HALF_TURN / 2);
            a[j][(j + n - half) % n] += integer(HALF_TURN / 2);
        }
        if q >= 4 {
            a[j][(j + 1) % n] -= integer(NEIGHBOUR);
            a[j][(j + n - 1) % n] -= integer(NEIGHBOUR);
        }
    }
    a
}

/// `c₀I + A` on the in-phase block.
fn offset_block(a: &[Vec<Rat>], offset: &Rat) -> Vec<Vec<Rat>> {
    a.iter()
        .enumerate()
        .map(|(i, row)| {
            row.iter()
                .enumerate()
                .map(|(j, x)| if i == j { x + offset } else { x.clone() })
                .collect()
        })
        .collect()
}

/// The inertia `(+, 0, −)` of a symmetric block.
fn signs(block: &[Vec<Rat>]) -> (usize, usize, usize) {
    let found = inertia(&SymmetricForm::from_rows(block.to_vec()).expect("a symmetric block"));
    (found.positive, found.zero, found.negative)
}

/// **The ring's offset**: the least `c₀ ∈ 2^(−10)ℤ` making `c₀I + A ⪰ 0`, by bisection on the
/// inertia.
fn least_offset(a: &[Vec<Rat>]) -> Rat {
    let unit = Rat::new(BigInt::one(), BigInt::one() << OFFSET_GRAIN as usize);
    let settles = |steps: i64| signs(&offset_block(a, &(&unit * integer(steps)))).2 == 0;
    let (mut low, mut high) = (-1i64, 1i64);
    while !settles(high) {
        high *= 2;
    }
    while high - low > 1 {
        let middle = (low + high) / 2;
        if settles(middle) {
            high = middle;
        } else {
            low = middle;
        }
    }
    unit * integer(high)
}

/// The realified form of an in-phase block: the same block on both coordinates of every node.
fn realify(block: &[Vec<Rat>]) -> ExactRatMatrix {
    let n = block.len();
    ExactRatMatrix::shaped(
        2 * n,
        2 * n,
        (0..2 * n)
            .map(|i| {
                (0..2 * n)
                    .map(|j| {
                        if i % 2 == j % 2 {
                            block[i / 2][j / 2].clone()
                        } else {
                            Rat::zero()
                        }
                    })
                    .collect()
            })
            .collect(),
    )
    .expect("a square realified form")
}

/// The ring's material at pump strength `strength`: `C = I`, `K`, `D = 0`, the pump standing on the
/// real axis.
fn material(stiffness: &ExactRatMatrix, strength: Rat) -> ResonatorMaterial {
    let n = stiffness.rows();
    ResonatorMaterial::new(
        ExactRatMatrix::identity(n).expect("identity"),
        stiffness.clone(),
        ExactRatMatrix::zero(n, n).expect("zero"),
        Some(
            PumpDeclaration::new(strength, Carrier::sheet(false), PumpStep::Stand)
                .expect("a nonnegative pump"),
        ),
    )
    .expect("a declared resonator")
}

/// A prepared ring: the two stages at the pump's strength (the bank) or at zero (the control).
fn prepared(
    ring: usize,
    stiffness: &ExactRatMatrix,
    schedule: (usize, usize),
    pumped: bool,
) -> PumpedRing {
    let strength = if pumped { pump() } else { Rat::zero() };
    PumpedRing::new(
        ring,
        &Rat::one(),
        &Rat::one(),
        Some(&word_lattice()),
        &[
            PumpStage {
                material: material(stiffness, Rat::zero()),
                ticks: schedule.0,
            },
            PumpStage {
                material: material(stiffness, strength),
                ticks: schedule.1,
            },
        ],
    )
    .expect("a certified pumped ring")
}

/// A ring's spectral declaration, per `q`.
struct Spectrum {
    q: u64,
    offset: Rat,
    unpumped: (usize, usize, usize),
    pumped: (usize, usize, usize),
    stiffness: ExactRatMatrix,
}

fn spectrum(q: u64) -> Spectrum {
    let a = contacts(q);
    let offset = least_offset(&a);
    let block = offset_block(&a, &offset);
    let lowered = offset_block(&block, &(integer(-2) * pump()));
    Spectrum {
        q,
        unpumped: signs(&block),
        pumped: signs(&lowered),
        stiffness: realify(&block),
        offset,
    }
}

/// The bank's moiré rings, pumped or the control.
struct Bank {
    rings: Vec<((u64, u64), PumpedRing)>,
    declaration: u64,
}

fn bank(spectra: &[Spectrum], pumped: bool) -> Bank {
    let rings: Vec<((u64, u64), PumpedRing)> = rates()
        .into_par_iter()
        .enumerate()
        .map(|(index, (p, q))| {
            let s = &spectra[(q - 2) as usize];
            (
                (p, q),
                prepared(index, &s.stiffness, (INTEGRATION, LOCKING), pumped),
            )
        })
        .collect();
    let declaration = rings.iter().map(|(_, ring)| ring.solve_work()).sum();
    Bank { rings, declaration }
}

/// **A ring's proposals** (module header): the phase classes whose half-turn sheets lie nearest its
/// sheets (least Hamming distance, ascending), each followed by its two adjacent classes, the lock's
/// unresolved fibre at the port grain; charged per port compared.
fn proposals_of(p: u64, q: u64, sheets: &[bool], ops: &mut u64) -> Vec<Key> {
    let distances: Vec<usize> = (0..q)
        .map(|c| {
            sheets
                .iter()
                .enumerate()
                .filter(|(j, sheet)| {
                    *ops += DECODE;
                    port_sheet(q, c, *j as u64) != **sheet
                })
                .count()
        })
        .collect();
    let least = *distances.iter().min().expect("a class");
    let mut classes: Vec<u64> = Vec::new();
    for c in (0..q).filter(|c| distances[*c as usize] == least) {
        for class in [c, (c + q - 1) % q, (c + 1) % q] {
            if !classes.contains(&class) {
                classes.push(class);
            }
        }
    }
    classes.into_iter().map(|c| (p, q, c)).collect()
}

/// **A lock's grating**: the grating whose half-turn sheets its sheets are exactly, charged per port
/// compared.
fn decode(p: u64, q: u64, sheets: &[bool], ops: &mut u64) -> Option<Key> {
    (0..q).find_map(|c| {
        for (j, sheet) in sheets.iter().enumerate() {
            *ops += DECODE;
            if port_sheet(q, c, j as u64) != *sheet {
                return None;
            }
        }
        Some((p, q, c))
    })
}

// -------------------------------------------------------------------------------------------
// an arm's outcome

/// One arm on one seed: the work to its first certified key (none when it certified none), the work
/// it spent in all, the milliseconds, whether the certified key is future-equivalent to the truth
/// (uncharged), and the passages whose balance closed out of those run.
#[derive(Clone, Debug, Default)]
struct Outcome {
    certified: Option<u64>,
    spent: u64,
    ms: u128,
    sound: bool,
    closed: usize,
    passages: usize,
    proposals: usize,
}

// -------------------------------------------------------------------------------------------
// the moiré arms

enum Kind {
    Blind,
    Parity,
}

fn moire(kind: &Kind, seed: u64) -> Moire {
    let class = match kind {
        Kind::Blind => MoireClass::Sheets,
        Kind::Parity => MoireClass::Parity,
    };
    Moire::draw(&family(), class, &mut Draw::new(seed)).expect("a drawn moiré")
}

fn truth_keys(terrain: &Moire) -> Vec<Key> {
    terrain
        .gratings()
        .iter()
        .map(|g| (g.numerator(), g.denominator(), g.phase()))
        .collect()
}

/// **Enumeration on the blind moiré**: channel by channel over the family's gratings.
fn enumerate_blind(terrain: &Moire, cells: &[usize]) -> Outcome {
    let started = Instant::now();
    let (all, truth) = (gratings(), truth_keys(terrain));
    let mut ops = 0u64;
    let mut sound = true;
    let mut found = 0;
    for channel in 0..RINGS {
        let bits: Vec<bool> = cells.iter().map(|c| (c >> channel) & 1 == 1).collect();
        if let Some(key) = all.iter().copied().find(|key| {
            ops += GENERATE;
            channel_agrees(*key, &bits, &mut ops)
        }) {
            found += 1;
            sound &= equals_forever(&[key], &[truth[channel]]);
        }
    }
    Outcome {
        certified: (found == RINGS).then_some(ops),
        spent: ops,
        ms: started.elapsed().as_millis(),
        sound,
        ..Outcome::default()
    }
}

/// **Enumeration on the parity moiré**: joint keys in lexicographic order of their indices.
fn enumerate_parity(terrain: &Moire, cells: &[usize], longest: u64) -> Outcome {
    let started = Instant::now();
    let (all, truth) = (gratings(), truth_keys(terrain));
    let mut ops = 0u64;
    let mut certified = None;
    let mut sound = false;
    'search: for a in &all {
        for b in &all {
            for c in &all {
                ops += GENERATE;
                if joint_agrees([*a, *b, *c], cells, longest, &mut ops) {
                    certified = Some(ops);
                    sound = equals_forever(&[*a, *b, *c], &truth);
                    break 'search;
                }
            }
        }
    }
    Outcome {
        certified,
        spent: ops,
        ms: started.elapsed().as_millis(),
        sound,
        ..Outcome::default()
    }
}

/// **The bank's passages over a moiré**: every ring over the same cells, its proposal decoded.
fn bank_proposals(bank: &Bank, kind: &Kind, cells: &[usize], outcome: &mut Outcome) -> Vec<Key> {
    let drive: Vec<Rat> = cells
        .iter()
        .map(|&cell| match kind {
            Kind::Blind => integer(RINGS as i64 - 2 * i64::from(cell.count_ones())),
            Kind::Parity => integer(1 - 2 * cell as i64),
        })
        .collect();
    let mut proposals = Vec::new();
    for ((p, q), ring) in &bank.rings {
        let n = ring.width();
        let last = ring.ticks() - 1;
        let passage = ring
            .pass([vec![Rat::zero(); n], vec![Rat::zero(); n]], last, |t| {
                let mut beta = vec![Rat::zero(); n];
                let port = (t as u64 * p % q) as usize;
                beta[2 * port] = drive[t].clone();
                beta
            })
            .expect("a pumped passage");
        outcome.spent += passage.work.total();
        outcome.passages += 1;
        outcome.closed += usize::from(passage.closes());
        let sheets = passage.sheets.last().expect("the last read");
        proposals.extend(proposals_of(*p, *q, sheets, &mut outcome.spent));
    }
    outcome.proposals = proposals.len();
    proposals
}

/// **The bank (or the control) on the blind moiré**: proposals certified channel by channel.
fn bank_blind(bank: &Bank, terrain: &Moire, cells: &[usize]) -> Outcome {
    let started = Instant::now();
    let mut outcome = Outcome::default();
    let proposals = bank_proposals(bank, &Kind::Blind, cells, &mut outcome);
    let truth = truth_keys(terrain);
    let (mut found, mut sound) = (0, true);
    for channel in 0..RINGS {
        let bits: Vec<bool> = cells.iter().map(|c| (c >> channel) & 1 == 1).collect();
        if let Some(key) = proposals
            .iter()
            .copied()
            .find(|key| channel_agrees(*key, &bits, &mut outcome.spent))
        {
            found += 1;
            sound &= equals_forever(&[key], &[truth[channel]]);
        }
    }
    outcome.certified = (found == RINGS).then_some(outcome.spent);
    outcome.sound = sound;
    outcome.ms = started.elapsed().as_millis();
    outcome
}

/// **The bank (or the control) on the parity moiré**: triples of distinct rings' proposals.
fn bank_parity(bank: &Bank, terrain: &Moire, cells: &[usize], longest: u64) -> Outcome {
    let started = Instant::now();
    let mut outcome = Outcome::default();
    let proposals = bank_proposals(bank, &Kind::Parity, cells, &mut outcome);
    let truth = truth_keys(terrain);
    'search: for i in 0..proposals.len() {
        for j in i + 1..proposals.len() {
            for l in j + 1..proposals.len() {
                let keys = [proposals[i], proposals[j], proposals[l]];
                outcome.spent += GENERATE;
                if joint_agrees(keys, cells, longest, &mut outcome.spent) {
                    outcome.certified = Some(outcome.spent);
                    outcome.sound = equals_forever(&keys, &truth);
                    break 'search;
                }
            }
        }
    }
    outcome.ms = started.elapsed().as_millis();
    outcome
}

// -------------------------------------------------------------------------------------------
// the rotor crib

fn crib_field() -> Field {
    let mut declared = FieldDeclaration::campaign_one(CRIB_POPULATION);
    declared.rings[CRIB_RING].lock = (0..7).collect();
    Field::declare(declared).expect("the crib's field")
}

/// One crib and what every arm reads of it: the cells, the ring's steps, the stage table, and the
/// first revisit of the joint state `(ring 0's phase, ring 1's position, cell)` (module header): the
/// transition from a state is a function of the state under every key, so a key that reproduces the
/// passage through a revisit repeats its cycle forever, and is future-equivalent.
struct Crib {
    crib: RotorCrib,
    steps: Vec<u64>,
    stages: Vec<Vec<usize>>,
    revisit: Option<(usize, usize)>,
    period: usize,
}

fn crib(field: &Field, seed: u64) -> Crib {
    let configurations = [0u64; 4];
    let crib = RotorCrib::draw(
        field,
        CRIB_RING,
        &configurations,
        CRIB_CELLS,
        &mut Draw::new(seed),
    )
    .expect("a drawn crib");
    let steps = ring_steps(field, CRIB_RING, &crib.cells, &configurations).expect("the steps");
    let period = field.ring(CRIB_RING).period() as usize;
    let machine = field.ring(CRIB_RING).machine().expect("the ring's machine");
    let stages = (0..period)
        .map(|m| {
            machine
                .stage(&BigUint::from(m))
                .expect("a stage")
                .images()
                .to_vec()
        })
        .collect();
    // Ring 0 (period 5, first in carry order) moves on the cells alone; ring 1 by its lock and ring
    // 0's carry. The joint state at cell j.
    let first = ring_steps(field, 0, &crib.cells, &configurations).expect("ring 0's steps");
    let first_period = field.ring(0).period();
    let state = |j: usize| {
        (
            first[j] % first_period,
            steps[j] % period as u64,
            crib.cells[j],
        )
    };
    let mut met = std::collections::HashMap::new();
    let revisit =
        (0..crib.cells.len()).find_map(|j| met.insert(state(j), j).map(|earlier| (earlier, j)));
    Crib {
        revisit,
        crib,
        steps,
        stages,
        period,
    }
}

impl Crib {
    /// The stage table's charge.
    fn table(&self) -> u64 {
        (self.period * self.period) as u64 * STAGE
    }

    /// **Certify `(k, S)`**: it reproduces the passage, which revisits a joint state (module header).
    fn reproduces(&self, key: usize, board: &[usize], ops: &mut u64) -> bool {
        let d = self.period;
        *ops += d as u64;
        let mut inverse = vec![0; d];
        for (x, y) in board.iter().enumerate() {
            inverse[*y] = x;
        }
        let cells = &self.crib.cells;
        for j in 0..cells.len() - 1 {
            *ops += CRIB_CELL;
            let position = (key + self.steps[j] as usize) % d;
            if inverse[self.stages[position][board[cells[j]]]] != cells[j + 1] {
                return false;
            }
        }
        self.revisit.is_some()
    }

    /// The truth's check after the fact (uncharged): the key's crib from the passage's start equals
    /// the truth's over four passages.
    fn equivalent(&self, field: &Field, key: usize, board: &[usize]) -> bool {
        let truth = &self.crib.truth;
        let length = 4 * self.crib.cells.len();
        let produce = |key: u64, board: &PortPermutation| {
            rotor_crib(
                field,
                CRIB_RING,
                key,
                board,
                &truth.configurations,
                length,
                truth.start,
            )
            .expect("a produced crib")
        };
        let board = PortPermutation::new(board.to_vec()).expect("a board");
        produce(key as u64, &board) == produce(truth.key, &truth.board)
    }
}

/// The next permutation in lexicographic order, in place; false at the last.
fn next_permutation(values: &mut [usize]) -> bool {
    let n = values.len();
    let Some(i) = (0..n.saturating_sub(1))
        .rev()
        .find(|&i| values[i] < values[i + 1])
    else {
        return false;
    };
    let j = (i + 1..n)
        .rev()
        .find(|&j| values[j] > values[i])
        .expect("a larger value");
    values.swap(i, j);
    values[i + 1..].reverse();
    true
}

/// **Enumeration on the crib**: keys `0, …, 6`, boards in lexicographic order.
fn enumerate_crib(field: &Field, c: &Crib) -> Outcome {
    let started = Instant::now();
    let mut ops = c.table();
    let mut outcome = Outcome::default();
    'search: for key in 0..c.period {
        let mut board: Vec<usize> = (0..c.period).collect();
        loop {
            ops += BOARD;
            if c.reproduces(key, &board, &mut ops) {
                outcome.certified = Some(ops);
                outcome.sound = c.equivalent(field, key, &board);
                break 'search;
            }
            if !next_permutation(&mut board) {
                break;
            }
        }
    }
    outcome.spent = ops;
    outcome.ms = started.elapsed().as_millis();
    outcome
}

/// A candidate's images on the menu ports, completed with the unused images ascending.
fn complete(images: &[Option<usize>], d: usize) -> Option<Vec<usize>> {
    let mut used = vec![false; d];
    for image in images.iter().flatten() {
        if used[*image] {
            return None;
        }
        used[*image] = true;
    }
    let mut free = (0..d).filter(|i| !used[*i]);
    images
        .iter()
        .map(|image| image.or_else(|| free.next()))
        .collect()
}

/// **Menu propagation on the crib** (`hnn::keys`): one key at a time, its survivors certified.
fn menu_crib(field: &Field, c: &Crib) -> Outcome {
    let started = Instant::now();
    let d = c.period;
    let mut ops = c.table();
    let mut outcome = Outcome::default();
    let menu = crib_menu(field, CRIB_RING, &c.crib.cells, CRIB_OFFSET, &[0; 4]).expect("the menu");
    let edges = menu.edges().len() as u64;
    ops += edges * EDGE;
    let keys = candidate_keys(field, CRIB_RING).expect("the keys");
    'search: for key in 0..d {
        let propagation = menu.propagate(&keys[key..=key]).expect("propagation");
        ops += edges * (STAGE + INVOLUTION) * d as u64 + propagation.work * TRAVERSAL;
        outcome.proposals += propagation.candidates.len();
        for candidate in &propagation.candidates {
            let images: Vec<Option<usize>> = (0..d).map(|p| candidate.images.image(p)).collect();
            if let Some(board) = complete(&images, d)
                && c.reproduces(key, &board, &mut ops)
            {
                outcome.certified = Some(ops);
                outcome.sound = c.equivalent(field, key, &board);
                break 'search;
            }
        }
    }
    outcome.spent = ops;
    outcome.ms = started.elapsed().as_millis();
    outcome
}

/// **The board bank (or its control) on the crib**: the wire graph per key, a seed per passage.
fn bank_crib(field: &Field, c: &Crib, pumped: bool) -> Outcome {
    let started = Instant::now();
    let d = c.period;
    let mut ops = c.table();
    let mut outcome = Outcome::default();
    let menu = crib_menu(field, CRIB_RING, &c.crib.cells, CRIB_OFFSET, &[0; 4]).expect("the menu");
    let edges = menu.edges().len() as u64;
    ops += edges * EDGE;
    let keys: Vec<Clock> = candidate_keys(field, CRIB_RING).expect("the keys");
    let ports = menu.menu_ports();
    let wires = ports.len() * d;
    let index = |port: usize| ports.binary_search(&port).expect("a menu port");
    'search: for key in 0..d {
        let mut laplacian = vec![vec![0i64; wires]; wires];
        for edge in menu.edges() {
            let stage = edge.stage(&keys[key]).expect("a stage");
            ops += STAGE * d as u64;
            let (a, b) = (index(edge.from()), index(edge.to()));
            for i in 0..d {
                ops += WIRE;
                let (u, v) = (a * d + i, b * d + stage.apply(i).expect("an image"));
                laplacian[u][u] += 1;
                laplacian[v][v] += 1;
                laplacian[u][v] -= 1;
                laplacian[v][u] -= 1;
            }
        }
        let block: Vec<Vec<Rat>> = laplacian
            .iter()
            .map(|row| row.iter().map(|x| integer(*x)).collect())
            .collect();
        let ring = prepared(
            key,
            &realify(&block),
            (CRIB_INTEGRATION, CRIB_LOCKING),
            pumped,
        );
        ops += ring.solve_work();
        let n = ring.width();
        for seed in 0..d {
            let kick = 2 * seed;
            let passage = ring
                .pass(
                    [vec![Rat::zero(); n], vec![Rat::zero(); n]],
                    ring.ticks() - 1,
                    |t| {
                        let mut beta = vec![Rat::zero(); n];
                        if t == 0 {
                            beta[kick] = integer(-1);
                        }
                        beta
                    },
                )
                .expect("a pumped passage");
            ops += passage.work.total() + wires as u64;
            outcome.passages += 1;
            outcome.closed += usize::from(passage.closes());
            let lit = passage.sheets.last().expect("the last read");
            // The Bombe's stop: one lit wire a menu port, their images distinct.
            let mut images: Vec<Option<usize>> = vec![None; d];
            let mut stop = true;
            for (a, port) in ports.iter().enumerate() {
                let on: Vec<usize> = (0..d).filter(|i| lit[a * d + i]).collect();
                if on.len() == 1 {
                    images[*port] = Some(on[0]);
                } else {
                    stop = false;
                }
            }
            if !stop {
                continue;
            }
            let Some(board) = complete(&images, d) else {
                continue;
            };
            outcome.proposals += 1;
            if c.reproduces(key, &board, &mut ops) {
                outcome.certified = Some(ops);
                outcome.sound = c.equivalent(field, key, &board);
                break 'search;
            }
        }
    }
    outcome.spent = ops;
    outcome.ms = started.elapsed().as_millis();
    outcome
}

// -------------------------------------------------------------------------------------------
// (2): the prior

/// The Stern–Brocot path length `n` of `p/q` and the self-delimiting description `ℓ = n + |γ(n)|`.
fn description((p, q): (u64, u64)) -> (u64, u64) {
    let address = LockAddress::from_ratio(&BigInt::from(p), &BigInt::from(q)).expect("an address");
    let n: u64 = address
        .partial_quotients()
        .iter()
        .map(|a| a.to_u64().expect("a small quotient"))
        .sum::<u64>()
        - 1;
    let gamma = 2 * u64::from(u64::BITS - 1 - n.leading_zeros()) + 1;
    (n, n + gamma)
}

/// The rotation orbits of `{−1, +1}^q`: each least rotation with its orbit's size.
fn orbits(q: u64) -> Vec<(u64, u64)> {
    let mask = (1u64 << q) - 1;
    let rotate = |x: u64, r: u64| ((x << r) | (x >> (q - r))) & mask;
    (0..=mask)
        .filter_map(|x| {
            let turns: Vec<u64> = (0..q).map(|r| rotate(x, r)).collect();
            (turns.iter().min() == Some(&x)).then(|| {
                let mut distinct = turns.clone();
                distinct.sort_unstable();
                distinct.dedup();
                (x, distinct.len() as u64)
            })
        })
        .collect()
}

/// **A ring's lock time** from its initial pattern, undriven: the first read of `T_B` from which the
/// sheets equal the last read, when it decodes; none otherwise.
fn lock_time(ring: &PumpedRing, q: u64, pattern: u64) -> (Option<usize>, bool) {
    let n = ring.width();
    let mut u = vec![Rat::zero(); n];
    for j in 0..q as usize {
        u[2 * j] = if (pattern >> j) & 1 == 1 {
            integer(-1)
        } else {
            integer(1)
        };
    }
    let passage = ring
        .pass([u, vec![Rat::zero(); n]], INTEGRATION, |_| {
            vec![Rat::zero(); n]
        })
        .expect("a pumped passage");
    let last = passage.sheets.last().expect("the last read");
    let mut ops = 0;
    if decode(1, q, last, &mut ops).is_none() {
        return (None, passage.closes());
    }
    let from = passage
        .sheets
        .iter()
        .rposition(|read| read != last)
        .map_or(0, |t| t + 1);
    (Some(from), passage.closes())
}

/// Each `q`'s lock-time distribution over its `2^q` patterns: counts by read, then none.
struct Locks {
    q: u64,
    counts: Vec<u64>,
    none: u64,
    closed: usize,
    runs: usize,
    equivariant: Option<bool>,
}

fn locks(bank: &Bank) -> Vec<Locks> {
    (2..=DENOMINATOR)
        .into_par_iter()
        .map(|q| {
            let ring = &bank
                .rings
                .iter()
                .find(|((_, rq), _)| *rq == q)
                .expect("a ring of every denominator")
                .1;
            let mut counts = vec![0u64; LOCKING];
            let (mut none, mut closed, mut runs) = (0u64, 0usize, 0usize);
            for (pattern, size) in orbits(q) {
                let (tau, closes) = lock_time(ring, q, pattern);
                runs += 1;
                closed += usize::from(closes);
                match tau {
                    Some(t) => counts[t] += size,
                    None => none += size,
                }
            }
            // The orbit reading is checked on every pattern where it is cheap.
            let equivariant = (q <= 4).then(|| {
                let mask = (1u64 << q) - 1;
                (0..=mask).all(|x| {
                    let least = (0..q)
                        .map(|r| ((x << r) | (x >> (q - r))) & mask)
                        .min()
                        .expect("a rotation");
                    lock_time(ring, q, x).0 == lock_time(ring, q, least).0
                })
            });
            Locks {
                q,
                counts,
                none,
                closed,
                runs,
                equivariant,
            }
        })
        .collect()
}

/// **(2)**: the basins, the mass law, their total variation and the ordering.
fn prior(bank: &Bank) {
    let started = Instant::now();
    let tables = locks(bank);
    println!(
        "(2) the prior: the bank undriven, each ring's initial in-phase signs over {{−1, +1}}^q"
    );
    for t in &tables {
        let total = 1u64 << t.q;
        println!(
            "  q = {}: {} rotation orbits run, {} closed; locked at read 0: {}, at later reads: {}, none: {} of {total}{}",
            t.q,
            t.runs,
            t.closed,
            t.counts[0],
            t.counts[1..].iter().sum::<u64>(),
            t.none,
            t.equivariant.map_or(String::new(), |e| format!(
                "; rotation equivariance on every pattern: {e}"
            ))
        );
    }
    let distribution = |q: u64| -> (Vec<Rat>, Rat) {
        let t = &tables[(q - 2) as usize];
        let total = Rat::from_integer(BigInt::from(1u64 << q));
        (
            t.counts
                .iter()
                .map(|c| Rat::from_integer(BigInt::from(*c)) / &total)
                .collect(),
            Rat::from_integer(BigInt::from(t.none)) / &total,
        )
    };
    let rings = rates();
    let laws: Vec<(Vec<Rat>, Rat)> = rings.iter().map(|(_, q)| distribution(*q)).collect();
    // P(τ ≥ t) and P(τ > t), t < T_B (τ = none counts as beyond every read).
    let at_least =
        |r: usize, t: usize| -> Rat { laws[r].0[t..].iter().cloned().sum::<Rat>() + &laws[r].1 };
    let beyond = |r: usize, t: usize| -> Rat {
        laws[r].0[t + 1..].iter().cloned().sum::<Rat>() + &laws[r].1
    };
    let mut basins = vec![Rat::zero(); rings.len()];
    let mut plural = Rat::zero();
    for t in 0..LOCKING {
        let mut unique_total = Rat::zero();
        for (r, basin) in basins.iter_mut().enumerate() {
            let others: Rat = (0..rings.len())
                .filter(|s| *s != r)
                .map(|s| beyond(s, t))
                .product();
            let here = &laws[r].0[t] * others;
            unique_total += &here;
            *basin += here;
        }
        let minimum = (0..rings.len()).map(|s| at_least(s, t)).product::<Rat>()
            - (0..rings.len()).map(|s| beyond(s, t)).product::<Rat>();
        plural += minimum - unique_total;
    }
    let none: Rat = laws.iter().map(|(_, n)| n.clone()).product();
    let total: Rat = basins.iter().cloned().sum::<Rat>() + &plural + &none;
    assert!(
        total.is_one(),
        "the basins, the plural lock and none partition the configurations"
    );
    let descriptions: Vec<(u64, u64)> = rings.iter().map(|r| description(*r)).collect();
    let masses: Vec<Rat> = descriptions
        .iter()
        .map(|(_, l)| Rat::new(BigInt::one(), BigInt::one() << *l as usize))
        .collect();
    let normalizer: Rat = masses.iter().cloned().sum();
    let law: Vec<Rat> = masses.iter().map(|m| m / &normalizer).collect();
    println!(
        "  the bank's configurations: 2^122, the product over its 21 rings; the mass law π(p/q) = 2^(−ℓ)/Z, Z = {}",
        ratio(&normalizer)
    );
    let mut variation = plural.clone() + &none;
    for (r, (p, q)) in rings.iter().enumerate() {
        let (n, l) = descriptions[r];
        variation += (&basins[r] - &law[r]).abs();
        println!(
            "  {p}/{q}: Stern–Brocot n = {n}, ℓ = {l}; basin {} {}, π {} {}",
            ratio(&basins[r]),
            enclosure(&basins[r]),
            ratio(&law[r]),
            enclosure(&law[r])
        );
    }
    variation /= integer(2);
    println!(
        "  the plural lock {} {}, none {} {}",
        ratio(&plural),
        enclosure(&plural),
        ratio(&none),
        enclosure(&none)
    );
    let mut violations = 0usize;
    for a in 0..rings.len() {
        for b in 0..rings.len() {
            if descriptions[a].1 < descriptions[b].1 && basins[a] < basins[b] {
                violations += 1;
            }
        }
    }
    let within = variation <= tolerance();
    println!(
        "  total variation {} {} against the tolerance {}: {}; ordering violations (a strictly shorter description with a strictly smaller basin): {violations}",
        ratio(&variation),
        enclosure(&variation),
        ratio(&tolerance()),
        if within { "within" } else { "above" }
    );
    println!(
        "  (2) {}; {} ms",
        if within && violations == 0 {
            "holds"
        } else {
            "fails"
        },
        started.elapsed().as_millis()
    );
}

// -------------------------------------------------------------------------------------------
// the modes

fn print_bank(spectra: &[Spectrum], banks: &[(&str, &Bank)]) {
    println!(
        "the bank: 21 rings (rates p/q, 2 ≤ q ≤ {DENOMINATOR}), C = I, D = 0, h = 1, Y = 1, the pump on the real axis, σ = 0 for T_A = {INTEGRATION} ticks, then {} for T_B = {LOCKING}; the chart (L_c, D_c, L_w) = (32, 16, 16)",
        ratio(&pump())
    );
    for s in spectra {
        println!(
            "  q = {}: c₀ = {}; the in-phase block's inertia (+, 0, −) unpumped {:?}, pumped {:?}",
            s.q,
            ratio(&s.offset),
            s.unpumped,
            s.pumped
        );
    }
    for (name, bank) in banks {
        println!(
            "  the {name}'s declaration (the rings' solves, data-free): {} operations",
            bank.declaration
        );
    }
}

/// One terrain's arms over its seeds.
struct Terrain {
    name: &'static str,
    arms: Vec<&'static str>,
    outcomes: Vec<Vec<Outcome>>,
    declarations: Vec<u64>,
    revisits: Vec<Option<(usize, usize)>>,
}

fn report(terrain: &Terrain, seeds: &[u64]) -> bool {
    println!("{}:", terrain.name);
    for (s, seed) in seeds.iter().enumerate() {
        let row: Vec<String> = terrain
            .arms
            .iter()
            .zip(&terrain.outcomes)
            .map(|(arm, outcomes)| {
                let o = &outcomes[s];
                let closes = if o.passages > 0 {
                    format!(", {} of {} passages closed", o.closed, o.passages)
                } else {
                    String::new()
                };
                let proposals = if o.proposals > 0 {
                    format!(", {} proposals", o.proposals)
                } else {
                    String::new()
                };
                match o.certified {
                    Some(w) => format!(
                        "{arm} {w} ({} ms{closes}{proposals}; truth-equivalent {})",
                        o.ms, o.sound
                    ),
                    None => format!(
                        "{arm} none after {} ({} ms{closes}{proposals})",
                        o.spent, o.ms
                    ),
                }
            })
            .collect();
        let covered = match terrain.revisits.get(s) {
            None => String::new(),
            Some(Some((a, b))) => format!(" [the joint state at cell {a} returns at cell {b}]"),
            Some(None) => " [no joint state returns: uncertifiable]".to_string(),
        };
        println!("  seed {seed}{covered}: {}", row.join("; "));
    }
    let sums: Vec<Option<u64>> = terrain
        .outcomes
        .iter()
        .zip(&terrain.declarations)
        .map(|(outcomes, declaration)| {
            outcomes
                .iter()
                .map(|o| o.certified)
                .sum::<Option<u64>>()
                .map(|w| w + declaration)
        })
        .collect();
    let spent: Vec<u64> = terrain
        .outcomes
        .iter()
        .zip(&terrain.declarations)
        .map(|(outcomes, declaration)| outcomes.iter().map(|o| o.spent).sum::<u64>() + declaration)
        .collect();
    let ms: Vec<u128> = terrain
        .outcomes
        .iter()
        .map(|outcomes| outcomes.iter().map(|o| o.ms).sum())
        .collect();
    for (a, arm) in terrain.arms.iter().enumerate() {
        println!(
            "  {arm}: work to certified keys summed (with its declaration {}): {}; spent {}; {} ms",
            terrain.declarations[a],
            sum_text(sums[a]),
            spent[a],
            ms[a]
        );
    }
    let bank = sums[0];
    let mut holds = bank.is_some();
    for (a, arm) in terrain.arms.iter().enumerate().skip(1) {
        let below = match (bank, sums[a]) {
            (Some(b), Some(c)) => {
                println!(
                    "  the bank against {arm}: {} {} {} (bank over {arm}: {})",
                    b,
                    if b < c {
                        "<"
                    } else if b == c {
                        "="
                    } else {
                        ">"
                    },
                    c,
                    quotient(b, c)
                );
                b < c
            }
            (Some(_), None) => {
                println!("  the bank against {arm}: {arm} missed a seed");
                true
            }
            (None, _) => {
                println!("  the bank against {arm}: the bank missed a seed");
                false
            }
        };
        holds &= below;
    }
    println!(
        "  (1) on {}: {}",
        terrain.name,
        if holds { "holds" } else { "fails" }
    );
    holds
}

/// The measured run (or the preflight): every terrain's arms over its seeds, then (2).
fn run(seeds_of: impl Fn(u64) -> Vec<u64>, full_prior: bool) {
    let started = Instant::now();
    let spectra: Vec<Spectrum> = (2..=DENOMINATOR).map(spectrum).collect();
    let (pumped, control) = (bank(&spectra, true), bank(&spectra, false));
    print_bank(&spectra, &[("bank", &pumped), ("control", &control)]);
    let longest = longest_period(RINGS);
    println!(
        "the certification windows: T_max {} for one channel, {} for three gratings; {} gratings, {} joint keys",
        DENOMINATOR,
        factored(longest),
        factored(family().gratings()),
        factored(family().gratings().pow(3))
    );
    let mut verdicts = Vec::new();
    for (name, kind, base) in [
        ("the blind moiré", Kind::Blind, BLIND_SEED),
        ("the parity moiré", Kind::Parity, PARITY_SEED),
    ] {
        let seeds = seeds_of(base);
        let per_seed: Vec<[Outcome; 3]> = seeds
            .par_iter()
            .map(|seed| {
                let terrain = moire(&kind, *seed);
                let cells = terrain.emit(MOIRE_CELLS);
                match kind {
                    Kind::Blind => [
                        bank_blind(&pumped, &terrain, &cells),
                        bank_blind(&control, &terrain, &cells),
                        enumerate_blind(&terrain, &cells),
                    ],
                    Kind::Parity => [
                        bank_parity(&pumped, &terrain, &cells, longest),
                        bank_parity(&control, &terrain, &cells, longest),
                        enumerate_parity(&terrain, &cells, longest),
                    ],
                }
            })
            .collect();
        for (seed, _) in seeds.iter().zip(&per_seed) {
            let terrain = moire(&kind, *seed);
            let keys: Vec<String> = truth_keys(&terrain)
                .iter()
                .map(|(p, q, c)| format!("{p}/{q} @ {c}/{q}"))
                .collect();
            println!("  {name}, seed {seed}: the truth {}", keys.join(", "));
        }
        let terrain = Terrain {
            name,
            arms: vec!["bank", "control", "enumeration"],
            outcomes: (0..3)
                .map(|a| per_seed.iter().map(|o| o[a].clone()).collect())
                .collect(),
            declarations: vec![pumped.declaration, control.declaration, 0],
            revisits: Vec::new(),
        };
        verdicts.push(report(&terrain, &seeds));
    }
    let field = crib_field();
    let seeds = seeds_of(CRIB_SEED);
    let per_seed: Vec<(Option<(usize, usize)>, [Outcome; 4])> = seeds
        .par_iter()
        .map(|seed| {
            let c = crib(&field, *seed);
            (
                c.revisit,
                [
                    bank_crib(&field, &c, true),
                    bank_crib(&field, &c, false),
                    enumerate_crib(&field, &c),
                    menu_crib(&field, &c),
                ],
            )
        })
        .collect();
    for seed in &seeds {
        let c = crib(&field, *seed);
        println!(
            "  the rotor crib, seed {seed}: the truth key {}, board {:?}",
            c.crib.truth.key,
            c.crib.truth.board.images()
        );
    }
    let terrain = Terrain {
        name: "the rotor crib",
        arms: vec!["bank", "control", "enumeration", "menu propagation"],
        outcomes: (0..4)
            .map(|a| per_seed.iter().map(|(_, o)| o[a].clone()).collect())
            .collect(),
        declarations: vec![0, 0, 0, 0],
        revisits: per_seed.iter().map(|(c, _)| *c).collect(),
    };
    verdicts.push(report(&terrain, &seeds));
    println!(
        "(1): {} (blind {}, parity {}, crib {})",
        if verdicts.iter().all(|v| *v) {
            "holds"
        } else {
            "fails"
        },
        verdicts[0],
        verdicts[1],
        verdicts[2]
    );
    if full_prior {
        prior(&pumped);
    } else {
        let started = Instant::now();
        let ring = &pumped.rings.last().expect("a ring").1;
        for pattern in [0b0000_1111u64, 0b0101_0101, 0b0011_1100] {
            let _ = lock_time(ring, DENOMINATOR, pattern);
        }
        println!(
            "(2) preflight: three q = {DENOMINATOR} lock-time passages in {} ms (the full reading runs every rotation orbit of q ≤ {DENOMINATOR})",
            started.elapsed().as_millis()
        );
    }
    println!(
        "elapsed {} ms; peak resident {} kB",
        started.elapsed().as_millis(),
        peak_kb().map_or_else(|| "unread".to_string(), |kb| kb.to_string())
    );
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>()
        .as_slice()
    {
        ["bank"] => {
            let spectra: Vec<Spectrum> = (2..=DENOMINATOR).map(spectrum).collect();
            let (pumped, control) = (bank(&spectra, true), bank(&spectra, false));
            print_bank(&spectra, &[("bank", &pumped), ("control", &control)]);
            for (p, q) in rates() {
                let (n, l) = description((p, q));
                println!("  {p}/{q}: Stern–Brocot n = {n}, ℓ = {l}");
            }
        }
        ["diagnose", seed] => {
            let seed: u64 = seed.parse().expect("a seed");
            let spectra: Vec<Spectrum> = (2..=DENOMINATOR).map(spectrum).collect();
            let pumped = bank(&spectra, true);
            for kind in [Kind::Blind, Kind::Parity] {
                let terrain = moire(&kind, seed);
                let cells = terrain.emit(MOIRE_CELLS);
                let truth = truth_keys(&terrain);
                println!("truth {truth:?}");
                let drive: Vec<Rat> = cells
                    .iter()
                    .map(|&cell| match kind {
                        Kind::Blind => integer(RINGS as i64 - 2 * i64::from(cell.count_ones())),
                        Kind::Parity => integer(1 - 2 * cell as i64),
                    })
                    .collect();
                for ((p, q), ring) in &pumped.rings {
                    if !truth
                        .iter()
                        .any(|(tp, tq, _)| tq == q && (tp == p || tp + p == *q))
                    {
                        continue;
                    }
                    let n = ring.width();
                    let passage = ring
                        .pass(
                            [vec![Rat::zero(); n], vec![Rat::zero(); n]],
                            INTEGRATION - 1,
                            |t| {
                                let mut beta = vec![Rat::zero(); n];
                                beta[2 * (t as u64 * p % q) as usize] = drive[t].clone();
                                beta
                            },
                        )
                        .expect("a passage");
                    let first = &passage.sheets[0];
                    let last = passage.sheets.last().unwrap();
                    let mut ops = 0;
                    let x: Vec<String> = (0..*q as usize)
                        .map(|j| {
                            let v = &passage.state[0][2 * j];
                            format!("{}", v.numer() / v.denom())
                        })
                        .collect();
                    println!(
                        "  ring {p}/{q}: sheets at T_A {:?} decode {:?}; at the end {:?} decode {:?}; x {:?}",
                        first,
                        decode(*p, *q, first, &mut ops),
                        last,
                        decode(*p, *q, last, &mut ops),
                        x
                    );
                }
            }
        }
        ["preflight"] => run(|base| vec![base - BLIND_SEED + DEVELOPMENT_SEED], false),
        ["run"] => run(|base| (0..SEEDS).map(|s| base + s).collect(), true),
        _ => eprintln!("usage: hnn_ring_search -- bank | preflight | run"),
    }
}

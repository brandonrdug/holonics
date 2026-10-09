//! The duplex's laws (module header of `compression::keys::duplex`).
//!
//! **Development and acceptance are separated.** Development, per chart: the terrain's draw (the
//! first seed upward from `DEVELOPMENT_SEED + (chart << 16)` whose terrain generates ℤ/D, steps no
//! class by zero and carries one collision of advances, a designed placement) and the receiver's
//! openings `DEVELOPMENT_KEYS`. Acceptance: every key (asserted disjoint from the openings),
//! length, damage and substitution is drawn from streams of `ACCEPTANCE_SEED`, and none of them
//! founds or selects anything. The receiver is founded once per chart, outside any acceptance word.
//!
//! **Three exterior charts**, each a known-truth `SteppedTerrain` whose receiving cells are the
//! chart's classes, with `σ` the chart's own half-turn: text digits (base four, two bits a digit,
//! shown four to a byte only in the receipts), twelve pitch classes (the tritone), and eight
//! amplitude levels (phase inversion).
//!
//! **Receipts.** Every test prints exact counts with `eprintln!` (run with `--nocapture`):
//! integers and rationals only, never a float, a percentage or a decimal.
//!
//! **Cost.** The brute-force cross-checks enumerate a family completely: `∏|F_k| = 2^s` members
//! with `s ≤ 3` slipped contacts, an exponential cost declared and bounded here. The decoder never
//! enumerates.

use std::sync::OnceLock;

use num_traits::Signed;

use super::*;
use crate::compression::keys::transport::SteppedTerrain;
use crate::holarchy::terrain::Draw;

// -------------------------------------------------------------------------------------------
// the charts and their development

/// A boundary chart: its helix, the chart's half-turn `σ` and the injective contact velocities.
struct ChartSpec {
    name: &'static str,
    periods: [u64; 2],
    sigma: fn(usize) -> usize,
    plus: fn(usize) -> RatVec3,
}

/// Bit complement of a base-four digit.
fn digit_complement(x: usize) -> usize {
    3 - x
}

/// The tritone.
fn tritone(x: usize) -> usize {
    (x + 6) % 12
}

/// Phase inversion of an amplitude level.
fn phase_inversion(x: usize) -> usize {
    7 - x
}

/// The rectangle `(±2, ±1, 0)`, arranged so that `v₊(3 − x)` is `v₊(x)` with `y, z` negated: the
/// dyad `diag(1, −1, −1)`.
fn rectangle(x: usize) -> RatVec3 {
    match x {
        0 => RatVec3::from_i64(2, 1, 0),
        1 => RatVec3::from_i64(-2, 1, 0),
        2 => RatVec3::from_i64(-2, -1, 0),
        _ => RatVec3::from_i64(2, -1, 0),
    }
}

/// Any injective exact chart: `(x, x², 1)`.
fn pitch_helix(x: usize) -> RatVec3 {
    let x = x as i64;
    RatVec3::from_i64(x, x * x, 1)
}

/// Any injective exact chart: `(x, 1, x³)`.
fn level_ramp(x: usize) -> RatVec3 {
    let x = x as i64;
    RatVec3::from_i64(x, 1, x * x * x)
}

static CHARTS: [ChartSpec; 3] = [
    ChartSpec {
        name: "text digits (base four)",
        periods: [7, 4],
        sigma: digit_complement,
        plus: rectangle,
    },
    ChartSpec {
        name: "twelve pitch classes",
        periods: [5, 12],
        sigma: tritone,
        plus: pitch_helix,
    },
    ChartSpec {
        name: "eight amplitude levels",
        periods: [5, 8],
        sigma: phase_inversion,
        plus: level_ramp,
    },
];

/// Development: where each chart's terrain scan starts, and the receiver's openings.
const DEVELOPMENT_SEED: u64 = 0x4845_4c49_0000_0001;
const DEVELOPMENT_KEYS: [u64; 2] = [0, 5];
/// The scan is declared once: a terrain that is not designed within it is a test failure, and the
/// ceiling is never raised.
const SCAN_CEILING: u64 = 1 << 12;
/// Acceptance: the streams every key, length and damage is drawn from.
const ACCEPTANCE_SEED: u64 = 0x4845_4c49_00ac_0001;
const ACCEPTANCE_KEYS: usize = 8;
const DAMAGED_KEYS: usize = 4;
const LENGTHS: [usize; 7] = [0, 1, 2, 5, 12, 24, 48];
const DAMAGE_LENGTHS: [usize; 3] = [12, 24, 48];

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// [definition; agent-inferred] **The designed placement**: the advances generate `ℤ/D` (so the
/// founded receiver reaches every lift and separates every two phases), no class stands still,
/// and two classes share an advance (a coordinated substitution between them has reached
/// difference zero). Whether the receiver absorbs anything is read from its own quotient and
/// pinned against the shift law; this selection only guarantees the case exists.
fn designed(terrain: &SteppedTerrain) -> bool {
    let advances = terrain.advances();
    let generated = advances
        .iter()
        .fold(terrain.helix().period(), |g, &a| gcd(g, a));
    let collision = (0..advances.len()).any(|i| advances[..i].contains(&advances[i]));
    generated == 1 && collision && advances.iter().all(|&a| a != 0)
}

/// One chart in the state development leaves it.
struct Setting {
    spec: &'static ChartSpec,
    index: usize,
    seed: u64,
    scan: u64,
    helix: CarryHelix,
    terrain: SteppedTerrain,
    transport: LocatedTransport,
    pairing: Pairing,
    contacts: ContactChart,
}

impl Setting {
    fn build(index: usize) -> Self {
        let spec = &CHARTS[index];
        let helix =
            CarryHelix::new(spec.periods.to_vec()).expect("the chart's periods are coprime");
        let classes = usize::try_from(helix.cells()).expect("a cell count fits");
        let first = DEVELOPMENT_SEED + ((index as u64) << 16);
        let (scan, terrain) = (0..SCAN_CEILING)
            .map(|scan| {
                (
                    scan,
                    SteppedTerrain::draw(helix.clone(), &mut Draw::new(first + scan)),
                )
            })
            .find(|(_, terrain)| designed(terrain))
            .expect("a development seed draws a designed placement within the declared scan");
        let transport = LocatedTransport::of_terrain(&terrain);
        let pairing = Pairing::new((0..classes).map(spec.sigma).collect())
            .expect("the chart's half-turn is a fixed-point-free involution");
        let contacts = ContactChart::new((0..classes).map(spec.plus).collect())
            .expect("the chart's contact velocities are injective");
        Self {
            spec,
            index,
            seed: first + scan,
            scan,
            helix,
            terrain,
            transport,
            pairing,
            contacts,
        }
    }

    /// The receiver, founded once per chart on the development keys and shared.
    fn receiver(&self) -> &'static Receiver {
        static RECEIVERS: [OnceLock<Receiver>; 3] =
            [OnceLock::new(), OnceLock::new(), OnceLock::new()];
        RECEIVERS[self.index].get_or_init(|| {
            Receiver::found(&self.transport, &DEVELOPMENT_KEYS)
                .expect("the receiver is founded on the development keys")
        })
    }

    fn headline(&self) -> String {
        format!(
            "chart={:?} periods={:?} D={} D_low={} cells={}",
            self.spec.name,
            self.spec.periods,
            self.helix.period(),
            self.helix.grain(),
            self.helix.cells()
        )
    }
}

fn settings() -> Vec<Setting> {
    (0..CHARTS.len()).map(Setting::build).collect()
}

fn decoder(setting: &Setting) -> Decoder<'_> {
    Decoder::new(setting.receiver(), &setting.transport, &setting.pairing)
        .expect("the receiver is founded on the transport's helix")
}

/// The acceptance keys of a chart: drawn from the acceptance stream, distinct and disjoint from the
/// development openings.
fn acceptance_keys(setting: &Setting, count: usize) -> Vec<u64> {
    let mut draw = Draw::new(ACCEPTANCE_SEED + ((setting.index as u64) << 8));
    let period = usize::try_from(setting.helix.period()).expect("a period fits");
    let mut keys: Vec<u64> = Vec::new();
    while keys.len() < count {
        let key = draw.below(period) as u64;
        if !DEVELOPMENT_KEYS.contains(&key) && !keys.contains(&key) {
            keys.push(key);
        }
    }
    assert!(keys.iter().all(|key| !DEVELOPMENT_KEYS.contains(key)));
    keys
}

/// The test's display of a word: text digits four to a byte (display only), letters otherwise.
fn show(setting: &Setting, word: &[usize]) -> String {
    if setting.index == 0 {
        word.chunks(4)
            .map(|digits| {
                let byte = digits.iter().fold(0usize, |byte, &digit| byte * 4 + digit);
                format!("{byte:02x}")
            })
            .collect::<Vec<_>>()
            .join(" ")
    } else {
        format!("{word:?}")
    }
}

/// Every word of a length over `classes` letters.
fn all_words(classes: usize, length: usize) -> Vec<Vec<usize>> {
    let mut words: Vec<Vec<usize>> = vec![Vec::new()];
    for _ in 0..length {
        let mut longer = Vec::with_capacity(words.len() * classes);
        for word in &words {
            for letter in 0..classes {
                let mut extended = word.clone();
                extended.push(letter);
                longer.push(extended);
            }
        }
        words = longer;
    }
    words
}

/// The supremum-norm separation of two classes at one coordinate: a position's readings, or (past
/// the positions) the terminal windings.
fn separation_at(left: &ReceiverClass, right: &ReceiverClass, coordinate: usize) -> Rat {
    if coordinate < left.readings().len() {
        left.readings()[coordinate]
            .iter()
            .zip(&right.readings()[coordinate])
            .map(|(x, y)| (x - y).abs())
            .fold(Rat::zero(), |widest, d| if d > widest { d } else { widest })
    } else {
        Rat::from_integer(BigInt::from(left.winding().abs_diff(right.winding())))
    }
}

/// The supremum-norm separation of two full class tuples.
fn separation(left: &ReceiverClass, right: &ReceiverClass) -> Rat {
    (0..=left.readings().len())
        .map(|coordinate| separation_at(left, right, coordinate))
        .fold(Rat::zero(), |widest, d| if d > widest { d } else { widest })
}

/// Every member of the product of the local factors, `∏|F_k|` words: the exponential cross-check.
fn enumerate(admitted: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut words: Vec<Vec<usize>> = vec![Vec::new()];
    for letters in admitted {
        let mut next = Vec::with_capacity(words.len() * letters.len());
        for word in &words {
            for &letter in letters {
                let mut extended = word.clone();
                extended.push(letter);
                next.push(extended);
            }
        }
        words = next;
    }
    words
}

// -------------------------------------------------------------------------------------------
// the damaged duplexes

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Side {
    Strand,
    Partner,
}

/// A damaged duplex of the covered repairable channel: at each contact at most one strand changed.
struct Case {
    duplex: Duplex,
    side: Side,
    damage: Damage,
    strand: Vec<usize>,
    partner: Vec<usize>,
}

/// The chart's damaged duplexes: unseen keys, three lengths, damage on either strand at one to
/// three drawn contacts, each to a drawn other letter.
fn cases(setting: &Setting) -> Vec<Case> {
    let mut draw = Draw::new(ACCEPTANCE_SEED + ((setting.index as u64) << 8) + 1);
    let classes = setting.pairing.classes();
    let mut cases = Vec::new();
    for &key in &acceptance_keys(setting, DAMAGED_KEYS) {
        for &length in &DAMAGE_LENGTHS {
            let word = setting.terrain.passage(key, length);
            let duplex = Duplex::place(&setting.transport, &setting.pairing, key, &word)
                .expect("a passage of the transport is placed");
            for side in [Side::Strand, Side::Partner] {
                let count = 1 + draw.below(3);
                let mut contacts: Vec<usize> = Vec::new();
                while contacts.len() < count {
                    let contact = draw.below(length);
                    if !contacts.contains(&contact) {
                        contacts.push(contact);
                    }
                }
                let mut substitutions = Vec::new();
                for &contact in &contacts {
                    let original = match side {
                        Side::Strand => duplex.strand()[contact],
                        Side::Partner => duplex.partner()[length - 1 - contact],
                    };
                    let letter = (original + 1 + draw.below(classes - 1)) % classes;
                    substitutions.push((contact, letter));
                }
                let damage = match side {
                    Side::Strand => Damage::new(substitutions, Vec::new()),
                    Side::Partner => Damage::new(Vec::new(), substitutions),
                };
                let (strand, partner) = damage
                    .apply(&duplex, &setting.pairing)
                    .expect("a declared damage applies");
                cases.push(Case {
                    duplex: duplex.clone(),
                    side,
                    damage,
                    strand,
                    partner,
                });
            }
        }
    }
    cases
}

/// A damaged duplex with its truth's class and its free, unmarked decoding, read once per chart.
struct Run {
    case: Case,
    truth: ReceiverClass,
    free: Decoded,
}

fn runs(index: usize) -> &'static [Run] {
    static RUNS: [OnceLock<Vec<Run>>; 3] = [OnceLock::new(), OnceLock::new(), OnceLock::new()];
    RUNS[index].get_or_init(|| {
        let setting = Setting::build(index);
        let receiver = setting.receiver();
        let decoder = decoder(&setting);
        cases(&setting)
            .into_iter()
            .map(|case| {
                let truth = receiver
                    .class(case.duplex.lifts())
                    .expect("the truth's lifts are read");
                let free = decoder
                    .decode(
                        case.duplex.key(),
                        &case.strand,
                        &case.partner,
                        Template::Unmarked,
                        Fit::Free,
                    )
                    .expect("a damaged duplex of the covered channel decodes");
                Run { case, truth, free }
            })
            .collect()
    })
}

// -------------------------------------------------------------------------------------------
// the pairing, the lifts and the residues

/// [proved-derived; implemented-exact] **The pairing is a fixed-point-free involution and its
/// complement-reverse an anti-automorphism.** The refusals (a fixed class, a non-involution, an
/// entry outside the classes); on each chart's half-turn `σ̄∘σ̄ = id`, `σ̄(vw) = σ̄(w)σ̄(v)`, and the
/// self-paired words of length `2m` number `|A|^m` and are `u ++ σ̄(u)`, with none of odd length
/// (Lean `Transport/HelicalCode.{even_length_of_fixed, fixed_eq_take_append, card_fixedWords}`);
/// on four letters the fixed-point-free involutions are exactly the three translations of the
/// Klein group, and each preserves the type of every point substitution
/// (`free_involution_iff`, `free_involution_commutes`).
#[test]
fn a_pairing_is_a_fixed_point_free_involution_and_its_complement_reverse_an_anti_automorphism() {
    assert!(matches!(
        Pairing::new(Vec::new()),
        Err(CompressionError::EmptyFamily { .. })
    ));
    assert!(matches!(
        Pairing::new(vec![1, 0, 2, 3]),
        Err(CompressionError::Helix { reason }) if reason.contains("no fixed class")
    ));
    assert!(matches!(
        Pairing::new(vec![1, 2, 0, 3]),
        Err(CompressionError::Helix { reason }) if reason.contains("involution")
    ));
    assert_eq!(
        Pairing::new(vec![1, 0, 5, 3]),
        Err(CompressionError::IndexOutside {
            index: 5,
            population: 4
        })
    );
    assert!(Pairing::new(vec![0]).is_err());
    assert!(Pairing::new(vec![1, 0, 3, 2]).is_ok());

    let mut free = Vec::new();
    for code in 0..256usize {
        let sigma: Vec<usize> = (0..4usize).map(|i| (code >> (2 * i)) & 3).collect();
        if Pairing::new(sigma.clone()).is_ok() {
            free.push(sigma);
        }
    }
    assert_eq!(free.len(), 3);
    for sigma in &free {
        let v = sigma[0];
        assert!(v != 0);
        for x in 0..4 {
            assert_eq!(sigma[x], x ^ v);
        }
        for t in 0..4 {
            for x in 0..4 {
                assert_eq!(sigma[x ^ t], sigma[x] ^ t);
            }
        }
    }

    let mut draw = Draw::new(ACCEPTANCE_SEED);
    for spec in &CHARTS {
        let classes = usize::try_from(spec.periods[1]).expect("a class count fits");
        let pairing = Pairing::new((0..classes).map(spec.sigma).collect())
            .expect("the chart's half-turn is a pairing");
        let reverse = |word: &[usize]| pairing.complement_reverse(word).unwrap();
        let mut laws = 0usize;
        for _ in 0..64 {
            let (m, n) = (draw.below(10), draw.below(10));
            let v: Vec<usize> = (0..m).map(|_| draw.below(classes)).collect();
            let w: Vec<usize> = (0..n).map(|_| draw.below(classes)).collect();
            assert_eq!(reverse(&reverse(&w)), w);
            let joined: Vec<usize> = v.iter().chain(&w).copied().collect();
            let swapped: Vec<usize> = reverse(&w).into_iter().chain(reverse(&v)).collect();
            assert_eq!(reverse(&joined), swapped);
            assert_eq!(reverse(&w).len(), w.len());
            if reverse(&w) == w {
                assert_eq!(w.len() % 2, 0);
            }
            laws += 1;
        }
        let mut counts = Vec::new();
        for half in 0..=2usize {
            let words = all_words(classes, 2 * half);
            let fixed: Vec<&Vec<usize>> = words
                .iter()
                .filter(|w| reverse(w.as_slice()) == w.as_slice())
                .collect();
            assert_eq!(fixed.len(), classes.pow(half as u32));
            for w in &fixed {
                let mut rebuilt = w[..half].to_vec();
                rebuilt.extend(reverse(&w[..half]));
                assert_eq!(&rebuilt, *w);
            }
            counts.push(fixed.len());
        }
        for length in [1usize, 3] {
            assert!(
                all_words(classes, length)
                    .iter()
                    .all(|w| reverse(w.as_slice()) != w.as_slice())
            );
        }
        eprintln!(
            "helical-duplex (a) pairing: chart={:?} classes={classes} word laws checked={laws} \
             self-paired words of length 0, 2, 4 = {counts:?} (|A|^m), of length 1, 3 = 0; \
             Klein: 3 of 256 maps on four letters are fixed-point-free involutions",
            spec.name
        );
    }
}

/// [proved-derived; implemented-exact] **Coprime residues recover the lift, and the winding keeps
/// the carry.** On every helix, `of_residues(residues(ℓ)) = ℓ` for every `ℓ ∈ [0, D)` and the `D`
/// residue tuples are distinct (Lean `HNN/Prediction.joint_residue_determines_position`); a wrong
/// length or a residue at its period is refused. Along a passage the odometer's carries count the
/// whole windings, and `ℓ = (windings)·D + (the lift of the residues)`: the helix is a circle plus
/// its carry, in both charts.
#[test]
fn coprime_residues_recover_the_lift_and_the_winding_keeps_the_carry() {
    let mut helices: Vec<CarryHelix> = CHARTS
        .iter()
        .map(|spec| CarryHelix::new(spec.periods.to_vec()).unwrap())
        .collect();
    helices.push(CarryHelix::new(vec![2, 3, 5]).unwrap());
    helices.push(CarryHelix::new(vec![3, 4, 5]).unwrap());
    for helix in &helices {
        let period = helix.period();
        let mut tuples: Vec<Vec<u64>> = Vec::new();
        for lift in 0..period {
            let residues = helix.residues(lift);
            assert_eq!(helix.of_residues(&residues), Ok(lift));
            tuples.push(residues);
        }
        tuples.sort();
        tuples.dedup();
        assert_eq!(tuples.len() as u64, period);
        let rings = helix.periods().len();
        assert!(matches!(
            helix.of_residues(&vec![0; rings + 1]),
            Err(CompressionError::Helix { .. })
        ));
        assert!(matches!(
            helix.of_residues(&vec![0; rings - 1]),
            Err(CompressionError::Helix { .. })
        ));
        let mut outside = vec![0; rings];
        outside[rings - 1] = helix.periods()[rings - 1];
        assert!(matches!(
            helix.of_residues(&outside),
            Err(CompressionError::Helix { .. })
        ));
        eprintln!(
            "helical-duplex (b) crt: periods={:?} D={period} residue tuples recovered={} (all distinct), refusals: \
             wrong length (two), residue at its period",
            helix.periods(),
            tuples.len()
        );
    }
    for setting in settings() {
        let helix = &setting.helix;
        let period = helix.period();
        let advances = setting.transport.advances();
        let mut steps = 0usize;
        let mut turns_total = 0u64;
        for &key in &acceptance_keys(&setting, ACCEPTANCE_KEYS) {
            let word = setting.terrain.passage(key, 48);
            let lifts = setting.transport.lifts(key, &word).unwrap();
            let mut digits = helix.digits(lifts[0]);
            let mut windings = 0u64;
            for (k, &letter) in word.iter().enumerate() {
                let (stepped, carries) =
                    helix.step_digits(&digits, &helix.digits(advances[letter]));
                windings += carries[carries.len() - 1];
                digits = stepped;
                let phase = helix.of_digits(&digits);
                assert_eq!(phase, lifts[k + 1] % period);
                assert_eq!(helix.of_residues(&helix.residues(lifts[k + 1])), Ok(phase));
                assert_eq!(lifts[k + 1], windings * period + phase);
                steps += 1;
            }
            turns_total += windings;
        }
        eprintln!(
            "helical-duplex (b) carry: {} acceptance passages of 48, steps checked={steps}, \
             whole windings counted by the odometer's last carry in total={turns_total}; every \
             lift = windings·D + the residues' lift",
            ACCEPTANCE_KEYS
        );
    }
}

/// [definition; implemented-exact] **The absolute lifts** step by the located advances and reduce
/// only for the reading: `ℓ_0 = key mod D`, `ℓ_(k+1) − ℓ_k = A(u_k)`, phases follow
/// `LocatedTransport::step`, a passage regenerates, a class outside the advances is refused.
#[test]
fn the_lifts_carry_the_winding_and_step_the_phase() {
    for setting in settings() {
        let transport = &setting.transport;
        let period = setting.helix.period();
        let advances = transport.advances();
        let mut checked = 0usize;
        for &key in &acceptance_keys(&setting, ACCEPTANCE_KEYS) {
            for &length in &LENGTHS {
                let word = setting.terrain.passage(key, length);
                let lifts = transport.lifts(key, &word).unwrap();
                assert_eq!(lifts.len(), length + 1);
                assert_eq!(lifts[0], key % period);
                assert_eq!(
                    transport.lifts(key + 3 * period, &word).unwrap(),
                    lifts,
                    "the key is reduced"
                );
                assert_eq!(transport.regenerate(key, length), Some(word.clone()));
                for k in 0..length {
                    assert_eq!(lifts[k + 1] - lifts[k], advances[word[k]]);
                    assert_eq!(transport.emit(lifts[k] % period), Some(word[k]));
                    assert_eq!(
                        transport.step(lifts[k] % period),
                        Some(lifts[k + 1] % period)
                    );
                    checked += 1;
                }
            }
        }
        assert_eq!(
            transport.lifts(0, &[setting.pairing.classes()]),
            Err(CompressionError::IndexOutside {
                index: setting.pairing.classes(),
                population: setting.pairing.classes()
            })
        );
        eprintln!(
            "helical-duplex lifts: {} steps checked on unseen keys and lengths {LENGTHS:?}; \
             a class outside the advances is refused",
            checked
        );
    }
}

/// [definition; implemented-exact] **A substitution carries a signed shift that moves every later
/// lift.** `Δ = A(u′) − A(u)` is signed and not reduced (`−D < Δ < D`), antisymmetric, zero exactly
/// when the advances are equal, and a class outside the advances is refused. On placed words: the
/// damaged word's absolute lifts equal the clean ones up to the substituted position and are moved
/// by `Δ` after it.
#[test]
fn a_substitution_carries_a_signed_shift_that_moves_every_later_lift() {
    for setting in settings() {
        let transport = &setting.transport;
        let advances = transport.advances();
        let period = setting.helix.period() as i64;
        let classes = setting.pairing.classes();
        for was in 0..classes {
            for now in 0..classes {
                let shift = carried_shift(transport, was, now).unwrap();
                assert_eq!(shift, advances[now] as i64 - advances[was] as i64);
                assert_eq!(shift, -carried_shift(transport, now, was).unwrap());
                assert_eq!(shift == 0, advances[now] == advances[was]);
                assert!(-period < shift && shift < period);
            }
            assert_eq!(carried_shift(transport, was, was).unwrap(), 0);
        }
        assert!(matches!(
            carried_shift(transport, 0, classes),
            Err(CompressionError::IndexOutside { .. })
        ));
        assert!(matches!(
            carried_shift(transport, classes, 0),
            Err(CompressionError::IndexOutside { .. })
        ));
        let mut moved_lifts = 0usize;
        for &key in &acceptance_keys(&setting, 4) {
            let word = setting.terrain.passage(key, 24);
            let lifts = transport.lifts(key, &word).unwrap();
            for i in [0usize, 7, 23] {
                let now = (word[i] + 1) % classes;
                let mut damaged = word.clone();
                damaged[i] = now;
                let after = transport.lifts(key, &damaged).unwrap();
                let shift = carried_shift(transport, word[i], now).unwrap();
                for k in 0..=24 {
                    let expected = if k <= i {
                        lifts[k] as i64
                    } else {
                        lifts[k] as i64 + shift
                    };
                    assert_eq!(after[k] as i64, expected);
                    moved_lifts += usize::from(k > i && shift != 0);
                }
            }
        }
        eprintln!(
            "helical-duplex shift: the carried shift Δ = A(u′) − A(u) over all {} ordered class pairs is signed, \
             antisymmetric and zero exactly on equal advances; {moved_lifts} later lifts of damaged words moved by \
             exactly Δ and none before the substitution",
            classes * classes
        );
    }
}

/// [proved-derived; implemented-exact] **The unit-rate slip vanishes exactly on the complement.**
/// For every pair of classes, read through `PairContact` and `pair_lock`: the slip is
/// `v₊(a) − v₊(σ(b))`, it is zero exactly when the pair locks, and that is exactly when
/// `b = σ(a)`, so `|A|` of the `|A|²` pairs lock. The same injective chart on both sides would lock
/// equal letters, not complements. A repeated velocity is refused. On the text chart `σ` is the
/// dyad `diag(1, −1, −1)`. The slipped contacts through the contacts equal the pairing's.
#[test]
fn the_unit_rate_slip_vanishes_exactly_on_the_complement() {
    let translation = |velocity: &RatVec3| {
        SituatedScrew::new(
            ScrewGenerator::new(RatVec3::zero(), velocity.clone()),
            RatVec3::zero(),
        )
    };
    let mut draw = Draw::new(ACCEPTANCE_SEED + 7);
    for setting in settings() {
        let (pairing, contacts) = (&setting.pairing, &setting.contacts);
        let classes = pairing.classes();
        let (mut locked_pairs, mut same_chart_locks) = (0usize, 0usize);
        for a in 0..classes {
            for b in 0..classes {
                let locked = contacts.locked(pairing, a, b).unwrap();
                let slip = contacts.slip(pairing, a, b).unwrap();
                assert_eq!(locked, b == pairing.pair(a).unwrap());
                assert_eq!(slip == RatVec3::zero(), locked);
                let image = pairing.pair(b).unwrap();
                assert_eq!(
                    slip,
                    contacts
                        .plus(a)
                        .unwrap()
                        .subtract(contacts.plus(image).unwrap())
                );
                locked_pairs += usize::from(locked);
                let same = ScrewPair::new(
                    translation(contacts.plus(a).unwrap()),
                    translation(contacts.plus(b).unwrap()),
                );
                let equal_letters = pair_lock(&same, &BigInt::one(), &BigInt::one()).unwrap();
                assert_eq!(equal_letters, a == b);
                same_chart_locks += usize::from(equal_letters);
            }
        }
        assert_eq!(locked_pairs, classes);
        assert_eq!(same_chart_locks, classes);
        let mut repeated: Vec<RatVec3> = (0..classes).map(setting.spec.plus).collect();
        repeated[classes - 1] = repeated[0].clone();
        assert_eq!(
            ContactChart::new(repeated),
            Err(CompressionError::NotInjective { port: classes - 1 })
        );
        if setting.index == 0 {
            for a in 0..classes {
                let v = contacts.plus(a).unwrap();
                let image = contacts.plus(pairing.pair(a).unwrap()).unwrap();
                assert_eq!(
                    *image,
                    RatVec3::new(v.x.clone(), -v.y.clone(), -v.z.clone())
                );
            }
        }
        let mut slipped_words = 0usize;
        for _ in 0..32 {
            let n = draw.below(12);
            let strand: Vec<usize> = (0..n).map(|_| draw.below(classes)).collect();
            let partner: Vec<usize> = (0..n).map(|_| draw.below(classes)).collect();
            let by_letters = pairing.slipped(&strand, &partner).unwrap();
            assert_eq!(
                contacts.slipped(pairing, &strand, &partner).unwrap(),
                by_letters
            );
            slipped_words += by_letters.len();
        }
        eprintln!(
            "helical-duplex (i) contacts: {} pairs {} locked = |A| = {classes} (zero slip iff b = σ(a)); \
             one chart on both sides would lock {same_chart_locks} equal-letter pairs; \
             slipped contacts by letters = by locks on 32 random word pairs ({slipped_words} slips)",
            classes * classes,
            locked_pairs
        );
    }
}

// -------------------------------------------------------------------------------------------
// fit first, placement and the channel

/// [proved-derived; implemented-exact] **Fit first.** A strand that is no passage of the transport
/// from the key returns its located defect, never a duplex. For one substituted letter at `i` the
/// defect positions equal `{i} ∪ {k > i : emit((ℓ_k + Δ) mod D) ≠ u_k}`, derived from the shift
/// `Δ = A(u′_i) − A(u_i)` without stepping the damaged word; for a random word they equal the
/// explicit stepping. Both equal the transport's own patch count, and a word fits exactly when
/// the key lies in its key fibre.
#[test]
fn a_strand_that_is_no_passage_returns_its_located_defect_and_never_a_duplex() {
    for setting in settings() {
        let transport = &setting.transport;
        let period = setting.helix.period();
        let advances = transport.advances();
        let classes = setting.pairing.classes();
        let mut draw = Draw::new(ACCEPTANCE_SEED + ((setting.index as u64) << 8) + 2);
        let (mut passages, mut substituted, mut garbage, mut defects) =
            (0usize, 0usize, 0usize, 0usize);
        for &key in &acceptance_keys(&setting, ACCEPTANCE_KEYS) {
            for &length in &[1usize, 2, 5, 12, 24] {
                let word = setting.terrain.passage(key, length);
                assert_eq!(transport.regenerate(key, length), Some(word.clone()));
                assert!(Duplex::place(transport, &setting.pairing, key, &word).is_ok());
                assert!(transport.keys(&word).contains(&(key % period)));
                passages += 1;
                let lifts = transport.lifts(key, &word).unwrap();
                for _ in 0..3 {
                    let i = draw.below(length);
                    let letter = (word[i] + 1 + draw.below(classes - 1)) % classes;
                    let mut damaged = word.clone();
                    damaged[i] = letter;
                    let shift = carried_shift(transport, word[i], letter).unwrap();
                    let expected: Vec<usize> = (0..length)
                        .filter(|&k| match k.cmp(&i) {
                            std::cmp::Ordering::Less => false,
                            std::cmp::Ordering::Equal => true,
                            std::cmp::Ordering::Greater => {
                                let shifted = u64::try_from(lifts[k] as i64 + shift).unwrap();
                                transport.emit(shifted % period) != Some(word[k])
                            }
                        })
                        .collect();
                    match Duplex::place(transport, &setting.pairing, key, &damaged) {
                        Err(DuplexDefect::Unfit { positions }) => {
                            assert_eq!(positions, expected);
                            assert!(positions.contains(&i));
                            assert_eq!(positions.len(), transport.patches(&damaged, key));
                            assert!(!transport.keys(&damaged).contains(&(key % period)));
                            defects += positions.len();
                        }
                        other => panic!("a substituted strand is no passage: {other:?}"),
                    }
                    substituted += 1;
                }
            }
        }
        for _ in 0..16 {
            let key = draw.below(usize::try_from(period).unwrap()) as u64;
            let length = 1 + draw.below(30);
            let word: Vec<usize> = (0..length).map(|_| draw.below(classes)).collect();
            let mut lift = key % period;
            let mut expected = Vec::new();
            for (k, &letter) in word.iter().enumerate() {
                if transport.emit(lift) != Some(letter) {
                    expected.push(k);
                }
                lift = (lift + advances[letter]) % period;
            }
            match Duplex::place(transport, &setting.pairing, key, &word) {
                Ok(_) => {
                    assert!(expected.is_empty());
                    assert_eq!(transport.regenerate(key, length), Some(word.clone()));
                }
                Err(DuplexDefect::Unfit { positions }) => {
                    assert_eq!(positions, expected);
                    assert_eq!(positions.len(), transport.patches(&word, key));
                    defects += positions.len();
                }
                Err(other) => panic!("a random word fits or is located: {other:?}"),
            }
            garbage += 1;
        }
        eprintln!(
            "helical-duplex (c) fit-first: {} passages placed, {substituted} one-letter substitutions and \
             {garbage} random words refused with their located defects (positions equal the shift law / explicit \
             stepping / the transport's patch count; {defects} defect positions in all)",
            passages
        );
    }
}

/// [proved-derived; implemented-exact] **Placement pairs the partner before the quotient.** On
/// unseen keys and lengths including `n = 0` and `n = 1`: the partner is `σ̄(u)`; its absolute
/// lifts advance by the strand's advances in reverse, `ℓ′_(k+1) − ℓ′_k = A(u_(n−1−k))`, and carry
/// the strand's whole winding; their phases are the mirror chart's, `ℓ′_k mod D = R(ℓ_(n−k))`; the
/// two partner equations hold on phases for every `k < n`; the partner ends at the phase of the
/// reflected key and only the phase (the integer differs in general); each strand is the other's
/// key; and the mirror gauge regenerates the strand itself, not the partner.
#[test]
fn placement_pairs_the_partner_before_the_quotient_on_unseen_keys_and_lengths() {
    for setting in settings() {
        let (transport, pairing) = (&setting.transport, &setting.pairing);
        let period = setting.helix.period();
        let advances = transport.advances();
        let mirror = transport.reflected();
        let keys = acceptance_keys(&setting, ACCEPTANCE_KEYS);
        let (mut placed, mut equations, mut integer_differs) = (0usize, 0usize, 0usize);
        for &key in &keys {
            for &length in &LENGTHS {
                let word = setting.terrain.passage(key, length);
                let duplex = Duplex::place(transport, pairing, key, &word).unwrap();
                placed += 1;
                let (lifts, partner_lifts) = (duplex.lifts(), duplex.partner_lifts());
                assert_eq!(duplex.len(), length);
                assert_eq!(duplex.key(), key);
                assert_eq!((lifts.len(), partner_lifts.len()), (length + 1, length + 1));
                assert_eq!(
                    duplex.partner().to_vec(),
                    pairing.complement_reverse(&word).unwrap()
                );
                assert_eq!(lifts.to_vec(), transport.lifts(key, &word).unwrap());
                for k in 0..length {
                    assert_eq!(
                        partner_lifts[k + 1] - partner_lifts[k],
                        advances[word[length - 1 - k]]
                    );
                    assert_eq!(
                        partner_lifts[k] % period,
                        transport.reflect_key(lifts[length - k])
                    );
                    let arrival = partner_lifts[k + 1] % period;
                    assert_eq!(mirror.step(arrival), Some(partner_lifts[k] % period));
                    assert_eq!(
                        mirror.emit(arrival).and_then(|class| pairing.pair(class)),
                        Some(duplex.partner()[k])
                    );
                    equations += 2;
                }
                assert_eq!(partner_lifts[length] % period, transport.reflect_key(key));
                if partner_lifts[length] != transport.reflect_key(key) {
                    integer_differs += 1;
                }
                assert_eq!(
                    transport.reflect_key(partner_lifts[0]),
                    lifts[length] % period
                );
                assert_eq!(transport.reflect_key(partner_lifts[length]), key % period);
                assert_eq!(
                    partner_lifts[length] - partner_lifts[0],
                    lifts[length] - lifts[0]
                );
                assert_eq!(
                    mirror.regenerate(transport.reflect_key(key), length),
                    Some(word.clone())
                );
                assert_eq!(
                    duplex.contacts(),
                    (0..length).map(|k| (k, length - 1 - k)).collect::<Vec<_>>()
                );
            }
            let empty = Duplex::place(transport, pairing, key, &[]).unwrap();
            assert!(empty.is_empty() && empty.contacts().is_empty() && empty.partner().is_empty());
            assert_eq!(empty.lifts().to_vec(), vec![key % period]);
            assert_eq!(
                empty.partner_lifts().to_vec(),
                vec![transport.reflect_key(key)]
            );
            let word = setting.terrain.passage(key, 1);
            let single = Duplex::place(transport, pairing, key, &word).unwrap();
            let end = key % period + advances[word[0]];
            assert_eq!(single.contacts(), vec![(0, 0)]);
            assert_eq!(
                single.partner().to_vec(),
                vec![pairing.pair(word[0]).unwrap()]
            );
            assert_eq!(
                single.partner_lifts().to_vec(),
                vec![
                    transport.reflect_key(end),
                    transport.reflect_key(end) + advances[word[0]]
                ]
            );
        }
        let wrong = Pairing::new(vec![1, 0]).unwrap();
        assert!(matches!(
            Duplex::place(transport, &wrong, 1, &[0]),
            Err(DuplexDefect::Compression(CompressionError::Extent { .. }))
        ));
        eprintln!(
            "helical-duplex (d) placement: {} duplexes placed on {} unseen keys and lengths {LENGTHS:?} \
             (n = 0 and n = 1 explicit), {equations} partner equations checked on phases, \
             partner endpoint equals reflect_key(key) as a phase in all and differs as an integer in \
             {integer_differs}",
            placed,
            keys.len()
        );
    }
}

/// [proved-derived; implemented-exact] **A single-strand damage slips exactly its contacts.** On
/// damaged duplexes of either strand at drawn contacts, the slipped set `{k : y′_(n−1−k) ≠ σ(x′_k)}`
/// equals the declared damaged set, read by letters and through the contacts' locks; at each
/// slipped contact the two candidates differ and the truth's letter is one of them (the covered
/// channel).
#[test]
fn single_strand_damage_slips_exactly_the_damaged_contacts() {
    for setting in settings() {
        let pairing = &setting.pairing;
        let (mut total, mut on_strand, mut on_partner, mut substituted) =
            (0usize, 0usize, 0usize, 0usize);
        for case in cases(&setting) {
            let length = case.duplex.len();
            let damaged = case.damage.damaged_contacts();
            let slipped = pairing.slipped(&case.strand, &case.partner).unwrap();
            assert_eq!(slipped, damaged);
            assert_eq!(
                setting
                    .contacts
                    .slipped(pairing, &case.strand, &case.partner)
                    .unwrap(),
                slipped
            );
            match case.side {
                Side::Strand => {
                    assert_eq!(case.partner, case.duplex.partner());
                    on_strand += 1;
                }
                Side::Partner => {
                    assert_eq!(case.strand, case.duplex.strand());
                    on_partner += 1;
                }
            }
            for &k in &slipped {
                let own = case.strand[k];
                let implied = pairing.pair(case.partner[length - 1 - k]).unwrap();
                assert_ne!(own, implied);
                let truth = case.duplex.strand()[k];
                assert!(truth == own || truth == implied);
            }
            substituted += slipped.len();
            total += 1;
        }
        eprintln!(
            "helical-duplex (e) channel: {} damaged duplexes ({on_strand} on the strand, {on_partner} on the \
             partner), {substituted} substituted contacts = {substituted} slipped contacts, sets equal in {total}",
            total
        );
    }
}

// -------------------------------------------------------------------------------------------
// release, the diameter equation, witnesses and the supports

/// [proved-derived; implemented-exact] **The free family is released exactly when every
/// coordinate is constant, and the truth round-trips on the covered channel.** The expectation is
/// derived from the shift law without the decoder: the advances generate `ℤ/D`, so the founded
/// receiver separates every two phases, and the family is constant exactly when every slipped
/// contact's two candidates have equal advances. A released class is the truth's class (the truth
/// is a member of the covered channel's family), the member count is `2^s`, and an intact duplex
/// is released with its own class.
#[test]
fn a_repair_family_is_released_exactly_when_every_coordinate_is_constant() {
    for index in 0..CHARTS.len() {
        let setting = Setting::build(index);
        let advances = setting.transport.advances();
        let decoder = decoder(&setting);
        let receiver = setting.receiver();
        let (mut released, mut held, mut members) = (0usize, 0usize, BigUint::zero());
        let mut shown = false;
        for run in runs(index) {
            let case = &run.case;
            let length = case.duplex.len();
            let slipped = setting
                .pairing
                .slipped(&case.strand, &case.partner)
                .unwrap();
            let expect_released = slipped.iter().all(|&k| {
                let implied = setting.pairing.pair(case.partner[length - 1 - k]).unwrap();
                advances[case.strand[k]] == advances[implied]
            });
            let receipt = run.free.receipt();
            assert_eq!(receipt.slipped, slipped);
            assert_eq!(
                receipt.members,
                BigUint::from(2u32).pow(slipped.len() as u32)
            );
            members += &receipt.members;
            match &run.free {
                Decoded::Released { class, .. } => {
                    assert!(expect_released);
                    assert_eq!(*class, run.truth);
                    assert!(receipt.diameter.is_zero());
                    assert!(receipt.distinct.iter().all(|&d| d == 1));
                    released += 1;
                }
                Decoded::Held {
                    held: held_family, ..
                } => {
                    assert!(!expect_released);
                    assert!(receipt.diameter > Rat::zero());
                    assert!(receipt.distinct.iter().any(|&d| d > 1));
                    assert_ne!(held_family.classes[0], held_family.classes[1]);
                    held += 1;
                    if !shown {
                        shown = true;
                        eprintln!(
                            "helical-duplex (f) held witness pair: chart={:?} slipped contacts={:?} \
                             members={} witness strands {:?} / {:?} (letters {} / {}) differ first at \
                             coordinate {} of {} (positions 0..={length}, then the winding); \
                             family diameter={}",
                            setting.spec.name,
                            receipt.slipped,
                            receipt.members,
                            held_family.witnesses[0].letters,
                            held_family.witnesses[1].letters,
                            show(&setting, &held_family.witnesses[0].letters),
                            show(&setting, &held_family.witnesses[1].letters),
                            held_family.coordinate,
                            length + 1,
                            receipt.diameter
                        );
                    }
                }
            }
        }
        for run in runs(index).iter().take(3) {
            let duplex = &run.case.duplex;
            let intact = decoder
                .decode(
                    duplex.key(),
                    duplex.strand(),
                    duplex.partner(),
                    Template::Unmarked,
                    Fit::Free,
                )
                .unwrap();
            let Decoded::Released { class, receipt } = &intact else {
                panic!("an intact duplex slips nothing and is released");
            };
            assert_eq!(*class, run.truth);
            assert_eq!(receipt.members, BigUint::one());
            assert!(receipt.slipped.is_empty());
            assert_eq!(class, &receiver.class(duplex.lifts()).unwrap());
        }
        eprintln!(
            "helical-duplex (f) free family: {} released (class equals the truth's) and {held} held of {} \
             damaged duplexes; members over all families={members}; intact duplexes released with their own class",
            released,
            released + held
        );
    }
}

/// [proved-derived; implemented-exact] **The family diameter is the maximum over its coordinates,
/// and the supports are exact.** Against the complete enumeration of every member (`2^s ≤ 8`, the
/// declared exponential cross-check): the member count; for every position `k`, `|X_k|` is the
/// number of distinct absolute lifts and obeys `|X_k| ≤ min(2^(slips before k), k(D − 1) + 1)`;
/// each coordinate's distinct readings (never pooled across positions) and distinct windings equal
/// the receipt's; the diameter of the full class tuples equals the maximum of the coordinates'
/// diameters and equals the decoder's. The transition work is `Σ_(k<n) |X_k||F_k|`, counted.
#[test]
fn the_family_diameter_is_the_maximum_over_its_coordinates_and_the_supports_are_exact() {
    for index in 0..CHARTS.len() {
        let setting = Setting::build(index);
        let (transport, receiver) = (&setting.transport, setting.receiver());
        let decoder = decoder(&setting);
        let period = setting.helix.period();
        let (mut enumerated, mut widest_seen, mut work) = (0usize, Rat::zero(), 0u64);
        for run in runs(index) {
            let case = &run.case;
            let (key, length) = (case.duplex.key(), case.duplex.len());
            let receipt = run.free.receipt();
            let (slipped, admitted) = decoder
                .factors(&case.strand, &case.partner, Template::Unmarked)
                .unwrap();
            let words = enumerate(&admitted);
            enumerated += words.len();
            assert_eq!(BigUint::from(words.len()), receipt.members);
            let lifts: Vec<Vec<u64>> = words
                .iter()
                .map(|word| transport.lifts(key, word).unwrap())
                .collect();
            let classes: Vec<ReceiverClass> = lifts
                .iter()
                .map(|lifts| receiver.class(lifts).unwrap())
                .collect();
            let mut transitions = 0u64;
            for k in 0..=length {
                let mut at: Vec<u64> = lifts.iter().map(|lifts| lifts[k]).collect();
                at.sort_unstable();
                at.dedup();
                assert_eq!(at.len(), receipt.reached[k]);
                assert_eq!(receipt.supported[k], receipt.reached[k]);
                let slips_before = slipped.iter().filter(|&&j| j < k).count();
                assert!(at.len() <= 1usize << slips_before);
                assert!((at.len() as u64) <= (k as u64) * (period - 1) + 1);
                if k < length {
                    transitions += at.len() as u64 * admitted[k].len() as u64;
                }
                let mut readings: Vec<&Vec<Rat>> = Vec::new();
                for class in &classes {
                    if !readings.contains(&&class.readings()[k]) {
                        readings.push(&class.readings()[k]);
                    }
                }
                assert_eq!(readings.len(), receipt.distinct[k]);
            }
            assert_eq!(receipt.forward, transitions);
            assert_eq!(receipt.backward, 0);
            work += transitions;
            let mut windings: Vec<u64> = classes.iter().map(ReceiverClass::winding).collect();
            windings.sort_unstable();
            windings.dedup();
            assert_eq!(windings.len(), receipt.distinct[length + 1]);
            let mut by_tuple = Rat::zero();
            let mut by_coordinate = vec![Rat::zero(); length + 2];
            for i in 0..classes.len() {
                for j in (i + 1)..classes.len() {
                    let tuple = separation(&classes[i], &classes[j]);
                    if tuple > by_tuple {
                        by_tuple = tuple;
                    }
                    for (coordinate, widest) in by_coordinate.iter_mut().enumerate() {
                        let here = separation_at(&classes[i], &classes[j], coordinate);
                        if here > *widest {
                            *widest = here;
                        }
                    }
                }
            }
            let maximum = by_coordinate.iter().fold(Rat::zero(), |widest, d| {
                if *d > widest { d.clone() } else { widest }
            });
            assert_eq!(by_tuple, maximum);
            assert_eq!(by_tuple, receipt.diameter);
            assert_eq!(
                receipt.diameter.is_zero(),
                matches!(run.free, Decoded::Released { .. })
            );
            assert_eq!(
                receipt.diameter.is_zero(),
                receipt.distinct.iter().all(|&d| d == 1)
            );
            if by_tuple > widest_seen {
                widest_seen = by_tuple;
            }
        }
        eprintln!(
            "helical-duplex (f) diameter equation: {} families enumerated completely ({enumerated} members in all); \
             |X_k| = distinct lifts and within min(2^slips, k(D-1)+1); distinct readings per coordinate and \
             windings equal; tuple diameter = max over coordinates = the decoder's in all; widest diameter seen={widest_seen}; \
             forward transitions Σ|X_k||F_k| = {work}",
            runs(index).len()
        );
    }
}

/// [proved-derived; implemented-exact] **Witnesses are actual members that attain the diameter.**
/// For every held family: each witness has the full length, every letter lies in its local factor,
/// its lifts are the transport's stepping of its letters, its class is the receiver's reading of
/// them, the two classes differ, and their full-tuple separation equals the family diameter, with
/// the stated coordinate attaining it.
#[test]
fn the_held_witnesses_are_actual_members_that_attain_the_diameter() {
    for index in 0..CHARTS.len() {
        let setting = Setting::build(index);
        let (transport, receiver) = (&setting.transport, setting.receiver());
        let decoder = decoder(&setting);
        let mut witnessed = 0usize;
        for run in runs(index) {
            let Decoded::Held { held, receipt } = &run.free else {
                continue;
            };
            let case = &run.case;
            let (key, length) = (case.duplex.key(), case.duplex.len());
            let (_, admitted) = decoder
                .factors(&case.strand, &case.partner, Template::Unmarked)
                .unwrap();
            for (member, class) in held.witnesses.iter().zip(&held.classes) {
                assert_eq!(member.letters.len(), length);
                assert_eq!(member.lifts.len(), length + 1);
                for k in 0..length {
                    assert!(admitted[k].contains(&member.letters[k]));
                }
                assert_eq!(member.lifts, transport.lifts(key, &member.letters).unwrap());
                assert_eq!(*class, receiver.class(&member.lifts).unwrap());
            }
            assert_ne!(held.witnesses[0], held.witnesses[1]);
            assert_ne!(held.classes[0], held.classes[1]);
            let (first, second) = (&held.classes[0], &held.classes[1]);
            assert_eq!(separation(first, second), receipt.diameter);
            assert_eq!(
                separation_at(first, second, held.coordinate),
                receipt.diameter
            );
            assert!(held.coordinate <= length + 1);
            witnessed += 1;
        }
        eprintln!(
            "helical-duplex (f) witnesses: {witnessed} held families, each with two actual full-length members \
             (letters in their local factors, lifts and classes recomputed), distinct classes, attaining the \
             family diameter at the stated coordinate"
        );
    }
}

/// [proved-derived; implemented-exact] **The supports keep the carry.** A handcrafted transport on
/// the helix `(3, 4)` with advances `(9, 4, 10, 3)`, generating `ℤ/12`, and two slipped contacts
/// whose candidate advances differ by `5` and `7` (summing to `D = 12`): two lifts of one phase and
/// different windings (`19` and `7`) are different supported states; the class reads the winding,
/// so lifts `[0, 9, 19]` and `[0, 9, 7]` agree at every position and differ at the winding
/// coordinate only; and the free family holds `1, 2, 4` states with `1, 2, 3` distinct readings and
/// `2` distinct windings (a support reduced modulo `D` would hold three states and one winding).
/// Release never discards the carry.
#[test]
fn the_supports_keep_the_carry_and_the_class_reads_the_winding() {
    let helix = CarryHelix::new(vec![3, 4]).unwrap();
    let transport = LocatedTransport::new(
        helix,
        vec![9, 4, 10, 3],
        vec![Some(0), Some(3), Some(2), Some(1)],
    )
    .unwrap();
    let pairing = Pairing::new(vec![1, 0, 3, 2]).unwrap();
    let receiver = Receiver::found(&transport, &[0]).unwrap();
    assert_eq!(receiver.encoding().reached(), 12);
    let decoder = Decoder::new(&receiver, &transport, &pairing).unwrap();

    let (same, shifted) = (
        receiver.class(&[0, 9, 19]).unwrap(),
        receiver.class(&[0, 9, 7]).unwrap(),
    );
    assert_eq!(same.readings(), shifted.readings());
    assert_ne!(same.winding(), shifted.winding());
    assert_eq!(same.first_difference(&shifted), Some(3));

    let (strand, partner) = ([0usize, 2], [2usize, 0]);
    let decoded = decoder
        .decode(0, &strand, &partner, Template::Unmarked, Fit::Free)
        .unwrap();
    let receipt = decoded.receipt();
    assert_eq!(receipt.slipped, vec![0, 1]);
    assert_eq!(receipt.members, BigUint::from(4u32));
    assert_eq!(receipt.reached, vec![1, 2, 4]);
    assert_eq!(receipt.supported, vec![1, 2, 4]);
    assert_eq!(receipt.distinct, vec![1, 2, 3, 2]);
    // X_0 has one state and F_0 two letters, X_1 two states and F_1 two letters.
    assert_eq!(receipt.forward, 2 + 4);
    assert!(matches!(decoded, Decoded::Held { .. }));
    for k in 0..3usize {
        assert!((receipt.reached[k] as u64) <= (k as u64) * 11 + 1);
    }
    let (_, admitted) = decoder
        .factors(&strand, &partner, Template::Unmarked)
        .unwrap();
    let support = decoder.support(0, &admitted, Fit::Free).unwrap();
    let mut lifts: Vec<u64> = support.levels[2]
        .nodes
        .iter()
        .map(|node| node.lift)
        .collect();
    lifts.sort_unstable();
    assert_eq!(lifts, vec![7, 12, 14, 19]);
    eprintln!(
        "helical-duplex carry: supports X_0, X_1, X_2 hold {:?} states; lifts of X_2 = {lifts:?} (19 and 7 are one \
         phase, two windings); distinct readings per coordinate {:?}, family diameter={}",
        receipt.reached, receipt.distinct, receipt.diameter
    );
}

/// [proved-derived; implemented-exact] **Every supported state extends to an actual family
/// member.** The equation `diameter = max over coordinates` rests on it. For every state of every
/// support of every damaged duplex, in the free family and in the fit-constrained one: the member
/// through it has the full length, passes through the state, takes every letter from its local
/// factor, steps by the transport, and in the fit-constrained family is the transport's own
/// passage. (The states that died in the backward pass extend to none: the empty-family test.)
#[test]
fn every_supported_state_extends_to_an_actual_member() {
    for index in 0..CHARTS.len() {
        let setting = Setting::build(index);
        let transport = &setting.transport;
        let decoder = decoder(&setting);
        let mut states = 0usize;
        for run in runs(index) {
            let case = &run.case;
            let (key, length) = (case.duplex.key(), case.duplex.len());
            let (_, admitted) = decoder
                .factors(&case.strand, &case.partner, Template::Unmarked)
                .unwrap();
            for fit in [Fit::Free, Fit::Transport] {
                let support = decoder.support(key, &admitted, fit).unwrap();
                for (level, here) in support.levels.iter().enumerate() {
                    for (at, node) in here.nodes.iter().enumerate() {
                        assert!(node.alive);
                        let member = decoder.member(&support, &admitted, fit, level, at).unwrap();
                        assert_eq!(member.letters.len(), length);
                        assert_eq!(member.lifts.len(), length + 1);
                        assert_eq!(member.lifts[level], node.lift);
                        for k in 0..length {
                            assert!(admitted[k].contains(&member.letters[k]));
                        }
                        assert_eq!(member.lifts, transport.lifts(key, &member.letters).unwrap());
                        if fit == Fit::Transport {
                            assert_eq!(
                                transport.regenerate(key, length),
                                Some(member.letters.clone())
                            );
                        }
                        states += 1;
                    }
                }
            }
        }
        eprintln!(
            "helical-duplex (f) complete support: {states} supported states over {} damaged duplexes, in the free \
             and the fit-constrained family, each extended to an actual full-length member through it",
            runs(index).len()
        );
    }
}

// -------------------------------------------------------------------------------------------
// templates, the fit-constrained family and the empty case

/// [proved-derived; implemented-exact] **A template frame makes the repair unique.** Marking the
/// intact side (the partner when the strand was damaged, the strand when the partner was) collapses
/// every slipped factor: one member, released, and the round trip holds: the released class is the
/// truth's.
#[test]
fn a_template_frame_collapses_each_slipped_factor_and_the_round_trip_holds() {
    for index in 0..CHARTS.len() {
        let setting = Setting::build(index);
        let decoder = decoder(&setting);
        let mut unique = 0usize;
        for run in runs(index) {
            let case = &run.case;
            let template = match case.side {
                Side::Strand => Template::Partner,
                Side::Partner => Template::Strand,
            };
            let decoded = decoder
                .decode(
                    case.duplex.key(),
                    &case.strand,
                    &case.partner,
                    template,
                    Fit::Free,
                )
                .unwrap();
            let Decoded::Released { class, receipt } = &decoded else {
                panic!("a marked template leaves one member and releases");
            };
            assert_eq!(*class, run.truth);
            assert_eq!(receipt.members, BigUint::one());
            assert_eq!(receipt.reached, vec![1; case.duplex.len() + 1]);
            assert_eq!(receipt.forward, case.duplex.len() as u64);
            unique += 1;
        }
        eprintln!(
            "helical-duplex (f) template: {unique} damaged duplexes, each repaired to one member by marking the \
             intact side; released class equals the truth's in all"
        );
    }
}

/// [proved-derived; implemented-exact] **The fit-constrained family, and how often the transport
/// alone resolves the side.** With the key and the transport, a member must be a passage: the only
/// passage from the key is the truth, which is in the family on the covered channel, so the family
/// is that one word and is released with the truth's class. Pinned against the free family
/// filtered by the transport's own `regenerate`, and the added cost is a backward sweep equal to
/// the forward one: `Σ|X_k||F_k| = n + s`.
#[test]
fn the_transport_alone_resolves_the_side_when_the_key_is_known() {
    for index in 0..CHARTS.len() {
        let setting = Setting::build(index);
        let (transport, receiver) = (&setting.transport, setting.receiver());
        let decoder = decoder(&setting);
        let (mut held_free, mut resolved, mut resolved_of_held) = (0usize, 0usize, 0usize);
        for run in runs(index) {
            let case = &run.case;
            let (key, length) = (case.duplex.key(), case.duplex.len());
            let decoded = decoder
                .decode(
                    key,
                    &case.strand,
                    &case.partner,
                    Template::Unmarked,
                    Fit::Transport,
                )
                .unwrap();
            let Decoded::Released { class, receipt } = &decoded else {
                panic!("the transport leaves the truth alone in the family");
            };
            assert_eq!(*class, run.truth);
            assert_eq!(receipt.members, BigUint::one());
            assert_eq!(receipt.reached, vec![1; length + 1]);
            assert_eq!(receipt.supported, vec![1; length + 1]);
            let slips = receipt.slipped.len();
            assert_eq!(receipt.forward, (length + slips) as u64);
            assert_eq!(receipt.backward, receipt.forward);
            let (_, admitted) = decoder
                .factors(&case.strand, &case.partner, Template::Unmarked)
                .unwrap();
            let fitting: Vec<Vec<usize>> = enumerate(&admitted)
                .into_iter()
                .filter(|word| {
                    transport.regenerate(key, length).as_deref() == Some(word.as_slice())
                })
                .collect();
            assert_eq!(fitting, vec![case.duplex.strand().to_vec()]);
            assert_eq!(*class, receiver.class(case.duplex.lifts()).unwrap());
            resolved += 1;
            if matches!(run.free, Decoded::Held { .. }) {
                held_free += 1;
                resolved_of_held += 1;
            }
        }
        eprintln!(
            "helical-duplex (g) fit-constrained: the transport alone resolves {resolved} of {} damaged duplexes \
             (including {resolved_of_held} of the {held_free} held by the free family), each to the truth's class \
             with one member; backward sweep = forward sweep = n + s transitions",
            runs(index).len()
        );
    }
}

/// [proved-derived; implemented-exact] **An empty fit-constrained family is never released.** It
/// is the typed defect `NoCompatibleSource` naming the slipped contacts, and no witness is owed.
/// On the handcrafted transport (advances `(9, 4, 10, 3)`, labels `(0, 3, 2, 1)`) the supports die
/// exactly where the transport admits no candidate (`1, 1, 0` states reached; none supported; four
/// transitions each way), and the states that died extend to no member. On the charts: a
/// coordinated complementary change slips nothing yet its one letter cannot fit, so the family
/// empties at the substituted position and the defect names no slipped contact; a contact changed
/// on both strands, not complementarily, slips with two candidates that both miss the transport,
/// and the defect names it. The free decoder still releases or holds there (the truth is not in
/// the family: outside the covered channel).
#[test]
fn an_empty_fit_constrained_family_is_the_typed_no_compatible_source_defect() {
    let helix = CarryHelix::new(vec![3, 4]).unwrap();
    let crafted = LocatedTransport::new(
        helix,
        vec![9, 4, 10, 3],
        vec![Some(0), Some(3), Some(2), Some(1)],
    )
    .unwrap();
    let crafted_pairing = Pairing::new(vec![1, 0, 3, 2]).unwrap();
    let crafted_receiver = Receiver::found(&crafted, &[0]).unwrap();
    let crafted_decoder = Decoder::new(&crafted_receiver, &crafted, &crafted_pairing).unwrap();
    let (strand, partner) = ([0usize, 2], [2usize, 0]);
    assert_eq!(
        crafted_decoder.decode(0, &strand, &partner, Template::Unmarked, Fit::Transport),
        Err(DuplexDefect::NoCompatibleSource {
            slipped: vec![0, 1]
        })
    );
    let (_, admitted) = crafted_decoder
        .factors(&strand, &partner, Template::Unmarked)
        .unwrap();
    let support = crafted_decoder
        .support(0, &admitted, Fit::Transport)
        .unwrap();
    let reached: Vec<usize> = support
        .levels
        .iter()
        .map(|level| level.nodes.len())
        .collect();
    let supported: Vec<usize> = support
        .levels
        .iter()
        .map(|level| level.nodes.iter().filter(|node| node.alive).count())
        .collect();
    assert_eq!(reached, vec![1, 1, 0]);
    assert_eq!(supported, vec![0, 0, 0]);
    assert_eq!((support.forward, support.backward), (4, 4));
    // An unsupported state extends to no member: the states that died are exactly those with no
    // supported extension.
    assert_eq!(
        crafted_decoder.member(&support, &admitted, Fit::Transport, 0, 0),
        Err(DuplexDefect::Unextendable { level: 0 })
    );
    assert_eq!(
        crafted_decoder.member(&support, &admitted, Fit::Transport, 1, 0),
        Err(DuplexDefect::Unextendable { level: 1 })
    );
    assert!(
        crafted_decoder
            .decode(0, &strand, &partner, Template::Unmarked, Fit::Free)
            .is_ok()
    );

    let mismatched = Pairing::new(vec![1, 0]).unwrap();
    assert!(matches!(
        Decoder::new(&crafted_receiver, &crafted, &mismatched),
        Err(DuplexDefect::Compression(CompressionError::Extent { .. }))
    ));
    let other = LocatedTransport::new(
        CarryHelix::new(vec![5, 4]).unwrap(),
        vec![1, 2, 3, 4],
        (0..4usize).map(Some).collect(),
    )
    .unwrap();
    assert!(matches!(
        Decoder::new(&crafted_receiver, &other, &crafted_pairing),
        Err(DuplexDefect::Declared { .. })
    ));

    for setting in settings() {
        let decoder = decoder(&setting);
        let (transport, pairing) = (&setting.transport, &setting.pairing);
        let classes = pairing.classes();
        let mut draw = Draw::new(ACCEPTANCE_SEED + ((setting.index as u64) << 8) + 4);
        let (mut coordinated, mut both) = (0usize, 0usize);
        for &key in &acceptance_keys(&setting, 4) {
            for &length in &[12usize, 24] {
                let word = setting.terrain.passage(key, length);
                let duplex = Duplex::place(transport, pairing, key, &word).unwrap();
                for _ in 0..3 {
                    let k = draw.below(length);
                    let letter = (word[k] + 1 + draw.below(classes - 1)) % classes;
                    let damage = Damage::coordinated(pairing, &[(k, letter)]).unwrap();
                    let (strand, partner) = damage.apply(&duplex, pairing).unwrap();
                    assert_eq!(
                        decoder.decode(key, &strand, &partner, Template::Unmarked, Fit::Transport),
                        Err(DuplexDefect::NoCompatibleSource {
                            slipped: Vec::new()
                        })
                    );
                    let (_, admitted) = decoder
                        .factors(&strand, &partner, Template::Unmarked)
                        .unwrap();
                    let support = decoder.support(key, &admitted, Fit::Transport).unwrap();
                    let reached: Vec<usize> = support
                        .levels
                        .iter()
                        .map(|level| level.nodes.len())
                        .collect();
                    let mut expected = vec![1usize; k + 1];
                    expected.extend(vec![0usize; length - k]);
                    assert_eq!(reached, expected);
                    assert!(
                        support
                            .levels
                            .iter()
                            .all(|level| level.nodes.iter().all(|node| !node.alive))
                    );
                    assert_eq!(support.forward, k as u64 + 1);
                    assert_eq!(support.backward, k as u64 + 1);
                    coordinated += 1;

                    let a = (word[k] + 1 + draw.below(classes - 1)) % classes;
                    let c = loop {
                        let c = draw.below(classes);
                        if c != word[k] && c != a {
                            break c;
                        }
                    };
                    let both_sides = Damage::new(vec![(k, a)], vec![(k, pairing.pair(c).unwrap())]);
                    let (strand, partner) = both_sides.apply(&duplex, pairing).unwrap();
                    assert_eq!(pairing.slipped(&strand, &partner).unwrap(), vec![k]);
                    assert_eq!(
                        decoder.decode(key, &strand, &partner, Template::Unmarked, Fit::Transport),
                        Err(DuplexDefect::NoCompatibleSource { slipped: vec![k] })
                    );
                    let (_, admitted) = decoder
                        .factors(&strand, &partner, Template::Unmarked)
                        .unwrap();
                    assert!(!admitted[k].contains(&word[k]));
                    let free = decoder
                        .decode(key, &strand, &partner, Template::Unmarked, Fit::Free)
                        .unwrap();
                    assert_eq!(free.receipt().members, BigUint::from(2u32));
                    both += 1;
                }
            }
        }
        eprintln!(
            "helical-duplex (g) empty family: {coordinated} coordinated and {both} two-sided changes on unseen keys, \
             each fit-constrained decoding the typed NoCompatibleSource defect (slipped contacts named: none and \
             one), nothing released; the supports reach 1 state up to the substituted position and 0 after"
        );
    }
}

// -------------------------------------------------------------------------------------------
// coverage and the residual

/// [agent-inferred; implemented-exact] **Coordinated changes are outside the covered channel, and
/// are counted against the truth.** A coordinated complementary substitution slips nothing (the
/// pairing is blind to it), its local factor is the singleton observed letter, so the free decoder
/// releases the observed word's class with one member, the truth is not in the family, and the
/// online decoder gives no truth guarantee. The harness counts it against the known truth: absorbed
/// when the class equals the truth's, residual when it differs and was released anyway. The shift
/// law predicts both without the decoder: absorbed exactly when every substituted position's two
/// advances are equal, and the first coordinate that separates a residual is the position after the
/// first substitution with unequal advances. Exhaustive over every single substitution of two
/// words, and drawn for two to three substitutions.
#[test]
fn coordinated_substitutions_are_outside_the_coverage_and_counted_against_the_truth() {
    for setting in settings() {
        let (transport, pairing, receiver) =
            (&setting.transport, &setting.pairing, setting.receiver());
        let decoder = decoder(&setting);
        let classes = pairing.classes();
        let keys = acceptance_keys(&setting, ACCEPTANCE_KEYS);
        let (mut single, mut multiple) = (0usize, 0usize);
        let (mut absorbed, mut residual, mut slips) = (0usize, 0usize, 0usize);
        for &key in &keys[..2] {
            let word = setting.terrain.passage(key, 24);
            let duplex = Duplex::place(transport, pairing, key, &word).unwrap();
            let truth = receiver.class(duplex.lifts()).unwrap();
            for k in 0..word.len() {
                for letter in 0..classes {
                    if letter == word[k] {
                        continue;
                    }
                    let damage = Damage::coordinated(pairing, &[(k, letter)]).unwrap();
                    let (strand, partner) = damage.apply(&duplex, pairing).unwrap();
                    slips += pairing.slipped(&strand, &partner).unwrap().len();
                    slips += setting
                        .contacts
                        .slipped(pairing, &strand, &partner)
                        .unwrap()
                        .len();
                    assert!(matches!(
                        Duplex::place(transport, pairing, key, &strand),
                        Err(DuplexDefect::Unfit { .. })
                    ));
                    let decoded = decoder
                        .decode(key, &strand, &partner, Template::Unmarked, Fit::Free)
                        .unwrap();
                    let Decoded::Released { class, receipt } = &decoded else {
                        panic!("no slip leaves a singleton family, which is released");
                    };
                    assert_eq!(receipt.members, BigUint::one());
                    assert_ne!(strand, word);
                    assert_eq!(
                        *class,
                        receiver
                            .class(&transport.lifts(key, &strand).unwrap())
                            .unwrap()
                    );
                    let equal = carried_shift(transport, word[k], letter).unwrap() == 0;
                    match Absorption::between(&truth, class) {
                        Absorption::Absorbed => {
                            assert!(equal);
                            assert_eq!(*class, truth);
                            absorbed += 1;
                        }
                        Absorption::Residual { at } => {
                            assert!(!equal);
                            assert_eq!(at, k + 1);
                            assert_ne!(*class, truth);
                            residual += 1;
                        }
                    }
                    single += 1;
                }
            }
        }
        let mut draw = Draw::new(ACCEPTANCE_SEED + ((setting.index as u64) << 8) + 3);
        for _ in 0..24 {
            let key = keys[draw.below(keys.len())];
            let length = DAMAGE_LENGTHS[draw.below(DAMAGE_LENGTHS.len())];
            let word = setting.terrain.passage(key, length);
            let duplex = Duplex::place(transport, pairing, key, &word).unwrap();
            let truth = receiver.class(duplex.lifts()).unwrap();
            let count = 2 + draw.below(2);
            let mut substitutions: Vec<(usize, usize)> = Vec::new();
            while substitutions.len() < count {
                let k = draw.below(length);
                if substitutions.iter().any(|&(j, _)| j == k) {
                    continue;
                }
                substitutions.push((k, (word[k] + 1 + draw.below(classes - 1)) % classes));
            }
            let damage = Damage::coordinated(pairing, &substitutions).unwrap();
            let (strand, partner) = damage.apply(&duplex, pairing).unwrap();
            slips += pairing.slipped(&strand, &partner).unwrap().len();
            let decoded = decoder
                .decode(key, &strand, &partner, Template::Unmarked, Fit::Free)
                .unwrap();
            let Decoded::Released { class, receipt } = &decoded else {
                panic!("no slip leaves a singleton family, which is released");
            };
            assert_eq!(receipt.members, BigUint::one());
            let unequal: Vec<usize> = substitutions
                .iter()
                .filter(|&&(k, letter)| carried_shift(transport, word[k], letter).unwrap() != 0)
                .map(|&(k, _)| k)
                .collect();
            match Absorption::between(&truth, class) {
                Absorption::Absorbed => {
                    assert!(unequal.is_empty());
                    absorbed += 1;
                }
                Absorption::Residual { at } => {
                    assert_eq!(Some(at), unequal.iter().min().map(|k| k + 1));
                    residual += 1;
                }
            }
            multiple += 1;
        }
        assert_eq!(slips, 0);
        assert_eq!(absorbed + residual, single + multiple);
        let mut outside = 0usize;
        for &key in &keys[..2] {
            let word = setting.terrain.passage(key, 24);
            let duplex = Duplex::place(transport, pairing, key, &word).unwrap();
            for _ in 0..4 {
                let k = draw.below(24);
                let a = (word[k] + 1 + draw.below(classes - 1)) % classes;
                let c = loop {
                    let c = draw.below(classes);
                    if c != word[k] && c != a {
                        break c;
                    }
                };
                let both_sides = Damage::new(vec![(k, a)], vec![(k, pairing.pair(c).unwrap())]);
                let (strand, partner) = both_sides.apply(&duplex, pairing).unwrap();
                let (slipped, admitted) = decoder
                    .factors(&strand, &partner, Template::Unmarked)
                    .unwrap();
                assert_eq!(slipped, vec![k]);
                assert!(!admitted[k].contains(&word[k]));
                outside += 1;
            }
        }
        eprintln!(
            "helical-duplex (h) coverage: {} coordinated cases ({single} single, exhaustive over two words of 24 and \
             all {} other letters; {multiple} drawn with two or three substitutions): slipped contacts={slips} \
             (the pairing is blind); online released with one member in all; against the known truth \
             absorbed={absorbed} (class equals the truth's) residual={residual} (class differs, released anyway); \
             {outside} contacts changed on both strands, not complementarily, slip with candidates that miss the truth",
            single + multiple,
            classes - 1
        );
    }
}

/// [definition; implemented-exact] **An unreached lift is refused, never substituted.** A
/// receiver opened at one coset of a proper subgroup (advances `2, 4, 6, 8` on the helix `(3, 4)`
/// generate the even lifts) reads the even lifts and refuses the odd ones with
/// `EncodingError::Unreached`; a class reading an odd lift is refused too; and a receiver with no
/// openings is not founded.
#[test]
fn an_unreached_lift_is_refused_and_never_substituted() {
    let transport = LocatedTransport::new(
        CarryHelix::new(vec![3, 4]).unwrap(),
        vec![2, 4, 6, 8],
        (0..4usize).map(Some).collect(),
    )
    .unwrap();
    let receiver = Receiver::found(&transport, &[0]).unwrap();
    assert_eq!(receiver.encoding().reached(), 6);
    assert!(receiver.reading(2).is_ok());
    assert_eq!(
        receiver.reading(1),
        Err(DuplexDefect::Encoding(EncodingError::Unreached))
    );
    assert_eq!(
        receiver.class(&[0, 2, 3]),
        Err(DuplexDefect::Encoding(EncodingError::Unreached))
    );
    assert!(receiver.class(&[0, 2, 14]).is_ok());
    assert!(matches!(
        Receiver::found(&transport, &[]),
        Err(DuplexDefect::Encoding(EncodingError::Chart { .. }))
    ));
    eprintln!(
        "helical-duplex unreached: a receiver opened at lift 0 reaches {} of 12 lifts; an odd lift refuses \
         with Unreached, as does a class that reads one",
        receiver.encoding().reached()
    );
}

/// [definition; implemented-exact] **A malformed partner contact is refused before any index
/// arithmetic.** The contact is bounded against the duplex before it is reversed, so even the
/// largest machine index returns the typed `IndexOutside`, never an overflow.
#[test]
fn a_malformed_partner_contact_is_refused_before_any_index_arithmetic() {
    let transport = LocatedTransport::new(
        CarryHelix::new(vec![3, 4]).unwrap(),
        vec![0, 3, 6, 9],
        (0..4usize).map(Some).collect(),
    )
    .unwrap();
    let pairing = Pairing::new(vec![3, 2, 1, 0]).unwrap();
    let strand = transport.regenerate(0, 3).unwrap();
    let duplex = Duplex::place(&transport, &pairing, 0, &strand).unwrap();
    for contact in [3, usize::MAX] {
        assert_eq!(
            Damage::new(Vec::new(), vec![(contact, 0)]).apply(&duplex, &pairing),
            Err(DuplexDefect::Compression(CompressionError::IndexOutside {
                index: contact,
                population: 3,
            }))
        );
    }
    eprintln!(
        "helical-duplex malformed contact: partner contacts 3 and usize::MAX on a duplex of 3 are \
         refused as IndexOutside before any reversal"
    );
}

/// [proved-derived; implemented-exact] **A changed transport on the same helix is refused the
/// founded quotient.** On the helix `(3, 4)` the advances `0, 3, 6, 9` keep the lifts `0` and `1` in
/// one cell under every future, so the founded receiver identifies them. Changing one advance to
/// `2` sends them to the lifts `2` and `3`, which a receiver founded on the changed transport
/// separates. Helix equality does not preserve the quotient, so the decoder binds the producing
/// transport and refuses the changed one.
#[test]
fn a_changed_transport_on_the_same_helix_is_refused_its_founded_quotient() {
    let helix = CarryHelix::new(vec![3, 4]).unwrap();
    let labels: Vec<Option<usize>> = (0..4usize).map(Some).collect();
    let old = LocatedTransport::new(helix.clone(), vec![0, 3, 6, 9], labels.clone()).unwrap();
    let new = LocatedTransport::new(helix, vec![0, 3, 2, 9], labels).unwrap();
    let pairing = Pairing::new(vec![3, 2, 1, 0]).unwrap();
    let founded = Receiver::found(&old, &[0, 1, 2]).unwrap();
    assert_eq!(founded.reading(0).unwrap(), founded.reading(1).unwrap());
    let refounded = Receiver::found(&new, &[0, 1, 2]).unwrap();
    assert_ne!(refounded.reading(0).unwrap(), refounded.reading(1).unwrap());
    assert!(matches!(
        Decoder::new(&founded, &new, &pairing),
        Err(DuplexDefect::Declared { .. })
    ));
    assert!(Decoder::new(&founded, &old, &pairing).is_ok());
    assert!(Decoder::new(&refounded, &new, &pairing).is_ok());
    eprintln!(
        "helical-duplex changed transport: the receiver founded on advances 0, 3, 6, 9 identifies \
         lifts 0 and 1; one advance changed to 2 separates them, and the decoder refuses the changed \
         transport its founded quotient"
    );
}

/// The development and acceptance statement, printed once per chart so that a reader of the
/// receipts sees which seeds are which.
#[test]
fn the_receipts_state_which_seeds_are_development_and_which_are_acceptance() {
    for setting in settings() {
        let receiver = setting.receiver();
        assert_eq!(receiver.encoding().reached() as u64, setting.helix.period());
        let keys = acceptance_keys(&setting, ACCEPTANCE_KEYS);
        eprintln!(
            "helical-duplex setting: {} | DEVELOPMENT: terrain seed={:#x} (scan offset {} of at most {SCAN_CEILING}), \
             advances={:?}, labels={:?}, receiver opened at keys {DEVELOPMENT_KEYS:?}, reached={} of D={}, founded \
             dimension={} | ACCEPTANCE: seed stream={:#x}, keys={keys:?} (disjoint from the openings: {}), \
             lengths {LENGTHS:?}, damaged lengths {DAMAGE_LENGTHS:?}",
            setting.headline(),
            setting.seed,
            setting.scan,
            setting.terrain.advances(),
            setting.terrain.labels(),
            receiver.encoding().reached(),
            setting.helix.period(),
            receiver.encoding().dimension(),
            ACCEPTANCE_SEED + ((setting.index as u64) << 8),
            keys.iter().all(|key| !DEVELOPMENT_KEYS.contains(key)),
        );
        let sample = setting.terrain.passage(keys[0], 24);
        eprintln!(
            "helical-duplex setting: sample strand from acceptance key {}: {} / its partner {}",
            keys[0],
            show(&setting, &sample),
            show(
                &setting,
                &setting.pairing.complement_reverse(&sample).unwrap()
            )
        );
    }
}

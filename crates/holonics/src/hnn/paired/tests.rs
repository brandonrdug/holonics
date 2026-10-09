//! The paired carrier's laws (module header of `hnn::paired`).
//!
//! **Fixtures.** One-ring fields of a declared period, reflection axis, lock and class chart, whose
//! source ring is paired by a declared family or by two roles; a test constitution that holds one
//! source port and is read through `ConstitutionRead`; and one two-ring field read through the real
//! `Constitution` (`Constitution::initial`, then `with_ports` to place a declared port). Every word is
//! drawn from a seeded stream, and every expectation is either a hand-derived literal (pinned with the
//! convention it reads) or computed from the definition in the scatter form `(B v)[2F(i)+r] = v[2i+r]`,
//! independent of the owner's gather form.
//!
//! **Receipts.** Every test prints exact counts with `eprintln!` (run with `--nocapture`): integers
//! only, never a float, a percentage or a decimal.
//!
//! **Cost.** The largest enumerations are the `6⁶` pairing tables of six classes, the `5⁵` reflector
//! tables of five ports and the `5⁵` maps of campaign 1's classes (each a few allocations), and the
//! `4⁰ + … + 4⁵` words over four classes of the last test, each ingested twice; the partner-law test
//! runs 54 words per setting.

use std::collections::{BTreeMap, BTreeSet};

use super::*;
use crate::compression::landmark::context::Landmarks;
use crate::geometry::RatVec3;
use crate::geometry::screw::ScrewGenerator;
use crate::hnn::constitution::{CAMPAIGN_ONE_BUDGET, Constitution, declared_source_port};
use crate::hnn::field::{
    ConstitutionRead, ContactDeclaration, CribDeclaration, FieldDeclaration, RingDeclaration,
};
use crate::hnn::moment::PairPort;
use crate::hnn::tests::support::encoded;
use crate::ratio::{integer, rat};
use crate::receiver::population::PortPopulation;

// -------------------------------------------------------------------------------------------
// the fixtures

/// A seeded stream (SplitMix64): the words and the free halves of the ports.
struct Stream(u64);

impl Stream {
    fn draw(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, bound: usize) -> usize {
        (self.draw() % bound as u64) as usize
    }

    /// A half-integer in `[−2, 2]`.
    fn half(&mut self) -> Rat {
        rat(self.below(9) as i64 - 4, 2)
    }

    fn vector(&mut self, width: usize) -> Vec<Rat> {
        (0..width).map(|_| self.half()).collect()
    }

    fn matrix(&mut self, rows: usize, columns: usize) -> ExactRatMatrix {
        let entries: Vec<Vec<Rat>> = (0..rows).map(|_| self.vector(columns)).collect();
        ExactRatMatrix::shaped(rows, columns, entries).unwrap()
    }

    fn word(&mut self, length: usize, family: &[usize]) -> Vec<usize> {
        (0..length)
            .map(|_| family[self.below(family.len())])
            .collect()
    }
}

/// The reflector `F(p) = axis − p (mod period)`.
fn reflection(period: u64, axis: u64) -> Vec<usize> {
    (0..period)
        .map(|port| ((axis + period - port) % period) as usize)
        .collect()
}

/// A closing ring of `period` nodes on the quarter turns of the unit circle about `e_z`.
fn ring_declaration(period: u64, lock: Vec<u64>, reflector: Vec<usize>) -> RingDeclaration {
    RingDeclaration {
        period,
        screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
        placements: (0..period)
            .map(|node| FieldDeclaration::quarter_turn(node, period))
            .collect(),
        lock,
        reflector,
        admittance: integer(2),
        initial: 0,
    }
}

/// A declared field with no receiver, the lattices by rule, and a population of `2¹⁶` cells.
fn declare(
    rings: Vec<RingDeclaration>,
    contacts: Vec<ContactDeclaration>,
    sources: Vec<usize>,
    alphabet: usize,
    offsets: Vec<usize>,
) -> Field {
    Field::declare(
        FieldDeclaration {
            rings,
            contacts,
            loops: Vec::new(),
            sources,
            offsets,
            alphabet,
            step: integer(1),
            exponent_grain: 1,
            receivers: Vec::new(),
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 16,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap()
}

/// A field of one source ring.
fn field_of(
    period: u64,
    lock: Vec<u64>,
    reflector: Vec<usize>,
    alphabet: usize,
    offsets: Vec<usize>,
) -> Field {
    declare(
        vec![ring_declaration(period, lock, reflector)],
        Vec::new(),
        vec![0],
        alphabet,
        offsets,
    )
}

/// A field of two rings joined by one contact: ring 0 of period 3 with `first_lock`, ring 1 of period
/// 5 holding the four classes, the reflector `p ↦ −p` on both.
fn two_ring_field(sources: Vec<usize>, first_lock: Vec<u64>) -> Field {
    declare(
        vec![
            ring_declaration(3, first_lock, reflection(3, 0)),
            ring_declaration(5, vec![0, 1, 2, 3], reflection(5, 0)),
        ],
        vec![ContactDeclaration {
            from: 0,
            to: 1,
            channel: vec![(0, 0)],
            admittance: integer(2),
            exponent: integer(0),
        }],
        sources,
        4,
        Vec::new(),
    )
}

/// A test constitution that holds one source port (the owner of `Θ` is the learning side's
/// `Constitution`; the real one is read in its own test).
#[derive(Clone)]
struct Medium {
    ring: usize,
    port: ExactRatMatrix,
    empty: ExactRatMatrix,
    standing: Vec<Rat>,
    slices: Vec<(Vec<Rat>, Vec<Rat>)>,
    transport: Rat,
}

impl Medium {
    fn new(ring: usize, port: ExactRatMatrix) -> Self {
        Self {
            ring,
            port,
            empty: ExactRatMatrix::zero(0, 0).unwrap(),
            standing: Vec::new(),
            slices: Vec::new(),
            transport: Rat::one(),
        }
    }

    fn at_modulus(mut self, modulus: Rat) -> Self {
        self.transport = modulus;
        self
    }
}

impl ConstitutionRead for Medium {
    fn standing(&self, _ring: usize) -> &[Rat] {
        &self.standing
    }
    fn passive_factor(&self, _ring: usize) -> &ExactRatMatrix {
        &self.empty
    }
    fn contrast_port(&self, _ring: usize) -> &ExactRatMatrix {
        &self.empty
    }
    fn slices(&self, _ring: usize) -> &[(Vec<Rat>, Vec<Rat>)] {
        &self.slices
    }
    fn source_port(&self, ring: usize) -> Option<&ExactRatMatrix> {
        (ring == self.ring).then_some(&self.port)
    }
    fn pair_port(&self, _ring: usize, _offset: usize) -> Option<&PairPort> {
        None
    }
    fn contact_storage(&self, _contact: usize) -> &ExactRatMatrix {
        &self.empty
    }
    fn contact_stiffness(&self, _contact: usize) -> &ExactRatMatrix {
        &self.empty
    }
    fn contact_dissipation(&self, _contact: usize) -> &ExactRatMatrix {
        &self.empty
    }
    fn receiving_map(&self, _ring: usize) -> Option<&ExactRatMatrix> {
        None
    }
    fn landmarks(&self, _ring: usize) -> Option<&Landmarks> {
        None
    }
    fn population(&self, _ring: usize) -> Option<&PortPopulation> {
        None
    }
    fn transport(&self, _ring: usize) -> Rat {
        self.transport.clone()
    }
}

/// One paired source ring, declared, admitted, with its equivariant port in a test constitution.
struct Setting {
    name: &'static str,
    period: u64,
    field: Field,
    free: ExactRatMatrix,
    carrier: PairedCarrier,
    medium: Medium,
    /// The classes a word may use: those of the family.
    family: Vec<usize>,
}

fn setting(
    name: &'static str,
    period: u64,
    axis: u64,
    alphabet: usize,
    declared: PairingDeclaration,
    lock: Vec<u64>,
    seed: u64,
) -> Setting {
    let field = field_of(period, lock, reflection(period, axis), alphabet, Vec::new());
    let free = Stream(seed).matrix(2 * period as usize, alphabet);
    let port = PairedCarrier::complete_port(&field, 0, &declared, &free).unwrap();
    let carrier = PairedCarrier::admit(&field, 0, &declared, &port).unwrap();
    let family = (0..alphabet)
        .filter(|&class| carrier.sigma().image(class).is_some())
        .collect();
    Setting {
        name,
        period,
        field,
        free,
        carrier,
        medium: Medium::new(0, port),
        family,
    }
}

/// `d = 5`, axis 0 (`p ↦ −p`, campaign 1's reflector), four classes paired `(0 1)(2 3)`, every
/// class fitting the lock.
fn setting_one() -> Setting {
    setting(
        "family (0 1)(2 3), d = 5, axis 0",
        5,
        0,
        4,
        PairingDeclaration::Family {
            table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
        },
        vec![0, 1, 2, 3],
        0x4845_4c49_0002_0001,
    )
}

/// `d = 6`, axis 2, six classes as two roles `{0, 2, 4}` and `{1, 3, 5}`.
fn setting_two() -> Setting {
    setting(
        "roles {0,2,4} / {1,3,5}, d = 6, axis 2",
        6,
        2,
        6,
        PairingDeclaration::Roles {
            first: vec![0, 2, 4],
            second: vec![1, 3, 5],
        },
        vec![0, 1, 2, 3, 4, 5],
        0x4845_4c49_0002_0002,
    )
}

/// `d = 7`, axis 3, two roles `{1}` / `{2}` inside four classes: classes 0 and 3 are outside the
/// family and do not fit the lock.
fn setting_three() -> Setting {
    setting(
        "roles {1} / {2} of four classes, d = 7, axis 3",
        7,
        3,
        4,
        PairingDeclaration::Roles {
            first: vec![1],
            second: vec![2],
        },
        vec![1, 2],
        0x4845_4c49_0002_0003,
    )
}

/// A strand or partner passage: the Current it reached and the moment it counted.
struct Run {
    current: Current,
    moment: SourceMoment,
}

/// Ingest `word` from the lift point `opening`, with `ring` re-keyed to `rekey` first when given.
fn run(field: &Field, ring: usize, opening: &[BigInt], rekey: Option<u64>, word: &[usize]) -> Run {
    let mut current = Current::at(field, opening.to_vec()).unwrap();
    if let Some(phase) = rekey {
        current.rekey(field, ring, phase).unwrap();
    }
    let mut moment = SourceMoment::open(field, &current);
    let mut fed = 0;
    while fed < word.len() {
        fed += moment
            .ingest(field, &mut current, &encoded(field, &word[fed..]))
            .unwrap()
            .cells;
    }
    Run { current, moment }
}

/// `σ̄(u)_k = σ(u_(n−1−k))`, from a table of `σ`.
fn complement_reverse(table: &[Option<usize>], word: &[usize]) -> Vec<usize> {
    word.iter()
        .rev()
        .map(|&class| table[class].unwrap())
        .collect()
}

/// A copy of a matrix with one entry replaced.
fn with_entry(port: &ExactRatMatrix, row: usize, column: usize, value: Rat) -> ExactRatMatrix {
    let mut rows = port.to_rows();
    rows[row][column] = value;
    ExactRatMatrix::shaped(port.rows(), port.columns(), rows).unwrap()
}

/// The first `(column, partner, row)` at which `B E e_column` differs from `E e_partner`, computed
/// from the definition in the scatter form `(B v)[2F(i) + r] = v[2i + r]`, classes in ascending order.
fn first_failure(
    port: &ExactRatMatrix,
    reflector: &[usize],
    table: &[Option<usize>],
) -> Option<(usize, usize, usize)> {
    for (class, partner) in table.iter().enumerate() {
        let Some(partner) = *partner else {
            continue;
        };
        let mut lifted = vec![Rat::zero(); port.rows()];
        for (node, &target) in reflector.iter().enumerate() {
            for coordinate in 0..2 {
                lifted[2 * target + coordinate] =
                    port.get(2 * node + coordinate, class).unwrap().clone();
            }
        }
        for (row, entry) in lifted.iter().enumerate() {
            if entry != port.get(row, partner).unwrap() {
                return Some((class, partner, row));
            }
        }
    }
    None
}

fn halves(values: &[i64]) -> Vec<Rat> {
    values.iter().map(|&value| rat(value, 2)).collect()
}

fn dyad(defect: PairedDefect) -> DyadRefusal {
    match defect {
        PairedDefect::Dyad(refusal) => refusal,
        other => panic!("not a dyad refusal: {other:?}"),
    }
}

// -------------------------------------------------------------------------------------------
// the reflector and the pairing

/// [proved-derived] The dihedral relation `F(F(i) + 1) = i − 1` holds exactly for the reflections
/// `i ↦ c − i`: of the `d^d` tables of `d` ports, `d` pass, for every `d` from 2 to 5. The named
/// defects are the first failing port.
#[test]
fn a_reflector_is_dihedral_exactly_when_it_is_c_minus_i() {
    let mut tables = 0usize;
    let mut passing = 0usize;
    for ports in 2..=5usize {
        let mut reflections = 0usize;
        for index in 0..ports.pow(ports as u32) {
            let mut rest = index;
            let images: Vec<usize> = (0..ports)
                .map(|_| {
                    let digit = rest % ports;
                    rest /= ports;
                    digit
                })
                .collect();
            let reflection = (0..ports).any(|axis| {
                images
                    .iter()
                    .enumerate()
                    .all(|(port, &image)| image == (axis + ports - port) % ports)
            });
            assert_eq!(
                reflector_defect(&images).is_none(),
                reflection,
                "{images:?}"
            );
            reflections += usize::from(reflection);
            tables += 1;
        }
        assert_eq!(reflections, ports, "the reflections of the {ports}-gon");
        passing += reflections;
    }
    eprintln!("reflector tables {tables}, dihedral {passing}");
    // The skew involution of period 4 that Ring::declare accepts: the relation fails at port 0.
    assert_eq!(
        reflector_defect(&[1, 0, 2, 3]),
        Some(ReflectorDefect::NotDihedral {
            port: 0,
            found: 2,
            expected: 3
        })
    );
    // A 3-cycle is no involution; an image past the ports is no map of them.
    assert_eq!(
        reflector_defect(&[1, 2, 0]),
        Some(ReflectorDefect::NotInvolution {
            port: 0,
            returns: 2
        })
    );
    assert_eq!(
        reflector_defect(&[0, 5]),
        Some(ReflectorDefect::Outside {
            port: 1,
            image: 5,
            ports: 2
        })
    );
    // Campaign 1's reflector p ↦ −p is the reflection with c = 0.
    assert_eq!(reflector_defect(&[0, 4, 3, 2, 1]), None);
}

/// [proved-derived] A pairing is a fixed-point-free involution of an even family or the free swap
/// of two roles. The pairings of `m` classes, counted over every map: 0, 1, 0, 3, 0, 15 for
/// `m = 1 … 6` (the perfect matchings, `(m − 1)!!` for even `m`, none for odd; Lean
/// `card_free_involutions_fin4` for `m = 4`), and the native consumer's `Pairing::new`
/// (`compression::keys::duplex`) accepts exactly the same tables and reads the same `σ`. Every other
/// declaration is refused, typed.
#[test]
fn the_pairing_is_typed_and_a_fixed_point_free_involution_needs_an_even_family() {
    let mut counted = Vec::new();
    for (classes, expected) in [(1usize, 0usize), (2, 1), (3, 0), (4, 3), (5, 0), (6, 15)] {
        let mut resolved = 0usize;
        for index in 0..classes.pow(classes as u32) {
            let mut rest = index;
            let table: Vec<(usize, usize)> = (0..classes)
                .map(|class| {
                    let image = rest % classes;
                    rest /= classes;
                    (class, image)
                })
                .collect();
            let matching = table
                .iter()
                .all(|&(class, image)| image != class && table[image].1 == class);
            let declared = PairingDeclaration::Family {
                table: table.clone(),
            };
            // The native consumer's pairing (compression::keys::duplex) accepts exactly the tables
            // this declaration resolves, and reads the same σ.
            let native = crate::compression::keys::duplex::Pairing::new(
                table.iter().map(|&(_, image)| image).collect(),
            );
            match declared.resolve(classes) {
                Ok(sigma) => {
                    assert!(matching, "{table:?}");
                    assert_eq!(sigma.kind(), PairingKind::Family);
                    assert_eq!(sigma.classes(), classes);
                    let native = native.expect("the native pairing accepts the same table");
                    for class in 0..classes {
                        assert_eq!(native.pair(class), sigma.image(class));
                    }
                    resolved += 1;
                }
                Err(defect) => {
                    assert!(!matching, "{table:?}: {defect}");
                    assert!(native.is_err(), "{table:?}");
                }
            }
        }
        assert_eq!(resolved, expected, "{classes} classes");
        counted.push((classes, resolved));
    }
    eprintln!("pairings by class count {counted:?}");

    let family = |table: Vec<(usize, usize)>, alphabet: usize| {
        PairingDeclaration::Family { table }
            .resolve(alphabet)
            .unwrap_err()
    };
    assert_eq!(family(vec![], 4), PairingDefect::Empty);
    assert_eq!(
        family(vec![(0, 1), (1, 4)], 4),
        PairingDefect::ClassOutside {
            class: 4,
            alphabet: 4
        }
    );
    assert_eq!(
        family(vec![(0, 1), (0, 1)], 4),
        PairingDefect::ClassRepeated { class: 0 }
    );
    assert_eq!(
        family(vec![(0, 1), (1, 0), (2, 3)], 4),
        PairingDefect::OddFamily { classes: 3 }
    );
    assert_eq!(
        family(vec![(0, 1), (1, 0), (2, 3), (3, 5)], 6),
        PairingDefect::ImageOutside { class: 3, image: 5 }
    );
    assert_eq!(
        family(vec![(0, 1), (1, 0), (2, 2), (3, 3)], 4),
        PairingDefect::FixedClass { class: 2 }
    );
    assert_eq!(
        family(vec![(0, 1), (1, 2), (2, 3), (3, 0)], 4),
        PairingDefect::NotInvolution { class: 0 }
    );

    let roles = |first: Vec<usize>, second: Vec<usize>, alphabet: usize| {
        PairingDeclaration::Roles { first, second }
            .resolve(alphabet)
            .unwrap_err()
    };
    assert_eq!(
        roles(vec![0, 1], vec![2], 4),
        PairingDefect::RoleLengths {
            first: 2,
            second: 1
        }
    );
    assert_eq!(roles(vec![], vec![], 4), PairingDefect::Empty);
    assert_eq!(
        roles(vec![0, 1], vec![1, 2], 4),
        PairingDefect::ClassRepeated { class: 1 }
    );
    assert_eq!(
        roles(vec![0, 4], vec![1, 2], 4),
        PairingDefect::ClassOutside {
            class: 4,
            alphabet: 4
        }
    );

    // An even sub-family of a five-class chart is a family; two roles are a pairing; the classes
    // outside either have no image.
    let sub = PairingDeclaration::Family {
        table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
    }
    .resolve(5)
    .unwrap();
    assert_eq!(
        sub.table().to_vec(),
        vec![Some(1), Some(0), Some(3), Some(2), None]
    );
    assert_eq!(sub.pairs().to_vec(), vec![(0, 1), (2, 3)]);
    let swap = PairingDeclaration::Roles {
        first: vec![0, 1],
        second: vec![2, 3],
    }
    .resolve(5)
    .unwrap();
    assert_eq!(swap.kind(), PairingKind::Roles);
    assert_eq!(
        swap.table().to_vec(),
        vec![Some(2), Some(3), Some(0), Some(1), None]
    );
    assert_eq!(swap.pairs().to_vec(), vec![(0, 2), (1, 3)]);
    assert_eq!(swap.image(4), None);
    assert_eq!(swap.image(9), None);

    // The native duplex's pairing (the bit complement of a base-four digit) declares the same σ here.
    let native = Pairing::new(vec![3, 2, 1, 0]).unwrap();
    let complement = PairingDeclaration::of_duplex(&native).resolve(4).unwrap();
    assert_eq!(
        complement.table().to_vec(),
        vec![Some(3), Some(2), Some(1), Some(0)]
    );
    assert_eq!(complement.pairs().to_vec(), vec![(0, 3), (1, 2)]);
}

// -------------------------------------------------------------------------------------------
// the admission

/// Campaign 1 declares five classes, so no pairing exists on its alphabet: every one of the `5⁵`
/// maps of its classes is refused as an odd family, none being a fixed-point-free involution. The
/// alphabet is not changed to fit. An even sub-family of the five classes admits once its port is
/// completed, and the field's lock `{0}` then refuses the read at the first class it does not tick.
#[test]
fn campaign_ones_five_classes_admit_no_pairing_and_the_alphabet_is_not_changed_to_fit() {
    let field = Field::declare(FieldDeclaration::campaign_one(1 << 17)).unwrap();
    assert_eq!(field.alphabet(), 5);
    let founded = declared_source_port(&field, 0).unwrap().unwrap();
    let (mut refused, mut matchings) = (0usize, 0usize);
    for index in 0..5usize.pow(5) {
        let mut rest = index;
        let table: Vec<(usize, usize)> = (0..5)
            .map(|class| {
                let image = rest % 5;
                rest /= 5;
                (class, image)
            })
            .collect();
        matchings += usize::from(
            table
                .iter()
                .all(|&(class, image)| image != class && table[image].1 == class),
        );
        let declared = PairingDeclaration::Family { table };
        assert_eq!(
            PairedCarrier::admit(&field, 0, &declared, &founded),
            Err(PairedDefect::Pairing(PairingDefect::OddFamily {
                classes: 5
            }))
        );
        refused += 1;
    }
    assert_eq!((refused, matchings), (3125, 0));
    eprintln!("campaign 1: {refused} maps of five classes refused, {matchings} pairings exist");

    let roles = PairingDeclaration::Roles {
        first: vec![0, 1],
        second: vec![2, 3],
    };
    let completed = PairedCarrier::complete_port(&field, 0, &roles, &founded).unwrap();
    let carrier = PairedCarrier::admit(&field, 0, &roles, &completed).unwrap();
    assert_eq!(carrier.sigma().image(4), None);
    let current = Current::at_rest(&field);
    let moment = SourceMoment::open(&field, &current);
    assert_eq!(
        carrier.partner_moment(&field, &current, &moment, 0),
        Err(PairedDefect::LockMisses { ring: 0, class: 1 })
    );
}

/// A ring of period 4 whose reflector is `[1, 0, 2, 3]` is an involution, which `Ring::declare`
/// accepts, and fails the dihedral relation at port 0 (`F(F(0) + 1) = 2`, not `3`). The reflection
/// `[1, 0, 3, 2]` of the same period is admitted. `Ring::declare` is not tightened.
#[test]
fn a_period_four_reflector_that_passes_declare_fails_the_dihedral_relation() {
    let declared = PairingDeclaration::Family {
        table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
    };
    let silent = ExactRatMatrix::zero(8, 4).unwrap();
    let skew = field_of(4, vec![0, 1, 2, 3], vec![1, 0, 2, 3], 4, Vec::new());
    assert_eq!(skew.ring(0).reflector().images().to_vec(), vec![1, 0, 2, 3]);
    assert_eq!(
        PairedCarrier::admit(&skew, 0, &declared, &silent),
        Err(PairedDefect::Reflector {
            ring: 0,
            defect: ReflectorDefect::NotDihedral {
                port: 0,
                found: 2,
                expected: 3
            }
        })
    );
    let straight = field_of(4, vec![0, 1, 2, 3], vec![1, 0, 3, 2], 4, Vec::new());
    let carrier = PairedCarrier::admit(&straight, 0, &declared, &silent).unwrap();
    assert_eq!(carrier.axis(), 1);
    assert_eq!(carrier.reflector().to_vec(), vec![1, 0, 3, 2]);
    assert_eq!((carrier.period(), carrier.width()), (4, 8));
}

/// The founded sign matrix `E_0` (`declared_source_port`, the declared sign sequence times ½) carries
/// no pairing: admission refuses it naming the first failing column and row. On campaign 1 the first
/// family column fails at row 0 (`E_0[0][0] = −½`, `E_0[0][1] = E_0[0][2] = +½`, hand-read from the
/// sequence), for roles `{0,1}/{2,3}` against column 2 and for the family `(0 1)(2 3)` against column 1.
/// The expectation is also computed from the definition in the scatter form.
#[test]
fn the_founded_sign_matrix_is_refused_naming_its_first_failing_column() {
    let field = Field::declare(FieldDeclaration::campaign_one(1 << 17)).unwrap();
    let founded = declared_source_port(&field, 0).unwrap().unwrap();
    let reflector = field.ring(0).reflector().images().to_vec();
    assert_eq!(reflector, vec![0, 4, 3, 2, 1]);
    let declarations = [
        (
            PairingDeclaration::Roles {
                first: vec![0, 1],
                second: vec![2, 3],
            },
            (0usize, 2usize, 0usize),
        ),
        (
            PairingDeclaration::Family {
                table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
            },
            (0, 1, 0),
        ),
    ];
    for (declared, (column, partner, row)) in declarations {
        let sigma = declared.resolve(5).unwrap();
        assert_eq!(
            first_failure(&founded, &reflector, sigma.table()),
            Some((column, partner, row))
        );
        assert_eq!(
            PairedCarrier::admit(&field, 0, &declared, &founded),
            Err(PairedDefect::Equivariance {
                ring: 0,
                column,
                partner,
                row
            })
        );
        // Completed on its leader columns the same port is admitted: the founded values are kept
        // where they are free, and forced where the pairing forces them.
        let completed = PairedCarrier::complete_port(&field, 0, &declared, &founded).unwrap();
        assert_eq!(first_failure(&completed, &reflector, sigma.table()), None);
        PairedCarrier::admit(&field, 0, &declared, &completed).unwrap();
        for &(leader, _) in sigma.pairs() {
            for row in 0..completed.rows() {
                assert_eq!(
                    completed.get(row, leader).unwrap(),
                    founded.get(row, leader).unwrap()
                );
            }
        }
    }
    eprintln!("founded E_0 on campaign 1: first failing column 0, row 0, for both declarations");
}

/// The ring and the port are certified before the carrier exists: a ring outside the field, a ring
/// that is no source, a port of another shape, and an equivariant port with columns outside the
/// family left free.
#[test]
fn the_ring_the_source_and_the_port_shape_are_certified() {
    let declared = PairingDeclaration::Family {
        table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
    };
    let setting = setting_one();
    let port = setting.medium.port.clone();
    assert_eq!(
        PairedCarrier::admit(&setting.field, 3, &declared, &port),
        Err(PairedDefect::RingOutside { ring: 3, rings: 1 })
    );
    let behind = two_ring_field(vec![1], vec![]);
    assert_eq!(
        PairedCarrier::admit(&behind, 0, &declared, &port),
        Err(PairedDefect::NotSource { ring: 0 })
    );
    // A pairing with a fixed class is refused at the admission, naming the class.
    let fixed = PairingDeclaration::Family {
        table: vec![(0, 1), (1, 0), (2, 2), (3, 3)],
    };
    assert_eq!(
        PairedCarrier::admit(&setting.field, 0, &fixed, &port),
        Err(PairedDefect::Pairing(PairingDefect::FixedClass {
            class: 2
        }))
    );
    assert_eq!(
        setting
            .carrier
            .certify(&ExactRatMatrix::zero(3, 4).unwrap()),
        Err(PairedDefect::PortShape {
            rows: 3,
            columns: 4,
            expected_rows: 10,
            expected_columns: 4
        })
    );
    assert_eq!(
        setting.carrier.lift(&[Rat::one()]),
        Err(PairedDefect::Shape {
            what: "a vector on the paired ring's carrier",
            expected: 10,
            found: 1
        })
    );
    assert_eq!(
        setting
            .carrier
            .equivariant_port(&ExactRatMatrix::zero(3, 4).unwrap()),
        Err(PairedDefect::PortShape {
            rows: 3,
            columns: 4,
            expected_rows: 10,
            expected_columns: 4
        })
    );
    // Columns outside the family are not read: they are free in a paired port.
    let outside = setting_three();
    let loose = with_entry(&outside.medium.port, 0, 0, integer(7));
    let loose = with_entry(&loose, 5, 3, integer(-9));
    outside.carrier.certify(&loose).unwrap();
    // A carrier admitted on ring 1 of a two-ring field finds no such ring in a one-ring field, and
    // a vector of the wrong width has no half-turn.
    let silent = two_ring_field(vec![1], vec![]);
    let free = Stream(5).matrix(10, 4);
    let carrier_behind = PairedCarrier::admit(
        &silent,
        1,
        &declared,
        &PairedCarrier::complete_port(&silent, 1, &declared, &free).unwrap(),
    )
    .unwrap();
    assert_eq!(carrier_behind.ring(), 1);
    assert_eq!(
        carrier_behind.half_turn(&setting.field, &vec![Rat::zero(); 10], &BigInt::one()),
        Err(PairedDefect::RingOutside { ring: 1, rings: 1 })
    );
    assert_eq!(
        setting
            .carrier
            .half_turn(&setting.field, &[Rat::one()], &BigInt::one()),
        Err(PairedDefect::Shape {
            what: "a vector on the paired ring's carrier",
            expected: 10,
            found: 1
        })
    );
}

/// A completed port is the leader columns as given, the followers `B` of them (computed in the scatter
/// form), and the classes outside the family untouched; it is admitted, and its kind and pairs are the
/// declaration's.
#[test]
fn the_admitted_case_builds_each_follower_column_from_its_leader() {
    for setting in [setting_one(), setting_two(), setting_three()] {
        let carrier = &setting.carrier;
        let port = &setting.medium.port;
        let reflector = carrier.reflector().to_vec();
        for &(leader, follower) in carrier.sigma().pairs() {
            for (node, &target) in reflector.iter().enumerate() {
                for coordinate in 0..2 {
                    assert_eq!(
                        port.get(2 * target + coordinate, follower).unwrap(),
                        setting.free.get(2 * node + coordinate, leader).unwrap(),
                        "{}",
                        setting.name
                    );
                }
            }
            for row in 0..port.rows() {
                assert_eq!(
                    port.get(row, leader).unwrap(),
                    setting.free.get(row, leader).unwrap()
                );
            }
        }
        for class in 0..carrier.sigma().classes() {
            if carrier.sigma().image(class).is_none() {
                for row in 0..port.rows() {
                    assert_eq!(
                        port.get(row, class).unwrap(),
                        setting.free.get(row, class).unwrap()
                    );
                }
            }
        }
        assert_eq!(
            first_failure(port, &reflector, carrier.sigma().table()),
            None
        );
        carrier.certify(port).unwrap();
        eprintln!(
            "{}: kind {:?}, pairs {:?}, family {:?}, axis {}",
            setting.name,
            carrier.sigma().kind(),
            carrier.sigma().pairs(),
            setting.family,
            carrier.axis()
        );
    }
    assert_eq!(setting_one().carrier.sigma().kind(), PairingKind::Family);
    assert_eq!(setting_two().carrier.sigma().kind(), PairingKind::Roles);
    assert_eq!(setting_two().carrier.axis(), 2);
    assert_eq!(setting_three().carrier.axis(), 3);
}

/// Certification names the first failing column in class order and its first differing row. One
/// entry moved in a follower column fails the leader's column first; one moved in a leader column
/// fails that column at the row that reads it; one moved outside the family is not read.
#[test]
fn equivariance_names_the_first_failing_column_and_row() {
    let setting = setting_one();
    let port = &setting.medium.port;
    let reflector = setting.carrier.reflector().to_vec();
    assert_eq!(reflector, vec![0, 4, 3, 2, 1]);
    let moved = |row: usize, column: usize| {
        with_entry(
            port,
            row,
            column,
            port.get(row, column).unwrap().clone() + Rat::one(),
        )
    };
    // (3, 3) is a follower entry of the pair (2 3): column 2 fails first, at row 3.
    let table = setting.carrier.sigma().table().to_vec();
    for ((row, column), expected) in [
        ((3usize, 3usize), (2usize, 3usize, 3usize)),
        // (5, 0) is a leader entry read by row 7 of column 0 (F(3) = 2, so row 2·3 + 1 reads source 5).
        ((5, 0), (0, 1, 7)),
        // (9, 1) is a follower entry of the pair (0 1), compared at its own row.
        ((9, 1), (0, 1, 9)),
        // (4, 2) is a leader entry read by row 6 of column 2.
        ((4, 2), (2, 3, 6)),
    ] {
        let broken = moved(row, column);
        assert_eq!(
            first_failure(&broken, &reflector, &table),
            Some(expected),
            "entry ({row}, {column})"
        );
        assert_eq!(
            setting.carrier.certify(&broken),
            Err(PairedDefect::Equivariance {
                ring: 0,
                column: expected.0,
                partner: expected.1,
                row: expected.2
            }),
            "entry ({row}, {column})"
        );
    }
}

// -------------------------------------------------------------------------------------------
// the lift

/// [proved-derived] On the carrier, `B² = 1` and `B P B = P⁻¹` exactly, for every dihedral reflector of
/// every period from 2 to 7 (all `d` axes), with `P` the ring's own `Ring::rotate`. Then `B Pᵏ = P⁻ᵏ B`
/// and `(B Pᵏ)² = 1` for `k` over two turns each way (Lean `dihedral_swap`, `dihedral_reflection_sq`).
#[test]
fn the_lift_is_an_involution_that_inverts_the_rotor_on_the_carrier() {
    let mut stream = Stream(0x4845_4c49_0003_0001);
    let declared = PairingDeclaration::Family {
        table: vec![(0, 1), (1, 0)],
    };
    let (mut rings, mut vectors, mut powers) = (0usize, 0usize, 0usize);
    for period in 2..=7u64 {
        for axis in 0..period {
            let field = field_of(
                period,
                (0..period).collect(),
                reflection(period, axis),
                2,
                Vec::new(),
            );
            let free = stream.matrix(2 * period as usize, 2);
            let port = PairedCarrier::complete_port(&field, 0, &declared, &free).unwrap();
            let carrier = PairedCarrier::admit(&field, 0, &declared, &port).unwrap();
            assert_eq!(carrier.axis(), axis as usize);
            let ring = field.ring(0);
            for _ in 0..3 {
                let v = stream.vector(2 * period as usize);
                let bv = carrier.lift(&v).unwrap();
                // B² = 1.
                assert_eq!(carrier.lift(&bv).unwrap(), v);
                // B P B = P⁻¹.
                let pbv = ring.rotate(&bv, &BigInt::one());
                assert_eq!(
                    carrier.lift(&pbv).unwrap(),
                    ring.rotate(&v, &BigInt::from(-1))
                );
                let reach = 2 * period as i64;
                for k in -reach..=reach {
                    let turns = BigInt::from(k);
                    let rotated = ring.rotate(&v, &turns);
                    // B Pᵏ = P⁻ᵏ B.
                    assert_eq!(
                        carrier.lift(&rotated).unwrap(),
                        ring.rotate(&bv, &-turns.clone())
                    );
                    // (B Pᵏ)² = 1.
                    let once = carrier.half_turn(&field, &v, &turns).unwrap();
                    assert_eq!(once, carrier.lift(&rotated).unwrap());
                    assert_eq!(carrier.half_turn(&field, &once, &turns).unwrap(), v);
                    powers += 1;
                }
                vectors += 1;
            }
            rings += 1;
        }
    }
    eprintln!("lift law: {rings} reflectors, {vectors} vectors, {powers} powers, all exact");
}

// -------------------------------------------------------------------------------------------
// the partner, at its first real caller

/// The hand-computed anchor of the moment's phase convention. Period 4, axis 1 (`F = [1, 0, 3, 2]`),
/// two classes paired `(0 1)`, every class on the lock, the port `E e_0 = (1, 2 | 0, 0 | …)` (node 0)
/// and `E e_1 = B E e_0` (node 1). A cell is counted at the phase after its step, so a word of two
/// cells from phase 0 sits at phases 1 and 2, and `ν̂(2) = ½`:
///
/// ```text
/// u = 0 0:  m̃ = ½ (P⁻¹ + P⁻²) E e_0 = (0 0 0 0 | ½ 1 | ½ 1),     s(0) = P² m̃ = (½ 1 | ½ 1 | 0 0 0 0)
/// σ̄u = 1 1: m̃ = ½ (P⁻¹ + P⁻²) E e_1 = (½ 1 | 0 0 0 0 | ½ 1),   s(0) = (0 0 | ½ 1 | ½ 1 | 0 0)
/// u = 0 1:  s(0) = (0 0 | 1 2 | 0 0 0 0), and σ̄u = u (a σ-palindrome)
/// ```
///
/// and `s(0)(σ̄u) = B P⁻¹ s(0)(u)` reads the same numbers.
#[test]
fn the_phase_convention_is_pinned_by_a_hand_computed_anchor() {
    let field = field_of(4, vec![0, 1], reflection(4, 1), 2, Vec::new());
    let declared = PairingDeclaration::Family {
        table: vec![(0, 1), (1, 0)],
    };
    let rows: Vec<Vec<Rat>> = [
        [1, 0],
        [2, 0],
        [0, 1],
        [0, 2],
        [0, 0],
        [0, 0],
        [0, 0],
        [0, 0],
    ]
    .iter()
    .map(|row| row.iter().map(|&value| integer(value)).collect())
    .collect();
    let port = ExactRatMatrix::shaped(8, 2, rows).unwrap();
    let carrier = PairedCarrier::admit(&field, 0, &declared, &port).unwrap();
    // The declared pairing completes the leader column to the same port.
    let leader_only = with_entry(&with_entry(&port, 2, 1, Rat::zero()), 3, 1, Rat::zero());
    assert_eq!(carrier.equivariant_port(&leader_only).unwrap(), port);
    let medium = Medium::new(0, port);
    let table = carrier.sigma().table().to_vec();
    let opening = vec![BigInt::zero()];

    let read = |word: &[usize]| {
        let strand = run(&field, 0, &opening, None, word);
        let encode = strand.moment.encode(&field, &medium, 0).unwrap();
        let open = strand
            .moment
            .open_storage(&field, &medium, &strand.current)
            .unwrap()[0]
            .clone();
        (strand, encode, open)
    };

    let (strand, encode, open) = read(&[0, 0]);
    let counts =
        |passage: &Run, phase: usize| passage.moment.phase_counts(0, phase).unwrap().to_vec();
    assert_eq!(counts(&strand, 1), vec![1u64, 0]);
    assert_eq!(counts(&strand, 2), vec![1u64, 0]);
    assert_eq!(counts(&strand, 0), vec![0u64, 0]);
    assert_eq!(counts(&strand, 3), vec![0u64, 0]);
    assert_eq!(encode, halves(&[0, 0, 0, 0, 1, 2, 1, 2]));
    assert_eq!(open, halves(&[1, 2, 1, 2, 0, 0, 0, 0]));
    let (partner, partner_encode, partner_open) = read(&complement_reverse(&table, &[0, 0]));
    assert_eq!(complement_reverse(&table, &[0, 0]), vec![1, 1]);
    assert_eq!(counts(&partner, 1), vec![0u64, 1]);
    assert_eq!(counts(&partner, 2), vec![0u64, 1]);
    assert_eq!(partner_encode, halves(&[1, 2, 0, 0, 0, 0, 1, 2]));
    assert_eq!(partner_open, halves(&[0, 0, 1, 2, 1, 2, 0, 0]));
    // The partner of the strand, opened at phase 0: the dyad moment is the moment of 1 1, as a value.
    assert_eq!(
        carrier
            .partner_moment(&field, &strand.current, &strand.moment, 0)
            .unwrap(),
        partner.moment
    );
    let face = carrier
        .partner_face(&field, &medium, &strand.current, &strand.moment, 0)
        .unwrap();
    assert_eq!(face.read, partner_open);
    assert_eq!(face.transported, partner_open);
    assert!(face.is_exact());
    // c₀ = s + s′ + n + 1 = 3: m̃(σ̄u) = B P³ m̃(u).
    assert_eq!(
        carrier
            .half_turn(&field, &encode, &BigInt::from(3))
            .unwrap(),
        partner_encode
    );

    let (strand, encode, open) = read(&[0, 1]);
    assert_eq!(encode, halves(&[0, 0, 0, 0, 0, 0, 2, 4]));
    assert_eq!(open, halves(&[0, 0, 2, 4, 0, 0, 0, 0]));
    assert_eq!(complement_reverse(&table, &[0, 1]), vec![0, 1]);
    let face = carrier
        .partner_face(&field, &medium, &strand.current, &strand.moment, 0)
        .unwrap();
    assert_eq!(face.read, open);
    assert_eq!(face.transported, open);
    assert_eq!(
        carrier
            .partner_moment(&field, &strand.current, &strand.moment, 0)
            .unwrap(),
        strand.moment
    );
    // The residual is the exact difference, never hidden: a face that is not its transport shows it.
    let off = PartnerFace {
        read: halves(&[1, 2, 3]),
        transported: halves(&[1, 1, 5]),
    };
    assert!(!off.is_exact());
    assert_eq!(off.residual(), halves(&[0, 1, -2]));
    eprintln!("anchor: n = 2, ν̂(2) = 1/2, phases 1 and 2, c₀ = 3, three words read exactly");
}

/// [proved-derived] **The partner law at its first real caller**, on unseen words (a seeded stream,
/// every length from 0 to three turns and a half), for three settings (a family and two role
/// pairings; periods 5, 6, 7; axes 0, 2, 3; one with classes outside the family) and three openings
/// each (winding and phase of the strand, phase of the partner):
///
/// - the partner moment formed from the strand's counts equals, as a value, the moment ingest of
///   `σ̄(u)` makes from a Current re-keyed to the partner's phase, and the dyad is an involution of
///   the retained counts (applied to the partner it returns the strand's moment);
/// - `encode` of the partner is `B P^(c₀)` of the strand's, `c₀ = s + s′ + n + 1`;
/// - `open_storage` of the partner is `B P^(−(n−1))` of the strand's, with an exact residual of zero,
///   and both maps are involutions;
/// - the population, and so the chart value `ν̂(n)`, is the same for both.
#[test]
fn the_partner_strands_moment_and_face_are_the_dyad_image_of_the_strands() {
    let mut stream = Stream(0x4845_4c49_0004_0001);
    let mut receipt = Vec::new();
    for setting in [setting_one(), setting_two(), setting_three()] {
        let d = setting.period;
        let openings = [(0u64, 0u64, 0u64), (2, d - 1, 1), (1, d / 2, d - 1)];
        let lengths = [
            0,
            1,
            2,
            3,
            d as usize - 1,
            d as usize,
            d as usize + 1,
            2 * d as usize + 1,
            3 * d as usize + 2,
        ];
        let table = setting.carrier.sigma().table().to_vec();
        let mut cases = 0u64;
        let mut cells = 0u64;
        for (winding, phase, partner_phase) in openings {
            let opening = vec![BigInt::from(winding * d + phase)];
            for length in lengths {
                for _ in 0..2 {
                    let u = stream.word(length, &setting.family);
                    let partner_word = complement_reverse(&table, &u);
                    let strand = run(&setting.field, 0, &opening, None, &u);
                    let partner = run(
                        &setting.field,
                        0,
                        &opening,
                        Some(partner_phase),
                        &partner_word,
                    );
                    let n = length as u64;

                    // The retained counts.
                    let derived = setting
                        .carrier
                        .partner_moment(
                            &setting.field,
                            &strand.current,
                            &strand.moment,
                            partner_phase,
                        )
                        .unwrap();
                    assert_eq!(derived, partner.moment, "{}: {u:?}", setting.name);
                    let back = setting
                        .carrier
                        .partner_moment(&setting.field, &partner.current, &partner.moment, phase)
                        .unwrap();
                    assert_eq!(back, strand.moment, "{}: {u:?}", setting.name);
                    assert_eq!(strand.moment.population(0).unwrap(), n);
                    assert_eq!(partner.moment.population(0).unwrap(), n);

                    // The phase-carried frame: encode.
                    let medium = &setting.medium;
                    let forward = strand.moment.encode(&setting.field, medium, 0).unwrap();
                    let backward = partner.moment.encode(&setting.field, medium, 0).unwrap();
                    let c0 = BigInt::from(phase + partner_phase + n + 1);
                    assert_eq!(
                        setting
                            .carrier
                            .half_turn(&setting.field, &forward, &c0)
                            .unwrap(),
                        backward,
                        "{}: {u:?}",
                        setting.name
                    );

                    // The reading frame: open_storage, through partner_face.
                    let face = setting
                        .carrier
                        .partner_face(
                            &setting.field,
                            medium,
                            &strand.current,
                            &strand.moment,
                            partner_phase,
                        )
                        .unwrap();
                    let actual = partner
                        .moment
                        .open_storage(&setting.field, medium, &partner.current)
                        .unwrap();
                    assert_eq!(face.read, actual[0], "{}: {u:?}", setting.name);
                    assert!(face.is_exact(), "{}: {u:?}", setting.name);
                    assert!(face.residual().iter().all(Zero::is_zero));
                    let forward_open = strand
                        .moment
                        .open_storage(&setting.field, medium, &strand.current)
                        .unwrap()[0]
                        .clone();
                    let turns = BigInt::one() - BigInt::from(n);
                    assert_eq!(
                        face.transported,
                        setting
                            .carrier
                            .half_turn(&setting.field, &forward_open, &turns)
                            .unwrap()
                    );
                    // The half-turn is an involution of the faces.
                    let twice = setting
                        .carrier
                        .half_turn(&setting.field, &face.read, &turns)
                        .unwrap();
                    assert_eq!(twice, forward_open);
                    cases += 1;
                    cells += n;
                }
            }
        }
        receipt.push((setting.name, cases, cells));
    }
    for (name, cases, cells) in receipt {
        eprintln!(
            "{name}: {cases} words, {cells} cells, every count and face exact, residual zero"
        );
    }
}

/// The partner read joins the moment's phase counts and refuses, typed, each carrier whose
/// normalization or rounding would break the reflection: a leaky count, a transport below one, a
/// reframed moment, declared pair offsets, a ring that did not tick once a cell, a count outside the
/// family, a Current that is not the strand's, a second source ring, an opening past the period; and
/// the carrier's own ring, class chart, lock, constitution port and class map.
#[test]
fn the_partner_read_refuses_where_normalization_or_rounding_would_break_it() {
    let setting = setting_one();
    let (field, carrier, medium) = (&setting.field, &setting.carrier, &setting.medium);
    let opening = vec![BigInt::zero()];
    let strand = run(field, 0, &opening, None, &[0, 1, 2]);
    let table = carrier.sigma().table().to_vec();

    // A foreign field: the same shape with another axis.
    let other = field_of(5, vec![0, 1, 2, 3], reflection(5, 1), 4, Vec::new());
    let rest = Current::at_rest(&other);
    assert_eq!(
        carrier.partner_moment(&other, &rest, &SourceMoment::open(&other, &rest), 0),
        Err(PairedDefect::ForeignField { ring: 0 })
    );
    // An opening past the period.
    assert_eq!(
        dyad(
            carrier
                .partner_moment(field, &strand.current, &strand.moment, 5)
                .unwrap_err()
        ),
        DyadRefusal::Opening {
            ring: 0,
            phase: 5,
            period: 5
        }
    );
    // A Current that is not the strand's reached lift point.
    let stale = Current::at(field, vec![BigInt::from(1)]).unwrap();
    match dyad(
        carrier
            .partner_moment(field, &stale, &strand.moment, 0)
            .unwrap_err(),
    ) {
        DyadRefusal::Moment(inner) => assert!(matches!(*inner, HnnError::Unadmitted { .. })),
        other => panic!("{other:?}"),
    }
    // A reframed moment.
    let mut reframed = strand.moment.clone();
    reframed
        .synchronize_clock(field, &strand.current, 0, &[0])
        .unwrap();
    assert_eq!(
        dyad(
            carrier
                .partner_moment(field, &strand.current, &reframed, 0)
                .unwrap_err()
        ),
        DyadRefusal::Reframed
    );
    // A leaky count, and a transport below one: the moment refuses, and the constitution is refused first.
    let leaky = medium.clone().at_modulus(rat(1, 2));
    let mut current = Current::at_rest(field);
    let mut leaky_moment = SourceMoment::open_with(field, &current, &leaky).unwrap();
    leaky_moment
        .ingest(field, &mut current, &encoded(field, &[0, 1, 2, 3]))
        .unwrap();
    assert_eq!(
        dyad(
            carrier
                .partner_moment(field, &current, &leaky_moment, 0)
                .unwrap_err()
        ),
        DyadRefusal::Leaky { ring: 0 }
    );
    assert_eq!(
        dyad(
            carrier
                .partner_face(field, medium, &current, &leaky_moment, 0)
                .unwrap_err()
        ),
        DyadRefusal::Leaky { ring: 0 }
    );
    assert_eq!(
        carrier.partner_face(field, &leaky, &current, &leaky_moment, 0),
        Err(PairedDefect::Transport {
            ring: 0,
            modulus: Box::new(rat(1, 2))
        })
    );
    assert_eq!(
        carrier.partner_face(field, &leaky, &strand.current, &strand.moment, 0),
        Err(PairedDefect::Transport {
            ring: 0,
            modulus: Box::new(rat(1, 2))
        })
    );
    // A constitution with no source port for the ring.
    let absent = Medium::new(7, medium.port.clone());
    assert_eq!(
        carrier.partner_face(field, &absent, &strand.current, &strand.moment, 0),
        Err(PairedDefect::MissingSourcePort { ring: 0 })
    );
    // Declared pair offsets.
    let paired = field_of(5, vec![0, 1, 2, 3], reflection(5, 0), 4, vec![1]);
    let carrier_paired = PairedCarrier::admit(
        &paired,
        0,
        &PairingDeclaration::Family {
            table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
        },
        &medium.port,
    )
    .unwrap();
    let rest = Current::at_rest(&paired);
    assert_eq!(
        dyad(
            carrier_paired
                .partner_moment(&paired, &rest, &SourceMoment::open(&paired, &rest), 0)
                .unwrap_err()
        ),
        DyadRefusal::PairOffsets { offsets: vec![1] }
    );
    // A ring that does not tick on a class of the family: the carrier is admitted, the field refuses
    // the read at the class, and the moment (read directly) refuses the ticks.
    let short = field_of(5, vec![0, 1, 2], reflection(5, 0), 4, Vec::new());
    let carrier_short = PairedCarrier::admit(
        &short,
        0,
        &PairingDeclaration::Family {
            table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
        },
        &medium.port,
    )
    .unwrap();
    let ticked = run(&short, 0, &opening, None, &[0, 3, 1]);
    assert_eq!(
        carrier_short.partner_moment(&short, &ticked.current, &ticked.moment, 0),
        Err(PairedDefect::LockMisses { ring: 0, class: 3 })
    );
    assert_eq!(
        ticked
            .moment
            .dyad(&short, &ticked.current, 0, &table, 0)
            .unwrap_err(),
        DyadRefusal::Ticks {
            ring: 0,
            cells: 3,
            ticks: 2
        }
    );
    // A count of a class outside the family.
    let outside = field_of(5, vec![0, 1, 2, 3], reflection(5, 0), 4, Vec::new());
    let roles = PairingDeclaration::Roles {
        first: vec![1],
        second: vec![2],
    };
    let free = Stream(3).matrix(10, 4);
    let carrier_outside = PairedCarrier::admit(
        &outside,
        0,
        &roles,
        &PairedCarrier::complete_port(&outside, 0, &roles, &free).unwrap(),
    )
    .unwrap();
    let counted = run(&outside, 0, &opening, None, &[1, 0, 2]);
    assert_eq!(
        dyad(
            carrier_outside
                .partner_moment(&outside, &counted.current, &counted.moment, 0)
                .unwrap_err()
        ),
        DyadRefusal::Outside {
            ring: 0,
            phase: 2,
            class: 0,
            count: 1
        }
    );
    // A second source ring.
    let twin = declare(
        vec![
            ring_declaration(3, vec![], reflection(3, 0)),
            ring_declaration(5, vec![0, 1, 2, 3], reflection(5, 0)),
        ],
        vec![ContactDeclaration {
            from: 0,
            to: 1,
            channel: vec![(0, 0)],
            admittance: integer(2),
            exponent: integer(0),
        }],
        vec![0, 1],
        4,
        Vec::new(),
    );
    let twin_free = Stream(4).matrix(10, 4);
    let family = PairingDeclaration::Family {
        table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
    };
    let carrier_twin = PairedCarrier::admit(
        &twin,
        1,
        &family,
        &PairedCarrier::complete_port(&twin, 1, &family, &twin_free).unwrap(),
    )
    .unwrap();
    let twin_rest = Current::at_rest(&twin);
    assert_eq!(
        dyad(
            carrier_twin
                .partner_moment(&twin, &twin_rest, &SourceMoment::open(&twin, &twin_rest), 0)
                .unwrap_err()
        ),
        DyadRefusal::Sources { ring: 1 }
    );
    // A class map of another width, and one that is no involution.
    assert_eq!(
        strand
            .moment
            .dyad(field, &strand.current, 0, &[Some(1), Some(0)], 0)
            .unwrap_err(),
        DyadRefusal::ClassMap {
            expected: 4,
            found: 2
        }
    );
    assert_eq!(
        strand
            .moment
            .dyad(
                field,
                &strand.current,
                0,
                &[Some(1), Some(2), None, None],
                0
            )
            .unwrap_err(),
        DyadRefusal::NotInvolution { class: 0 }
    );
    eprintln!("partner read: every refusal named, nothing rounded or substituted");
}

/// **The source port is plastic**: the carrier keeps no port, and each read certifies the port the
/// constitution holds now. A declared different equivariant port reads exactly (and gives another
/// face); a declared different port off the equivariant subspace is refused, naming the first failing
/// column and row, whether it is one moved entry, or the founded sign matrix; the admitted port reads
/// again once it is placed back. These are declared ports, not deposits: a deposit
/// (`hnn::executed::pair_deposit`) moves a located pair's consequence column only, while equivariance
/// asks the column of its dyad image's partner to move by `B` of that, the slip of a reversed pair the
/// law does not read (module header), so a deposit takes a port off the subspace in general.
#[test]
fn a_port_that_a_later_change_takes_off_the_equivariant_subspace_is_refused_at_the_read() {
    let setting = setting_one();
    let (field, carrier) = (&setting.field, &setting.carrier);
    let opening = vec![BigInt::from(2 * 5 + 3)];
    let u = vec![0, 2, 3, 1, 1, 0, 2];
    let table = carrier.sigma().table().to_vec();
    let strand = run(field, 0, &opening, None, &u);
    let partner = run(field, 0, &opening, Some(2), &complement_reverse(&table, &u));

    // The admitted port reads exactly.
    let admitted = carrier
        .partner_face(field, &setting.medium, &strand.current, &strand.moment, 2)
        .unwrap();
    assert!(admitted.is_exact());

    // Another equivariant port, declared: lawful, exact against the actual partner, and a different face.
    let other = carrier
        .equivariant_port(&Stream(0x4845_4c49_0005_0001).matrix(10, 4))
        .unwrap();
    let other_medium = Medium::new(0, other);
    let lawful = carrier
        .partner_face(field, &other_medium, &strand.current, &strand.moment, 2)
        .unwrap();
    let actual = partner
        .moment
        .open_storage(field, &other_medium, &partner.current)
        .unwrap();
    assert_eq!(lawful.read, actual[0]);
    assert!(lawful.is_exact());
    assert_ne!(lawful.read, admitted.read);

    // A declared port with one entry moved: refused at the first failing column and row.
    let port = &setting.medium.port;
    let moved = with_entry(port, 4, 2, port.get(4, 2).unwrap().clone() + Rat::one());
    let off = Medium::new(0, moved.clone());
    assert_eq!(
        first_failure(&moved, carrier.reflector(), &table),
        Some((2, 3, 6))
    );
    assert_eq!(
        carrier.partner_face(field, &off, &strand.current, &strand.moment, 2),
        Err(PairedDefect::Equivariance {
            ring: 0,
            column: 2,
            partner: 3,
            row: 6
        })
    );

    // The founded sign matrix of the same field, declared in its place: refused at column 0.
    let founded = declared_source_port(field, 0).unwrap().unwrap();
    let founded_medium = Medium::new(0, founded);
    assert_eq!(
        carrier.partner_face(field, &founded_medium, &strand.current, &strand.moment, 2),
        Err(PairedDefect::Equivariance {
            ring: 0,
            column: 0,
            partner: 1,
            row: 0
        })
    );

    // Placed back, the admitted port reads again, exactly as before.
    let again = carrier
        .partner_face(field, &setting.medium, &strand.current, &strand.moment, 2)
        .unwrap();
    assert_eq!(again, admitted);
    eprintln!(
        "plastic port: admitted exact, another equivariant port exact, 2 off-subspace ports refused"
    );
}

/// The same, through the real `Constitution` (the actual consumer of `encode` and `open_storage`): a
/// two-ring field whose source ring 0 is paired. The founded constitution holds the sign sequence and
/// is refused at column 0; `with_ports` places a declared equivariant port (the founded leader columns
/// completed) and the read is exact against the actual partner's open under the same constitution; a
/// declared port with one entry moved is refused at the column and row.
#[test]
fn the_real_constitution_is_read_at_its_current_port() {
    let field = declare(
        vec![
            ring_declaration(5, vec![0, 1, 2, 3], reflection(5, 0)),
            ring_declaration(2, vec![0, 1], reflection(2, 0)),
        ],
        vec![ContactDeclaration {
            from: 0,
            to: 1,
            channel: vec![(0, 0)],
            admittance: integer(2),
            exponent: integer(0),
        }],
        vec![0],
        4,
        Vec::new(),
    );
    let declared = PairingDeclaration::Family {
        table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
    };
    let founded_port = declared_source_port(&field, 0).unwrap().unwrap();
    let completed = PairedCarrier::complete_port(&field, 0, &declared, &founded_port).unwrap();
    let carrier = PairedCarrier::admit(&field, 0, &declared, &completed).unwrap();
    let table = carrier.sigma().table().to_vec();
    let founded = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
    let opening = vec![BigInt::from(5 + 1), BigInt::zero()];
    let u = vec![2, 0, 1, 3, 3, 0, 2, 1, 0];
    let strand = run(&field, 0, &opening, None, &u);
    let partner = run(
        &field,
        0,
        &opening,
        Some(4),
        &complement_reverse(&table, &u),
    );

    assert_eq!(
        carrier.partner_face(&field, &founded, &strand.current, &strand.moment, 4),
        Err(PairedDefect::Equivariance {
            ring: 0,
            column: 0,
            partner: 1,
            row: 0
        })
    );
    let placed = founded
        .clone()
        .with_ports(0, None, Some(completed.clone()), None)
        .unwrap();
    let face = carrier
        .partner_face(&field, &placed, &strand.current, &strand.moment, 4)
        .unwrap();
    let actual = partner
        .moment
        .open_storage(&field, &placed, &partner.current)
        .unwrap();
    assert_eq!(face.read, actual[0]);
    assert!(face.is_exact());
    assert_eq!(
        carrier
            .partner_moment(&field, &strand.current, &strand.moment, 4)
            .unwrap(),
        partner.moment
    );
    let moved = with_entry(
        &completed,
        4,
        2,
        completed.get(4, 2).unwrap().clone() + Rat::one(),
    );
    let changed = placed.with_ports(0, None, Some(moved), None).unwrap();
    assert_eq!(
        carrier.partner_face(&field, &changed, &strand.current, &strand.moment, 4),
        Err(PairedDefect::Equivariance {
            ring: 0,
            column: 2,
            partner: 3,
            row: 6
        })
    );
    eprintln!(
        "real constitution: founded refused at column 0, placed equivariant port exact, moved entry refused"
    );
}

/// The unit tick is certified from the field. A source ring behind a ring that never ticks (an empty
/// lock never wraps, so never carries) reads exactly, on ring index 1; behind a ring that ticks, the
/// carry may add to its advance and the read is refused with the earlier ring named.
#[test]
fn a_source_ring_behind_a_silent_ring_reads_and_one_behind_a_ticking_ring_is_refused() {
    let declared = PairingDeclaration::Family {
        table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
    };
    let silent = two_ring_field(vec![1], vec![]);
    let free = Stream(0x4845_4c49_0006_0001).matrix(10, 4);
    let port = PairedCarrier::complete_port(&silent, 1, &declared, &free).unwrap();
    let carrier = PairedCarrier::admit(&silent, 1, &declared, &port).unwrap();
    let medium = Medium::new(1, port.clone());
    let table = carrier.sigma().table().to_vec();
    let mut stream = Stream(0x4845_4c49_0006_0002);
    let mut cases = 0u64;
    for (winding, phase, partner_phase) in [(0u64, 0u64, 0u64), (3, 4, 1)] {
        let opening = vec![BigInt::zero(), BigInt::from(winding * 5 + phase)];
        for length in [0, 1, 4, 5, 6, 12] {
            let u = stream.word(length, &[0, 1, 2, 3]);
            let strand = run(&silent, 1, &opening, None, &u);
            let partner = run(
                &silent,
                1,
                &opening,
                Some(partner_phase),
                &complement_reverse(&table, &u),
            );
            let derived = carrier
                .partner_moment(&silent, &strand.current, &strand.moment, partner_phase)
                .unwrap();
            assert_eq!(derived, partner.moment, "{u:?}");
            let face = carrier
                .partner_face(
                    &silent,
                    &medium,
                    &strand.current,
                    &strand.moment,
                    partner_phase,
                )
                .unwrap();
            let actual = partner
                .moment
                .open_storage(&silent, &medium, &partner.current)
                .unwrap();
            assert_eq!(face.read, actual[1], "{u:?}");
            assert!(face.is_exact());
            cases += 1;
        }
    }
    let ticking = two_ring_field(vec![1], vec![0]);
    let carrier_ticking = PairedCarrier::admit(&ticking, 1, &declared, &port).unwrap();
    let rest = Current::at_rest(&ticking);
    assert_eq!(
        carrier_ticking.partner_moment(&ticking, &rest, &SourceMoment::open(&ticking, &rest), 0),
        Err(PairedDefect::CarriedClock {
            ring: 1,
            earlier: 0
        })
    );
    eprintln!("behind a silent ring: {cases} words exact; behind a ticking ring: refused");
}

// -------------------------------------------------------------------------------------------
// information at the retained quotient

/// One class of sources that share a length and a forward face.
#[derive(Default)]
struct Group {
    partners: BTreeSet<Vec<Rat>>,
    retained: BTreeSet<Vec<u64>>,
    words: usize,
}

/// **Information at the retained quotient: redundancy.** On the undamped, conservative carrier
/// (modulus one) the partner's face is `B P^(−(n−1))` of the strand's, so it is a function of the
/// forward face and the length. Every word of up to five letters over four classes (up to four for the
/// second port; period 4, axis 1, `(0 1)(2 3)`) is read through the actual moment and grouped by length
/// and forward face: in no group do the partner faces differ, for a generic equivariant port and for a
/// port whose classes `0, 2` and `1, 3` coincide (so distinct retained counts share a face). The groups
/// with more than one word, and those with more than one retained count table, are counted; the exact
/// residual of the law is zero on every word. No source of one length shares a forward face and differs
/// in its partner's, and damping alone would establish none. No metric claim is made.
#[test]
fn the_partner_adds_no_information_at_the_retained_quotient() {
    let field = field_of(4, vec![0, 1, 2, 3], reflection(4, 1), 4, Vec::new());
    let declared = PairingDeclaration::Family {
        table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
    };
    let mut stream = Stream(0x4845_4c49_0007_0001);
    let generic_free = stream.matrix(8, 4);
    let lead = stream.vector(8);
    let merged_free = ExactRatMatrix::shaped(
        8,
        4,
        (0..8)
            .map(|row| {
                vec![
                    lead[row].clone(),
                    Rat::zero(),
                    lead[row].clone(),
                    Rat::zero(),
                ]
            })
            .collect(),
    )
    .unwrap();
    let opening = vec![BigInt::zero()];
    for (name, free, longest) in [
        ("generic", generic_free, 5usize),
        ("merged", merged_free, 4),
    ] {
        let port = PairedCarrier::complete_port(&field, 0, &declared, &free).unwrap();
        let carrier = PairedCarrier::admit(&field, 0, &declared, &port).unwrap();
        let medium = Medium::new(0, port);
        let table = carrier.sigma().table().to_vec();
        let mut groups: BTreeMap<(usize, Vec<Rat>), Group> = BTreeMap::new();
        let mut words = 0usize;
        for length in 0..=longest {
            for index in 0..4usize.pow(length as u32) {
                let mut rest = index;
                let u: Vec<usize> = (0..length)
                    .map(|_| {
                        let class = rest % 4;
                        rest /= 4;
                        class
                    })
                    .collect();
                let strand = run(&field, 0, &opening, None, &u);
                let partner = run(
                    &field,
                    0,
                    &opening,
                    Some(0),
                    &complement_reverse(&table, &u),
                );
                let forward = strand
                    .moment
                    .open_storage(&field, &medium, &strand.current)
                    .unwrap()[0]
                    .clone();
                let backward = partner
                    .moment
                    .open_storage(&field, &medium, &partner.current)
                    .unwrap()[0]
                    .clone();
                let turns = BigInt::one() - BigInt::from(length as u64);
                assert_eq!(
                    backward,
                    carrier.half_turn(&field, &forward, &turns).unwrap(),
                    "{name}: {u:?}"
                );
                let retained: Vec<u64> = (0..4)
                    .flat_map(|phase| strand.moment.phase_counts(0, phase).unwrap().to_vec())
                    .collect();
                let group = groups.entry((length, forward)).or_default();
                group.partners.insert(backward);
                group.retained.insert(retained);
                group.words += 1;
                words += 1;
            }
        }
        assert!(
            groups.values().all(|group| group.partners.len() == 1),
            "{name}: a partner face differs within a forward face"
        );
        let shared = groups.values().filter(|group| group.words >= 2).count();
        let distinct = groups
            .values()
            .filter(|group| group.retained.len() >= 2)
            .count();
        let widest = groups.values().map(|group| group.words).max().unwrap();
        eprintln!(
            "{name}: {words} words, {} (length, face) groups, {shared} with two or more words, {distinct} with two or more retained count tables, largest {widest}; no group has two partner faces",
            groups.len()
        );
        assert!(shared >= 1, "{name}");
        if name == "merged" {
            assert!(distinct >= 1);
        }
    }
}

//! Declared fields and a test constitution for the forward laws. The constitution here is a test
//! implementor of [`ConstitutionRead`]; the owner of `Θ` is the learning side's `Constitution`.

use num_bigint::BigInt;
use num_traits::{One, Zero};

use crate::geometry::RatVec3;
use crate::geometry::screw::ScrewGenerator;
use crate::hnn::field::{
    ConstitutionRead, ContactDeclaration, CribDeclaration, Field, FieldDeclaration,
    ReceiverDeclaration, RingDeclaration,
};
use crate::hnn::moment::PairPort;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer, rat};

/// SplitMix64: exact, deterministic, no float.
pub(super) struct Draw(u64);

impl Draw {
    pub(super) fn new(seed: u64) -> Self {
        Self(seed)
    }

    pub(super) fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A small rational `p/q`, `p ∈ [−3, 3]`, `q ∈ [1, 3]`.
    pub(super) fn rational(&mut self) -> Rat {
        let p = (self.next() % 7) as i64 - 3;
        let q = (self.next() % 3) as i64 + 1;
        rat(p, q)
    }

    /// A small dyadic rational `p/q`, `p ∈ [−3, 3]`, `q ∈ {1, 2, 4}`: on every lattice `L ≥ 2`.
    pub(super) fn dyadic(&mut self) -> Rat {
        let p = (self.next() % 7) as i64 - 3;
        let q = 1 << (self.next() % 3);
        rat(p, q)
    }

    /// A small half-integer `p/2`, `p ∈ [−3, 3]`: in `½ℤ`, on every lattice `L ≥ 1`.
    pub(super) fn half(&mut self) -> Rat {
        rat((self.next() % 7) as i64 - 3, 2)
    }

    pub(super) fn half_vector(&mut self, width: usize) -> Vec<Rat> {
        (0..width).map(|_| self.half()).collect()
    }

    pub(super) fn half_matrix(&mut self, rows: usize, columns: usize) -> ExactRatMatrix {
        ExactRatMatrix::shaped(
            rows,
            columns,
            (0..rows).map(|_| self.half_vector(columns)).collect(),
        )
        .unwrap()
    }

    pub(super) fn dyadic_vector(&mut self, width: usize) -> Vec<Rat> {
        (0..width).map(|_| self.dyadic()).collect()
    }

    pub(super) fn dyadic_matrix(&mut self, rows: usize, columns: usize) -> ExactRatMatrix {
        ExactRatMatrix::shaped(
            rows,
            columns,
            (0..rows).map(|_| self.dyadic_vector(columns)).collect(),
        )
        .unwrap()
    }

    pub(super) fn below(&mut self, bound: usize) -> usize {
        (self.next() % bound as u64) as usize
    }

    pub(super) fn vector(&mut self, width: usize) -> Vec<Rat> {
        (0..width).map(|_| self.rational()).collect()
    }

    pub(super) fn matrix(&mut self, rows: usize, columns: usize) -> ExactRatMatrix {
        ExactRatMatrix::shaped(
            rows,
            columns,
            (0..rows).map(|_| self.vector(columns)).collect(),
        )
        .unwrap()
    }
}

/// The sixteen integer points of `x² + y² = 65`, counterclockwise from `(8, 1)`.
const CIRCLE: [(i64, i64); 16] = [
    (8, 1),
    (7, 4),
    (4, 7),
    (1, 8),
    (-1, 8),
    (-4, 7),
    (-7, 4),
    (-8, 1),
    (-8, -1),
    (-7, -4),
    (-4, -7),
    (-1, -8),
    (1, -8),
    (4, -7),
    (7, -4),
    (8, -1),
];

/// A closing ring of `period ≤ 16` on the circle `x² + y² = 65` about `e_z`, pitch 0, reflector
/// `p ↦ −p`, at phase 0, with the declared lock.
pub(super) fn ring(period: u64, lock: Vec<u64>) -> RingDeclaration {
    RingDeclaration {
        period,
        screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
        placements: (0..period as usize)
            .map(|node| RatVec3::from_i64(CIRCLE[node].0, CIRCLE[node].1, 0))
            .collect(),
        lock,
        reflector: (0..period)
            .map(|p| ((period - p) % period) as usize)
            .collect(),
        admittance: integer(2),
        initial: 0,
    }
}

/// A contact matching the first `nodes` nodes of both ends, `Y_a = 2`, with exponent `β`.
pub(super) fn contact(from: usize, to: usize, nodes: usize, exponent: i64) -> ContactDeclaration {
    ContactDeclaration {
        from,
        to,
        channel: (0..nodes).map(|node| (node, node)).collect(),
        admittance: integer(2),
        exponent: integer(exponent),
    }
}

/// A small field for the tick's laws: rings of periods `periods` (all locks `{0}`), the declared
/// contacts, source ring 0, `|A| = 2`, `Δ = {1}`, receiver ring `receiver` with aperture 1.
pub(super) fn small_field(
    periods: &[u64],
    contacts: Vec<ContactDeclaration>,
    receiver: usize,
) -> Field {
    Field::declare(
        FieldDeclaration {
            rings: periods
                .iter()
                .map(|period| ring(*period, vec![0]))
                .collect(),
            contacts,
            loops: Vec::new(),
            sources: vec![0],
            offsets: vec![1],
            alphabet: 2,
            step: integer(1),
            exponent_grain: 1,
            receivers: vec![ReceiverDeclaration {
                ring: receiver,
                aperture: 1,
                tolerance: rat(1, 16),
            }],
            crib: CribDeclaration {
                window: 16,
                offset: 1,
            },
            population: 1 << 20,
            lattice: Default::default(),
        }
        .by_lattice_rule(),
    )
    .unwrap()
}

/// Five rings of periods 2, 3, 2, 3, 4: the five-cycle plus the chord 0–3, channels of one or two
/// nodes (so each `U_a` is a proper partial isometry), exponents 0 and 2.
pub(super) fn chorded_field() -> Field {
    small_field(
        &[2, 3, 2, 3, 4],
        vec![
            contact(0, 1, 2, 2),
            contact(1, 2, 1, 0),
            contact(2, 3, 2, 2),
            contact(3, 4, 2, 0),
            contact(4, 0, 1, 2),
            contact(0, 3, 1, 2),
        ],
        2,
    )
}

/// The six-cycle of rings of period 3, every node on the channel.
pub(super) fn six_cycle() -> Field {
    small_field(
        &[3; 6],
        (0..6).map(|g| contact(g, (g + 1) % 6, 3, 0)).collect(),
        3,
    )
}

/// Which parts of a generic constitution are nonzero.
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct Parts {
    pub(super) dissipative: bool,
    pub(super) resist: bool,
    pub(super) contrast: bool,
    pub(super) stiff: bool,
    pub(super) store: bool,
    pub(super) standing: bool,
}

/// A test constitution: every operand the forward pass reads.
#[derive(Clone, Debug)]
pub(super) struct Medium {
    pub(super) standing: Vec<Vec<Rat>>,
    pub(super) passive: Vec<ExactRatMatrix>,
    pub(super) contrast: Vec<ExactRatMatrix>,
    pub(super) slices: Vec<Vec<(Vec<Rat>, Vec<Rat>)>>,
    pub(super) source: Vec<Option<ExactRatMatrix>>,
    pub(super) pair: Vec<Option<PairPort>>,
    pub(super) storage: Vec<ExactRatMatrix>,
    pub(super) stiffness: Vec<ExactRatMatrix>,
    pub(super) dissipation: Vec<ExactRatMatrix>,
    pub(super) receiving: Vec<Option<ExactRatMatrix>>,
}

fn diagonal(n: usize, value: Rat) -> ExactRatMatrix {
    ExactRatMatrix::identity(n).unwrap().scaled(&value)
}

fn unit(n: usize, i: usize) -> Vec<Rat> {
    (0..n)
        .map(|j| if i == j { Rat::one() } else { Rat::zero() })
        .collect()
}

impl Medium {
    /// **Campaign 1's initial constitution** (design (d), "The initial constitution and its
    /// priors"): `E = 0`; the pair port's outputs 0 with `±1` reads; `R` a `±1` pattern times 1/2;
    /// `W_c = 0`; `W_s = −¼I`; the slices the skew cyclic shift; `q = 0`; `C = I`, `K = D = ¼I`.
    /// The `±1` patterns here come from the test generator, not the declared sign generator.
    pub(super) fn initial(field: &Field, seed: u64) -> Self {
        let mut draw = Draw::new(seed);
        let mut sign = move || {
            if draw.next() & 1 == 1 {
                Rat::one()
            } else {
                -Rat::one()
            }
        };
        let a = field.alphabet();
        let widths: Vec<usize> = field.rings().iter().map(|ring| ring.width()).collect();
        let receivers: Vec<usize> = field.receivers().iter().map(|r| r.ring).collect();
        Self {
            standing: widths.iter().map(|n| vec![Rat::zero(); *n]).collect(),
            passive: widths.iter().map(|n| diagonal(*n, rat(1, 2))).collect(),
            contrast: widths.iter().map(|n| diagonal(*n, Rat::zero())).collect(),
            slices: widths
                .iter()
                .map(|&n| {
                    (0..n)
                        .map(|rho| (unit(n, rho), unit(n, (rho + 1) % n)))
                        .collect()
                })
                .collect(),
            source: (0..widths.len())
                .map(|g| {
                    field
                        .is_source(g)
                        .then(|| ExactRatMatrix::zero(widths[g], a).unwrap())
                })
                .collect(),
            pair: (0..widths.len())
                .map(|g| {
                    field.is_source(g).then(|| {
                        let rank = widths[g];
                        PairPort::new(
                            vec![vec![Rat::zero(); widths[g]]; rank],
                            (0..rank)
                                .map(|_| (0..a).map(|_| sign()).collect())
                                .collect(),
                            (0..rank)
                                .map(|_| (0..a).map(|_| sign()).collect())
                                .collect(),
                        )
                        .unwrap()
                    })
                })
                .collect(),
            storage: field
                .contacts()
                .iter()
                .map(|c| diagonal(c.width(), Rat::one()))
                .collect(),
            stiffness: field
                .contacts()
                .iter()
                .map(|c| diagonal(c.width(), rat(1, 2)))
                .collect(),
            dissipation: field
                .contacts()
                .iter()
                .map(|c| diagonal(c.width(), rat(1, 2)))
                .collect(),
            receiving: (0..widths.len())
                .map(|g| {
                    receivers.contains(&g).then(|| {
                        ExactRatMatrix::shaped(
                            2 * a,
                            widths[g],
                            (0..2 * a)
                                .map(|_| (0..widths[g]).map(|_| sign() * rat(1, 2)).collect())
                                .collect(),
                        )
                        .unwrap()
                    })
                })
                .collect(),
        }
    }

    /// Campaign 1's initial constitution with a random encoder `E` and pair-port outputs on the
    /// source rings: the declared medium carrying a nonzero change.
    pub(super) fn encoding(field: &Field, seed: u64) -> Self {
        let mut draw = Draw::new(seed);
        let mut medium = Self::initial(field, seed ^ 0xA5);
        for ring in field.sources().to_vec() {
            let width = field.ring(ring).width();
            medium.source[ring] = Some(draw.matrix(width, field.alphabet()));
            let pair = medium.pair[ring].as_ref().unwrap();
            medium.pair[ring] = Some(
                PairPort::new(
                    (0..pair.rank()).map(|_| draw.vector(width)).collect(),
                    pair.current_reads().to_vec(),
                    pair.earlier_reads().to_vec(),
                )
                .unwrap(),
            );
        }
        medium
    }

    /// A generic constitution: random slices and ports, the declared parts nonzero.
    pub(super) fn generic(field: &Field, seed: u64, parts: Parts) -> Self {
        let mut draw = Draw::new(seed);
        let a = field.alphabet();
        let widths: Vec<usize> = field.rings().iter().map(|ring| ring.width()).collect();
        let zero = |n: usize| diagonal(n, Rat::zero());
        let mut medium = Self::initial(field, seed ^ 0x55);
        medium.standing = widths
            .iter()
            .map(|&n| {
                if parts.standing {
                    draw.vector(n)
                } else {
                    vec![Rat::zero(); n]
                }
            })
            .collect();
        medium.passive = widths
            .iter()
            .map(|&n| {
                if parts.resist {
                    draw.matrix(n, n)
                } else {
                    zero(n)
                }
            })
            .collect();
        medium.contrast = widths
            .iter()
            .map(|&n| {
                if parts.contrast {
                    draw.matrix(n, n).scaled(&rat(1, 8))
                } else {
                    zero(n)
                }
            })
            .collect();
        medium.slices = widths
            .iter()
            .map(|&n| (0..n).map(|_| (draw.vector(n), draw.vector(n))).collect())
            .collect();
        medium.source = (0..widths.len())
            .map(|g| field.is_source(g).then(|| draw.matrix(widths[g], a)))
            .collect();
        medium.pair = (0..widths.len())
            .map(|g| {
                field.is_source(g).then(|| {
                    PairPort::new(
                        (0..2).map(|_| draw.vector(widths[g])).collect(),
                        (0..2).map(|_| draw.vector(a)).collect(),
                        (0..2).map(|_| draw.vector(a)).collect(),
                    )
                    .unwrap()
                })
            })
            .collect();
        let contacts: Vec<usize> = field.contacts().iter().map(|c| c.width()).collect();
        medium.storage = contacts
            .iter()
            .map(|&k| {
                if parts.store {
                    draw.matrix(k, k)
                } else {
                    zero(k)
                }
            })
            .collect();
        medium.stiffness = contacts
            .iter()
            .map(|&k| {
                if parts.stiff {
                    draw.matrix(k, k)
                } else {
                    zero(k)
                }
            })
            .collect();
        medium.dissipation = contacts
            .iter()
            .map(|&k| {
                if parts.dissipative {
                    draw.matrix(k, k)
                } else {
                    zero(k)
                }
            })
            .collect();
        medium.receiving = (0..widths.len())
            .map(|g| {
                field
                    .receivers()
                    .iter()
                    .any(|r| r.ring == g)
                    .then(|| draw.matrix(2 * a, widths[g]))
            })
            .collect();
        medium
    }
}

impl ConstitutionRead for Medium {
    fn standing(&self, ring: usize) -> &[Rat] {
        &self.standing[ring]
    }
    fn passive_factor(&self, ring: usize) -> &ExactRatMatrix {
        &self.passive[ring]
    }
    fn contrast_port(&self, ring: usize) -> &ExactRatMatrix {
        &self.contrast[ring]
    }
    fn slices(&self, ring: usize) -> &[(Vec<Rat>, Vec<Rat>)] {
        &self.slices[ring]
    }
    fn source_port(&self, ring: usize) -> Option<&ExactRatMatrix> {
        self.source[ring].as_ref()
    }
    fn pair_port(&self, ring: usize, _offset: usize) -> Option<&PairPort> {
        self.pair[ring].as_ref()
    }
    fn contact_storage(&self, contact: usize) -> &ExactRatMatrix {
        &self.storage[contact]
    }
    fn contact_stiffness(&self, contact: usize) -> &ExactRatMatrix {
        &self.stiffness[contact]
    }
    fn contact_dissipation(&self, contact: usize) -> &ExactRatMatrix {
        &self.dissipation[contact]
    }
    fn receiving_map(&self, ring: usize) -> Option<&ExactRatMatrix> {
        self.receiving[ring].as_ref()
    }
    fn harmonic(&self, _ring: usize) -> Option<&[Rat]> {
        None
    }
}

/// A lift point with the declared phase classes.
pub(super) fn lift(phases: &[i64]) -> Vec<BigInt> {
    phases.iter().map(|p| BigInt::from(*p)).collect()
}

/// A random storage injection on every ring.
pub(super) fn injection(field: &Field, seed: u64) -> Vec<Vec<Rat>> {
    let mut draw = Draw::new(seed);
    field
        .rings()
        .iter()
        .map(|ring| draw.vector(ring.width()))
        .collect()
}

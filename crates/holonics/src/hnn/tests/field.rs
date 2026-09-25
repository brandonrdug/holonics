//! The field's declaration checks, selective stepping, the lift point and the exact code.

use num_bigint::{BigInt, BigUint};

use super::learning::{OPEN_BUDGET, chain_declaration, generic};
use super::support::{Draw, chorded_field, contact, ring, small_field};
use crate::geometry::RatVec3;
use crate::hnn::HnnError;
use crate::hnn::constitution::{Constitution, Locus, Steps};
use crate::hnn::field::ConstitutionRead;
use crate::hnn::field::{Current, End, Field, FieldDeclaration};
use crate::hnn::moment::capacity;
use crate::holon::conformance::check_tellegen;
use crate::ratio::Rat;
use crate::ratio::linear::vector::{form_matrix, is_zero};
use crate::ratio::{integer, rat};

/// Campaign 1's declared values, read from its declaration (design (d), "Declared values"): four
/// closing rings of periods 5, 7, 11, 13 in carry order, locks `{0}` on rings 0–2 and `∅` on ring 3,
/// reflectors `p ↦ −p`, every ring at phase 0 with `Y_g = 2`, node `k` at the quarter turn `⌊4k/d⌋`
/// (nodes 0 and 1 of ring 0 share `(1, 0)`: the period is combinatorial, review C2), the 4-cycle
/// with channels matching node `i < min(d_g, d_h)`, `β_a = 2`, `Y_a = 2`, its one loop, `𝒮 = {0}`,
/// `Δ = {1}`, `|A| = 256`, `h = 1`, `L = 1`, the receiver on ring 2 with aperture 2 and tolerance
/// 1/16, and the crib `W = 64` at offset 1. The field these declare is not built here (no test
/// builds a campaign's declared field): its capacity `n* = 6,148` is counted without declaring it
/// (`tests/moment.rs`), each law the declaration relies on is tested on the chain control or smaller,
/// and its readings are the notebook's release receipts (`research/notebook/hnn_design`).
#[test]
fn campaign_one_declares_its_values() {
    let declared = FieldDeclaration::campaign_one(6_148);
    let periods: Vec<u64> = declared.rings.iter().map(|r| r.period).collect();
    assert_eq!(periods, vec![5, 7, 11, 13]);
    let locks: Vec<&[u64]> = declared.rings.iter().map(|r| r.lock.as_slice()).collect();
    assert_eq!(locks, vec![&[0][..], &[0], &[0], &[]]);
    for ring in &declared.rings {
        let d = ring.period;
        assert!((0..d).all(|p| ring.reflector[p as usize] as u64 == (d - p) % d));
        assert!(
            (0..d).all(|k| ring.placements[k as usize] == FieldDeclaration::quarter_turn(k, d))
        );
        assert_eq!((ring.admittance.clone(), ring.initial), (integer(2), 0));
    }
    let quarter = |x, y| RatVec3::from_i64(x, y, 0);
    assert_eq!(
        declared.rings[0].placements,
        vec![
            quarter(1, 0),
            quarter(1, 0),
            quarter(0, 1),
            quarter(-1, 0),
            quarter(0, -1)
        ]
    );
    let contacts: Vec<(usize, usize, usize)> = declared
        .contacts
        .iter()
        .map(|c| (c.from, c.to, c.channel.len()))
        .collect();
    assert_eq!(contacts, vec![(0, 1, 5), (1, 2, 7), (2, 3, 11), (3, 0, 5)]);
    for contact in &declared.contacts {
        assert!(
            contact
                .channel
                .iter()
                .enumerate()
                .all(|(i, &(g, h))| g == i && h == i)
        );
        assert_eq!(
            (contact.admittance.clone(), contact.exponent.clone()),
            (integer(2), integer(2))
        );
    }
    assert_eq!(declared.loops, vec![vec![0, 1, 2, 3]]);
    assert_eq!(
        (declared.sources.clone(), declared.offsets.clone()),
        (vec![0], vec![1])
    );
    assert_eq!(
        (declared.alphabet, declared.step.clone()),
        (256, integer(1))
    );
    assert_eq!(declared.exponent_grain, 1);
    let receiver = &declared.receivers[..];
    assert_eq!(receiver.len(), 1);
    assert_eq!(
        (
            receiver[0].ring,
            receiver[0].aperture,
            receiver[0].tolerance.clone()
        ),
        (2, 2, rat(1, 16))
    );
    assert_eq!((declared.crib.window, declared.crib.offset), (64, 1));
    assert_eq!(declared.population, 6_148);
}

/// Guard 1: a population shorter than `n*` would leave the moment lossless, so it is refused, and
/// the capacity itself is admitted (the chain control, `n* = 71`).
#[test]
fn a_population_below_capacity_is_refused() {
    let n_star = capacity(&[2, 3, 2], &[0], 4, &[1]).unwrap().n_star();
    assert_eq!(n_star, 71);
    assert_eq!(
        Field::declare(chain_declaration(n_star - 1)),
        Err(HnnError::BelowCapacity {
            population: 70,
            n_star: 71
        })
    );
    assert!(Field::declare(chain_declaration(n_star)).is_ok());
}

/// One exponent per contact on its lattice `(2q_Q/L)ℤ`: with integer placements (`q_Q = 1`) and
/// `L = 1`, `β = 1` and `β = 3` are refused and `β = 0, 2, −4` admitted; `L = 2` admits `β = 1`.
#[test]
fn each_contact_exponent_lies_on_its_lattice() {
    for (beta, admitted) in [(0, true), (2, true), (-4, true), (1, false), (3, false)] {
        let mut declared = chain_declaration(1 << 20);
        declared.contacts[1].exponent = integer(beta);
        let result = Field::declare(declared);
        assert_eq!(result.is_ok(), admitted, "beta = {beta}");
        if !admitted {
            assert!(matches!(
                result,
                Err(HnnError::ExponentLattice { contact: 1, .. })
            ));
        }
    }
    let mut declared = chain_declaration(1 << 20);
    declared.exponent_grain = 2;
    declared.contacts[1].exponent = integer(1);
    assert!(Field::declare(declared).is_ok());
}

/// The declared lattices are exactly the learned loci, each at least the rule's
/// `⌈log₂(2 L_R X_ℓ)⌉`: a missing or an unlearned locus is refused, and so is a lattice coarser than
/// the rule's (the carried Gram's positivity and a read's bound below the grain need
/// `2 L_R X_ℓ ≤ 2^(L_ℓ)`); a finer one is admitted.
#[test]
fn each_declared_lattice_is_a_learned_locus_at_least_the_rule() {
    let declared = chain_declaration(1 << 20);
    let rule = declared.lattice_by_rule();
    let refuse = |edit: &dyn Fn(&mut FieldDeclaration)| {
        let mut declared = declared.clone();
        edit(&mut declared);
        Field::declare(declared)
    };
    assert_eq!(
        refuse(&|d| {
            d.lattice.remove(&Locus::Element(1));
        }),
        Err(HnnError::Lattice {
            locus: Locus::Element(1)
        })
    );
    assert_eq!(
        refuse(&|d| {
            d.lattice.insert(Locus::Junction(0), 9);
        }),
        Err(HnnError::Lattice {
            locus: Locus::Junction(0)
        })
    );
    let least = rule[&Locus::Channel(0)];
    assert_eq!(
        refuse(&|d| {
            d.lattice.insert(Locus::Channel(0), least - 1);
        }),
        Err(HnnError::LatticeBelowRule {
            locus: Locus::Channel(0),
            declared: least - 1,
            rule: least
        })
    );
    assert!(
        refuse(&|d| {
            d.lattice.insert(Locus::Channel(0), least + 3);
        })
        .is_ok()
    );
}

/// A ring is a closing rotor on its screw's circle: a period below 2, a placement off the circle,
/// a reflector that is not an involution, a notch outside the port chart and a screw with no
/// rotating axis are each refused; so are a channel matching a node twice and a contact from a ring
/// to itself.
#[test]
fn only_closing_rings_on_their_circle_are_declared() {
    let refuse = |edit: &dyn Fn(&mut FieldDeclaration)| {
        let mut declared = chain_declaration(1 << 20);
        edit(&mut declared);
        Field::declare(declared).unwrap_err()
    };
    assert!(matches!(
        refuse(&|d| {
            d.rings[2] = ring(1, vec![]);
        }),
        HnnError::RingPeriod { ring: 2, period: 1 }
    ));
    assert!(matches!(
        refuse(&|d| d.rings[1].placements[2] = RatVec3::from_i64(8, 0, 0)),
        HnnError::NotOnCircle { ring: 1, node: 2 }
    ));
    assert!(matches!(
        refuse(&|d| d.rings[1].placements[2] = RatVec3::from_i64(8, 1, 1)),
        HnnError::NotOnCircle { ring: 1, node: 2 }
    ));
    assert!(matches!(
        refuse(&|d| d.rings[1].reflector = vec![1, 2, 0]),
        HnnError::Reflector { ring: 1 }
    ));
    assert!(matches!(
        refuse(&|d| d.rings[0].lock = vec![2]),
        HnnError::Notch { ring: 0, .. }
    ));
    assert!(matches!(
        refuse(&|d| {
            d.rings[0].screw = crate::geometry::screw::ScrewGenerator::new(
                RatVec3::zero(),
                RatVec3::from_i64(0, 0, 1),
            )
        }),
        HnnError::NoRingAxis { ring: 0 }
    ));
    assert!(matches!(
        refuse(&|d| d.contacts[0].channel.push((0, 0))),
        HnnError::Channel { contact: 0, .. }
    ));
    assert!(matches!(
        refuse(&|d| d.contacts[0].to = 0),
        HnnError::SelfContact { contact: 0, .. }
    ));
}

/// Lean `HNN/Keys.selective_step_dormant`: a ring whose lock no input fits and that receives no
/// carry keeps its configuration; a ring steps by its lock plus its predecessor's carry, and the
/// last ring's carry is the joint clock's carry-out.
#[test]
fn selective_stepping_steps_by_lock_and_carry_and_a_dormant_ring_keeps_its_phase() {
    let field = small_field(
        &[2, 3, 2],
        vec![contact(0, 1, 1, 0), contact(1, 2, 1, 0)],
        2,
    );
    // Locks {0} on every ring; code 1 has port 1 on every ring, so nothing steps.
    let mut current = Current::at_rest(&field);
    for _ in 0..5 {
        let step = current.step(&field, 1).unwrap();
        assert_eq!(step.ticks, vec![0, 0, 0]);
    }
    assert_eq!(current.lift(), Current::at_rest(&field).lift());
    // Code 0 fits ring 0's lock (0 mod 2) and ring 1's (0 mod 3) and ring 2's (0 mod 2).
    let mut current = Current::at_rest(&field);
    let first = current.step(&field, 0).unwrap();
    assert_eq!(first.ticks, vec![1, 1, 1]);
    // Ring 0 wraps at its second step and carries into ring 1, which wraps and carries into
    // ring 2: each later ring takes its lock step plus the carry.
    let second = current.step(&field, 0).unwrap();
    assert_eq!(second.ticks, vec![1, 2, 2]);
    assert!(second.carry_out, "ring 2 steps 1 → 3 and wraps");
    assert_eq!(
        current.lift(),
        &[BigInt::from(2), BigInt::from(3), BigInt::from(3)]
    );
    assert_eq!(current.phase(&field, 1).unwrap(), 0);
    assert_eq!(current.winding(&field, 1).unwrap(), BigInt::from(1));
    assert!(matches!(
        current.step(&field, 2),
        Err(HnnError::CellOutside { code: 2, .. })
    ));
}

/// Re-keying sets a ring's phase class and keeps its winding; the jump is reported.
#[test]
fn rekeying_moves_only_the_phase_class() {
    let field = small_field(&[5, 2], vec![contact(0, 1, 1, 0)], 1);
    let mut current = Current::at(&field, vec![BigInt::from(17), 0.into()]).unwrap();
    assert_eq!(current.phase(&field, 0).unwrap(), 2);
    let jump = current.rekey(&field, 0, 4).unwrap();
    assert_eq!(jump, 2);
    assert_eq!(current.lift()[0], BigInt::from(19));
    assert_eq!(current.winding(&field, 0).unwrap(), BigInt::from(3));
    assert!(current.rekey(&field, 0, 5).is_err());
    assert!(Current::at(&field, vec![BigInt::from(-1), 0.into()]).is_err());
}

/// `U_a = ι_to ι_fromᵀ` is a partial isometry with reverse `U_aᵀ`: the connection's block
/// `T_a = U_aᵀ` satisfies `T Tᵀ T = T` and moves a vector's matched coordinates only (Lean
/// `HNN/Propagation.partialIsometry_transit`).
#[test]
fn the_channel_is_a_partial_isometry_with_its_transpose_as_reverse() {
    let field = chorded_field();
    let connection = field.connection();
    let mut draw = super::support::Draw::new(3);
    for (a, contact) in field.contacts().iter().enumerate() {
        let (g, h) = contact.ends();
        let (wg, wh) = (field.ring(g).width(), field.ring(h).width());
        let block = connection.transport(a).unwrap();
        assert_eq!((block.rows(), block.columns()), (wg, wh));
        let transpose = block.transpose().unwrap();
        assert_eq!(
            &block.multiply(&transpose).unwrap().multiply(block).unwrap(),
            block
        );
        let y = draw.vector(wh);
        let carried = block.apply(&y).unwrap();
        for (i, j) in contact
            .selection(End::From)
            .into_iter()
            .zip(contact.selection(End::To))
        {
            assert_eq!(carried[i], y[j]);
        }
        assert!(contact.width() < wg.max(wh), "a proper partial isometry");
    }
}

/// The contrast map `(M x)_r = Σ_(s a = r) T_a x_(t a) + Σ_(t a = r) T_aᵀ x_(s a) − x_r` read from
/// the connection's blocks is the design's standing contrast `Σ_(a∋r) U_(r←a) q_other − q_r`, and it
/// is symmetric, `⟨M x, y⟩ = ⟨x, M y⟩`, so the class covectors pull back to `q` through it.
#[test]
fn the_contrast_map_reads_the_connection_and_is_symmetric() {
    let field = chorded_field();
    let mut draw = super::support::Draw::new(9);
    let widths: Vec<usize> = field.rings().iter().map(|ring| ring.width()).collect();
    let x: Vec<Vec<Rat>> = widths.iter().map(|n| draw.vector(*n)).collect();
    let y: Vec<Vec<Rat>> = widths.iter().map(|n| draw.vector(*n)).collect();
    fn fields(v: &[Vec<Rat>]) -> Vec<&[Rat]> {
        v.iter().map(Vec::as_slice).collect()
    }
    let dot = crate::ratio::linear::vector::dot;
    let (mut left, mut right) = (Rat::from_integer(0.into()), Rat::from_integer(0.into()));
    for r in 0..widths.len() {
        let mx = field.contrast(r, &fields(&x)).unwrap();
        let mut expected: Vec<Rat> = x[r].iter().map(|v| -v).collect();
        for &a in field.incident(r) {
            let contact = field.contact(a);
            let (from, to) = contact.ends();
            let (here, there, other) = if from == r {
                (End::From, End::To, to)
            } else {
                (End::To, End::From, from)
            };
            for (i, j) in contact
                .selection(here)
                .into_iter()
                .zip(contact.selection(there))
            {
                expected[i] += &x[other][j];
            }
        }
        assert_eq!(mx, expected);
        left += dot(&mx, &y[r]);
        right += dot(&x[r], &field.contrast(r, &fields(&y)).unwrap());
    }
    assert_eq!(left, right);
    assert!(field.contrast(0, &fields(&x[1..])).is_err());
}

/// Every ring is a closing rotor (the cyclic shift of finite order `d_g`, its reflector `p ↦ −p`),
/// the parametric complex is the joint clock torus of the rings' periods, and the pair quadrance of
/// two rings reads their screws at their phases.
#[test]
fn the_field_reads_its_clock_torus_and_pair_geometry() {
    let field = small_field(&[2, 3], vec![contact(0, 1, 1, 0)], 1);
    for ring in field.rings() {
        assert_eq!(
            ring.machine().unwrap().period(),
            &BigUint::from(ring.period())
        );
        assert_eq!(
            ring.navigator().transport().order(),
            Some(BigUint::from(ring.period()))
        );
        assert_eq!(ring.reflection(0), 0);
        assert_eq!(ring.reflection(1) as u64, ring.period() - 1);
    }
    let torus = field.parametric();
    assert_eq!(torus.periods(), &[2u32, 3].map(BigUint::from)[..]);
    let at_rest = Current::at_rest(&field);
    assert_eq!(
        field.contact(0).pair(&field, at_rest.lift()).quadrance(),
        &integer(0)
    );
    // Ring 0 at phase 1 sits at (7, 4), ring 1 at phase 0 at (8, 1): Q = 1 + 9.
    let moved = Current::at(&field, vec![1.into(), 0.into()]).unwrap();
    assert_eq!(
        field.contact(0).pair(&field, moved.lift()).quadrance(),
        &integer(10)
    );
    // Pitch 0: a winding does not move a node.
    let wound = Current::at(&field, vec![3.into(), 0.into()]).unwrap();
    assert_eq!(
        field.contact(0).pair(&field, wound.lift()).quadrance(),
        &integer(10)
    );
}

/// The one exact code: every declared value changes it, the constitution's declared steps, budget
/// and the pending capacity included (review D3), and it is self-delimiting per field.
#[test]
fn describe_is_the_fields_exact_code() {
    let field = Field::declare(chain_declaration(1 << 20)).unwrap();
    let steps = Steps::campaign_one();
    let (budget, pending) = (crate::hnn::constitution::CAMPAIGN_ONE_BUDGET, 64);
    let describe = |field: &Field| field.describe(&steps, budget, pending);
    let code = describe(&field);
    assert!(!code.is_empty());
    let mut declared = chain_declaration(1 << 20);
    declared.receivers[0].tolerance = rat(1, 8);
    assert_ne!(describe(&Field::declare(declared).unwrap()), code);
    let mut declared = chain_declaration(1 << 20);
    declared.rings[2].initial = 1;
    assert_ne!(describe(&Field::declare(declared).unwrap()), code);
    let mut declared = chain_declaration(1 << 20);
    declared.contacts[1].admittance = integer(3);
    assert_ne!(describe(&Field::declare(declared).unwrap()), code);
    let halved = Steps {
        proxy: rat(1, 2),
        factor: steps.factor.clone(),
    };
    assert_ne!(field.describe(&halved, budget, pending), code);
    let slower = Steps {
        proxy: steps.proxy.clone(),
        factor: rat(1, 4),
    };
    assert_ne!(field.describe(&slower, budget, pending), code);
    assert_ne!(field.describe(&steps, budget / 2, pending), code);
    assert_ne!(field.describe(&steps, budget, pending + 1), code);
    assert_eq!(
        describe(&Field::declare(chain_declaration(1 << 20)).unwrap()),
        code
    );
}

/// Addition 2 (review F4; Lean `Holon/Complex.{blockIncidence, block_flat_closed}`): the field's
/// block connection incidence has one block per contact, the partial isometry `U_aᵀ` from ring
/// `h`'s nodes to ring `g`'s, so `(d_A q)_a = U_aᵀ q_h − q_g`: on the channel it is the transit's
/// difference `ι_hᵀ q_h − ι_gᵀ q_g`, off it `−q_g`. Its underlying complex is the field's
/// 1-skeleton with its declared loop as the one 2-cell (`∂∘∂ = 0`, no 1-cycle left), and on the
/// triangle whose loop carries every node of ring 0 around, the loop is flat and its covariant
/// face coboundary composes with `d_A` to zero.
#[test]
fn the_field_connection_is_the_block_incidence_of_its_channels() {
    let mut declared = chain_declaration(1 << 20);
    declared.rings = vec![ring(2, vec![0]), ring(2, vec![0]), ring(2, vec![])];
    declared.contacts = vec![
        contact(0, 1, 2, 2),
        contact(1, 2, 2, 0),
        contact(2, 0, 2, 0),
    ];
    declared.loops = vec![vec![0, 1, 2]];
    let field = Field::declare(declared.by_lattice_rule()).unwrap();
    assert_eq!(field.complex().cells(0), 3);
    assert_eq!(field.complex().cells(1), 3);
    assert_eq!(field.complex().cells(2), 1);
    assert_eq!(field.complex().betti(1).unwrap(), 0);
    let connection = field.connection();
    assert_eq!(
        connection.cell_complex().unwrap().boundary(1),
        field.complex().boundary(1)
    );
    let d = connection.matrix().unwrap();
    let sigma: usize = field.rings().iter().map(|ring| ring.width()).sum();
    assert_eq!((d.rows(), d.columns()), (sigma, sigma));
    let mut draw = Draw::new(5);
    let q: Vec<Rat> = (0..sigma).map(|_| draw.rational()).collect();
    let dq = d.apply(&q).unwrap();
    let offsets: Vec<usize> = field
        .rings()
        .iter()
        .scan(0, |at, ring| {
            let here = *at;
            *at += ring.width();
            Some(here)
        })
        .collect();
    let mut edge = 0;
    for contact in field.contacts() {
        let (g, h) = contact.ends();
        let width = field.ring(g).width();
        for coordinate in 0..width {
            let own = &q[offsets[g] + coordinate];
            let expected = match contact
                .selection(crate::hnn::field::End::From)
                .iter()
                .position(|c| *c == coordinate)
            {
                Some(j) => &q[offsets[h] + contact.selection(crate::hnn::field::End::To)[j]] - own,
                None => -own,
            };
            assert_eq!(dq[edge + coordinate], expected);
        }
        edge += width;
    }
    let loops = field.loop_walks();
    assert_eq!(loops.len(), 1);
    assert!(is_zero(
        connection
            .curvature(&loops[0].0, loops[0].1)
            .unwrap()
            .entries()
    ));
    let closed = connection
        .face_coboundary(&loops)
        .unwrap()
        .multiply(&d)
        .unwrap();
    assert!(is_zero(closed.entries()));
    assert!(connection.kirchhoff().is_ok());
}

/// Design (c) `Field::holon()` (review F2), block by block (guard 14): every ring and every contact
/// is its own Holon, certified on its own; the Holarchy keeps them and its gluing, and its whole,
/// assembled only when read, is Dirac (Tellegen), its navigators the rings' closing maps, and its
/// element relations the blocks read from the one constitution: ring 0's resistance is
/// `−W_s = f fᵀ`, contact 0's storage `(K_a, C_a⁻¹)`. The chart is rebuilt from a changed
/// constitution, never carried as a second owner, and a singular contact storage is refused.
#[test]
fn the_field_holon_is_a_read_only_holarchy_of_rings_and_contacts() {
    let field = small_field(&[2, 2], vec![contact(0, 1, 1, 0)], 1);
    let theta = generic(&field, 7);
    let holarchy = field.holon(&theta).unwrap();
    let sigma: usize = field.rings().iter().map(|ring| ring.width()).sum();
    let states: usize = field.contacts().iter().map(|c| 2 * c.width()).sum();
    let whole = holarchy.whole();
    let counts = whole.counts();
    assert_eq!((counts.storage, counts.external), (sigma + states, 0));
    assert_eq!(whole.navigators().len(), field.rings().len());
    for (navigator, ring) in whole.navigators().iter().zip(field.rings()) {
        assert_eq!(
            navigator.transport().order(),
            Some(BigUint::from(ring.period()))
        );
    }
    // Read: the whole is assembled once, from the retained blocks.
    assert!(check_tellegen(whole.port_holon().dirac()).unwrap() > 0);
    let width = field.ring(0).width();
    let factor = theta.passive_factor(0);
    let resistance = whole.port_holon().resistance().resistance();
    for i in 0..width {
        for j in 0..width {
            let expected: Rat = (0..factor.columns())
                .map(|m| factor.get(i, m).unwrap() * factor.get(j, m).unwrap())
                .sum();
            assert_eq!(resistance.get(i, j).unwrap(), &expected);
        }
    }
    let storage = form_matrix(whole.port_holon().storage());
    let k = field.contact(0).width();
    let (stiffness, store) = (theta.contact_stiffness(0), theta.contact_storage(0));
    let gram =
        |m: &crate::ratio::linear::ExactRatMatrix| m.multiply(&m.transpose().unwrap()).unwrap();
    let compliance = gram(store).inverse().unwrap();
    for i in 0..k {
        for j in 0..k {
            assert_eq!(
                storage.get(sigma + i, sigma + j).unwrap(),
                gram(stiffness).get(i, j).unwrap()
            );
            assert_eq!(
                storage.get(sigma + k + i, sigma + k + j).unwrap(),
                compliance.get(i, j).unwrap()
            );
        }
    }
    let initial = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET).unwrap();
    let other = field.holon(&initial).unwrap();
    assert_ne!(other.whole().active(), whole.active());
    // A singular contact storage has no momentum chart and is refused, not pseudo-inverted.
    let singular = initial
        .with_channel(
            0,
            crate::ratio::linear::ExactRatMatrix::zero(k, k).unwrap(),
            crate::ratio::linear::ExactRatMatrix::identity(k).unwrap(),
            crate::ratio::linear::ExactRatMatrix::identity(k).unwrap(),
        )
        .unwrap();
    assert!(matches!(field.holon(&singular), Err(HnnError::Linear(_))));
}

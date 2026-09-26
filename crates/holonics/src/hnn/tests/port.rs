//! The word's return and the execution port: the return is the exact adjoint of the word's tangent
//! map up to the logits, every material gradient is the directional derivative exactly (the
//! difference quotient on linear loci, the separately implemented tangent word elsewhere), each
//! method returns its six components, the clock law of ingest and keys, per-ring receipts in their
//! own clocks, the pending capacity and the release at width zero. The return reads the word's own
//! stored per-tick waves, the sanctioned realization; no checkpoint scheme is built.

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::learning::{chain, chain_with, generic, moment, pairing, phases};
use super::support::Draw;
use crate::hnn::HnnError;
use crate::hnn::constitution::{Constitution, Steps};
use crate::hnn::field::{ConstitutionRead, Current, End, Field};
use crate::hnn::moment::PairPort;
use crate::hnn::pending::PendingRatio;
use crate::hnn::port::{ExecutionPort, Handle, Pullback, ReceiptDetail, Transpose, WordReturn};
use crate::hnn::propagation::{Operands, contact_exponent, element_step, junction_swing, transit};
use crate::hnn::ratio::{Faces, HolonRatio, RatioCovector, TargetPhases, target_phases};
use crate::hnn::receiving::ActiveAddress;
use crate::hnn::reference::{Reference, compose, one_hot};
use crate::hnn::word::Word;
use crate::ratio::exponentiated::power_of_two;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, dot, scale, sub};
use crate::ratio::{Rat, integer, rat};
use crate::receiver::reception::{Component, InteractionReturn};
use crate::receiver::release::{BeyondTolerance, DecisionRule, WithinTolerance};

/// A word opened on a storage injection on every ring, its wave's logits and a covector from a
/// ratio against drawn targets.
fn injected(
    field: &Field,
    theta: &Constitution,
    seed: u64,
) -> (Vec<Vec<Rat>>, Vec<Vec<Rat>>, RatioCovector, Current) {
    let mut draw = Draw::new(seed);
    let current = Current::at(
        field,
        vec![BigInt::from(3), BigInt::from(4), BigInt::from(1)],
    )
    .unwrap();
    let phases = phases(field, theta, &current);
    let storage: Vec<Vec<Rat>> = field
        .rings()
        .iter()
        .map(|ring| draw.vector(ring.width()))
        .collect();
    let mut word = Word::open_on(field, theta, &current, storage.clone()).unwrap();
    let anchors = word.forward(&phases).unwrap();
    // The wave's reads: the tree part is a stored face and no function of the storage, so the
    // word's linear map from its opening storage is paired alone.
    let reads: Vec<_> = anchors
        .iter()
        .map(|anchor| phases.read(field, theta, &current, anchor).unwrap())
        .collect();
    let faces = Faces::of_reads(&reads, phases.grain()).unwrap();
    let logits = faces.logits.clone();
    let targets = [draw.below(4), draw.below(4)];
    let ratio = HolonRatio::compare(
        faces,
        &targets,
        &TargetPhases {
            branch: BigInt::from(3),
            phases: vec![draw.rational(), integer(1) + draw.rational()],
        },
    )
    .unwrap();
    (storage, logits, ratio.covector().unwrap(), current)
}

/// Design (d), "Word adjoint": `⟨g, T v⟩ = ⟨T* g, v⟩` exactly up to the logits, with `T` the word's
/// tangent map from the opening storage of every ring (Lean
/// `HolonicAdjointNormalization.dualMap_comp_reverse_order`, `HNN/Word.reaction_stage_adjoint`),
/// under the exact law.
#[test]
fn the_word_return_is_the_exact_adjoint_of_its_tangent_map() {
    let field = chain().with_exact_word();
    let theta = generic(&field, 61);
    let (storage, logits, covector, current) = injected(&field, &theta, 62);
    let phases = phases(&field, &theta, &current);
    let mut word = Word::open_on(&field, &theta, &current, storage.clone()).unwrap();
    word.forward(&phases).unwrap();
    let back = word
        .pull_back(
            &covector,
            theta.receiving_map(2).unwrap(),
            &current.lift()[2],
            &phases,
        )
        .unwrap();
    assert_eq!(
        pairing(covector.logits(), &logits),
        pairing(&back.opening, &storage)
    );
    assert!(!pairing(&back.opening, &storage).is_zero());
}

/// Lean `HNN/LatticeWord.{executed_adjoint_pairing, executed_adjoint_unique}` on the word: the return
/// pulls the covector back through the transposes of the charts the word executed (the lattice
/// charts of `(I − ½K)⁻¹` and `m⁻¹`, the junctions' charted weights), not through exact inverses.
/// On the executed charts with no transient split, `⟨g, T̂ v⟩ = ⟨T̂ᵀ g, v⟩` exactly; the exact law's
/// return, a different adjoint, pairs exactly only with its own word. On the lattices the return's
/// released remainders lie in their half-open cells.
#[test]
fn the_word_return_pulls_back_through_the_executed_charts() {
    let field = chain();
    let theta = generic(&field, 61);
    let (storage, _, _, current) = injected(&field.clone().with_exact_word(), &theta, 62);
    let phases = phases(&field, &theta, &current);
    let pulled = |operands: Operands| {
        let mut word = Word::on_operands(&field, operands, storage.clone()).unwrap();
        let anchors = word.forward(&phases).unwrap();
        let reads: Vec<_> = anchors
            .iter()
            .map(|anchor| phases.read(&field, &theta, &current, anchor).unwrap())
            .collect();
        let faces = Faces::of_reads(&reads, phases.grain()).unwrap();
        let logits = faces.logits.clone();
        let covector = HolonRatio::compare(
            faces,
            &[1, 3],
            &TargetPhases {
                branch: BigInt::from(3),
                phases: vec![rat(1, 3), rat(4, 3)],
            },
        )
        .unwrap()
        .covector()
        .unwrap();
        let back = word
            .pull_back(
                &covector,
                theta.receiving_map(2).unwrap(),
                &current.lift()[2],
                &phases,
            )
            .unwrap();
        (logits, covector, back)
    };
    let charted = Operands::at_cut(&field, &theta, &current).unwrap();
    let (logits, covector, back) = pulled(charted.clone().unsplit().unwrap());
    assert_eq!(
        pairing(covector.logits(), &logits),
        pairing(&back.opening, &storage),
        "the executed adjoint pairs exactly with the executed charts"
    );
    assert_eq!(back.released.entries, 0, "no split, no remainder");
    let exact = Operands::exact_at_cut(&field, &theta, &current).unwrap();
    let (exact_logits, exact_covector, exact_back) = pulled(exact);
    assert_eq!(
        pairing(exact_covector.logits(), &exact_logits),
        pairing(&exact_back.opening, &storage)
    );
    assert_ne!(
        exact_back.opening, back.opening,
        "the charts are not the exact inverses"
    );
    let (_, _, lattice_back) = pulled(charted);
    let unit = field.word_lattice().unwrap().transient().unit();
    assert!(lattice_back.released.entries > 0);
    assert!(lattice_back.released.largest <= unit / integer(2));
}

/// The compare at one cut: its pending ratio, fixed covector and complete pullback.
struct Cut {
    field: Field,
    theta: Constitution,
    pending: PendingRatio,
    covector: RatioCovector,
    pullback: Pullback,
    back: WordReturn,
    /// `J(θ)` at the cut's own constitution.
    base: Rat,
    /// The word's operands at the cut's own constitution, charted once.
    operands: Operands,
}

/// The compare at one cut of the chain at a constitution: the pending ratio of a drawn stream, its
/// covector against fixed targets, the word's return and the complete pullback.
fn cut_at(field: Field, theta: Constitution) -> Cut {
    let (current, open) = moment(&field, 66, 13);
    let phases = phases(&field, &theta, &current);
    let pending = PendingRatio::produce(
        &current,
        &open,
        &ActiveAddress::boundary(phases.depth()),
        &phases,
        0,
    )
    .unwrap();
    let (word, faces) = pending.read(&field, &theta).unwrap();
    let operands = word.operands().clone();
    let targets = [2usize, 1];
    let anchors = target_phases(&field, pending.anchor(), 2, &targets).unwrap();
    let faces_logits = faces.logits.clone();
    // The covector is the combined face's (the tree's at each phase's address plus the wave's); the
    // functional pairs it with the wave's logits, the tree part being a stored face.
    let combined = pending.against(&theta, &faces, &targets).unwrap().faces;
    let covector = HolonRatio::compare(combined, &targets, &anchors)
        .unwrap()
        .covector()
        .unwrap();
    let back = word
        .pull_back(
            &covector,
            theta.receiving_map(2).unwrap(),
            &pending.anchor()[2],
            &phases,
        )
        .unwrap();
    let (pullback, _) = compose(&field, &theta, &pending, &back, &targets).unwrap();
    let base = pairing(covector.logits(), &faces_logits);
    Cut {
        field,
        theta,
        pending,
        covector,
        pullback,
        back,
        base,
        operands,
    }
}

/// The chain's cut at a generic constitution, built once and shared by the pullback's laws.
fn cut() -> &'static Cut {
    static CUT: std::sync::OnceLock<Cut> = std::sync::OnceLock::new();
    CUT.get_or_init(|| {
        let field = chain().with_exact_word();
        let theta = generic(&field, 65);
        cut_at(field, theta)
    })
}

impl Cut {
    /// `J(θ) = Σ_j ⟨g_j, f_j(θ)⟩` at a pending ratio and constitution, `g` fixed.
    fn functional_of(&self, pending: &PendingRatio, theta: &Constitution) -> Rat {
        let (_, faces) = pending.read(&self.field, theta).unwrap();
        pairing(self.covector.logits(), &faces.logits)
    }

    /// The difference quotient along a perturbed constitution.
    fn quotient(&self, perturbed: &Constitution, epsilon: &Rat) -> Rat {
        (self.functional_of(&self.pending, perturbed) - &self.base) / epsilon
    }
}

fn frobenius(a: &ExactRatMatrix, b: &ExactRatMatrix) -> Rat {
    a.entries()
        .iter()
        .zip(b.entries())
        .map(|(x, y)| x * y)
        .sum()
}

fn nested(a: &[Vec<Rat>], b: &[Vec<Rat>]) -> Rat {
    pairing(a, b)
}

/// `(p − m)/2`, entrywise.
fn central(p: &ExactRatMatrix, m: &ExactRatMatrix) -> ExactRatMatrix {
    p.subtract(m).unwrap().scaled(&rat(1, 2))
}

/// **The separately implemented tangent word** (design (d), "Word adjoint"; forward mode): the
/// exact directional derivative of `J(θ) = Σ_j ⟨g_j, f_j(θ)⟩` along a material direction `δ`, from
/// the field and constitution at `θ + δ` and `θ − δ`. Every operand the word reads is at most
/// quadratic in the constitution's factors (`W_s = −f fᵀ`, `A_ρ = u vᵀ − v uᵀ`, `C = c cᵀ`, `K = b bᵀ`,
/// `D = F Fᵀ`) and linear in `W_c`, `R`, `E`, the pair port and `Y_a`, so each operand's tangent is
/// the exact central difference of the two operand sets. The tangent change then runs beside the
/// primal change through the word's local laws, each differentiated by hand and independent of the
/// reverse sweep:
///
/// ```text
/// junction  δv = (Y δs + Σ_a G δa + Σ_a δG (a − v)) / (Y + Σ_a G),  δb = 2δv − δs,  δc = δv − δs,  δo = 2δv − δa
/// element   (I − ½K) δs′ = (I + ½K) δb + W_c δc + δK x̄ + δW_c c
/// transit   M δω = h(δα_g − δα_h) + 2C δw − hK δu + 2δC w − hδK u − δM ω,
///           δM = 2δC + hδD + (h²/2)δK − (2h/G²)δG I,  δw′ = 2δω − δw,  δu′ = δu + hδω,
///           δout = δα ∓ ((2/G)δω − (2δG/G²)ω)
/// read      δf_j = δR P^τ v(e_j) + R P^τ δv(e_j)
/// ```
///
/// The primal it carries is checked against the word's own logits, so the two implementations run
/// the same ticks.
fn tangent(cut: &Cut, plus: (&Field, &Constitution), minus: (&Field, &Constitution)) -> Rat {
    let (field, theta) = (&cut.field, &cut.theta);
    let current = cut.pending.current(field).unwrap();
    let phases = cut.pending.phases();
    let receiving = phases.ring();
    let (half, two) = (rat(1, 2), integer(2));
    let at =
        |field: &Field, theta: &Constitution| Operands::at_cut(field, theta, &current).unwrap();
    let (ops, up, down) = (
        cut.operands.clone(),
        at(plus.0, plus.1),
        at(minus.0, minus.1),
    );
    let h = ops.step().clone();
    let moment = cut.pending.moment();
    let open =
        |field: &Field, theta: &Constitution| moment.open_storage(field, theta, &current).unwrap();
    let mut storage = open(field, theta);
    let (opened_up, opened_down) = (open(plus.0, plus.1), open(minus.0, minus.1));
    let mut d_storage: Vec<Vec<Rat>> = opened_up
        .iter()
        .zip(&opened_down)
        .map(|(p, m)| scale(&half, &sub(p, m)))
        .collect();
    let rings = ops.rings();
    let contacts = ops.contacts();
    let zeros = |n: usize| vec![Rat::zero(); n];
    let mut arrivals: Vec<[Vec<Rat>; 2]> = contacts
        .iter()
        .map(|contact| {
            let (from, to) = contact.ends();
            [zeros(rings[from].width()), zeros(rings[to].width())]
        })
        .collect();
    let mut d_arrivals = arrivals.clone();
    let mut states: Vec<[Vec<Rat>; 2]> = contacts
        .iter()
        .map(|contact| [zeros(contact.width()), zeros(contact.width())])
        .collect();
    let mut d_states = states.clone();
    let d_element: Vec<ExactRatMatrix> = (0..rings.len())
        .map(|r| central(up.rings()[r].element(), down.rings()[r].element()))
        .collect();
    let d_contrast: Vec<ExactRatMatrix> = (0..rings.len())
        .map(|r| central(up.rings()[r].contrast(), down.rings()[r].contrast()))
        .collect();
    let d_forms: Vec<[ExactRatMatrix; 3]> = (0..contacts.len())
        .map(|a| {
            let ((cp, kp, dp), (cm, km, dm)) =
                (up.contacts()[a].forms(), down.contacts()[a].forms());
            [central(cp, cm), central(kp, km), central(dp, dm)]
        })
        .collect();
    let d_conductance: Vec<Rat> = (0..contacts.len())
        .map(|a| (up.contacts()[a].conductance() - down.contacts()[a].conductance()) * &half)
        .collect();
    let identity = |n: usize| ExactRatMatrix::identity(n).unwrap();
    let (left, right): (Vec<ExactRatMatrix>, Vec<ExactRatMatrix>) = rings
        .iter()
        .map(|ring| {
            let n = ring.width();
            let half_k = ring.element().scaled(&half);
            (
                identity(n).subtract(&half_k).unwrap().inverse().unwrap(),
                identity(n).add(&half_k).unwrap(),
            )
        })
        .unzip();
    let solves: Vec<ExactRatMatrix> = contacts
        .iter()
        .map(|contact| {
            let (c, k, d) = contact.forms();
            c.scaled(&two)
                .add(&identity(contact.width()).scaled(&(&two * &h / contact.conductance())))
                .unwrap()
                .add(&d.scaled(&h))
                .unwrap()
                .add(&k.scaled(&(&h * &h / &two)))
                .unwrap()
                .inverse()
                .unwrap()
        })
        .collect();
    let apply = |m: &ExactRatMatrix, v: &[Rat]| m.apply(v).unwrap();
    let steps = phases.junction_steps();
    let (mut anchors, mut d_anchors) = (Vec::new(), Vec::new());
    for t in 0..steps {
        let mut junctions = Vec::with_capacity(rings.len());
        let mut d_junctions = Vec::with_capacity(rings.len());
        for (r, ring) in rings.iter().enumerate() {
            let incident = ops.incident(r);
            let incoming: Vec<(&Rat, &[Rat])> = incident
                .iter()
                .map(|&a| {
                    let slot = ops.end_slot(a, r);
                    (contacts[a].conductance(), arrivals[a][slot].as_slice())
                })
                .collect();
            let junction = junction_swing(ring.admittance(), &storage[r], &incoming).unwrap();
            let mut total = ring.admittance().clone();
            let mut weighted = scale(ring.admittance(), &d_storage[r]);
            for &a in incident {
                let slot = ops.end_slot(a, r);
                let g = contacts[a].conductance();
                total += g;
                weighted = add(&weighted, &scale(g, &d_arrivals[a][slot]));
                weighted = add(
                    &weighted,
                    &scale(
                        &d_conductance[a],
                        &sub(&arrivals[a][slot], &junction.anchor),
                    ),
                );
            }
            let d_anchor = scale(&total.recip(), &weighted);
            let d_wave = sub(&scale(&two, &d_anchor), &d_storage[r]);
            let d_drive = sub(&d_anchor, &d_storage[r]);
            let d_outgoing: Vec<Vec<Rat>> = incident
                .iter()
                .map(|&a| sub(&scale(&two, &d_anchor), &d_arrivals[a][ops.end_slot(a, r)]))
                .collect();
            junctions.push(junction);
            d_junctions.push((d_anchor, d_wave, d_drive, d_outgoing));
        }
        anchors.push(junctions[receiving].anchor.clone());
        d_anchors.push(d_junctions[receiving].0.clone());
        if t + 1 == steps {
            break;
        }
        for (r, ring) in rings.iter().enumerate() {
            let (junction, (_, d_wave, d_drive, _)) = (&junctions[r], &d_junctions[r]);
            let step = element_step(ring, &junction.storage_wave, &junction.contrast).unwrap();
            let rhs = add(
                &add(&apply(&right[r], d_wave), &apply(ring.contrast(), d_drive)),
                &add(
                    &apply(&d_element[r], &step.midpoint),
                    &apply(&d_contrast[r], &junction.contrast),
                ),
            );
            d_storage[r] = apply(&left[r], &rhs);
            storage[r] = step.next;
        }
        for (a, contact) in contacts.iter().enumerate() {
            let (from, to) = contact.ends();
            let position = |ring: usize| ops.incident(ring).iter().position(|&b| b == a).unwrap();
            let (at_from, at_to) = (position(from), position(to));
            let passed = transit(
                contact,
                &h,
                &junctions[from].outgoing[at_from],
                &junctions[to].outgoing[at_to],
                &states[a][0],
                &states[a][1],
            )
            .unwrap();
            let declared = field.contact(a);
            let (select_from, select_to) =
                (declared.selection(End::From), declared.selection(End::To));
            let (d_out_from, d_out_to) = (&d_junctions[from].3[at_from], &d_junctions[to].3[at_to]);
            let pick = |wave: &[Rat], selection: &[usize]| -> Vec<Rat> {
                selection.iter().map(|i| wave[*i].clone()).collect()
            };
            let (d_alpha_from, d_alpha_to) =
                (pick(d_out_from, &select_from), pick(d_out_to, &select_to));
            let (c, k, _) = contact.forms();
            let [dc, dk, dd] = &d_forms[a];
            let (g, dg) = (contact.conductance(), &d_conductance[a]);
            let ((u, w), (du, dw)) = (
                (&states[a][0], &states[a][1]),
                (&d_states[a][0], &d_states[a][1]),
            );
            let omega = &passed.midpoint;
            let d_m = dc
                .scaled(&two)
                .add(&dd.scaled(&h))
                .unwrap()
                .add(&dk.scaled(&(&h * &h / &two)))
                .unwrap()
                .add(&identity(contact.width()).scaled(&(-(&two * &h * dg) / (g * g))))
                .unwrap();
            let mut rhs = scale(&h, &sub(&d_alpha_from, &d_alpha_to));
            rhs = add(&rhs, &scale(&two, &apply(c, dw)));
            rhs = sub(&rhs, &scale(&h, &apply(k, du)));
            rhs = add(&rhs, &scale(&two, &apply(dc, w)));
            rhs = sub(&rhs, &scale(&h, &apply(dk, u)));
            rhs = sub(&rhs, &apply(&d_m, omega));
            let d_omega = apply(&solves[a], &rhs);
            let exchange = sub(
                &scale(&(&two / g), &d_omega),
                &scale(&(&two * dg / (g * g)), omega),
            );
            let mut arrive_from = d_out_from.clone();
            for (index, coordinate) in select_from.iter().enumerate() {
                arrive_from[*coordinate] = &d_alpha_from[index] - &exchange[index];
            }
            let mut arrive_to = d_out_to.clone();
            for (index, coordinate) in select_to.iter().enumerate() {
                arrive_to[*coordinate] = &d_alpha_to[index] + &exchange[index];
            }
            d_states[a] = [
                add(du, &scale(&h, &d_omega)),
                sub(&scale(&two, &d_omega), dw),
            ];
            d_arrivals[a] = [arrive_from, arrive_to];
            arrivals[a] = [passed.arrive_from, passed.arrive_to];
            states[a] = [passed.displacement, passed.rate];
        }
    }
    let map = theta.receiving_map(receiving).unwrap();
    let d_map = central(
        plus.1.receiving_map(receiving).unwrap(),
        minus.1.receiving_map(receiving).unwrap(),
    );
    let (ring, lift) = (field.ring(receiving), &current.lift()[receiving]);
    // The pending read is the wave's (the tree part is a stored face, added at compare).
    let (_, faces) = cut.pending.read(field, theta).unwrap();
    let waves = faces.logits;
    let mut derivative = Rat::zero();
    for (j, epoch) in phases.epochs().enumerate() {
        let (v, dv) = (
            ring.rotate(&anchors[epoch], lift),
            ring.rotate(&d_anchors[epoch], lift),
        );
        assert_eq!(
            apply(map, &v),
            waves[j],
            "the primal is the word's own read"
        );
        let d_logits = add(&apply(&d_map, &v), &apply(map, &dv));
        derivative += dot(&cut.covector.logits()[j], &d_logits);
    }
    derivative
}

/// Design (c), `compare`'s complete pullback, on the loci in which `J(θ) = Σ_j ⟨g_j, f_j(θ)⟩` is
/// linear (`R`, `E`, the pair port's outputs and both its reads): each material gradient is the
/// difference quotient, exactly.
#[test]
fn every_linear_locus_gradient_is_the_exact_difference_quotient() {
    let cut = cut();
    let theta = &cut.theta;
    let mut draw = Draw::new(67);
    let unit = integer(1);
    let (ring_r, map_gradient) = &cut.pullback.receiving;
    let direction = draw.matrix(8, 4);
    let moved = theta
        .clone()
        .with_ports(
            *ring_r,
            None,
            None,
            Some(theta.receiving_map(2).unwrap().add(&direction).unwrap()),
        )
        .unwrap();
    assert_eq!(
        cut.quotient(&moved, &unit),
        frobenius(map_gradient, &direction)
    );
    let direction = draw.matrix(4, 4);
    let moved = theta
        .clone()
        .with_ports(
            0,
            None,
            Some(theta.source_port(0).unwrap().add(&direction).unwrap()),
            None,
        )
        .unwrap();
    let source_gradient = cut.pullback.rings[0].source.as_ref().unwrap();
    assert_eq!(
        cut.quotient(&moved, &unit),
        frobenius(source_gradient, &direction)
    );
    let pair = theta.pair_port(0, 1).unwrap();
    let shift = |base: &[Vec<Rat>], by: &[Vec<Rat>]| -> Vec<Vec<Rat>> {
        base.iter()
            .zip(by)
            .map(|(x, d)| x.iter().zip(d).map(|(x, d)| x + d).collect())
            .collect()
    };
    let [output_gradient, current_gradient, earlier_gradient] = &cut.pullback.rings[0].pair[0].1;
    for (family, gradient) in [output_gradient, current_gradient, earlier_gradient]
        .into_iter()
        .enumerate()
    {
        // The outputs live on ring 0's width and the reads on the exterior chart: four each.
        let by: Vec<Vec<Rat>> = (0..pair.rank()).map(|_| draw.vector(4)).collect();
        let mut parts = [
            pair.outputs().to_vec(),
            pair.current_reads().to_vec(),
            pair.earlier_reads().to_vec(),
        ];
        parts[family] = shift(&parts[family], &by);
        let [outputs, current, earlier] = parts;
        let moved = theta
            .clone()
            .with_pair(0, 1, PairPort::new(outputs, current, earlier).unwrap())
            .unwrap();
        assert_eq!(
            cut.quotient(&moved, &unit),
            nested(gradient, &by),
            "pair part {family}"
        );
    }
}

/// Design (c), `compare`'s complete pullback, on the element's loci, in which `J` is not linear
/// (the contrast port, the passive factor, the slices' `u` and `v`): moving all four at once along
/// drawn directions, the separately implemented tangent word's directional derivative ([`tangent`])
/// is exactly the sum of the four gradients' pairings with them (every operand is at most quadratic
/// in these factors, so the central difference is exact); and the class covector is the slices'
/// own derivative, `⟨∂ℓ/∂u_ρ, u_ρ⟩ = σ_ρ g_σρ`.
#[test]
fn every_element_gradient_is_the_tangent_words_derivative() {
    let cut = cut();
    let (field, theta) = (&cut.field, &cut.theta);
    let mut draw = Draw::new(68);
    let ring = 1;
    let n = field.ring(ring).width();
    let (passive, contrast, slices) = (
        theta.passive_factor(ring).clone(),
        theta.contrast_port(ring).clone(),
        theta.slices(ring).to_vec(),
    );
    let (to_contrast, to_passive) = (draw.matrix(n, n), draw.matrix(n, n));
    let bends: [Vec<Vec<Rat>>; 2] = [
        (0..n).map(|_| draw.vector(n)).collect(),
        (0..n).map(|_| draw.vector(n)).collect(),
    ];
    let moved = |sign: &Rat| {
        let shift = |x: &[Rat], d: &[Rat]| x.iter().zip(d).map(|(x, d)| x + sign * d).collect();
        let bent: Vec<(Vec<Rat>, Vec<Rat>)> = slices
            .iter()
            .enumerate()
            .map(|(rho, (u, v))| (shift(u, &bends[0][rho]), shift(v, &bends[1][rho])))
            .collect();
        theta
            .clone()
            .with_element(
                ring,
                passive.add(&to_passive.scaled(sign)).unwrap(),
                contrast.add(&to_contrast.scaled(sign)).unwrap(),
                bent,
            )
            .unwrap()
    };
    let pulled = &cut.pullback.rings[ring];
    let (du, dv): (Vec<Vec<Rat>>, Vec<Vec<Rat>>) = pulled.slices.iter().cloned().unzip();
    assert_eq!(
        tangent(
            cut,
            (field, &moved(&integer(1))),
            (field, &moved(&integer(-1)))
        ),
        frobenius(&pulled.contrast, &to_contrast)
            + frobenius(&pulled.passive, &to_passive)
            + nested(&du, &bends[0])
            + nested(&dv, &bends[1]),
        "the contrast port, the passive factor and the slices"
    );
    let current = cut.pending.current(field).unwrap();
    let sheets = Operands::at_cut(field, theta, &current).unwrap().rings()[ring]
        .sheets()
        .to_vec();
    for (rho, ((du, _), (u, _))) in cut.pullback.rings[ring]
        .slices
        .iter()
        .zip(theta.slices(ring))
        .enumerate()
    {
        let along: Rat = du.iter().zip(u).map(|(a, b)| a * b).sum();
        let class = &cut.pullback.rings[ring].classes[rho];
        assert_eq!(along, if sheets[rho] { class.clone() } else { -class });
    }
}

/// Design (c), `compare`'s complete pullback, on the channel's loci (the storage, stiffness and
/// dissipation factors): moving every channel factor of every contact at once along drawn
/// directions, the tangent word's directional derivative ([`tangent`]) is exactly the sum of the
/// gradients' pairings with them (each form is a square of its factor, so the central difference is
/// exact).
#[test]
fn every_channel_gradient_is_the_tangent_words_derivative() {
    let cut = cut();
    let (field, theta) = (&cut.field, &cut.theta);
    let mut draw = Draw::new(69);
    let directions: Vec<[ExactRatMatrix; 3]> = (0..field.contacts().len())
        .map(|a| {
            let k = field.contact(a).width();
            [draw.matrix(k, k), draw.matrix(k, k), draw.matrix(k, k)]
        })
        .collect();
    let moved = |sign: &Rat| {
        directions
            .iter()
            .enumerate()
            .fold(theta.clone(), |moved, (a, [c, b, f])| {
                let step = |factor: &ExactRatMatrix, d: &ExactRatMatrix| {
                    factor.add(&d.scaled(sign)).unwrap()
                };
                moved
                    .with_channel(
                        a,
                        step(theta.contact_storage(a), c),
                        step(theta.contact_stiffness(a), b),
                        step(theta.contact_dissipation(a), f),
                    )
                    .unwrap()
            })
    };
    let paired: Rat = directions
        .iter()
        .zip(&cut.pullback.contacts)
        .map(|([c, b, f], pulled)| {
            frobenius(&pulled.storage, c)
                + frobenius(&pulled.stiffness, b)
                + frobenius(&pulled.dissipation, f)
        })
        .sum();
    assert_eq!(
        tangent(
            cut,
            (field, &moved(&integer(1))),
            (field, &moved(&integer(-1)))
        ),
        paired,
        "the channel factors"
    );
}

/// Design (c), `compare`'s complete pullback, on the contact's conductance `G_a = 2^(n_a) Y_a`:
/// moving `Y_0` by one moves `G_0` by `2^(n_0)`, so the tangent word's derivative in `Y_0` is the
/// conductance covector times `2^(n_0)`, exactly.
#[test]
fn the_conductance_gradient_is_the_derivative_in_the_admittance() {
    let cut = cut();
    let (field, theta) = (&cut.field, &cut.theta);
    // The conductance: G_0 = 2^(n_0) Y_0, so moving Y_0 by one moves G_0 by 2^(n_0).
    let exponent = contact_exponent(field, 0, cut.pending.anchor()).unwrap();
    assert_eq!(
        tangent(
            cut,
            (&chain_with(integer(3)).with_exact_word(), theta),
            (&chain_with(integer(1)).with_exact_word(), theta)
        ),
        &cut.back.conductance[0] * power_of_two(&exponent.carry).unwrap(),
        "the conductance"
    );
}

/// Design (c), `compare`'s complete pullback: the moment covector is the derivative in the moment's
/// phase counts. `J` is linear in the counts, so moving the counts moves `J` by exactly their
/// pairing with it.
#[test]
fn the_moment_covector_is_the_derivative_in_the_phase_counts() {
    let cut = cut();
    let (field, theta) = (&cut.field, &cut.theta);
    let pair = theta.pair_port(0, 1).unwrap();
    let current = cut.pending.current(field).unwrap();
    // The moment covector, at a constitution whose pair port emits nothing (so the offset counts
    // do not enter `J`): moving the counts from one stream's to another's at the same anchor moves
    // `J` by their pairing with it.
    let silent = PairPort::new(
        vec![vec![Rat::zero(); 4]; pair.rank()],
        pair.current_reads().to_vec(),
        pair.earlier_reads().to_vec(),
    )
    .unwrap();
    let quiet = cut_at(
        chain().with_exact_word(),
        theta.clone().with_pair(0, 1, silent).unwrap(),
    );
    let covector = quiet.pullback.rings[0].moment.as_ref().unwrap();
    let (_, other) = moment(&quiet.field, 68, 21);
    let moved = PendingRatio::produce(
        &current,
        &other,
        quiet.pending.address(),
        quiet.pending.phases(),
        0,
    )
    .unwrap();
    let first = quiet.pending.moment();
    let mut predicted = Rat::zero();
    for (phase, row) in covector.iter().enumerate() {
        let (after, before) = (
            other.phase_counts(0, phase).unwrap(),
            first.phase_counts(0, phase).unwrap(),
        );
        for ((value, a), b) in row.iter().zip(after).zip(before) {
            predicted += value * Rat::from_integer(BigInt::from(*a) - BigInt::from(*b));
        }
    }
    assert_ne!(predicted, Rat::zero());
    assert_eq!(
        quiet.functional_of(&moved, &quiet.theta) - &quiet.base,
        predicted
    );
}

/// The declared rule that releases at the grain, holding beyond it.
fn releasing() -> DecisionRule {
    DecisionRule::new(
        "release at the grain",
        WithinTolerance::Release,
        BeyondTolerance::Hold,
    )
}

/// The declared rule that holds at every width.
fn holding() -> DecisionRule {
    DecisionRule::new("hold", WithinTolerance::Hold, BeyondTolerance::Hold)
}

fn shape<F, P, D, H, R>(returned: &InteractionReturn<F, P, D, H, R>) -> [bool; 5] {
    [
        returned.forward.is_present(),
        returned.pullback.is_present(),
        returned.deposit.is_present(),
        returned.order.is_present(),
        returned.phases.is_present(),
    ]
}

/// Design (c), the port table: each method returns the owner's `InteractionReturn` with the six
/// components of #73, a component it does not produce being a declared absence; each receipt has
/// one region per ring. The keys are located at the first boundary, from the crib that closed the
/// aeon, and return the published ring clocks as their material; `close_aeon` returns the transpose
/// of `V` per pending ratio as its pullback.
#[test]
fn every_port_method_returns_its_six_components() {
    let field = chain();
    let reference = Reference::campaign_one();
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let rings = field.rings().len();
    let stream = [0, 1, 2, 3, 0, 2, 1, 3].repeat(8);
    let (moment, ingested) = reference
        .ingest(&mut resident, None, &one_hot(&stream))
        .unwrap();
    assert_eq!(shape(&ingested), [true, false, false, true, false]);
    let ingested = ingested.forward.into_present().unwrap();
    assert!(ingested.carry_out);
    let admitted = resident.admitted().to_vec();
    let closed = reference.close_aeon(&mut resident, &admitted).unwrap();
    assert_eq!(shape(&closed), [true, true, false, true, true]);
    let crib = &stream[ingested.cells.saturating_sub(8)..ingested.cells];
    let keys = reference
        .locate_keys(&mut resident, &one_hot(crib), 1)
        .unwrap();
    assert_eq!(shape(&keys), [true, false, true, true, false]);
    let location = keys.forward.present().unwrap();
    let clocks = keys.deposit.present().unwrap();
    assert_eq!(clocks.len(), rings);
    for (ring, clock) in location.rings.iter().zip(clocks) {
        // A published ring's clock reads the lift point at the boundary; a fallen-back ring has none.
        assert_eq!(clock.is_some(), ring.carried.is_some());
        if let Some(clock) = clock {
            assert_eq!(
                BigInt::from(clock.ticks()),
                resident.current().lift()[ring.ring]
            );
        }
    }
    let (_, ingested) = reference
        .ingest(&mut resident, Some(&moment), &one_hot(&[1, 3, 2]))
        .unwrap();
    assert_eq!(shape(&ingested), [true, false, false, true, false]);
    let phases = resident.admitted()[0].clone();
    let (pending, refined) = reference.refine(&mut resident, &moment, &phases).unwrap();
    assert_eq!(shape(&refined), [true, false, false, true, true]);
    let released = reference
        .release(&mut resident, &pending, &releasing())
        .unwrap();
    assert_eq!(shape(&released), [true, false, false, true, true]);
    let held = reference
        .release(&mut resident, &pending, &holding())
        .unwrap();
    assert_eq!(shape(&held), [false, false, false, true, true]);
    let (staged, compared) = reference
        .compare(&mut resident, pending, &one_hot(&[0, 3]))
        .unwrap();
    assert_eq!(shape(&compared), [true, true, true, true, true]);
    let deposited = reference.deposit(&mut resident, staged).unwrap();
    assert_eq!(shape(&deposited), [true, false, true, false, false]);
    let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let discarded = reference
        .discard(&mut resident, Handle::Pending(pending))
        .unwrap();
    assert_eq!(shape(&discarded), [true, false, false, false, false]);
    for receipt in [
        &closed.receipt,
        &keys.receipt,
        &ingested.receipt,
        &refined.receipt,
        &compared.receipt,
        &deposited.receipt,
        &discarded.receipt,
    ] {
        assert_eq!(receipt.rings.regions(), rings);
    }
    let census = reference.census();
    assert_eq!(census.pending_capacity, 64);
}

/// Design (c), `release` and `close_aeon` (review §4): the release reads its width from its
/// receiving phases (the largest fibre of the window's faces, a certified bound on the code
/// lengths' movement over the receiver's fibre, below the grain), returns the RIDE/FOUND split as a
/// reading (declared absent on campaign 1's unit-weight rings, whose capacity is singular), and
/// takes the decision as data; `close_aeon` returns, per carried pending ratio, the transpose of
/// `V`: the retained loci its diamond reads.
#[test]
fn the_release_reads_its_width_and_the_boundary_returns_the_transpose() {
    let field = chain();
    let reference = Reference::campaign_one();
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let stream = [0, 1, 2, 3, 0, 2, 1, 3].repeat(8);
    let (moment, _) = reference
        .ingest(&mut resident, None, &one_hot(&stream[..4]))
        .unwrap();
    let phases = resident.admitted()[0].clone();
    let (pending, refined) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let largest = refined
        .forward
        .present()
        .unwrap()
        .faces
        .iter()
        .flat_map(|face| face.fibres())
        .max()
        .unwrap();
    let released = reference
        .release(&mut resident, &pending, &releasing())
        .unwrap();
    let ReceiptDetail::Release {
        width,
        tolerance,
        split,
        ..
    } = &released.receipt.detail
    else {
        panic!("a release receipt");
    };
    assert_eq!(width.diameter(), &largest);
    assert_eq!(
        tolerance,
        &Rat::new(BigInt::from(1), BigInt::from(phases.grain()))
    );
    assert!(width.diameter() < tolerance);
    assert!(released.forward.is_present());
    assert!(
        split
            .iter()
            .all(|part| matches!(part, Component::Absent(reason) if reason.contains("singular")))
    );
    let (_, ingested) = reference
        .ingest(&mut resident, Some(&moment), &one_hot(&stream[4..]))
        .unwrap();
    assert!(ingested.forward.present().unwrap().carry_out);
    let admitted = resident.admitted().to_vec();
    let closed = reference.close_aeon(&mut resident, &admitted).unwrap();
    let transposes = closed.pullback.present().unwrap();
    let reads: Vec<_> = crate::hnn::retention::Diamond::of(&field, &phases)
        .retained(&field)
        .into_iter()
        .collect();
    assert_eq!(transposes, &vec![(pending, Transpose::Retained(reads))]);
}

/// Design (c), R2 M12, review D1: ingest stops at the joint clock's carry-out and the resident
/// refuses cells until `close_aeon`; keys are located only between `close_aeon` and the next ingest,
/// from a crib no longer than the closed aeon (the cells it read), and at no other time.
#[test]
fn the_clock_law_of_ingest_and_keys() {
    let field = chain();
    let reference = Reference::campaign_one();
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    assert_eq!(
        reference
            .locate_keys(&mut resident, &one_hot(&[0; 4]), 1)
            .unwrap_err(),
        HnnError::KeysNotAdmitted
    );
    let zeros = one_hot(&vec![0; 64]);
    let (moment, ingested) = reference.ingest(&mut resident, None, &zeros).unwrap();
    let ingested = ingested.forward.into_present().unwrap();
    assert!(ingested.carry_out && ingested.cells < zeros.len());
    let crib = one_hot(&vec![0; ingested.cells]);
    assert_eq!(
        reference.locate_keys(&mut resident, &crib, 1).unwrap_err(),
        HnnError::KeysNotAdmitted
    );
    assert_eq!(
        reference
            .ingest(&mut resident, Some(&moment), &one_hot(&[1]))
            .unwrap_err(),
        HnnError::AeonAwaitingClose
    );
    let admitted = resident.admitted().to_vec();
    reference.close_aeon(&mut resident, &admitted).unwrap();
    assert!(matches!(
        reference.locate_keys(&mut resident, &one_hot(&vec![0; ingested.cells + 1]), 1),
        Err(HnnError::Shape { .. })
    ));
    reference.locate_keys(&mut resident, &crib, 1).unwrap();
    reference
        .ingest(&mut resident, Some(&moment), &one_hot(&[1]))
        .unwrap();
    assert_eq!(
        reference.close_aeon(&mut resident, &admitted).unwrap_err(),
        HnnError::NotAtCarryOut
    );
    assert_eq!(
        reference
            .ingest(&mut resident, None, &[vec![(0, rat(1, 2))]])
            .unwrap_err(),
        HnnError::CellNotOneHot { position: 0 }
    );
}

/// Per-ring receipts in their own clocks: a word's receipt counts every ring's junction steps in
/// the hop clock `h`; an ingest's counts each ring's selective ticks.
#[test]
fn per_ring_receipts_are_read_in_their_own_clocks() {
    let field = chain();
    let reference = Reference::campaign_one();
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let before = resident.current().lift().to_vec();
    let (moment, ingested) = reference
        .ingest(&mut resident, None, &one_hot(&[0, 3, 0, 2, 0]))
        .unwrap();
    let ticks: Vec<Rat> = resident
        .current()
        .lift()
        .iter()
        .zip(&before)
        .map(|(a, b)| Rat::from_integer(a - b))
        .collect();
    assert_eq!(ingested.receipt.rings.readings(), ticks.as_slice());
    let phases = resident.admitted()[0].clone();
    let (_, refined) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let steps = Rat::from_integer(BigInt::from(phases.junction_steps()));
    assert!(refined.receipt.rings.readings().iter().all(|r| *r == steps));
    assert!(
        refined
            .receipt
            .rings
            .charts()
            .iter()
            .all(|chart| chart.clock() == field.step() && chart.clock_exponent() == 0)
    );
    assert_eq!(refined.receipt.balances.len(), phases.junction_steps() - 1);
    assert!(refined.receipt.balances.iter().all(|b| b.closes()));
}

/// Guard 3's capacity: `refine` refuses beyond the pending capacity; `discard` frees a handle, and
/// an unknown handle is refused.
#[test]
fn refine_refuses_beyond_the_pending_capacity() {
    let field = chain();
    let reference = Reference::new(2, Steps::campaign_one(), 1 << 40);
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let (moment, _) = reference
        .ingest(&mut resident, None, &one_hot(&[1, 2]))
        .unwrap();
    let phases = resident.admitted()[0].clone();
    let (first, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    reference.refine(&mut resident, &moment, &phases).unwrap();
    assert_eq!(
        reference
            .refine(&mut resident, &moment, &phases)
            .unwrap_err(),
        HnnError::PendingCapacity { capacity: 2 }
    );
    reference
        .discard(&mut resident, Handle::Pending(first))
        .unwrap();
    reference.refine(&mut resident, &moment, &phases).unwrap();
    assert!(matches!(
        reference.discard(&mut resident, Handle::Pending(first)),
        Err(HnnError::UnknownHandle { .. })
    ));
}

/// Design (c)'s handles under refusal (review S11, S12, S14): a compare refused for its target (the
/// wrong aperture, a cell that is not one-hot) leaves its pending ratio open, and a deposit refused
/// as stale leaves the published constitution, the first law's ledger and its staged deposit as
/// they were; a pending handle's bits count its ratio and the logits it emitted.
#[test]
fn a_refused_compare_or_deposit_leaves_its_handle_and_the_resident() {
    let field = chain();
    let reference = Reference::new(4, Steps::campaign_one(), 1 << 40);
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let (moment, _) = reference
        .ingest(&mut resident, None, &one_hot(&[1, 2]))
        .unwrap();
    let phases = resident.admitted()[0].clone();
    let (pending, refined) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let emitted: u64 = refined
        .forward
        .present()
        .unwrap()
        .logits
        .iter()
        .flatten()
        .map(|x| x.numer().bits() + x.denom().bits())
        .sum();
    let (_, _, handles) = reference.read(&resident).unwrap();
    let bits = handles
        .iter()
        .find(|(handle, _)| *handle == Handle::Pending(pending))
        .unwrap()
        .1;
    assert!(emitted > 0 && bits > emitted);
    assert!(matches!(
        reference.compare(&mut resident, pending, &one_hot(&[1])),
        Err(HnnError::Shape { .. })
    ));
    assert_eq!(
        reference
            .compare(
                &mut resident,
                pending,
                &[vec![(1, rat(1, 2))], vec![(0, Rat::one())]]
            )
            .unwrap_err(),
        HnnError::CellNotOneHot { position: 0 }
    );
    let (first, _) = reference
        .compare(&mut resident, pending, &one_hot(&[1, 0]))
        .unwrap();
    let (again, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let (second, _) = reference
        .compare(&mut resident, again, &one_hot(&[2, 3]))
        .unwrap();
    reference.deposit(&mut resident, first).unwrap();
    let (published, ledger) = (resident.constitution().clone(), resident.ledger().clone());
    assert_eq!(
        reference.deposit(&mut resident, second).unwrap_err(),
        HnnError::StaleDeposit {
            staged: 0,
            published: 1
        }
    );
    assert_eq!(resident.constitution(), &published);
    assert_eq!(resident.ledger(), &ledger);
    reference
        .discard(&mut resident, Handle::Staged(second))
        .unwrap();
}

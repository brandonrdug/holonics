//! Loop 1c's diagnostics (the
//! [pin](../../../../../research/records/2026-10-01_LOOP_1C_PERSISTENCE_REPRESENTATION_AND_REACH_PINNED_BEFORE_ITS_RUNS.md)):
//! the placement read over another span's mass (a landing's normalization and entry, apart), the
//! release under a declared order, and the representation search's readings (each decision term's
//! gradient at `E`, and the comparison re-read on frozen sites). Diagnostics, never laws: one test
//! per stated identity and per boundary case.

use num_traits::Zero;

use super::learning::{generic, moment};
use super::prediction::{executed_requests, joint, joint_bank};
use super::support::Draw;
use crate::hnn::executed::{
    Comparison, Context, Request, TermSite, compare, frozen_reread, proposal_returns,
    site_gradients,
};
use crate::hnn::field::ConstitutionRead;
use crate::hnn::prediction::{
    BankPlacement, LockOrder, Refinement, bank_release, bank_release_ordered,
};
use crate::hnn::ring::turn;
use crate::ratio::{Rat, rat};

/// `a · s` componentwise.
fn scaled(a: &[Rat], s: &Rat) -> Vec<Rat> {
    a.iter().map(|x| x * s).collect()
}

/// `a − b` componentwise.
fn minus(a: &[Rat], b: &[Rat]) -> Vec<Rat> {
    a.iter().zip(b).map(|(x, y)| x - y).collect()
}

/// **A landing splits into its normalization and its entry** (`BankPlacement::storage_over`; Lean
/// `HNN/IndexedOpen.transported_weight_insert`): read from station `j = 1` over the section `S`
/// (station 0 locked, `j`'s candidate placed), a later lock `k = 2` lands. At `ρ = 3/4` and at
/// `ρ = 1`:
/// - over its own span the read is the release's storage exactly (`mass = cells`);
/// - the normalization alone (`S`'s data over `S ∪ k`'s mass) and the entry alone (`S ∪ k`'s data
///   over `S`'s mass) differ from the native landing and from the decision's read by `k`'s image
///   at its two weights: `storage(S ∪ k) − storage_over(S, S ∪ k) = w₁ I_k` and
///   `storage_over(S ∪ k, S) − storage(S) = w₂ I_k`, with `w₁ = k`'s weight over `S ∪ k` and `w₂`
///   the weight over `S` of station 0, which lies at `k`'s distance from `j`: so
///   `w₂ (storage(S ∪ k) − storage_over(S, S ∪ k)) = w₁ (storage_over(S ∪ k, S) − storage(S))`
///   exactly on the chart;
/// - the mass reads only which stations are placed, never their classes;
/// - a landing moves the read (`k`'s image is not zero on this instance).
#[test]
fn a_landing_splits_into_its_normalization_and_its_entry() {
    let field = joint();
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    for (modulus, cells) in [(rat(3, 4), 2usize), (Rat::from_integer(1.into()), 8)] {
        let theta = generic(&field, 91).with_transport(0, modulus.clone()).unwrap();
        let (current, request) = moment(&field, 92, cells);
        let placement = BankPlacement::of(&field, &theta, &current, &request, &refinement).unwrap();
        let j = 1;
        for candidate in 0..3 {
            let section = [Some(2), Some(candidate), None, None];
            for later in 0..3 {
                let landed = [Some(2), Some(candidate), Some(later), None];
                assert_eq!(
                    placement.storage_over(j, &landed, &landed),
                    placement.storage(j, &landed)
                );
                let native = placement.storage(j, &landed);
                let decision = placement.storage(j, &section);
                let normalization = placement.storage_over(j, &section, &landed);
                let entry = placement.storage_over(j, &landed, &section);
                // The mass is class-blind.
                let other = [Some(2), Some(candidate), Some((later + 1) % 3), None];
                assert_eq!(placement.storage_over(j, &section, &other), normalization);
                let (_, over_landed) = placement.weights(j, &landed);
                let (_, over_section) = placement.weights(j, &section);
                let w1 = over_landed[2].clone().unwrap();
                let w2 = over_section[0].clone().unwrap();
                let entered_at_landing = minus(&native, &normalization);
                let entered_at_decision = minus(&entry, &decision);
                assert_eq!(scaled(&entered_at_landing, &w2), scaled(&entered_at_decision, &w1));
                assert!(entered_at_landing.iter().any(|x| !x.is_zero()), "k's image moves the read");
                if modulus < Rat::from_integer(1.into()) {
                    assert!(w1 < w2, "a later lock's mass lowers every weight below ρ = 1");
                }
            }
        }
    }
}

/// **The release under a declared order** (`prediction::bank_release_ordered`, a diagnostic):
/// [`LockOrder::Gap`] is the release's own iteration exactly; under [`LockOrder::Ascending`] and
/// [`LockOrder::Descending`] every refinement that locks locks exactly one station, the least (the
/// greatest) of its eligible stations, each lock's flip and lock certified on its reading, and the
/// release stops by the release's own rules (whole, plural or a refused certificate).
#[test]
fn the_release_under_a_declared_order_keeps_the_releases_rules() {
    let field = joint();
    let theta = generic(&field, 94);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let read = |amplitudes: &[crate::ratio::GaussianRat]| bank.read_turn(amplitudes, 12);
    let mut ordered_locks = 0usize;
    for seed in [95u64, 96, 97] {
        let (current, request) = moment(&field, seed, 8);
        let placement = BankPlacement::of(&field, &theta, &current, &request, &refinement).unwrap();
        let native = bank_release(&placement, &refinement, 3, &bank, 12, read, true).unwrap();
        let gap = bank_release_ordered(&placement, &refinement, 3, &bank, 12, read, true, LockOrder::Gap)
            .unwrap();
        assert_eq!(native.0, gap.0);
        assert_eq!(native.1.len(), gap.1.len());
        for order in [LockOrder::Ascending, LockOrder::Descending] {
            let (generation, refinements) =
                bank_release_ordered(&placement, &refinement, 3, &bank, 12, read, true, order).unwrap();
            for r in &refinements {
                let eligible: Vec<usize> = r.eligible.iter().map(|(s, _, _)| *s).collect();
                match eligible.iter().copied().reduce(|a, b| match order {
                    LockOrder::Ascending => a.min(b),
                    _ => a.max(b),
                }) {
                    Some(chosen) => {
                        if generation.uncertified.is_none() || !r.locked.is_empty() {
                            assert_eq!(r.locked, vec![chosen]);
                            ordered_locks += 1;
                        }
                    }
                    None => assert!(r.locked.is_empty()),
                }
            }
            for (_, _, growth, runner) in &generation.decisions {
                assert!(growth.exceeds(runner) && growth.is_locked());
            }
            let locked: usize = generation.locks.iter().map(Vec::len).sum();
            assert_eq!(generation.decisions.len(), locked);
            if generation.release.released() {
                assert_eq!(locked, 4);
                assert_eq!(generation.refinements, 4);
            } else {
                assert!(!generation.release.plural.is_empty());
            }
        }
    }
    assert!(ordered_locks > 0, "some declared order locked on this instance");
}

/// **Each decision term's gradient is its lock face's pullback to `E`** (`executed::site_gradients`):
/// one site a decision term, its `ℓ` the comparison's; for a drawn move `ΔE` at a fixed modulus, a
/// term's `⟨∂ℓ/∂E, ΔE⟩` is its contributions' `Σ c ⟨ĝ, δz⟩` exactly (the leading members' covectors
/// at their dyadic faces, the lock face's weights `θ − q` at the shares' faces, `δz` each
/// contribution's storage move read from its station), at `ρ = 1` and at `ρ = 3/4`.
#[test]
fn each_decision_terms_gradient_is_its_pullback_to_e() {
    let field = joint();
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let cases: [(u64, [usize; 4]); 2] = [(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2])];
    let mut read = 0usize;
    for (modulus, cells) in [(Rat::from_integer(1.into()), 8usize), (rat(3, 4), 2)] {
        let theta = generic(&field, 94).with_transport(0, modulus.clone()).unwrap();
        let requests: Vec<Request> = cases
            .iter()
            .map(|&(seed, targets)| {
                let (current, moment) = moment(&field, seed, cells);
                Request {
                    current,
                    moment,
                    targets: targets.to_vec(),
                    context: Context::Open,
                }
            })
            .collect();
        let (batch, gradients) =
            site_gradients(&field, &theta, &requests, &refinement, &bank, 12).unwrap();
        let terms: Vec<_> = batch.requests.iter().flat_map(|r| &r.terms).collect();
        assert_eq!(gradients.len(), terms.len());
        assert_eq!(gradients.len(), 8);
        for (g, t) in gradients.iter().zip(&terms) {
            assert_eq!(g.site, t.site);
            assert_eq!(g.lock, t.comparison.lock);
            assert_eq!(g.kind, t.kind);
        }
        let (_, contributions) = proposal_returns(
            &field,
            &theta,
            &requests,
            &refinement,
            &bank,
            12,
            Comparison::LOCK_DECISIONS,
        )
        .unwrap();
        let port = theta.source_port(0).unwrap().clone();
        let direction = Draw::new(98).matrix(port.rows(), port.columns());
        let moved = theta
            .clone()
            .with_ports(0, None, Some(port.add(&direction).unwrap()), None)
            .unwrap();
        // The lock face's proposal holds each term's resolved leading contributions, in order.
        let mut at = 0;
        for g in &gradients {
            let start = at;
            while at < contributions.len() && {
                let (request, station, cells, ..) = &contributions[at];
                (*request, *station) == (g.site.request, g.site.station)
                    && cells
                        .iter()
                        .zip(&g.site.cells)
                        .enumerate()
                        .all(|(s, (a, b))| s == *station || a == b)
            } {
                at += 1;
            }
            let own = &contributions[start..at];
            let Some((gradient, _)) = &g.gradient else { continue };
            assert_eq!(own.len(), 3);
            let mut expected = Rat::zero();
            for (request, station, cells, covector, weight) in own {
                assert_eq!((request, station), (&g.site.request, &g.site.station));
                let r = &requests[*request];
                let before = BankPlacement::of(&field, &theta, &r.current, &r.moment, &refinement)
                    .unwrap()
                    .storage(*station, cells);
                let after = BankPlacement::of(&field, &moved, &r.current, &r.moment, &refinement)
                    .unwrap()
                    .storage(*station, cells);
                expected += weight
                    * covector
                        .iter()
                        .zip(after.iter().zip(&before))
                        .map(|(c, (a, b))| c * (a - b))
                        .sum::<Rat>();
            }
            let paired: Rat = gradient
                .entries()
                .iter()
                .zip(direction.entries())
                .map(|(a, b)| a * b)
                .sum();
            assert_eq!(paired, expected, "at modulus {modulus}");
            read += 1;
        }
        assert_eq!(at, contributions.len());
    }
    assert!(read > 0, "some term's gradient was read");
}

/// **The frozen sites at their own constitution are its terms** (`executed::frozen_reread`): the
/// comparison's own decision sites re-read at the same constitution return the comparison and its
/// terms exactly, with nothing read afresh (every site's section was executed by the release).
#[test]
fn the_frozen_sites_at_their_own_constitution_are_its_terms() {
    let field = joint();
    let theta = generic(&field, 94);
    let refinement = Refinement::declare(&field, 0, 2, 1, 4, 2).unwrap();
    let bank = joint_bank();
    let requests =
        executed_requests(&field, &[(95, [0, 1, 2, 1]), (96, [1, 1, 0, 2])], Context::Open);
    let comparison = Comparison::LOCK_DECISIONS;
    let batch = compare(&field, &theta, &requests, &refinement, &bank, 12, comparison).unwrap();
    let sites: Vec<Vec<TermSite>> = batch
        .requests
        .iter()
        .map(|r| r.terms.iter().map(|t| t.site.clone()).collect())
        .collect();
    let (own, frozen, made) =
        frozen_reread(&field, &theta, &requests, &refinement, &bank, 12, comparison, &sites).unwrap();
    assert_eq!(own, batch);
    assert_eq!(made, 0);
    for (request, terms) in batch.requests.iter().zip(&frozen) {
        assert_eq!(&request.terms, terms);
    }
    // A storage read through `turn` is the bank's input form (the reading is a function of it).
    let r = &requests[0];
    let placement = BankPlacement::of(&field, &theta, &r.current, &r.moment, &refinement).unwrap();
    let cells = [Some(0), None, None, None];
    assert_eq!(
        bank.read_turn(&turn(&placement.storage(0, &cells)), 12).unwrap(),
        bank.read_turn(&turn(&placement.storage_over(0, &cells, &cells)), 12).unwrap()
    );
}

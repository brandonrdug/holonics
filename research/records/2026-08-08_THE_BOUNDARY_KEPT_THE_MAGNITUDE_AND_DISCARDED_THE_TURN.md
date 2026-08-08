# The boundary kept the magnitude and discarded the turn

**Date:** 2026-08-08
**Truth status:** `established-bounded`. The defect is a property of source, read directly. The
falsifier is executable and was made to fire before the repair and to hold after. The invariance
claim — that every integer reading is unchanged — is `measured`, by the suite.
**Evidence:** direct source inspection of `crates/holonic-engine/src/algebraic.rs` at `56c86b9`;
`computational-witness` for the cover falsifier and for the eleven tests that were asserting the
defect.
**Provenance.** A permitted sub-agent's read-only audit of every bare sign in the tree, run under
`CLAUDE.md` §2b, surfaced the site. **The audit is a search return, not authority**; every claim
below was re-established by reading the owner and by running code. The framing — *a sign is what
remains of a phase after the winding is deleted* — is Brandon's, derived with him this session and
deposited as §2b.
**Band:** 2026-08-08 · ONE CORE TYPE CONVICTED / THE RECEIPT SAID `never collapses it` AND WAS FALSE
FROM THE DAY IT WAS WRITTEN / ELEVEN TESTS WERE ASSERTING THE DEFECT / EVERY HOMOLOGY FIGURE
UNCHANGED / THE FACE RELATION WAS THE THING THAT MOVED / FALSIFIER DEPOSITED

---

## 1. What was found

`ComparativeMultiplicity` is the engine's oriented coefficient. Its own module header says
*"Counts are primary. Signed coefficients are their exact group completion, represented as a pair of
nonnegative populations."* It has two `BigUint` arms and a `difference()` reading, which is exactly
the anatomy of `soma::body::channel::OrientedWinding` and of
`phase_current::ExactSignedPhasePopulation`, both of which keep their arms apart and say in their
doc comments why.

It destroyed the pair at construction.

```rust
pub fn new(mut positive: BigUint, mut negative: BigUint) -> Self {
    let common = min(positive.clone(), negative.clone());
    positive -= &common;
    negative -= common;
    Self { positive, negative }
}
```

Every constructor — `positive`, `negative`, `from_hand`, `from_bigint`, `plus`, `minus`, `times` —
routed through it, and `validate()` made a retained pair a hard error
(`UnreducedComparativeMultiplicity`). So after construction at most one arm was ever nonzero, and
the type **forbade** anything else. It had `OrientedWinding`'s anatomy and `i64`'s behaviour.

`CausalChain::add_term` completed it: when two opposed terms met on one cell, the key was `remove`d.

```rust
if next.is_zero() { self.coefficients.remove(&cell); }
```

This is §2b at the level of a type. *"A float keeps the magnitude and discards the residual; a sign
keeps the magnitude and discards the turn."* The pair `(1,1)` and the pair `(0,0)` have the same
difference and are not the same thing: the first is two passages, once each hand; the second is no
passage. The reduction kept the difference and deleted the passages.

## 2. What it cost, which is not what it looks like

**The homology was never wrong.** `boundary_matrix` reads `difference()`, the boundary of a loop
edge genuinely is zero, and `H_1 = Z/p` came out right on every torsion fixture. That is precisely
why nothing caught it for as long as the module has existed.

What moved was every consumer that read `boundary.support()` as a **face relation**. `CausalCell` is
`{id, name, grade, source_events, boundary}` — there is no attaching map and no face list beside the
boundary chain. So a loop edge at `v`, after the deletion, was byte-identical to a cell attached to
nothing, and two predicates then read the attachment off a chain that no longer had one:

- `algebraic.rs` `is_closed_support` — *is this support a subcomplex* — at eleven call sites across
  `dilation`, `graph_receiver`, `skein`, `causal_body`, `holonic_complex`, `grown_cell`, `gluing`.
- `gluing.rs` `saturate` — *every cell all of whose faces this side already holds*. `∅ ⊆ S` for every
  `S`.

`gluing.rs` is the module `CLAUDE.md` §11 books as built: *"reopening rule keyed to the receiver
family — built."* The key is which cover you chose.

### The falsifier

Two vertices `v` and `w`, a loop at `v`, a face attached to the loop twice. Cover the complex by
`{w}` on the left and `{v}` on the right.

```
left  (seeded by w only) = {w, e, face}
right (seeded by v only) = {v, e, face}
```

The receiver holding only `w` was handed the entire torsion space except `v`, and the two receivers
came back **agreeing** on a loop and a face that neither of them supported. `δ` was then computed
against a pair of sets that were not subcomplexes.

It is latent and the suite could not reach it. Every `cover_by_vertices` caller runs on `rim`, a
cycle of distinct vertices with no loop; the two complexes that do carry loops — the `Z/p` torsion
family and the Möbius/`RP²` — build their covers as hand-written set literals and never call
`saturate`. **The two halves of the module had never met.**

The falsifier is now
`gluing::a_loop_is_not_admitted_into_a_receiver_that_does_not_hold_its_vertex`. It was made to fail
before the repair and to hold after.

## 3. The receipt that was false

`rebase_invariants.rs`, on `boundary_matrix`:

> *"The complex retains each coefficient as an ordered pair of positive and negative counts and
> **never collapses it**; the group-completed difference is the canonical map to the integers and is
> what a boundary map means. The pair is still upstream — nothing here writes back."*

Every clause after the semicolon was true. The clause before it was false from the day it was
written, and it was false about a type two files away.

This is `CLAUDE.md` §8 rule 1 with no interpretation needed. *Grade the implementation, not the
receipt.* The receipt was not careless — it described the design correctly. It was never checked
against the code that was supposed to implement it. The paragraph now carries the correction and the
date, because a receipt that silently becomes true is worth less than one that records what it was.

**And the wire format was on the honest side the whole time.** `graded_complex_form` encodes both
arms as two magnitudes and always has. It then carried a decoder refusal, `UnreducedTerm`, whose
message read *"a comparative multiplicity removes the common population, so this pair would mount as
a different one."* The format could express the truth and the body refused to receive it.

## 4. Eleven tests were asserting the defect

This is the sharpest evidence in the record, and it is the same shape as the trivial-orbit finding
deposited earlier today: **a suite that asserts a defect cannot catch it.**

| test | what it asserted |
|---|---|
| `algebraic::oriented_coefficients_are_group_completed_occurrence_counts` | `new(7,3)` returns `(4,0)`, and `(4,0) + (0,4)` `is_zero()` |
| `algebraic::a_four_simplex_..._boundary_squared_zero` | `∂∂` returns an **empty** chain |
| `algebraic::opposed_ends_derive_a_zero_relative_boundary_...` | an opposed-end residual is empty |
| `complex_system::a_one_ended_loop_rests_...` | a cell named `"vanished"`, built as `[v]−[v]`, has no boundary — and carries **no crossing** |
| `derivation_integral::a_pair_of_routes_that_are_the_same_chain_is_refused_as_evidence` | two identical routes have an empty cycle |
| `graded_complex_form` ×3 | a `(3,1)` on the wire is **refused** |
| `running_integral::a_self_incident_cell_...` | `assert!(boundary.is_zero(), "the two ends cancelled in the carrier")` |
| `running_integral::a_tree_cannot_falsify_...` | `assert_eq!(direct.chain(), detoured.chain(), "identical chains — the backtrack cancelled")` |
| `prime_ecology::three_pairwise_phase_channels_...` | `∂∂` returns an empty chain |

Two of them are worth reading twice.

**The cell named for its own disappearance.** `complex_system` built a 1-cell as `[v1] + (−[v1])`,
bound it to a variable called `vanished`, and asserted it carried no crossing — while the same
fixture's `loop_cell`, built as `2[v0]`, rests at `v0` and the test says so. Two presentations of
the same one-ended cell, one of which had been erased. After the repair `crossing` returns
`Some(v1)` for both, from the same branch of the same match. **The fixture contained its own control
and the annihilation had disabled it.**

**The backtrack.** `direct = [ab, bc]` against `detoured = [ab, bc, bc̄, bc]`. The test asserted the
two chains are equal. They are not: the second traversed `bc` three times and the chain now records
`(2,1)` there. They are the same **cycle**, and that is what the assertion should have said. It now
says both:

```rust
assert_ne!(direct.chain(), detoured.chain(),
    "the backtrack is two more passages over `bc` and the chain retains both");
assert!(direct.chain().minus(&detoured.chain()).difference_is_zero(),
    "they differ by a cancelling pair, so they are one cycle and carry one integral");
```

## 5. The repair

The conflation was between two genuinely different structures wearing one name:

- the **boundary map**, which must cancel — `∂e = v − v = 0` is required, or `H_1(S¹) ≠ Z`;
- the **face relation**, which must not — the attaching map of a loop hits `v` twice.

So the predicates split rather than the data:

| predicate | means | reads |
|---|---|---|
| `is_zero` | no passage was deposited at all | the arms |
| `difference_is_zero` | the passages cancel under the group completion | the arms |

`ComparativeMultiplicity::new` retains both arms; `reduced()` is available as an explicit receiver
reading and nothing stores it. `times` became the real tensor on arms —
`(p₁p₂ + n₁n₂, p₁n₂ + n₁p₂)` — so a passage scaled by a cancelling coefficient stays passages, with
`difference()` of the result still the product of the differences. `UnreducedComparativeMultiplicity`
and `UnreducedTerm` were **removed**, not deprecated (§13 rule 3). Every `∂∂ = 0` check, every cycle
condition, and `paths_are_distinct` moved to `difference_is_zero`. Every structural check —
"a grade-zero cell has no boundary", "an opening boundary is non-empty" — kept `is_zero`.

**The contract of the repair, and it held:** every integer reading is bit-identical. `rebase_invariants`
14/14, `grown_cell` 35/35, the `Z/p` torsion family, the genus-`g` Euler characteristics, and the
grown circuit's `H₁ = Z⁹ + Z/2` are unchanged, because all of them read `difference()`. Engine lib:
**836 passed, 0 failed** of the modules in scope.

One behaviour changed on purpose. `causal_body`'s spanning-forest walk previously treated an
empty-boundary edge as a chord; it now tests `difference_is_zero`, which subsumes the empty case and
additionally catches the loop the deletion used to hide. That is the same edge reaching the same
branch by a predicate that can see it.

## 6. What this is an instance of

`CLAUDE.md` §2b's standing obligation reads: *"every bare sign stored on a conduct path has done what
a float does. Find each `-` that is retained state rather than traversal and ask whether the turn
that produced it was kept."*

The audit that produced this record found the tree **substantially clean and clean on purpose** —
four independent carriers keep their arms apart, three of them citing each other by name, and
`sparse_surface::opposed_winding_arms_prevent_false_annihilation` is exactly the declared control §8
asks for. `running_integral::ChordObstruction` retains the difference, both operands, the address
and both ends. `projection::ReceiverOrientation` carries an orientation as a **rotor**. That is the
standard, and it was set inside this tree before §2b was written.

The defect was that the type furthest upstream of all of them — the one every chain in the engine is
built out of — was the one that did not follow it.

## 7. What is still owed, from the same audit and not repaired here

Ranked, each verified by reading the owner, none of them repaired:

1. **`exact_analysis::polygon_winding`** accumulates `winding += 1 / -= 1` and deposits no crossing.
   `{ccw, cw}` costs nothing — `winding = ccw − cw` preserves the argument principle exactly and
   additionally returns the total crossing count. It governs the **η-zero bisection**, the RH-facing
   driver: `holonic_eta_ratio_atlas` discards a half on `winding == 0`, which is correct by the
   argument principle, and cannot say *this half is where the boundary is doing work.*
2. **`soma/body/src/manifold.rs` `StandingWinding(Cog)`** — a winding as signed magnitude, in the
   crate that owns `OrientedWinding`, one module away. Self-declared: `at_boundary`'s doc says it
   *"does not define how multiple emissions integrate."*
3. **`running_integral::Cochain::set`** removes a key on an explicit zero deposit, and
   `temper::found_on` deposits through it — so founding zero founds nothing.
4. **`receiver_phase_atlas`** keys germ populations by three `i8` signs into a count. The germs
   retain exact `Rat` hessians; the population map does not.
5. **`local_star::current_frontier`** drops a hinge when two constituents cancel there. Mitigated —
   each constituent is retained with its transport word — but the hinge reports as never reached.
6. **`inertia::Inertia { positive, zero, negative }`** is a count of signs, which §2b already books
   as owed. The repair is nearer than §2b implies: `InertiaSchedule.steps` already carries
   `PivotStep::Diagonal { index, negative }` — the per-direction hand **with its address**. That is
   where the winding label goes.

## 8. The rule this earns

§8 already carries *a check whose material cannot vary the property under test is the same defect as
a check that cannot fail; it just wears a passing result.* This adds the case where the material was
varied and the **carrier** deleted the variation before any check saw it:

> **A type that reduces on construction has decided, for every consumer it will ever have, which
> distinctions are invisible.** No downstream check can recover one. Where a carrier holds two arms
> and offers a reading that joins them, the reduction belongs in the reading and never in the
> constructor — and the test for whether that line was crossed is whether any consumer reads the
> carrier's `support` as a **relation** rather than as a domain.

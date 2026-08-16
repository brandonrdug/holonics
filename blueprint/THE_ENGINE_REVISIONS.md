# The engine revisions — what the 2026-08-15 findings oblige

**Date:** 2026-08-15
**Status:** posed for ratification. Nothing here is scheduled until Brandon rules.
**Occasion:** Brandon — *"pose what the deposited findings mean in terms of engine revisions &
constructions for Eros."*

**Sources:** the six records of 2026-08-15, three Opus audits and one Sol (GPT-5.6, xhigh)
mathematics audit. **Every refutation below was verified against source or symbolically before it
was carried**, and the refuted claims are named so nothing builds on them.

---

## 0. The one statement, and it unifies the defects

Today's findings look like a scattered defect list. They are not. Every one of them is the same
defect in a different carrier:

> **The machine keeps dropping the half that came back.**
>
> - **the flywheel** is the previous meeting *returning* — never held, `held_live` 0 of 21,070
> - **the reflected amplitude** is the wave *returning* — the chain's transport was the scalar
>   transmission, which drops it and does not even compose
> - **the founding quantum** is the turn *returning* — mixed into one register with the circuit
>   crossing, so the ledger cannot separate two histories
> - **the deferred population** is the arrival *returning later* — retained since it was built and
>   read by nothing

**That is the spine's own central defect — the missing return edge — appearing four times in four
different carriers, at four grains.** It is not four repairs. It is one law applied four times:
*a carrier that discards what returns has quotiented without keeping its fiber, which this project
calls deletion rather than compression.*

**And the machine's own doctrine already names the fix in every case**: retain the fiber, exhibit
the remainder, never report a magnitude where a pair belongs.

---

## 1. THE GATE — one measurement, before any repair

**The return edge is not missing. It is unreachable by thirty lines.**

```text
   live_current.rs:3546-3590   the directed-contact loop   READS  enclosure(source_grain − 1)
   live_current.rs:3607-3637   the stance founder          WRITES e.stance / e.fly / e.fly_live
```

Both are in `enact_host_current`; the founder reaches `perceive_grain` through
`live_event_node_emitting`, and the PTX carries `perceive_grain`, `path_grain`, `thicken_branch`
and `enclosure_store`, so **it runs on the card too.** The contacts simply run first and can only
read a row a *previous* event left.

### THE GATE RAN, and it ruled out the repair it was declared to catch

```text
   grain1      8,938      source_grain == 1, so the contact reads depth 0
   deeper      1,348
   after_live      0      held_live TRUE at that depth AFTER the founder ran, same event
   after_dead 10,286      held_live FALSE
```

**8,938 of 10,286 events read depth 0 — exactly where the Cell-branch founder writes — and
`held_live` is still false after the founder ran.** So it is **not an ordering**, and reordering the
loop would have moved nothing while looking like a repair. The gate did the job it was declared for.

### One level down, and the founder is not the problem either

```text
   dark        0      no event is wholly dark — the founder ALWAYS runs
   f_cell  6,082      Cell branch
   f_cplx  4,204      Complex branch      6,082 + 4,204 = 10,286, every event
```

**And `sub_stance` is not a deadlock**, which an earlier reading suspected: `manifold.rs:5739-5742`
births it on the first non-pole arrival with no fold required.

**One instrument error, recorded because it is the session's own convicted shape.** A counter named
`folded` returned 0 and was nearly read as *the channel never folds*. It measured
`AtomEvent.fold.is_some()` — **a completed node handing up, not the channel fold**, which happens
separately and unconditionally at `manifold.rs:5736` when `deed_emanation` returns `Some`. A name
read as the thing it names, for the fourth time today. The channel is now measured directly, by
reading the frame either side of the founder in the same event.

### THE GATE IS ANSWERED — and it is the MATERIAL, not the wiring

The channel was measured directly, either side of the founder in the same event:

```text
   k_moved   1,348      the lineage channel DOES fold across the founder
   k_still   8,938
   deeper    1,348      source_grain > 1
   grain1    8,938      source_grain == 1
```

**The two pairs are equal, exactly.** `k_moved = deeper` and `k_still = grain1`, so

> **the channel folds precisely on the events whose `source_grain > 1`, and never on a grain-1
> event.** `1,348 : 8,938` reduced is **`674 : 4,469`**.

**So the engine is not miswired.** The founder always runs, `sub_stance` is not a deadlock, the
depths line up for the majority, and the fold works — **on the events that reach a sub-composition.**
What the ecology hands it is **8,938 of 10,286 shallow grain-1 events that never compose deeply
enough to fold at all**, and those are exactly the ones whose contacts read depth 0.

**That relocates the whole repair.** Revisions 0 and 1 assumed a wiring defect between two correct
halves. There is none. The question is now *why the ecology's events are overwhelmingly grain-1*,
which is a question about what the mouth admits and how a section is composed — not about ordering,
not about depth maps, and not about the fold.

**Three candidate repairs are therefore withdrawn before being built**: reordering the loop
(measured inert), remapping the depth (the depths agree where it matters), and wiring a deposit into
the directed path (the carrier refuses it for a reason, and the reason is upstream).

**Falsifier, unchanged and now better aimed:** `held_live` must leave zero **and** `found` must
leave zero. `B′` measured **2,233 windings** waiting in the material. A repair that raises the
grain-1 share without raising `found` has moved a count and not an edge.

---

## 2. THE LINK BECOMES TWO-COMPONENT — the largest revision, and it is forced by mathematics

**The scalar transport was wrong twice over.** It carried the amplitude transmission, which **does
not compose** —

```text
   τ_ij τ_jk − τ_ik = 2Y_i(Y_i−Y_j)(Y_j−Y_k) / [(Y_i+Y_j)(Y_j+Y_k)(Y_i+Y_k)]
```

zero only at `Y_i = Y_j` or `Y_j = Y_k` — and the repair to the admittance ratio, while correct for
composition, **is an exact coboundary `Y_i⁻¹Y_j`, so its holonomy is identically zero.** The plan's
claim that *holonomy begins at the third port* is **refuted**: no holonomy lives in the ratio at all.

**What composes and retains the return is a matrix.** Verified symbolically over `Rat`:

```text
   M(ρ) = ½ [ 1+ρ  1−ρ ]      M(ρ₁)·M(ρ₂) = M(ρ₁ρ₂)      τ = 1/M₁₁ ,  Γ = M₂₁/M₁₁
            [ 1−ρ  1+ρ ]
   J = diag(1,−1)             M(ρ)ᵀ J M(ρ) = ρ J
```

> **`Crossing` should carry `M`, and derive `τ` and `Γ` from it rather than storing either.** Then
> `Chain::compose` is matrix multiplication — exact, associative, and **carrying the reflected
> amplitude through the composition instead of beside it.**

**Four consequences, each of which the scalar could not express:**

1. **The chain gains a conserved form.** `Mᵀ g_{Y_i} M = g_{Y_j}` with `g_Y = Y·J` — an exact
   rational **isometry between admittance fibers**.

   > **AND IT DOES NOT CREATE HOLONOMY — this plan implied it might, and that is withdrawn.** The
   > family is **abelian**: `M(ρ₁)M(ρ₂) = M(ρ₁ρ₂)`, so a closed chain returns
   > `ρ = Y_source/Y_source = 1` and its holonomy is the identity **by construction** — a receipt
   > that could not have come out otherwise, which is the tautology rule.
   >
   > **Holonomy needs a link that does not commute with `M(ρ)`** — a propagation phase, which is not
   > expressible over `Rat`, or a lumped series/shunt element in the `(voltage, current)` chart.
   > **Neither exists in the tree.** So the matrix is the right carrier and it is *not* where
   > holonomy will come from, and a build that reported closure here would be reporting an identity.

   **A second honest bound**: at zero phase `M ↔ ρ` is a bijection and `det M = ζ` recovers the old
   carrier exactly, so the matrix carries **no more state** than the ratio did. The gain is that `Γ`
   becomes a **derived function of the composed transport**, where before there was no composite `Γ`
   at all.
2. **Rapidity adds.** Flux normalisation makes each link an honest `O(1,1)` boost of rapidity
   `−½ log ρ`, so the composed chain's total is a boost and the additive chart is the rapidity. *This
   is the genuine Lorentz structure* — on forward/returned amplitudes, **not** on the arrow's
   `(aim, cross)` pair, where `cross` is antisymmetric and `aim` symmetric and they provably cannot
   mix.
3. **`is_rebase()` stops lying — but the rule is subtler than this plan stated.** A chain that
   reflected currently returns `true` because `unconnected` records only what a caller passed to
   `reflect()`. **The correction: "a reflecting chain cannot compose to a pure rebase" is false.**
   `1 → 3 → 1` reflects at *both* links and composes to the identity, because with zero phase between
   two interfaces the returns cancel exactly — a zero-thickness layer is invisible. True of a
   monotone taper, false of an out-and-back. **The composite's own return decides**, not any link's.
4. **`service_rounds` becomes derived rather than declared.** `1/T = Σ_{n≥0} Γ^{2n}` is the
   multiple-reflection sum, and the matrix carries the reflections that sum is over.

**And two laws to wire that are absent from the tree:** `Γ_ik = (Γ_ij + Γ_jk)/(1 + Γ_ij Γ_jk)`, and
`τ_ik = τ_ij τ_jk / (1 + Γ_ij Γ_jk)` for a zero-phase intermediate — the denominator being exactly
what the scalar product omitted.

**Falsifier:** the matrix chain must reproduce every existing junction figure at a single link
(including the 576-pair host/device parity gate) **and** return a non-trivial reflected component on
a chain the scalar reported as a clean rebase.

---

## 3. THE LEDGER IS RETYPED, NOT REPAIRED

Sol exhibited an **exact collision**: `FoundThat(2+2i)` and `Ride(−2−i); Ride(−1)` return identical
`(D, B)` with different sweeps. `channel.rs:418` deposits the circuit crossing and the founding
quantum into one two-armed counter, so `S = 2π·winding + arg(basis)` **overcounts by one turn per
founding** and the ledger cannot separate histories. That fires the falsifier this plan declared.

**And the honest reading is not to force separation.** Sol's own note governs: *action is normally a
quotient of histories; requiring it to identify every history is itself too strong.*

> **So `ActionLedger` is misnamed rather than broken.** What it returns is **an oriented,
> species-erased deposit census plus a terminal weighted rotor** — a real invariant, and not an
> action. Rename it to what it is.

**If a true action is wanted it needs the split Sol derived** — `(C₊, C₋, B) ⊕ (F₊, F₋)` with
`C = D − F` — which is a change to the fold's own law and should not be made casually. The signed
phase error of the current form is exactly `2π(F₊ − F₋)`.

---

## 4. A CONTROL MUST EXHIBIT ITS OWN ORBIT — and this is the session's dominant defect

Across four audits the most common finding was **a control that cannot fail**:

| control | why it could not fail |
|---|---|
| the cocycle tests | authored values with a hand-picked "direct" equal to the product — asserts associativity of multiplication |
| the remount test | reseals using the same values it then asserts equal |
| `organ_difference` | every `OrganRest` ever built carries `b"a"`, `b"b"`, `b"declared"` — it has never touched a real organ |
| the superposition test | collects into a `BTreeMap`, so the second entry overwrites the first |
| arm C | passes on any overlap short of total, over a buffer where chance predicts ≈342 and it returned 415 |
| the coherence instrument | `|sweep|²` is dead code the compiler names, declared in six places |

**Re-measured 2026-08-15. Two rows of this table are now FALSE and are struck rather than deleted, because
the table's subject is the defect shape and a repaired instance is still its provenance.**

- `organ_difference` — repaired. `cargo run -q -p life --example the_rest_advances_or_the_model_is_frozen`
  now returns an organ arm over 103 deposited Lean artifacts, sealing a real `ConditionedRest` at
  44,468 against 90,846 octets: the conditioned arm moves `["derivation"]` and the reseal moves `[]`.
- the coherence instrument — removed, with its docs, on the same day.

The other four rows stand as written.

**The corpus already forbids this** — *a gauge whose group acts trivially on the declared material is
not a gauge* — and it is **not enforced anywhere.**

> **REVISION: every test asserting an invariance must also assert that the declared transformation
> MOVED something.** The one test in the tree that does this is
> `arrow.rs::the_hand_and_the_founding_survive_the_affine_gauge_while_the_magnitudes_move`, whose
> `a_magnitude_moved` flag is the pattern. Make it the convention, and consider making it a lint.

**This is worth more than any single repair above**, because it is the defect that let the other
defects stand.

---

## 5. JOIN WHAT IS ALREADY OWNED — before building anything

The finger-trap correction, with specific targets found this session:

| already owned | where | what it joins |
|---|---|---|
| `ExactReading::HarmonicReal` = `re² − im²`, exact over `Rat` | `model_surface.rs:61` | **the arrow's `(1,1)` form already has an owner.** `founds()` is `HarmonicReal ≤ 0`, and `causal_class = sense ∘ (·)²` exactly |
| `ExactRatMatrix` with a verified inverse | `exact_linear.rs:362` | **bypassed by the four modules its own doc names** — `diffusion`, `sheaf_diffusion`, `inverse_transport`, `generative_transport` — and the bypass **dropped the inverse-certificate check** |
| `simplicial.rs:689 is_affine` | | `Aff(1,ℂ) = Stab_{PGL₂}(∞)`, so the affine invariant *is* the cross-ratio with `∞` declared |
| `TABLET_THE_TURN.md` §5 | | already names `reach/aim/cross` as the friction triangle and the law of cosines — three steps of this line re-derive it |

> **And the sharpest one: `held_live = 0` is not an absence.** Since `Aff(1,ℂ)` fixes `∞`, an unheld
> fourth body is **the fourth body pinned at infinity — an absolute frame**, which is the archived
> fourth lesson arriving as a measurement.

---

## 6. WHAT IS NOT A CONSTRUCTION — refuted, and named so nothing builds on it

- **Hodge as `−aim`.** `aim` is the Euclidean inner product; its quadratic form is **positive
  definite** and cannot fail. What changes sign is the off-diagonal pairing past a right angle,
  which is what a definite form does. No realizer population, no certified remainder, and nothing in
  the tree records the sign of `aim`.
- **Riemann as the geometric-mean pole.** Nothing computes `√(ab)`, a Pythagorean mean, or a Thales
  lift. `AM·HM = GM²` is an algebraic identity quoted as *measured* — the tautology rule.
- **Yang–Mills as `kelvin.rs`.** Scalar; a three-vertex junction has a trivial structure group.
- **Holonomy at the third port.** The ratio cocycle is a coboundary; its holonomy is identically
  zero, adiabatic or abrupt.
- **The arrow's plane as Lorentzian covariance.** A classification only; the machine realises none of
  its isometries.

**The six-row Millennium table stands as acceptance criteria with `interpretation` as its ceiling.
Three rows were promoted to "acquired" and all three are withdrawn.**

---

## 7. SCOPE CALLS THAT ARE BRANDON'S

Named, not proposed:

- **11,214 lines under `soma/membrane`'s `historical` namespace with zero consumers tree-wide** —
  §13 rule 3 says superseded production machinery is removed rather than deprecated.
- **The ownership ratchet does not watch `crates/holonic-structure`** — the crate whose stated
  purpose is owning the substrate containers, and where four modules landed today. Its baseline
  carries zero rows for it, by declared aperture.
- **Four PTX entries compiled, asserted present by a `contains()` check, never launched.**
- **`approach_front.rs`, `communication.rs`, `face.rs`** — zero references. `model_surface.rs` was on
  that list until §5 found it owns the `(1,1)` form, which is the difference between *dead* and
  *unjoined*.

---

## 8. Ordered, with the gate first — AND THE STATE OF EACH, 2026-08-15

```text
   0   measure the founder's write depth against the contact's read depth   RAN — and ruled out 1
   1   close the ordering (or the depth map), and require found ≠ 0         WITHDRAWN, measured inert
   2   the two-component link — M(ρ), with τ and Γ derived                  BUILT and now DRIVEN
   3   retype the ledger to the census it is                                DONE — DepositCensus
   4   make "the gauge must move something" the convention                  CARRIER BUILT and APPLIED
   5   join HarmonicReal, exact_linear, is_affine                           DONE
```

### THE FOURTH REPAIR — built and reverted, and the reason is the finding

[The record](../research/records/2026-08-15_THE_FOURTH_REPAIR_WAS_BUILT_AND_REVERTED_AND_THE_SUB_COMPOSITION_IS_WHERE_IT_STOPS.md).

A composing mouth was added to `ErosBody` and wired into the live `Cell` branch, on the reasoning
that a `Cell` carries no interior to have been composed. **It pointed the wrong way**:
`geometry_face_with_atlas` returns `atom_node(relation.cog())`, so the `Cell` face **is an atom** and
belongs in the sub-illicium. Routing it into `perceive_grain(0)` declares a grain *above* what the
material founded. `holon-plate`'s carrier-extent assertion caught it; the mouth was **removed** rather
than left standing unjoined.

**And the defect is one level above all four repairs.** Measured on 24,000 octets through both
apertures at axis 256:

```text
                          WORD GRAIN        ATOM GRAIN
   arrivals                    3,704            22,987
   sub-illicium folded             0               905    <- THE GATE OPENS
   thoughts completed            357                 0
   deposited winding       373 : 311         585 : 583    <- the hands CANCEL
```

**The gate opens 905 times, the brick reaches `perceive_node_emitting`, and the word grain completes
nothing.** The atom path is not inert — 30,412 own words placed against the word grain's 31,720 — but
its deposited hands are balanced to within 2 of 1,168, which is the destructive regime. Nothing
accumulates a preferred turn, so no thought is ever founded to complete. **That is a statement about
the SWING at the word grain**, and it is where the next attempt goes.

*Falsifier:* a repair must move the drift away from balance **and** raise `thoughts completed` off
zero. One without the other is a count moved and not an edge.

### What was joined, and what each returned

| join | state | what it returned |
|---|---|---|
| `TransferMatrix` on a conduct path | **DONE** | 10,492 hops over the real repository; composite `τ = 5:3`, `Γ = 2:3` against a 150-digit hop product; an out-and-back of 9,697 links with 260 reflecting composes to `Γ = 0:1`; **reversal negates `Γ` exactly** — the magnitude is a function of the two ends, the hand of the direction |
| `DeclaredGauge` applied | **DONE** | wired into `traversible_chain`'s rescaling invariance, which had **no anti-vacuity arm at all**, plus 10,497 real members in the traversal driver |
| `communication::spread_from_each` | **DONE** | `the_measure_is_situated` built two covers by hand pairwise; the iterated form returns **radius 1 from the union and radius 2 from either half** — each half reaches the other only through the union |
| `Face` | **DONE** | the traversal profile was `Vec<u64>`; the out-and-back's ends are now addressed rather than indexed |
| `organ_difference` | **REPAIRED** | had never touched an organ — every `OrganRest` carried `b"a"`/`b"declared"`. Now seals a real `ConditionedRest` over 103 deposited Lean artifacts: `44,468 → 90,846` octets, fires on the conditioned arm and not on the reseal |
| the coherence instrument | **CUT** | `sweep_squared` and `scalar_sum_squared` were computed every passage and read by nothing, with docs still describing the withdrawn `\|sweep\|²` reading while `classify` read `d²` against `N` |

### Two rows of §7 and one of the roadmap were STALE

- **The conducted return at `temper`/`derivation_integral` is BUILT** — `returned_reading.rs:136`
  imports it on a **library** path and `the_reading_returns` drives it: leak → accumulation, 9 → 18
  committed stems, every movement naming the return that caused it.
- **`chain`, `relating` and `junction` are reached** — `traversible_chain.rs:24` imports them by
  name, which a path-shaped grep cannot see. *A census run with the wrong instrument decays
  immediately.*

**Bars.** No Millennium row grades any of it. No count is a cost. Every passage figure carries its
axis. And a control that has never fired has not been tested — which this round demonstrated three
times over.

# The rung refuses by name, and the unresolved pair is the remainder

**Date:** 2026-08-11
**Truth status:** `established-bounded` for every claim about the tree, each verified by reading the
owner; `proved-standard` for the external theorem, which is kernel-verified at its source;
`interpretation` where marked, and §6 is entirely so.
**Evidence:** direct source inspection of `structure_group.rs`, `supported_realizers.rs`,
`inertia.rs` (grep, this session); the zeta-23-lean repository read via its published README; a
GPT 5.6 Sol peer session (read-only, this session) whose four checkable tree-claims were each
verified against the owner before being carried; no driver was run.
**Provenance:** Brandon supplied the resource directly — *"here it is as a resource again:
https://github.com/anthropics/zeta-23-lean, from https://www.anthropic.com/research/riemann-zeta"* —
and ruled on the first framing's failure: *"You seem to have radically different ontological
perspectives on the issue, which to me reads less like a disagreement and more like you didn't
establish an agreed upon medium for the communication to actually occur and reconcile… Your word
choices are seemingly less founded in how the machinery actually functions."* Both received
2026-08-11 in the session that deposits this record.
**Band:** SOMA AND ENGINE SOURCE UNCHANGED / NO DRIVER RUN / FOUR TREE CLAIMS VERIFIED BY READING
THE OWNERS / EXTERNAL THEOREM READ AT ITS PUBLISHED SOURCE / TWO CONSTRUCTIONS POSED, NEITHER BUILT

---

## Present question

Anthropic released a kernel-verified Lean formalization (zeta-23-lean, Lean 4.33.0-rc2, axioms
`propext, Classical.choice, Quot.sound` only, no `sorry`) proving that **at least two thirds of the
nontrivial zeros of ζ lie on the critical line** — with simple-zero, distinct-zero,
Dirichlet-`L`, and ξ′ variants, and an explicit optimality ceiling for its own certificate class.
`CONSTRUCTION_STATE.md` carries this as a live tension against `CLAUDE.md` §2: the result *"obtains
a placement bound with no positive realizer, renouncing termwise positivity outright and paying with
two trace moments and a signature instead."* The present question: what is that result **in this
framework's own medium**, what does the tension actually adjudicate to, and what does the tree build
first because of it.

The first attempt at this question failed in a specific, corrected way, and the correction is part
of the deposit: the assistant described the certificate in receipt-vocabulary — "moments,"
"fractions," "aggregate" — while the peer model described it in navigation vocabulary, and the two
never formed a comparison cell because the boundaries were incompatible. `canon/TABLET_THE_OPERATIONS.md`
is the notation deposit that closes that failure class; this record is the zeta content restated
inside it.

## 1. What the external theorem is, in the medium

The explicit formula (Weil's, formalized in `Zeta23/WeilEF/`) is a transport law joining two
populations that cannot see each other's interiors — the primes and the zeros — through a declared
family of window functions. In the deposited notation: the window family is the **bra side**, the
zero population the **ket side**, and the certificate is built from exactly **two power-sum faces**
of the zero-side construction — `tr(P+Q)` and `‖P+Q‖²_F = tr((P+Q)²)` — plus a **signature**. The
finite core (`Zeta23/LinAlg/`, self-contained) is Sylvester's law of inertia both directions, von
Neumann's trace inequality, Weyl eigenvalue counting, and the rank–trace inequality

```text
   2c·tr(P+Q) − ‖P+Q‖²_F  ≥  Σⱼ k_c(mⱼ)      (proved TIGHT: equality = Σⱼ k_c(mⱼ) + c²·b)
```

with `P` positive semidefinite by Gram construction. **Positivity is not renounced; exhaustion is.**
What Weil's criterion would demand — the complete quadratic form nonnegative on the *full*
admissible test space — is exactly full placement (RH). The certificate pays two faces of it.

## 2. The certificate class is an instrument rung, and the ceiling is the rung refusing by name

The admissible windows are **bandwidth-one**: an index condition on the test family's Fourier
support. That is the canon's own definition of an instrument — *a declared receiver family whose
aperture is an index condition on a group*
(`research/records/2026-08-10_THE_INSTRUMENT_DECLARES_THE_APERTURE_AND_THE_REFUSAL_IS_THE_RETURN.md`)
— so the zeta-23 certificate class is a **rung**, exactly as the compass field `[ℚ(α):ℚ] = 2ⁿ` is a
rung. And the release proves its own aperture as a theorem: **every bandwidth-one certificate is
bounded by ≈ 0.6818287** (`Zeta23/PairCeiling/`). That is the rung refusing by name — the same
shape as the compass refusing `∛2` — and it means the route to full placement is **climbing rungs
(widening the declared family), never turning a scalar dial inside one rung.**

## 3. The unresolved pair is the remainder, and it lands on a live organ

A bounded-bandwidth window is a finite crystal: it cannot resolve two zeros closer than the
reciprocal of its aperture. What such a receiver returns for an unresolvable pair is the pair
**collapsed** — counted, never placed individually. So the missing third is not uncertainty; it is
the **collapsed-pair population of a declared receiver family**, which is precisely the return
species of `crates/holonic-engine/src/receiver_exact_compression.rs` — collapsed pairs, each with
the shortest word that would separate them. The zero-side block structure with multiplicities
(`Zeta23/ZeroSide/`, `FinalMult.lean`) is that population's bookkeeping in the formal artifact.
Montgomery's pair-correlation line is the standard mathematics of exactly these close pairs.

## 4. The tension, adjudicated — an OPEN pair with its witness, not a resolved side

Two lawful routes to **different receiver statements**:

| route | pays | returns |
|---|---|---|
| `CLAUDE.md` §2 (function-field, proved) | an ample class → Rosati positivity on the whole correspondence algebra ⊕ `π†π = q` | **pointwise** placement, `\|σ(π)\| = √q`, every eigenvalue |
| zeta-23 (kernel-verified) | two power-sum faces of a Gram-positive pair + a signature, at a bandwidth-one rung | a **placement count** ≥ 2/3, with the collapsed pairs as the counted remainder |

Per the spine's law, `OPEN` is not resolved by choosing. The fork that remains open, stated so it
can fire: **is the exhaustive receiver family reachable by climbing restriction bounds alone, or
does the top rung require a paid positive realizer — the ample-class analogue?** The witness: a
pointwise placement obtained with no positive realizer would falsify the universal form of §2's
slogan (the function-field instance survives regardless); conversely, a proved ceiling short of 1
for *every* restriction-bound family would establish that the top rung must be paid for.

## 5. Four tree-claims from the peer session, each verified against its owner

1. **`canon/THE_MILLENNIUM_FRAME.md`'s Yang–Mills row is stale.**
   `structure_group.rs:511` carries `curvature_commutator` — *"The curvature `a ∧ a`, as a return
   rather than a flag"* — plus `commutator_subgroup` and `separating_pairs`. The `a ∧ a` term
   exists; what the Yang–Mills-facing line lacks is a representation, a Wilson plaquette action, a
   transfer operator, and reflection positivity. Corrected in the frame the day this record is
   deposited.

   **AND THIS FOUR-ITEM LIST IS ITSELF STALE — corrected 2026-08-13.** Three of the four were built
   on 2026-08-11, the same day this record was deposited, and committed at `c911c03`:
   `crates/holonic-engine/src/lattice_gauge.rs` supplies `IntegralRepresentation`, `wilson_action`
   (`S = Σ_p (1 − χ(U_p)/dim)`, character form, exactly over `Rat`) and `transfer_operator` with an
   exact spectrum. **Only reflection positivity remains absent**, measured zero across `crates/` and
   `soma/`. The module's own no-mass-gap bar stands unchanged.
2. **`CLAUDE.md` §11's "positive form — built" row is stale the other way.**
   `supported_realizers.rs`'s own header: `xᵀ(MᵀM)x = |Mx|² ≥ 0` for every integer matrix — a
   positivity that cannot fail, removed 2026-08-08 as the check whose material cannot vary the
   property under test. The module's honest content is rank and cokernel, and `induced_placement`
   computes Gram rank/nullity: **no spectral placement is induced and its positive hand cannot
   fail.** It may not be cited as §2's placement organ.
3. **`inertia::congruence` refuses where the finite core of §1 lives.** `inertia.rs:524` returns
   `SingularChangeOfBasis` for a singular change of basis; the lawful return is the pull-back bound
   `n₊(PᵀAP) ≤ n₊(A)` with rank and kernel testimony. Two models converged on this construction
   independently — one from restriction of forms, one from the zeta-23 core — including the same
   strict control: `[[1,1],[1,1]]ᵀ·diag(1,−1)·[[1,1],[1,1]] = 0` must return **strict** inequality,
   not an error.
4. **The Millennium Hodge conjecture is rational, and the tree's finite model is of the integral
   variant.** If `pα` is algebraic then `α = (1/p)[pα]` is rationally algebraic, so
   `ObstructionSpecies::ReachableOnlyInMultiple` faithfully models Kollár's *integral* failure and
   must never be reported as a Millennium-Hodge obstruction after tensoring with ℚ.

## 6. Shape observations — `interpretation`, the assistant's, offered so they can be refused

- **Caffarelli–Kohn–Nirenberg has the same return species as zeta-23**: a positivity paid through a
  bounded receiver family (the local energy inequality) forces regularity everywhere except a
  parabolic-Hausdorff-dimension ≤ 1 set — placement off a counted exceptional population.
- **Gross–Zagier/Kolyvagin is §2's chain in arithmetic**: Néron–Tate height as the positive form,
  the Heegner point the realizer that pays, `L′(1)` the placement that rides; the regulator is the
  Gram determinant of the realizer population.
- **Reflection positivity is integration-by-reflection constructing the theory whose gap is the
  Yang–Mills problem**: the Osterwalder–Schrader construction builds the Hilbert space from
  `⟨θf, f⟩ ≥ 0` across a time slice — the same operation as the method of images in `diffusion.rs`
  and the seam `Fix(J)` on the RH side.

None of these is a route; each is the same **return species** appearing on different material, and
each names the standard literature where the instance is proved.

## 7. The two constructions this poses, neither built

1. **`pullback_inertia_bound` in `crates/holonic-engine/src/inertia.rs`.** Exact over `Rat`:
   accept any `P` (not necessarily invertible), return the pulled-back inertia with
   `n₊(PᵀAP) ≤ n₊(A)`, `n₋(PᵀAP) ≤ n₋(A)`, rank and kernel testimony. *Falsifiers:* must
   reproduce the tightness equality `Σ k_c(mⱼ) + c²·b` on a declared block fixture; must return
   strict inequality on the collapse witness above; invertible `P` must reproduce `congruence`
   exactly (Sylvester). Closes the sixth open construction in `CONSTRUCTION_STATE.md` and gives the
   body the finite core of the strongest RH movement in decades — pulled back from the actual
   completed zeta relation, which the spine's bar demands and which is satisfiable for the first
   time because the relation is now a kernel-verified artifact.
2. **A `lattice_gauge` mouth around `structure_group`.** An exact nontrivial representation, vertex
   gauge transformations, plaquette holonomy, the Wilson action, one transfer/correlation receiver.
   *Controls:* a gauge-equivalent pair returns identical action and spectrum; a deliberately
   altered plaquette moves both; an abelian control erases the commutator contribution. **No
   "mass gap" label unless a family carries lattice spacing, volume, and correlation-length
   scaling** — a finite matrix having a gap is nearly automatic and is not the problem.

## Owners

| object | owner |
|---|---|
| Sylvester inertia by exact elimination; the refusal at the seam | `crates/holonic-engine/src/inertia.rs:512-558` |
| passages named by character and winding | `crates/holonic-engine/src/winding_inertia.rs` |
| the collapsed-pair return species | `crates/holonic-engine/src/receiver_exact_compression.rs` |
| the discrete `a ∧ a` and basepoint-free holonomy class | `crates/holonic-engine/src/structure_group.rs` |
| Gram rank/cokernel (not placement) | `crates/holonic-engine/src/supported_realizers.rs` |
| the external artifact | `github.com/anthropics/zeta-23-lean`, read 2026-08-11 |
| the local negative on one transport candidate | `soma/formal/rh-source-transport/PROPORTIONAL_OBSTRUCTION.md` |

## What this does not establish

Nothing here proves, approaches, or schedules any Millennium problem, and no deed may be graded by
this record. The instrument-ladder reading of the certificate class is exact about the *artifact*
(the bandwidth condition and its ceiling are in the formal source); its identification with the
canon's instrument law is `interpretation`. §6's three observations are shape, not routes. The two
constructions in §7 are posed, not built, and their falsifiers have not fired because nothing
exists yet for them to fire on.

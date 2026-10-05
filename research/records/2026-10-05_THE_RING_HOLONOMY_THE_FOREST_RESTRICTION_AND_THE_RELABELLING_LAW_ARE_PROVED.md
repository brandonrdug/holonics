# The ring's holonomy closes a transported cycle, the forest restriction is the joint fibre's projection, and a located code ignores the labels

**Date.** October 5. **Issues.** #62 (the statements owed by #359, #366, #374 and #379), #63.
**Grade.** [proved-derived; formal-checked] for the theorems named below; [counterexample;
formal-checked] for the witnesses; [open] for what §4 leaves owed.

**Occasion.** Three statements were owed in #62 on October 5: the cycle-order condition of the
located keys in its corrected form with holonomy (#359 lane B, item 2 and its two corrections),
the repair's restriction as the joint fibre's projection (#366, repair record §8 item 1), and the
relabelling law of the located code (#374 §8 item 3, #379 §10 item 6). Each is now a Lean module
of `HolonicsResearch`, joined to its existing owner.

**The recorded failures this could repeat** ([lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md)):
a design thought in the programming language (each statement is stated on the ring cell's
connection incidence, the pair relations' fibre and the classes' relabelling, never on arrays or
offsets); bits read as progress (the relabelling law proves invariance, it claims no compression);
a located cause carried unrepaired (§2 records where the brief's forest statement needed its
hypothesis instead of weakening the theorem silently).

## 1. The ring's holonomy decides which turns a transported cycle carries

Owner: `lean/HolonicsResearch/Holon/RingCellHolonomy.lean`, namespace
`Holonics.HolonCore.RingCell`; atlas `holonomy.ring-step-period`, `holonomy.ring-cycle-closure`,
`holonomy.order-two-mobius-ring`.

On the ring cell `ℤ/d` with connection-valued incidence (`Holon/Complex.connectionIncidence`,
edge transports `g_x ∈ 𝕜ˣ`), the covariant step `(Pφ)(x) = g_x φ(x + 1)`:

```text
d_A = P − 1                                              connectionIncidence_eq_step_sub_one
P^d = hol · 1,  hol = Π_x g_x (from every base)           ringStep_pow_period, ringHolonomy_eq_prod
walkRead(d_A φ) around the ring = (hol − 1) φ(0)          ring_cell_curvature  (Holon/Complex.cell_curvature)
g_x ↦ k_x⁻¹ g_x k_(x+1) leaves hol fixed                  ringHolonomy_regauge
P^d = h ⇒ (P^δ)^N = h^(δ/g),  g = gcd(δ, d), N = d/g      pow_step_cycle (any monoid)
P^δ carries μ  ⇔  μ^N = hol^(δ/g)                         ring_carries_iff
hol = 1:  P^δ carries ζ  ⇔  ord ζ ∣ N                     flat_ring_carries_iff
δ ∣ d:    P^δ carries ζ  ⇔  hol = ζ^(N mod ord ζ)         carries_iff_remainder
```

"Carries" is the eigen-relation: some nonzero vertex field `φ` with `P^δ φ = μ φ`. The converse
half needs no root of `hol` in the field: the carried field is the cycle's own sum
`Σ_(i<N) μ^(N−1−i) P^(δi) δ₀`, turned by `μ` because `(P^δ − μ)Σ = (P^δ)^N − μ^N` and nonzero
because it reads `μ^(N−1)` at vertex `0` (`d ∤ δi` for `0 < i < N`, `not_dvd_step_mul`). So the
condition holds over `ℚ(i)` as well as over `ℂ`.

The order-2 instance [counterexample; formal-checked]: `d = 60 = 2²·3·5`, `δ = 2`, `N = 30`,
`ζ = i`. Every ring of holonomy `−1` carries `i` under `P²` (`sixty_mobius_carries_i`; the seam
`−1` realizes one, `sixty_seam_carries_i`), and no flat ring does (`sixty_flat_refuses_i`):
`i^30 = −1`, the remainder `i^(30 mod 4) = i²`. A ring's holonomy is gauge invariant, so it is
material: the turn the keys located requires the Möbius ring (`holon.mobius-annulus-orientation`).

## 2. The two-sided restriction on a forest is the joint fibre's projection

Owner: `lean/HolonicsResearch/Transport/ForestRestriction.lean`, namespace
`Holonics.Transport.ForestRestriction`; atlas `compression.forest-restriction-projection`,
`compression.restriction-cycle-obstruction`; added as a Lean owner of `compression.pair-repair` and
`compression.transport-repair`.

A forest of pair relations (`PairForest`) gives each cell at most one antecedent, a rank that rises
to the consequent, and a relation per edge; the repair's chains are one (`offsetChains`: the edges
`(t − δ, t)` on the span). The restriction `F_t ← F_t ∩ R(F_s) ∩ R⁻¹(F_u)` is `revise`.

```text
revise F ⊆ F, monotone; revise(proj) = proj; proj ⊆ revise^[n] D        revise_proj, proj_subset_iterate
a fixed iterate within Σ_v |D_v| sweeps                                 exists_fixed_iterate
fixed F ⊆ D, nonempty families ⇒ F ⊆ proj                               fixed_subset_proj
fibre ≠ ∅ ⇒ fixed iterate = proj at every cell                          restriction_eq_projection
some family empties ⇔ fibre = ∅                                         restriction_empties_iff
one root: an emptied family empties all; fixed iterate = proj           fixed_empty_spreads, tree_restriction_eq_projection
truth ∈ fibre, F_v = {a} ⇒ truth_v = a                                  released_class_is_truth
fibre = ArtifactRelease.step id Sat (Π_v D_v); widths never widen       jointFibre_eq_step, jointFibre_width_le
Releasable fibre {i} ⇔ |F_i| = 1  (the width-zero release)              releasable_iff_one_class
```

The inclusion `F ⊆ proj` is the construction: a class at a cell is lifted to its root by the
antecedents' supports (`exists_guide`, strong induction on the rank), then completed from the
roots down by consequent supports that keep the guide wherever it fits (`complete`,
`complete_spec`, `complete_agrees`).

[agent-inferred, from the mathematics] The brief's sentence "equals, at every vertex, the
projection" holds on a tree and fails on a forest of several trees: an inconsistent tree empties
only its own families, while the projection of the empty joint fibre is empty at every cell. The
forest theorem therefore carries the hypothesis that the fibre is nonempty, and its other half,
"some family empties exactly when the fibre is empty", is unconditional; that half is the repair
owner's refusal (an empty family refuses the key), so the owner's behaviour is covered on every
forest.

Acyclicity is load-bearing (`triangle_supported_but_empty`, [counterexample; formal-checked]): on
the triangle with `≠` over two classes every class has a support across every edge, yet the fibre
is empty.

## 3. A located code's length is invariant under relabelling; a residue chart's is not

Owner: `lean/HolonicsResearch/Compression/Relabelling.lean`, namespace
`Holonics.Compression.Relabelling`; atlas `compression.code-relabelling-invariance`,
`compression.residue-chart-not-carried`; added as a Lean owner of
`compression.transport-relabelling`.

```text
encode(c∘π⁻¹, π∘x) = encode(c, x);  L(π∘x) = L(x)                      encode_relabel, codeLength_relabel
prefix-free and Σ_a 2^(−ℓ_a) ∈ ℚ invariant                              prefixFree_relabel, kraftSum_relabel
Π_k p(x_k) invariant;  Π_k 2^(−ℓ(x_k)) = 2^(−L(x))                      passageMass_relabel, passageMass_dyadic
K(π∘x) = K(x)∘π⁻¹ ⇒ bits and length invariant                          carried_encode, carried_codeLength
first-occurrence codewords and count-read lengths are carried           firstOccurrence_carried, countLengths_carried
a uniform width (the literal code) is invariant in any chart            uniform_codeLength_relabel, literalCode_length_relabel
```

No logarithm is taken: the description length is the exponent of the passage's dyadic mass.
The residue chart [counterexample; formal-checked]: on `ℤ/3`, the prefix code `0 ↦ 0`, `1 ↦ 10`,
`2 ↦ 11` chosen by the numeric residue (Kraft sum `1`), kept on the values under the ring's turn
`u ↦ u + 1`, codes the passage `0` in one bit and its turned passage `1` in two
(`residue_codeLength_moves`); its dyadic mass moves from `1/2` to `1/4` (`residue_mass_moves`);
the constant residue coder is not carried (`residue_not_carried`). This is THE_MACHINE guard 9's
test stated in Lean.

## 4. Still owed in #62

- #359 item 2 is discharged on the ring cell. The Rust ring (`Ring::rotate`) consumes no `P^d = h`
  yet; its consumer is `geometry::complex::ConnectionIncidence`. #359 items 1 (the turn menu's
  fibre law) and 3 (the pair deposit's certified quadratic step) are not addressed here.
- #366 item 1 is discharged. Item 3's join (the width-zero release is the restriction's one-class
  family) is stated in the artifact chart (`releasable_iff_one_class` with
  `ArtifactRelease.releasable_iff_every_coordinate_width_is_zero`); item 2 (the repair codec as a
  Fold transition) is not addressed here.
- #374 item 5's chain case is an instance of `restriction_eq_projection` once the lift relation is
  read as one binary relation per edge; the soundness of the release over a fibre's union of
  members is owed.
- #374 item 3 and #379 item 6: the abstract law is proved (a carried coder's code length is
  invariant; the residue chart is not carried). That the located route's survivors on `π∘x` are
  those on `x` carried by `π` (the hypothesis `Carried` for `TransportLocation` itself) needs the
  location's law stated in Lean and remains owed.

## 5. Receipts

- Gate 4, `bash tools/lean_check.sh HolonicsResearch` on a worktree of `origin/main` (`f91666c0`)
  with the main checkout's Lean build copied: 10,328 jobs, exit 0, no `sorry`; 153,681 ms wall
  against a projection of about 130,000 ms (deadline 2,400,000 ms by an outer `timeout`; the excess
  is the rebuild of the modules where the copied cache differed from `origin/main`); peak resident
  set not measured. No Rust changed.
- `#print axioms` (each module's `Audit` section, 42 declarations): every one depends only on
  `propext`, `Quot.sound` and, for 32 of them, `Classical.choice`.
- Receipt: [`lean_check.txt`](2026-10-05_THE_RING_HOLONOMY_receipts/lean_check.txt).

# The self-stress is a supported realizer, and the flex space is a third selector

**Date:** 2026-08-21
**Kind:** derivation deposit — the rigidity join Brandon's protein-structure notes were pointing
at, stated as mathematics and instanced in Lean. **It schedules nothing.**
[`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
**Per Brandon's ruling of 2026-08-20, restated 2026-08-21, this line does not couple to the
engine**: the mathematics is theorized outside the engine and adapted within the mathematics
first. The only trees written are `soma/formal/` and `research/records/`.
**Truth grades:** `proved-derived` for the sixteen Lean theorems, kernel-checked, all sixteen
audited by `#print axioms` and depending only on `propext`, `Classical.choice`, `Quot.sound`;
`proved-standard` for the imported classical rigidity theorems, cited and not proved;
`interpretation` for every correspondence to the Riemann and Hodge routes and to protein
structure, marked in place; `open` for the named rungs.

---

## 0. Provenance

**Brandon, 2026-08-21:** the protein-structure notes *"despite sounding unrelated will be keystone
ideas for making more progress towards RH and Hodge for certain."* The protein mathematics itself
was deposited by Sol in
[`2026-08-21_THE_FOLD_IS_A_CONSTRAINT_ECOLOGY_THE_ACTIVE_SITE_IS_A_CATALYTIC_RECEIVER_AND_THE_CODEC_RECOVERS_ARCHETYPES.md`](2026-08-21_THE_FOLD_IS_A_CONSTRAINT_ECOLOGY_THE_ACTIVE_SITE_IS_A_CATALYTIC_RECEIVER_AND_THE_CODEC_RECOVERS_ARCHETYPES.md),
which carries the constraint carrier `(V, C_η, q, F_η, J_η, G, E_η, R_η, Γ_η)` and the standard
identities *motions = ker J, self-stresses = ker Jᵀ* — and stops one step short of naming what
those objects are in the vocabulary of the two route charts. This record takes that step and
proves its finite instances. The route charts are
[`2026-08-21_THE_RIEMANN_ROUTE_RUNS_FROM_A_KERNEL_CHECKED_ANCHOR_TO_A_REALIZER_AT_THE_ARCHIMEDEAN_PLACE.md`](2026-08-21_THE_RIEMANN_ROUTE_RUNS_FROM_A_KERNEL_CHECKED_ANCHOR_TO_A_REALIZER_AT_THE_ARCHIMEDEAN_PLACE.md)
and
[`2026-08-21_THE_HODGE_ROUTE_LIFTS_THE_CLASS_TO_A_SHAPE_AND_THE_SHAPES_ARE_THE_PARTICLES.md`](2026-08-21_THE_HODGE_ROUTE_LIFTS_THE_CLASS_TO_A_SHAPE_AND_THE_SHAPES_ARE_THE_PARTICLES.md).

---

## 1. The join, in four sentences

**A self-stress is a supported realizer.** It is a weighting on the bars that balances at every
joint — an object whose existence is a property of the configuration, physically supported in the
most literal sense, and never a declaration. **The form it induces on loads is the positive form a
realizer pays**: Connelly's super-stability theorem converts a positive-semidefinite stress matrix
of maximal rank into global rigidity — *placement* — which is the same chain as ample class →
positive Rosati involution → the Weil placement, on constraint material. **The radical of that
form is the rigid-body gauge**, so the descent-through-the-radical trichotomy proved in
`Paying.lean` and `AlgebraicGNS.lean` arrives on physical material with nothing reproved. **And
prestress stability demands positivity on the flex space** — the kernel of the rigidity Jacobian —
which is a *third* selection rule for "positivity on a declared subspace", read off the material
rather than declared, beside the involution selector of `ReflectedPositivity.lean` and the
Lefschetz selector, which are already proved not to share a selection rule.

That fourth sentence is the answer to the audit request's sharpest open question — *is "positivity
on a declared subspace, with the selector varying by line" a thesis, or a shape loose enough to
fit anything?* One measured negative was thin. A third selector, physically founded, with
witnesses whose positivity can fail, is evidence the shape is a real family.

---

## 2. What is proved, and where

Owner: `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/Rigidity.lean` — 242 lines,
**16 theorems, zero `sorry`**, all sixteen audited by `#print axioms`, none depending on
`sorryAx`. The library builds at 3,314 jobs with the module imported at the root.
**Measured after the merge: `Millennium/` is 27 files, 5,818 lines, 304 theorems** (by
`grep -cE '^[[:space:]]*theorem ' *.lean` summed, the count the cooling audit fixed).

### Instance one — the square with both diagonals, the realizer-pays shape

| theorem | what it establishes |
|---|---|
| `theStressBalancesAtEveryJoint` | sides at `+1`, diagonals at `−1` **is a self-stress**: four vanishing joint sums over `ℚ²` |
| `theAllOnesWeightingIsNotASelfStress` | the balance condition **can fail and does** — the all-ones weighting misses at the first joint |
| `theBarSumIsTheFactoredForm` | the stress-weighted bar sum over the six bars **is** `slot x · slot y` — the physical stress matrix and the rank-one square are one object, by polynomial identity |
| `theStressFormIsSymmetric`, `theStressFormIsNonnegative` | symmetric, positive semidefinite |
| `theNullConeIsTheSlotKernel`, `theRadicalIsTheSlotKernel` | null cone = radical = kernel of the slot functional — `Paying.theNullConeIsTheRadical` on a form small enough to see through |
| `theGaugeIsInTheRadical` | the constant load and the configuration's own two coordinate loads have vanishing slot — **the radical is exactly the affine gauge**, what no relative measurement sees |
| `theFormPaysOffTheRadical` | off the radical the form is strictly positive — the faithful row of the descent trichotomy |
| `theQuotientIsOneDimensional` | every load lands in the radical after subtracting one slot multiple — rank **one**, which is the maximal `n − d − 1 = 4 − 2 − 1` a planar four-joint stress matrix can have, the rank the imported global-rigidity theorems ask for |
| `theFlippedStressFailsAtTheWitness` | the sign-flipped stress fails positivity at an exhibited witness — positivity belongs to *this* stress, not to the structure |

### Instance two — the collinear triangle, the flex-selector shape

| theorem | what it establishes |
|---|---|
| `theCollinearStressBalances` | bars `12, 23` at `+2`, the long bar at `−1` is a self-stress on three collinear joints |
| `theTransverseMotionIsAFirstOrderFlex` | the transverse motion of the middle joint stationarizes every bar length — a genuine first-order flex |
| `theFlexIsNotARigidMotion` | no translation-plus-infinitesimal-rotation of the plane returns it: the ends force `b = 0` and `b + 2c = 0` while the middle forces `b + c = 1` |
| `theStressEnergyPaysOnTheFlex` | the stress energy on that flex is `4 > 0` — **positivity on the material's own selected subspace** |
| `theFlippedStressFailsOnTheFlex` | with the flipped stress the same sum is `−4 < 0` — the pay belongs to the stress |

The collinear triangle is the textbook prestress-stable framework: infinitesimally flexible, yet
rigid — the degenerate triangle inequality is tight, so no actual motion exists — with the
rigidity carried by exactly the second-order information the stress form sees. What is proved here
is the exact witness pair; the conversion of flex-positivity into rigidity is the imported
theorem.

### Imported, cited, not proved

Maxwell's counting rule and the Maxwell–Calladine index relation (motions minus self-stresses as
an index of the constraint map); Connelly's super-stability theorem (1982); prestress stability
implies rigidity (Connelly–Whiteley 1996); the generic characterization of global rigidity by a
maximal-rank self-stress (Gortler–Healy–Thurston 2010).

**Measured 2026-08-21** over `Mathlib` at `v4.27.0`:
`grep -rli "rigidity" Mathlib --include='*.lean'` → 2 files, both analytic (Liouville-type)
rigidity; `grep -rli "self.stress\|tensegrity\|infinitesimal.*flex"` → 0 files. A name search
over a stated scope, not a content-absence proof.

---

## 3. The correspondences, each graded `interpretation`

**To the Riemann route.** The route's pivot converts placement into a search for an object paying
a positive form. Rigidity is that search with the answer visible: the self-stress is found (or
fails to exist — `theAllOnesWeightingIsNotASelfStress` is what failure looks like), and placement
— unique embeddability — rides on the positivity it pays. *Find the stress* and *find the
archimedean realizer* are one question shape at two altitudes.

**To the Hodge route.** The index equivalence in `LorentzianPerp.lean` — reverse Cauchy–Schwarz
against a positive class ⟺ non-positivity on the perp — is the signature bookkeeping of
tensegrity: signed constraints (cables and struts) produce exactly the one-positive-direction
shape the Hodge index theorem states for the intersection form. And the matroid Hodge–Riemann
mechanism the engine already owns runs the ample chain on combinatorial material the same way the
stress matrix runs it on constraint material.

**To the protein.** The fold record's phase seams are rank-changing loci of the rigidity Jacobian
— the Lean development's *an obstruction belongs to a frame*, on physical material. **And
catalysis is a coboundary move**: an enzyme lowers the transition barrier without changing the
equilibrium endpoint — it changes the path representative and leaves the class untouched, which
is *why* a catalyst is reusable and deposits nothing. That is the method atlas's
reduce-then-extract-the-class arriving as chemistry, and it grounds the catalytic-morphology
objective the fold record adopts: a catalytic organ is one whose work reduction is a coboundary
in the energy chart, with the endpoint class its conserved quantity.

**To the codec's particle deed, feeding without scheduling.** The fold record's list of what an
M1 mathematical particle must carry — configuration, constraints, Jacobian, kernel/self-stress,
energy sections, phase seams — is the bar-framework vocabulary verbatim. Rigidity material is
exactly decidable over `ℚ` at any size, so it is calibration material where ground truth costs
nothing, the same role harmonic conjugation plays for M0.

---

## 4. What is owed, with falsifiers

**None is scheduled; the roadmap alone schedules.**

| owed | falsifier |
|---|---|
| **The general stress form over an arbitrary framework**, as a Lean structure joining `AlgebraicGNS`'s descent: the bar-sum form for a declared stress on a declared graph, its radical proved to contain the affine gauge in general, not per-instance. | A framework whose stress-form radical provably does not contain its affine gauge. |
| **The selector comparison, formalized.** The involution selector and the Lefschetz selector provably share no selection rule; state the flex selector in the same frame and measure it against both. | A common rule subsuming the flex selector and either other — which would weaken the three-selector evidence back toward a loose shape. |
| **The Maxwell–Calladine index as a Lean statement** on the concrete instances: motions minus stresses computed from the two kernels, matched against the count. | An instance where the computed index disagrees with the kernel dimensions. |
| **The tensegrity signature instance**: one cable/strut framework whose signed stress form exhibits the Lorentzian one-positive-direction shape against `LorentzianPerp`'s equivalence. | A signed framework satisfying the reverse inequality whose perp is not non-positive. |

## 5. Boundaries

No named conjecture is touched, and no claim about protein structure is made beyond what the fold
record already carries — the two instances are four and three joints over `ℚ`, and everything
proved about them is finite linear algebra. The imported rigidity theorems are cited with their
authors and not restated formally; nothing below depends on them. The correspondences in the
third section grade nothing and may not grade a deed. The engine is untouched, per Brandon's
ruling; the only trees written are `soma/formal/` and `research/records/`.

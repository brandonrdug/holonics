import Mathlib.Tactic

/-!
# Ricci: the Perelman schema enacted at the exact grain, with total retention

Perelman's proof of the Poincaré conjecture runs on six mechanisms: a flow on the morphology
itself, an adjoint-transported receiver whose reading ratchets, an anti-collapse bound, a finite
table of near-singular shapes, condensation that names its cut, and closure for the distinguished
class.  The proof is deterministic through and through — its "entropy" is a monotone functional
along a deterministic parabolic flow — but its smoothing stroke retains nothing: parabolic flow
quotients geometry below the receiver's grain with no fiber kept, which is why backward heat is
classically ill-posed.

**This file enacts the schema at the smallest exact grain, where the retention contract can be
total, and proves every clause.**  The terrain is a combinatorial circle with rational edge
lengths — the triangle, this project's quantum object — and the flow moves each length toward its
neighbours: the metric diffusing by its own second difference, which is the one-complex shadow of
the metric flowing by its own curvature.  Everything is exact over `ℚ`:

* **the flow conserves the total** — the normalization built in, the chain law with zero source;
* **the deviation contracts at exactly `1 − 3τ`** — the ratchet is not an inequality but an
  identity, and the rate is a winding eigenvalue: both nontrivial windings of the triangle carry
  `2cos(2π/3) = −1`, so the whole deviation plane contracts by one scalar;
* **the receiver ratchets**: the roundness reading obeys `W' = (1 − 3τ)² · W`, monotone on the
  declared aperture `0 ≤ τ ≤ 2/3`;
* **nothing collapses**: the minimum length is non-decreasing and the maximum non-increasing —
  the anti-collapse clause as two exact comparisons;
* **the only fixed shape is round** — the κ-solution table at this grain has one row, proved;
* **the round class is closed** — extinction: the flow holds it and the reading is zero;
* **the flow is invertible with testimony**: away from one aperture value the backward flow is
  exact and proved — *backward heat, well-posed at finite grain* — and the condensation into
  round part plus deviation reconstructs the metric exactly;
* **the classical deletion is localized**: at exactly `τ = 1/3` the flow collapses every triangle
  to round in one step — the unexhibited quotient of classical smoothing, caught at a single
  aperture value and exhibited as many-to-one by witness;
* **the ratchet can fail**: at `τ = 1` the reading quadruples, with the witness computed.

And on the square, the windings separate: the half-turn component contracts at `1 − 4τ` while the
two quarter-turn components contract at `1 − 2τ` — the flow's spectrum **is** the winding table
`1 − 2τ + 2τ·cos(2πk/n)`, and the fastest-dying mode is the finite shadow of the singularity
model selecting itself.

**Scope, stated plainly.**  Poincaré is a theorem about three-manifolds; nothing here is
three-dimensional, and this file replicates no step of Perelman's actual proof.  What it enacts,
kernel-checked, is the proof's *mechanism* under this project's retention contract — the
holonically revised flow in which "the flow forgets" becomes "the flow deposits."  The reading
that derives this schema and its transfer targets is the Poincaré record of 2026-08-21.

**Measured 2026-08-21** over `Mathlib` at `v4.27.0`: `grep -rli "ricci" Mathlib
--include='*.lean'` → **0 files**, and `mean curvature`/`curve shortening` likewise 0 — Ricci
flow has no formal presence in mathlib at any grain.  A name search over a stated scope, not a
content-absence proof.

Every `theorem` is discharged and none depends on `sorryAx`.  Nothing here claims movement on any
named conjecture.
-/

namespace Soma.Holonics.Millennium.Ricci

/-- A triangle terrain: three rational edge lengths on a combinatorial circle. -/
abbrev Tri : Type := ℚ × ℚ × ℚ

/-- One step of the flow at aperture `τ`: each length moves toward its two neighbours.  The
metric diffusing by its own second difference — the one-complex shadow of `∂g/∂t = −2 Ric`. -/
def flow (τ : ℚ) (ℓ : Tri) : Tri :=
  ((1 - 2*τ) * ℓ.1 + τ * (ℓ.2.1 + ℓ.2.2),
   (1 - 2*τ) * ℓ.2.1 + τ * (ℓ.1 + ℓ.2.2),
   (1 - 2*τ) * ℓ.2.2 + τ * (ℓ.1 + ℓ.2.1))

/-- The total length. -/
def total (ℓ : Tri) : ℚ := ℓ.1 + ℓ.2.1 + ℓ.2.2

/-- The mean length — the round representative's edge. -/
def mean (ℓ : Tri) : ℚ := total ℓ / 3

/-- The roundness reading: the receiver whose ratchet carries the argument.  *A deterministic
monotone functional, exactly as Perelman's entropy is; no stochastic object appears.* -/
def W (ℓ : Tri) : ℚ :=
  (ℓ.1 - mean ℓ) ^ 2 + (ℓ.2.1 - mean ℓ) ^ 2 + (ℓ.2.2 - mean ℓ) ^ 2

/-! ## 1. Conservation, contraction, and the ratchet -/

/-- **The flow conserves the total** — the chain law with zero source; the normalization is
built into the flow rather than imposed after it. -/
theorem theFlowConservesTheTotal (τ : ℚ) (ℓ : Tri) : total (flow τ ℓ) = total ℓ := by
  simp only [total, flow]; ring

/-- **The deviation contracts at exactly `1 − 3τ`, componentwise.**  The rate is a winding
eigenvalue: the triangle's two nontrivial windings both carry `2cos(2π/3) = −1`, so the
eigenvalue `1 − 2τ + τ·2cos(2π/3) = 1 − 3τ` governs the whole deviation plane at once. -/
theorem theDeviationContractsAtTheWindingRate (τ : ℚ) (ℓ : Tri) :
    (flow τ ℓ).1 - mean (flow τ ℓ) = (1 - 3*τ) * (ℓ.1 - mean ℓ) ∧
    (flow τ ℓ).2.1 - mean (flow τ ℓ) = (1 - 3*τ) * (ℓ.2.1 - mean ℓ) ∧
    (flow τ ℓ).2.2 - mean (flow τ ℓ) = (1 - 3*τ) * (ℓ.2.2 - mean ℓ) := by
  refine ⟨?_, ?_, ?_⟩ <;> (simp only [mean, total, flow]; ring)

/-- **The receiver's ratchet is an identity, not an estimate**: `W' = (1 − 3τ)² · W`.  The
classical proof has monotonicity; the exact grain has the rate. -/
theorem theReadingObeysItsExactRate (τ : ℚ) (ℓ : Tri) :
    W (flow τ ℓ) = (1 - 3*τ) ^ 2 * W ℓ := by
  simp only [W, mean, total, flow]; ring

/-- The reading is non-negative — a sum of squares. -/
theorem theReadingIsNonnegative (ℓ : Tri) : 0 ≤ W ℓ := by
  unfold W; positivity

/-- **The ratchet holds on the declared aperture** `0 ≤ τ ≤ 2/3`: the reading never increases.
The aperture is declared, not discovered — and its complement is a control below. -/
theorem theRatchetHoldsOnItsAperture {τ : ℚ} (h0 : 0 ≤ τ) (h1 : τ ≤ 2/3) (ℓ : Tri) :
    W (flow τ ℓ) ≤ W ℓ := by
  rw [theReadingObeysItsExactRate]
  have hW := theReadingIsNonnegative ℓ
  nlinarith [mul_nonneg (mul_nonneg h0 (by linarith : (0:ℚ) ≤ 2 - 3*τ)) hW]

/-! ## 2. Anti-collapse: extent may not slip below the grain -/

/-- **The minimum does not collapse and the maximum does not blow up**: on the aperture
`0 ≤ τ ≤ 1/2`, every bound below the lengths survives the flow and every bound above survives
it.  This is no-local-collapsing at the exact grain: the flow is forbidden from hiding extent
beneath the receiver. -/
theorem theExtentDoesNotCollapse {τ m M : ℚ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1/2) {ℓ : Tri}
    (hm : m ≤ ℓ.1 ∧ m ≤ ℓ.2.1 ∧ m ≤ ℓ.2.2) (hM : ℓ.1 ≤ M ∧ ℓ.2.1 ≤ M ∧ ℓ.2.2 ≤ M) :
    (m ≤ (flow τ ℓ).1 ∧ m ≤ (flow τ ℓ).2.1 ∧ m ≤ (flow τ ℓ).2.2) ∧
    ((flow τ ℓ).1 ≤ M ∧ (flow τ ℓ).2.1 ≤ M ∧ (flow τ ℓ).2.2 ≤ M) := by
  obtain ⟨hm1, hm2, hm3⟩ := hm
  obtain ⟨hM1, hM2, hM3⟩ := hM
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> (simp only [flow]; nlinarith)

/-! ## 3. The table of fixed shapes has one row, and the round class is closed -/

/-- **The only fixed shape is round.**  For any active aperture, the flow holds a triangle
exactly when its three lengths agree — the κ-solution table at this grain, with one row,
proved rather than assumed. -/
theorem theOnlyFixedShapeIsRound {τ : ℚ} (hτ : τ ≠ 0) (ℓ : Tri) :
    flow τ ℓ = ℓ ↔ ℓ.1 = ℓ.2.1 ∧ ℓ.2.1 = ℓ.2.2 := by
  constructor
  · intro h
    rw [Prod.ext_iff, Prod.ext_iff] at h
    obtain ⟨h1, h2, h3⟩ := h
    have e1 : τ * (ℓ.2.1 + ℓ.2.2 - 2 * ℓ.1) = 0 := by
      simp only [flow] at h1; linear_combination h1
    have e2 : τ * (ℓ.1 + ℓ.2.2 - 2 * ℓ.2.1) = 0 := by
      simp only [flow] at h2; linear_combination h2
    have d1 := (mul_eq_zero.mp e1).resolve_left hτ
    have d2 := (mul_eq_zero.mp e2).resolve_left hτ
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    rw [Prod.ext_iff, Prod.ext_iff]
    refine ⟨?_, ?_, ?_⟩ <;> (simp only [flow]; rw [h1, h2]; ring)

/-- **The round class is closed and its reading is zero** — extinction: the distinguished class
is held by the flow and the receiver has nothing left to read. -/
theorem theRoundClassIsClosed (τ r : ℚ) :
    flow τ (r, r, r) = (r, r, r) ∧ W (r, r, r) = 0 := by
  constructor
  · rw [Prod.ext_iff, Prod.ext_iff]
    refine ⟨?_, ?_, ?_⟩ <;> (simp only [flow]; ring)
  · simp only [W, mean, total]; ring

/-! ## 4. The retention contract: the flow deposits, and the backward flow is exact -/

/-- The backward flow: reconstruct the predecessor from the successor, away from the collapse
aperture. -/
def unflow (τ : ℚ) (ℓ : Tri) : Tri :=
  (mean ℓ + (ℓ.1 - mean ℓ) / (1 - 3*τ),
   mean ℓ + (ℓ.2.1 - mean ℓ) / (1 - 3*τ),
   mean ℓ + (ℓ.2.2 - mean ℓ) / (1 - 3*τ))

/-- **Backward heat is well-posed at the exact grain**: away from `τ = 1/3` the flow is
invertible, exactly, with the inverse exhibited.  The classical ill-posedness of backward heat is
not a law of diffusion; it is the signature of a quotient taken without its fiber. -/
theorem theFlowIsInvertibleWithTestimony {τ : ℚ} (hτ : 1 - 3*τ ≠ 0) (ℓ : Tri) :
    unflow τ (flow τ ℓ) = ℓ := by
  obtain ⟨d1, d2, d3⟩ := theDeviationContractsAtTheWindingRate τ ℓ
  have hm : mean (flow τ ℓ) = mean ℓ := by
    simp only [mean, theFlowConservesTheTotal]
  rw [Prod.ext_iff, Prod.ext_iff]
  refine ⟨?_, ?_, ?_⟩
  · show mean (flow τ ℓ) + ((flow τ ℓ).1 - mean (flow τ ℓ)) / (1 - 3*τ) = ℓ.1
    rw [d1, mul_div_cancel_left₀ _ hτ, hm]; ring
  · show mean (flow τ ℓ) + ((flow τ ℓ).2.1 - mean (flow τ ℓ)) / (1 - 3*τ) = ℓ.2.1
    rw [d2, mul_div_cancel_left₀ _ hτ, hm]; ring
  · show mean (flow τ ℓ) + ((flow τ ℓ).2.2 - mean (flow τ ℓ)) / (1 - 3*τ) = ℓ.2.2
    rw [d3, mul_div_cancel_left₀ _ hτ, hm]; ring

/-- **The condensation reconstructs**: round part plus deviation is the metric, exactly — the
quotient onto the round representative carries its fiber, so nothing is deposited unexhibited. -/
theorem theCondensationReconstructs (ℓ : Tri) :
    (mean ℓ + (ℓ.1 - mean ℓ), mean ℓ + (ℓ.2.1 - mean ℓ), mean ℓ + (ℓ.2.2 - mean ℓ)) = ℓ := by
  rw [Prod.ext_iff, Prod.ext_iff]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-! ## 5. The two controls: the deletion localized, and the ratchet broken -/

/-- **The classical deletion sits at exactly one aperture value.**  At `τ = 1/3` the flow
collapses every triangle to its round representative in a single step — the unexhibited quotient
of classical smoothing, localized — and it is many-to-one by witness: two different terrains land
on one round triangle. -/
theorem theCollapseApertureDeletes :
    (∀ ℓ : Tri, flow (1/3) ℓ = (mean ℓ, mean ℓ, mean ℓ)) ∧
    flow (1/3) ((0 : ℚ), 1, 2) = flow (1/3) ((1 : ℚ), 1, 1) := by
  constructor
  · intro ℓ
    rw [Prod.ext_iff, Prod.ext_iff]
    refine ⟨?_, ?_, ?_⟩ <;> (simp only [flow, mean, total]; ring)
  · rw [Prod.ext_iff, Prod.ext_iff]
    refine ⟨?_, ?_, ?_⟩ <;> (simp only [flow]; norm_num)

/-- **The ratchet can fail, with the rate exhibited**: past the aperture, at `τ = 1`, the
reading quadruples — `(1 − 3)² = 4` — and on the witness `(0, 1, 2)` it moves `2 → 8`.  The
monotonicity belongs to the aperture, not to the structure. -/
theorem theRatchetFailsPastItsAperture :
    (∀ ℓ : Tri, W (flow 1 ℓ) = 4 * W ℓ) ∧ W ((0 : ℚ), 1, 2) = 2 ∧ W (flow 1 ((0 : ℚ), 1, 2)) = 8 := by
  refine ⟨fun ℓ => ?_, ?_, ?_⟩
  · rw [theReadingObeysItsExactRate]; ring
  · simp only [W, mean, total]; norm_num
  · rw [theReadingObeysItsExactRate]; simp only [W, mean, total]; norm_num

/-! ## 6. The square: the windings separate, and the spectrum is the winding table -/

/-- A square terrain: four lengths on a combinatorial circle. -/
abbrev Quad : Type := ℚ × ℚ × ℚ × ℚ

/-- One step of the flow on the square. -/
def flow4 (τ : ℚ) (ℓ : Quad) : Quad :=
  ((1 - 2*τ) * ℓ.1 + τ * (ℓ.2.1 + ℓ.2.2.2),
   (1 - 2*τ) * ℓ.2.1 + τ * (ℓ.1 + ℓ.2.2.1),
   (1 - 2*τ) * ℓ.2.2.1 + τ * (ℓ.2.1 + ℓ.2.2.2),
   (1 - 2*τ) * ℓ.2.2.2 + τ * (ℓ.2.2.1 + ℓ.1))

/-- **The windings contract at their own rates** — the flow's spectrum is the winding table
`1 − 2τ + 2τ·cos(2πk/4)`.  The half-turn component (`k = 2`, `cos = −1`) contracts at `1 − 4τ`;
the two quarter-turn components (`k = 1, 3`, `cos = 0`) contract at `1 − 2τ`.  The
fastest-dying mode is the finite shadow of the singularity model selecting itself: which shape
the flow approaches is decided by which winding survives longest. -/
theorem theWindingsSeparateOnTheSquare (τ : ℚ) (ℓ : Quad) :
    ((flow4 τ ℓ).1 - (flow4 τ ℓ).2.1 + (flow4 τ ℓ).2.2.1 - (flow4 τ ℓ).2.2.2
        = (1 - 4*τ) * (ℓ.1 - ℓ.2.1 + ℓ.2.2.1 - ℓ.2.2.2)) ∧
    ((flow4 τ ℓ).1 - (flow4 τ ℓ).2.2.1 = (1 - 2*τ) * (ℓ.1 - ℓ.2.2.1)) ∧
    ((flow4 τ ℓ).2.1 - (flow4 τ ℓ).2.2.2 = (1 - 2*τ) * (ℓ.2.1 - ℓ.2.2.2)) := by
  refine ⟨?_, ?_, ?_⟩ <;> (simp only [flow4]; ring)

/-! ## 7. What remains open, named

The schema clause not enacted here is **surgery as a topology-changing cut**: a triangle has no
neck, so the condensation above carries the fiber without ever cutting.  The honest next grain is
a terrain that can pinch — two cycles joined at a neck edge, cut when the neck's length crosses
the declared scale, with the two resulting cycles and the ledger retained.  That construction and
the `n`-cycle spectrum through `2cos(2πk/n)` (irrational for general `n`, hence living on the
algebraic carriers `winding_inertia` already isolates exactly) are the named continuations; the
record carries them with falsifiers. -/

end Soma.Holonics.Millennium.Ricci

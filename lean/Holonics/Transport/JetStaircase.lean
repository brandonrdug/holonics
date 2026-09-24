import Holonics.Foundation.HigherDifferenceTransport
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# The jet staircase: the finite jet ladder, and the passage between difference orders

[definition] This owner states the law the Rust module
`crates/holonic-engine/src/jet_staircase.rs` implements. It is item **T8** of
`docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`. Four things are stated
here, in this order.

1. **Jet restriction is a projection, and its fibre is exactly what it forgets.** `truncate r` is
   the passage `J^s → J^r`: `truncate_idem` is idempotence, `truncate_comp` is the ladder
   `J^s → J^r` factoring through every intermediate rung, and `truncate_eq_iff` says two
   coefficient families have the same order-`r` jet **exactly when** they agree at every index up
   to `r` — so the fibre of one restriction step is the one coefficient it drops
   (`truncate_fibre_is_the_top_coefficient`).

2. **Difference data and jet data are one exact change of basis.** The chart is the Newton/Mahler
   one: the basis is `binom k n = C(n, k)` and `Δ` is the forward difference.
   `delta_binom_succ` is Pascal's rule read as `Δ C(·, k+1) = C(·, k)`, so the basis is a chain
   under `Δ` and `delta_ofCoefficients` shifts a jet's coefficients down by one. The change of
   basis is `coefficient_eq_iteratedDelta_at_zero`: the `j`-th Newton coefficient **is** the
   `j`-th iterated difference at the base. It is exact over `ℚ` and needs no factorial inverted.

3. **`Δ^{r+1}` annihilates a jet of order `r`.** `iteratedDelta_ofCoefficients_eq_zero`, by
   induction down the ladder. Its two instances are `square_secondDifference` and
   `square_thirdDifference`: the quadratic coordinate `n ↦ n²` has the constant second difference
   `2` and the vanishing third. That is the staircase the
   [August 24 record](../../../../research/records/2026-08-24_THE_HOLONIC_INTERACTION_IS_A_COVARIANT_STORAGE_FLUX_COMPLEX_AND_THE_CUSP_RAISES_DIFFERENCE_ORDER.md)
   reads on the induced flux face, where `Millennium/HolonicInteractionExterior.lean` proves
   `cuspFluxOrbit_secondDifference = 2 e₂₃` and `cuspFluxOrbit_thirdDifference = 0` for the orbit
   itself. This owner does not restate the cusp; it states the difference law that orbit satisfies.

4. **Reconstruction from `(Δ^k, boundary jet)` is exact.** `integrate` is one repeated summation
   with a constant of integration, `integrate_delta` inverts `Δ` from the boundary value, and
   `rebuild_iteratedDelta` composes `k` of them: the `k`-th difference column together with the
   `k` boundary differences returns the source exactly. That is the encoding the Rust owner
   measures the cost of.

[definition] `Δ` here **is** `Foundation/HigherDifferenceTransport.lean`'s own `difference`, at the
chronological shift on `ℕ`; `delta_eq_difference` is that identity and holds by `rfl`. This owner
founds no second difference operator.

Truth status: `[proved-derived] [formal-checked]` for every theorem below.
-/

namespace Holonics.Transport.JetStaircase

open Finset

/-! ## 1. The ladder: restriction is a projection with the stated fibre -/

/-- Forget every coefficient above order `r`. This is the jet ladder's one step, iterated. -/
def truncate (r : ℕ) (c : ℕ → ℚ) : ℕ → ℚ := fun i => if i ≤ r then c i else 0

/-- Restriction is idempotent: a jet of order `r` restricted to order `r` is itself. -/
theorem truncate_idem (r : ℕ) (c : ℕ → ℚ) : truncate r (truncate r c) = truncate r c := by
  funext i
  by_cases h : i ≤ r <;> simp [truncate, h]

/-- The ladder: `J^s → J^r` factors through every rung between them. -/
theorem truncate_comp {r s : ℕ} (h : r ≤ s) (c : ℕ → ℚ) :
    truncate r (truncate s c) = truncate r c := by
  funext i
  by_cases hi : i ≤ r
  · have : i ≤ s := le_trans hi h
    simp [truncate, hi, this]
  · simp [truncate, hi]

/-- **What a jet of order `r` retains**: two coefficient families have the same order-`r` jet
exactly when they agree at every index up to `r`. Everything above is forgotten. -/
theorem truncate_eq_iff (r : ℕ) (c d : ℕ → ℚ) :
    truncate r c = truncate r d ↔ ∀ i, i ≤ r → c i = d i := by
  constructor
  · intro h i hi
    have := congrFun h i
    simpa [truncate, hi] using this
  · intro h
    funext i
    by_cases hi : i ≤ r
    · simp [truncate, hi, h i hi]
    · simp [truncate, hi]

/-- **The fibre of one restriction step is the one coefficient it drops.** Two jets of order
`r + 1` with the same order-`r` restriction and the same top coefficient are equal as jets. -/
theorem truncate_fibre_is_the_top_coefficient (r : ℕ) (c d : ℕ → ℚ)
    (hlow : truncate r c = truncate r d) (htop : c (r + 1) = d (r + 1)) :
    truncate (r + 1) c = truncate (r + 1) d := by
  rw [truncate_eq_iff]
  intro i hi
  rcases Nat.lt_or_ge i (r + 1) with h | h
  · exact (truncate_eq_iff r c d).mp hlow i (Nat.lt_succ_iff.mp h)
  · have : i = r + 1 := le_antisymm hi h
    simpa [this] using htop

/-- A restriction step really can forget: two families differing only above `r` are one jet. -/
theorem truncate_forgets_above (r : ℕ) (c : ℕ → ℚ) (v : ℚ) :
    truncate r (fun i => if i = r + 1 then v else c i) = truncate r c := by
  funext i
  by_cases hi : i ≤ r
  · have : i ≠ r + 1 := by omega
    simp [truncate, hi, this]
  · simp [truncate, hi]

/-! ## 2. The difference operator, composed from the existing owner -/

/-- The chronological shift on `ℕ`, as a one-generator transport. -/
def step : Unit → ℕ → ℕ := fun _ n => n + 1

/-- The forward difference on sequences. -/
def Delta (f : ℕ → ℚ) : ℕ → ℚ := fun n => f (n + 1) - f n

/-- **This owner's difference is the existing owner's.** `Delta` is
`Foundation/HigherDifferenceTransport.lean`'s `difference` at the chronological shift, and the
identity holds definitionally: no second difference operator is founded here. -/
theorem delta_eq_difference (f : ℕ → ℚ) :
    Delta f = Holonics.HigherDifferenceTransport.difference step () f := rfl

/-- `Δ` is additive on a finite sum of faces. -/
theorem delta_sum (s : Finset ℕ) (F : ℕ → ℕ → ℚ) :
    Delta (fun n => ∑ k ∈ s, F k n) = fun n => ∑ k ∈ s, Delta (F k) n := by
  funext n
  simp only [Delta]
  rw [← Finset.sum_sub_distrib]

/-! ## 3. The Newton chart: the basis, and the exact change of basis -/

/-- The Newton/Mahler basis: `binom k n = C(n, k)`. -/
def binom (k : ℕ) : ℕ → ℚ := fun n => (n.choose k : ℚ)

/-- Pascal's rule, read as the basis being a chain under `Δ`. -/
theorem delta_binom_succ (k : ℕ) : Delta (binom (k + 1)) = binom k := by
  funext n
  simp only [Delta, binom, Nat.choose_succ_succ]
  push_cast
  ring

/-- The constant basis vector is annihilated. -/
theorem delta_binom_zero : Delta (binom 0) = fun _ => (0 : ℚ) := by
  funext n
  simp [Delta, binom]

/-- The basis vector at the base: `C(0, k)` is `1` at `k = 0` and `0` above. -/
theorem binom_at_zero (k : ℕ) : binom k 0 = if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp [binom]
  | succ k => simp [binom, Nat.choose_eq_zero_of_lt]

/-- A finite jet of order `r` in the Newton chart: `Σ_{k ≤ r} a k · C(·, k)`. -/
def ofCoefficients (r : ℕ) (a : ℕ → ℚ) : ℕ → ℚ :=
  fun n => ∑ k ∈ range (r + 1), a k * binom k n

/-- **One step down the staircase**: differencing a jet of order `r + 1` shifts its coefficients
down by one and lands on a jet of order `r`. -/
theorem delta_ofCoefficients (r : ℕ) (a : ℕ → ℚ) :
    Delta (ofCoefficients (r + 1) a) = ofCoefficients r (fun k => a (k + 1)) := by
  funext n
  simp only [Delta, ofCoefficients, ← Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ']
  have hzero : a 0 * binom 0 (n + 1) - a 0 * binom 0 n = 0 := by
    simp [binom]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl ?_
  intro k _
  have := congrFun (delta_binom_succ k) n
  simp only [Delta] at this
  rw [← mul_sub, this]

/-- **The change of basis, exactly**: the `j`-th Newton coefficient of a jet of order `r` is the
`j`-th iterated difference of that jet at the base. -/
theorem coefficient_eq_iteratedDelta_at_zero :
    ∀ (r : ℕ) (a : ℕ → ℚ) (j : ℕ), j ≤ r → (Delta^[j] (ofCoefficients r a)) 0 = a j := by
  intro r
  induction r with
  | zero =>
      intro a j hj
      have hj0 : j = 0 := Nat.le_zero.mp hj
      subst hj0
      simp [ofCoefficients, binom]
  | succ r ih =>
      intro a j hj
      cases j with
      | zero =>
          simp only [Function.iterate_zero, id_eq, ofCoefficients]
          rw [Finset.sum_range_succ']
          have : ∀ k ∈ range (r + 1), a (k + 1) * binom (k + 1) 0 = 0 := by
            intro k _
            simp [binom_at_zero]
          rw [Finset.sum_congr rfl this, Finset.sum_const_zero, zero_add]
          simp [binom]
      | succ j =>
          have hj' : j ≤ r := Nat.succ_le_succ_iff.mp hj
          have hstep : Delta^[j + 1] (ofCoefficients (r + 1) a)
              = Delta^[j] (ofCoefficients r (fun k => a (k + 1))) := by
            rw [Function.iterate_succ_apply, delta_ofCoefficients]
          rw [hstep]
          exact ih (fun k => a (k + 1)) j hj'

/-- **`Δ^{r+1}` annihilates a jet of order `r`.** The staircase has exactly `r + 1` steps. -/
theorem iteratedDelta_ofCoefficients_eq_zero :
    ∀ (r : ℕ) (a : ℕ → ℚ), Delta^[r + 1] (ofCoefficients r a) = fun _ => (0 : ℚ) := by
  intro r
  induction r with
  | zero =>
      intro a
      funext n
      simp [Delta, ofCoefficients, binom]
  | succ r ih =>
      intro a
      rw [Function.iterate_succ_apply, delta_ofCoefficients]
      exact ih (fun k => a (k + 1))

/-! ### The cusp's difference law on the induced face -/

/-- The quadratic coordinate's second difference is the constant `2` — the exact staircase the
induced cusp flux orbit carries on `e₂₃`. -/
theorem square_secondDifference (n : ℕ) :
    Delta^[2] (fun m : ℕ => ((m : ℚ)) ^ 2) n = 2 := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq, Delta]
  push_cast
  ring

/-- And its third difference vanishes: the staircase stops. -/
theorem square_thirdDifference (n : ℕ) :
    Delta^[3] (fun m : ℕ => ((m : ℚ)) ^ 2) n = 0 := by
  simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq, Delta]
  push_cast
  ring

/-! ## 4. Reconstruction from the difference column and the boundary jet -/

/-- One repeated summation, with its constant of integration. -/
def integrate (boundary : ℚ) (g : ℕ → ℚ) : ℕ → ℚ
  | 0 => boundary
  | n + 1 => integrate boundary g n + g n

/-- Differencing undoes the summation, whatever the boundary value. -/
theorem delta_integrate (boundary : ℚ) (g : ℕ → ℚ) : Delta (integrate boundary g) = g := by
  funext n
  simp [Delta, integrate]

/-- **Summation from the boundary value undoes differencing**: a sequence is its own boundary
value integrated against its own difference column. -/
theorem integrate_delta (f : ℕ → ℚ) : integrate (f 0) (Delta f) = f := by
  funext n
  induction n with
  | zero => simp [integrate]
  | succ n ih => simp [integrate, ih, Delta]

/-- `k` levels of repeated integration, innermost first, against the declared boundary
differences. -/
def rebuild : ℕ → (ℕ → ℚ) → (ℕ → ℚ) → (ℕ → ℚ)
  | 0, _, g => g
  | k + 1, b, g => rebuild k b (integrate (b k) g)

/-- **Exact reconstruction from `(Δ^k f, the k boundary differences)`.** This is the encoding the
Rust owner stores sparsely and measures the cost of; nothing is lost by it. -/
theorem rebuild_iteratedDelta :
    ∀ (k : ℕ) (f : ℕ → ℚ),
      rebuild k (fun i => (Delta^[i] f) 0) (Delta^[k] f) = f := by
  intro k
  induction k with
  | zero => intro f; simp [rebuild]
  | succ k ih =>
      intro f
      have hstep : Delta^[k + 1] f = Delta (Delta^[k] f) := by
        rw [Function.iterate_succ_apply']
      rw [rebuild, hstep, integrate_delta]
      exact ih f

section Audit

#print axioms truncate_idem
#print axioms truncate_comp
#print axioms truncate_eq_iff
#print axioms truncate_fibre_is_the_top_coefficient
#print axioms truncate_forgets_above
#print axioms delta_eq_difference
#print axioms delta_sum
#print axioms delta_binom_succ
#print axioms delta_binom_zero
#print axioms binom_at_zero
#print axioms delta_ofCoefficients
#print axioms coefficient_eq_iteratedDelta_at_zero
#print axioms iteratedDelta_ofCoefficients_eq_zero
#print axioms square_secondDifference
#print axioms square_thirdDifference
#print axioms delta_integrate
#print axioms integrate_delta
#print axioms rebuild_iteratedDelta

end Audit

end Holonics.Transport.JetStaircase

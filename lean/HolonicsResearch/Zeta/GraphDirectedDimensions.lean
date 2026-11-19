import Holonics.Foundation.FractalString

/-!
# Graph-directed complex dimensions lie among the zeros of the transfer determinant

[proved-standard; formal-checked]

Sources. Issue #410, the box "graph-directed complex dimensions lie among the zeros of
`det(1 − r^s M)`, with convergence and continuation, beyond
`FractalString.transferDet_mul_graphDirected_zeta`". `Foundation/FractalString` proves the
identity of formal power series `det(1 − T·M) · Σ_n a_n Tⁿ = 1_Sᵀ adj(1 − T·M) γ`, with
`a_n = Σ_(i∈S) Σ_j Σ_(w : ReturnWord M n i j) gap_j^s` and `γ_j = gap_j^s`
(`transferDet_mul_graphDirected_zeta`), and holds as owed the sentence "where the series
converges at `T = r^s` it is that polynomial over `det(1 − r^s·M)`, so the complex dimensions of
the graph-directed lattice string, the poles of its continuation, lie among the zeros of the
transfer determinant". The return-map laws are owned by `Aeon/Production/Zeta` (`ReturnWord`,
`card_returnWord`, `sum_returnWord`, `eval_charpolyRev`, `adjugate_transfer`). Atlas rows:
`fractal.graph-directed-words` (`docs/atlas/geometry.tsv`), whose limits column held the analytic
statement for a general gap vector and the continuation as not in Lean; `navigator.zeta` and
`aeon.zeta-perron-growth` (`docs/atlas/objects.tsv`) for the plain word count at real `T`
(`Aeon/Production/GrowthRate`). Lapidus–van Frankenhuijsen, *Fractal Geometry, Complex
Dimensions and Zeta Functions*, 2nd ed., Springer 2013, Ch. 2–3, for the self-similar and
graph-directed lattice strings.

Throughout `M : Matrix σ σ ℕ` is a return map (`M i k` parallel restrictions from `i` to `k`),
`S` a start set, `r` the ratio and `gap j` the first gap at the end state `j`; the word of depth
`n` from `i ∈ S` to `j` addresses a hole of length `gap_j·rⁿ` (`depthFace`). The graph-directed
zeta is `ζ(s) = Σ_n Σ_(i∈S) Σ_j Σ_w (gap_j·rⁿ)^s` (`graphDirectedZeta`), its two polynomial faces
in the scale chart are `D(s) = det(1 − r^s·M)` (`scaleDet`) and `N(s) = 1_Sᵀ adj(1 − r^s·M) γ(s)`
(`scaleNumerator`). The growth bound is the `l∞` one: any `C : ℕ` with every row sum
`Σ_j M i j ≤ C`, so that `C` bounds the `l∞` operator norm of `M` and `(Mⁿ)ᵢⱼ ≤ Cⁿ`.

What is proved.

1. **The two faces are the formal identity's polynomials read at `T = r^s`.** `D(s)` is
   `Matrix.charpolyRev` at `T = r^s` (`scaleDet_eq_eval`), and `N(s)` is the polynomial
   `1_Sᵀ adj(1 − T·M) γ` of `transferDet_mul_graphDirected_zeta` at `T = r^s`
   (`scaleNumerator_eq_eval`, from `adjugate_eval`: the adjugate commutes with reading `T`).
2. **Convergence.** For `0 ≤ r`, `gap ≥ 0` and `‖r^s‖·C < 1`, the depth faces are summable
   (`summable_depthFace`); each is the entry series `1_Sᵀ (r^s M)ⁿ γ` (`depthFace_eq`).
3. **The closed form.** On that region `D(s) ≠ 0` (`scaleDet_ne_zero`) and
   `ζ(s) = N(s)/D(s)` (`hasSum_depthFace`, `graphDirectedZeta_eq_div`): the resolvent
   `Σ_n (r^s M)ⁿ` converges in the `l∞` operator norm to an inverse of `1 − r^s M`
   (`resolvent_entries`), whose entries are `adj(1 − r^s M)ᵢⱼ / det(1 − r^s M)`.
4. **Continuation, and where the poles can be.** For `r > 0` and `gap > 0`, `D` and `N` are
   entire (`differentiable_scaleDet`, `differentiable_scaleNumerator`); `N/D` is differentiable
   wherever `D ≠ 0` (`differentiableAt_continuation`), agrees with `ζ` on the convergence region
   (`graphDirectedZeta_eqOn`), which is open (`isOpen_convergence`), so `ζ` is differentiable
   there (`differentiableOn_graphDirectedZeta`). Every point at which the continuation `N/D` fails
   to be differentiable is a zero of `D` (`scaleDet_eq_zero_of_not_differentiableAt`): the
   complex dimensions lie among the zeros of `det(1 − r^s M)`.
5. **Instances.** The one-state map `[N]` has `D(s) = 1 − N r^s` and `N(s) = g^s`
   (`oneState_scaleDet`, `oneState_scaleNumerator`), so its graph-directed zeta is
   `g^s / (1 − N r^s)` and equals the equal-ratio self-similar zeta of `FractalString`
   (`oneState_graphDirectedZeta`). The Cantor string is `[2]` at `r = g = ⅓`:
   `D(s) = 1 − 2·3^(−s)` (`cantor_scaleDet`), its graph-directed zeta is the Cantor string's zeta
   for `Re s > log 2/log 3` (`cantor_graphDirectedZeta`), and the points where the continuation
   fails to be differentiable lie among `log 2/log 3 + 2πik/log 3`
   (`cantor_dimensions_of_not_differentiableAt`). A two-state map, the golden-mean shift
   `[[1,1],[1,0]]`, has `D(s) = 1 − r^s − r^(2s)` (`goldenShift_scaleDet`).
6. [counterexample; formal-checked] **A zero of `D` need not be a pole**
   (`zero_of_scaleDet_not_pole`): with no start state the numerator vanishes, `N/D ≡ 0` is
   entire, and `D` still vanishes at `s = 1` for `[2]` and `r = ½`.

What is not claimed. Uniqueness of the continuation (the identity theorem), the order of a pole,
and that every zero of `D` is a pole: `N` can cancel a factor of `D`. Besides the empty start set,
a state that no start state reaches cancels: for `M = diag(2, 3)` and `S = {0}`,
`D = (1 − 2T)(1 − 3T)` and `N = (1 − 3T)·γ_0`, so the zeros of `1 − 3 r^s` are removable. Lean's
quotient reads `0` at such a point, so it is discontinuous there although the continuation
`γ_0/(1 − 2 r^s)` is analytic; item 4 states only that a point where the quotient fails to be
differentiable is a zero of `D`. The convergence region is the row-sum disc `‖r^s‖·C < 1`, not
the sharp disc `‖r^s‖·ρ(M) < 1` at the spectral radius: for the golden-mean shift the row sums
give `C = 2` where `ρ = φ`. The region's place does not limit the continuation, which `N/D` gives
off the zeros of `D` in every case. Outside the row-sum disc the scalar series can still converge
(the cancellation above makes it converge for `|r^s| < ½`, past the row-sum radius `⅓`), and its
sum there is not identified with `N/D` here: that needs the identity theorem, and it fails at a
zero of `D` inside its disc (at `r^s = ⅓` the series sums to `3·γ_0` while `D = 0`). Nonlattice
graph-directed strings (several ratios, no single scale variable `T = r^s`) are not treated.

Computational object: the helical pair interaction, read through a navigator's words as the epochs
of its return map `M` in the scale chart `T = r^s`. Of the winding guide's six general objects it
touches the tube (the resolvent `Σ_n (r^s M)ⁿ = (1 − r^s M)⁻¹`, the transfer summed along the
clocked span of epochs, is what converges), faces and placement (the transfer determinant, the
face `Transport/NavigatorTraceFaces` conserves, read at `T = r^s`, with the adjugate face `N`),
the helix (in the scale chart `r^s = e^(−s·log(1/r))` the imaginary part of `s` turns with period
`2π/log(1/r)`, the Cantor string's rotation of period `2π/log 3`) and the tower thread in its
continuing reading (the germ `ζ` continues to `N/D` off the zeros of `D`). The pair and cell
holonomy stay attached and are not used here.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Zeta.GraphDirectedDimensions

open Finset Filter Topology
open scoped Real
open Holonics.Aeon.Production.Zeta (ReturnWord sum_returnWord eval_charpolyRev
  eval_charpolyRev_oneState)
open Holonics.Foundation.FractalString (graphDirected_depth_face selfSimilarLength
  equalRatioZeta_eq_transfer cantorGap cantorStringZeta_eq norm_two_mul_three_cpow_neg_lt_one_iff
  cantor_complex_dimensions)

universe u

variable {σ : Type u} [Fintype σ] [DecidableEq σ]

/-! ## The scale chart: the zeta and its two polynomial faces -/

section Definitions

/-- [definition] **The depth-`n` face** of the graph-directed lattice string with return map `M`,
start set `S`, ratio `r` and gaps `gap`: a word of depth `n` from `i ∈ S` to `j` addresses a hole
of length `gap_j·rⁿ`, and the face sums `(gap_j·rⁿ)^s` over those words. -/
def depthFace (M : Matrix σ σ ℕ) (S : Finset σ) (r : ℝ) (gap : σ → ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ S, ∑ j, ∑ _w : ReturnWord M n i j, ((gap j * r ^ n : ℝ) : ℂ) ^ s

/-- [definition] **The graph-directed zeta** `ζ(s) = Σ_n Σ_(i∈S) Σ_j Σ_w (gap_j·rⁿ)^s`, the depth
faces summed up the tower (Lean's `tsum`, read where the faces are summable). -/
def graphDirectedZeta (M : Matrix σ σ ℕ) (S : Finset σ) (r : ℝ) (gap : σ → ℝ) (s : ℂ) : ℂ :=
  ∑' n, depthFace M S r gap s n

/-- [definition] **The transfer determinant in the scale chart**, `D(s) = det(1 − r^s·M)`. -/
def scaleDet (M : Matrix σ σ ℕ) (r : ℝ) (s : ℂ) : ℂ :=
  (1 - (r : ℂ) ^ s • M.map (Nat.cast : ℕ → ℂ)).det

/-- [definition] **The adjugate face in the scale chart**, `N(s) = 1_Sᵀ adj(1 − r^s·M) γ(s)` with
`γ_j(s) = gap_j^s`. -/
def scaleNumerator (M : Matrix σ σ ℕ) (S : Finset σ) (r : ℝ) (gap : σ → ℝ) (s : ℂ) : ℂ :=
  ∑ i, ∑ j, (if i ∈ S then (1 : ℂ) else 0) *
    (1 - (r : ℂ) ^ s • M.map (Nat.cast : ℕ → ℂ)).adjugate i j * (gap j : ℂ) ^ s

end Definitions

/-! ## The two faces are the formal identity's polynomials at `T = r^s` -/

section Bridge

/-- [proved-derived; formal-checked] `D(s)` is the transfer determinant `det(1 − T·M)`
(`Matrix.charpolyRev`) read at `T = r^s`. -/
theorem scaleDet_eq_eval (M : Matrix σ σ ℕ) (r : ℝ) (s : ℂ) :
    scaleDet M r s = (M.map (Nat.cast : ℕ → ℂ)).charpolyRev.eval ((r : ℂ) ^ s) :=
  (eval_charpolyRev _ _).symm

/-- [proved-derived; formal-checked] The adjugate commutes with reading `T`:
`adj(1 − z·B)ᵢⱼ = adj(1 − T·B)ᵢⱼ` evaluated at `T = z`. -/
theorem adjugate_eval {R : Type*} [CommRing R] (B : Matrix σ σ R) (z : R) (i j : σ) :
    (1 - z • B).adjugate i j =
      ((1 - (Polynomial.X : Polynomial R) • B.map Polynomial.C).adjugate i j).eval z := by
  have hmap : (Polynomial.evalRingHom z).mapMatrix
      (1 - (Polynomial.X : Polynomial R) • B.map Polynomial.C) = 1 - z • B := by
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul, Polynomial.coe_evalRingHom]
    split_ifs <;> simp <;> ring
  have h := congrArg (fun A : Matrix σ σ R => A i j)
    (RingHom.map_adjugate (Polynomial.evalRingHom z)
      (1 - (Polynomial.X : Polynomial R) • B.map Polynomial.C))
  simp only [hmap, RingHom.mapMatrix_apply, Matrix.map_apply, Polynomial.coe_evalRingHom] at h
  exact h.symm

/-- [proved-derived; formal-checked] `N(s)` is the polynomial `1_Sᵀ adj(1 − T·M) γ` of
`FractalString.transferDet_mul_graphDirected_zeta` read at `T = r^s`. -/
theorem scaleNumerator_eq_eval (M : Matrix σ σ ℕ) (S : Finset σ) (r : ℝ) (gap : σ → ℝ) (s : ℂ) :
    scaleNumerator M S r gap s =
      (∑ i, ∑ j, Polynomial.C (if i ∈ S then (1 : ℂ) else 0) *
          (1 - (Polynomial.X : Polynomial ℂ) •
            (M.map (Nat.cast : ℕ → ℂ)).map Polynomial.C).adjugate i j *
          Polynomial.C ((gap j : ℂ) ^ s)).eval ((r : ℂ) ^ s) := by
  simp only [scaleNumerator, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [adjugate_eval (M.map (Nat.cast : ℕ → ℂ)) ((r : ℂ) ^ s)]

end Bridge

/-! ## Convergence and the closed form -/

/-- [proved-derived; formal-checked] **The depth face as an entry series**: the depth-`n` face is
`1_Sᵀ (r^s M)ⁿ γ` (`graphDirected_depth_face`, `sum_returnWord`). -/
theorem depthFace_eq (M : Matrix σ σ ℕ) (S : Finset σ) {r : ℝ} {gap : σ → ℝ} (hr : 0 ≤ r)
    (hgap : ∀ j, 0 ≤ gap j) (s : ℂ) (n : ℕ) :
    depthFace M S r gap s n = ∑ i, ∑ j, (if i ∈ S then (1 : ℂ) else 0) *
      (((r : ℂ) ^ s • M.map (Nat.cast : ℕ → ℂ)) ^ n) i j * (gap j : ℂ) ^ s := by
  rw [depthFace, graphDirected_depth_face M S r gap hr hgap n s, sum_returnWord, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
  ring

section Convergence

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- [proved-standard; formal-checked] The `l∞` operator norm of a return map is at most any bound
`C` of its row sums. -/
theorem norm_map_le (M : Matrix σ σ ℕ) {C : ℕ} (hC : ∀ i, ∑ j, M i j ≤ C) :
    ‖M.map (Nat.cast : ℕ → ℂ)‖ ≤ C := by
  rw [Matrix.linfty_opNorm_def]
  have hsup : (univ.sup fun i => ∑ j, ‖M.map (Nat.cast : ℕ → ℂ) i j‖₊) ≤ (C : NNReal) := by
    refine Finset.sup_le fun i _ => ?_
    have hrow : ∑ j, ‖M.map (Nat.cast : ℕ → ℂ) i j‖₊ = ((∑ j, M i j : ℕ) : NNReal) := by
      push_cast
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [Matrix.map_apply]
    rw [hrow]
    exact_mod_cast hC i
  exact_mod_cast hsup

/-- [proved-standard; formal-checked] **The resolvent of a contraction.** For a complex matrix `A`
with `‖A‖ < 1` in the `l∞` operator norm, `det(1 − A) ≠ 0` and every entry series
`Σ_n (Aⁿ)ᵢⱼ` sums to `adj(1 − A)ᵢⱼ / det(1 − A)`. -/
theorem resolvent_entries {A : Matrix σ σ ℂ} (hA : ‖A‖ < 1) :
    (1 - A).det ≠ 0 ∧
      ∀ i j, HasSum (fun n => (A ^ n) i j) ((1 - A).det⁻¹ * (1 - A).adjugate i j) := by
  have hT : HasSum (fun n => A ^ n) (∑' n, A ^ n) := (summable_geometric_of_norm_lt_one hA).hasSum
  have hinv : (1 - A) * ∑' n, A ^ n = 1 := mul_neg_geom_series A hA
  have hdet : (1 - A).det ≠ 0 := by
    have h := congrArg Matrix.det hinv
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact left_ne_zero_of_mul_eq_one h
  have hadj : (1 - A).adjugate = (1 - A).det • ∑' n, A ^ n := by
    calc (1 - A).adjugate = (1 - A).adjugate * ((1 - A) * ∑' n, A ^ n) := by
          rw [hinv, Matrix.mul_one]
      _ = ((1 - A).adjugate * (1 - A)) * ∑' n, A ^ n := by rw [Matrix.mul_assoc]
      _ = (1 - A).det • ∑' n, A ^ n := by
          rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  refine ⟨hdet, fun i j => ?_⟩
  have hval : (1 - A).det⁻¹ * (1 - A).adjugate i j = (∑' n, A ^ n) i j := by
    rw [hadj, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hdet, one_mul]
  rw [hval]
  exact Pi.hasSum.1 (Pi.hasSum.1 hT i) j

/-- [proved-standard; formal-checked] **The graph-directed zeta converges to `N/D`.** For
`0 ≤ r`, `gap ≥ 0`, every row sum of `M` at most `C` and `‖r^s‖·C < 1`, the depth faces sum to
`1_Sᵀ adj(1 − r^s M) γ / det(1 − r^s M)`. -/
theorem hasSum_depthFace (M : Matrix σ σ ℕ) (S : Finset σ) {r : ℝ} {gap : σ → ℝ} (hr : 0 ≤ r)
    (hgap : ∀ j, 0 ≤ gap j) {C : ℕ} (hC : ∀ i, ∑ j, M i j ≤ C) {s : ℂ}
    (hs : ‖(r : ℂ) ^ s‖ * C < 1) :
    HasSum (depthFace M S r gap s) (scaleNumerator M S r gap s / scaleDet M r s) := by
  have hA : ‖(r : ℂ) ^ s • M.map (Nat.cast : ℕ → ℂ)‖ < 1 := by
    calc ‖(r : ℂ) ^ s • M.map (Nat.cast : ℕ → ℂ)‖
        ≤ ‖(r : ℂ) ^ s‖ * ‖M.map (Nat.cast : ℕ → ℂ)‖ := norm_smul_le _ _
      _ ≤ ‖(r : ℂ) ^ s‖ * C := mul_le_mul_of_nonneg_left (norm_map_le M hC) (norm_nonneg _)
      _ < 1 := hs
  obtain ⟨-, hentry⟩ := resolvent_entries hA
  have hfun : depthFace M S r gap s = fun n => ∑ i, ∑ j, (if i ∈ S then (1 : ℂ) else 0) *
      (((r : ℂ) ^ s • M.map (Nat.cast : ℕ → ℂ)) ^ n) i j * (gap j : ℂ) ^ s :=
    funext (depthFace_eq M S hr hgap s)
  rw [hfun]
  have hsum := hasSum_sum fun i (_ : i ∈ univ) => hasSum_sum fun j (_ : j ∈ univ) =>
    ((hentry i j).mul_left (if i ∈ S then (1 : ℂ) else 0)).mul_right ((gap j : ℂ) ^ s)
  have hval : scaleNumerator M S r gap s / scaleDet M r s = ∑ i, ∑ j,
      (if i ∈ S then (1 : ℂ) else 0) * ((1 - (r : ℂ) ^ s • M.map (Nat.cast : ℕ → ℂ)).det⁻¹ *
        (1 - (r : ℂ) ^ s • M.map (Nat.cast : ℕ → ℂ)).adjugate i j) * (gap j : ℂ) ^ s := by
    rw [scaleNumerator, scaleDet, div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hval]
  exact hsum

/-- [proved-standard; formal-checked] **The transfer determinant does not vanish on the
convergence region**: `‖r^s‖·C < 1` gives `det(1 − r^s M) ≠ 0`. -/
theorem scaleDet_ne_zero (M : Matrix σ σ ℕ) (r : ℝ) {C : ℕ} (hC : ∀ i, ∑ j, M i j ≤ C) {s : ℂ}
    (hs : ‖(r : ℂ) ^ s‖ * C < 1) : scaleDet M r s ≠ 0 := by
  have hA : ‖(r : ℂ) ^ s • M.map (Nat.cast : ℕ → ℂ)‖ < 1 := by
    calc ‖(r : ℂ) ^ s • M.map (Nat.cast : ℕ → ℂ)‖
        ≤ ‖(r : ℂ) ^ s‖ * ‖M.map (Nat.cast : ℕ → ℂ)‖ := norm_smul_le _ _
      _ ≤ ‖(r : ℂ) ^ s‖ * C := mul_le_mul_of_nonneg_left (norm_map_le M hC) (norm_nonneg _)
      _ < 1 := hs
  exact (resolvent_entries hA).1

end Convergence

/-- [proved-standard; formal-checked] **Convergence.** For `0 ≤ r`, `gap ≥ 0`, every row sum of
`M` at most `C` and `‖r^s‖·C < 1`, the graph-directed zeta's depth faces are summable. -/
theorem summable_depthFace (M : Matrix σ σ ℕ) (S : Finset σ) {r : ℝ} {gap : σ → ℝ} (hr : 0 ≤ r)
    (hgap : ∀ j, 0 ≤ gap j) {C : ℕ} (hC : ∀ i, ∑ j, M i j ≤ C) {s : ℂ}
    (hs : ‖(r : ℂ) ^ s‖ * C < 1) : Summable (depthFace M S r gap s) :=
  (hasSum_depthFace M S hr hgap hC hs).summable

/-- [proved-standard; formal-checked] **The closed form.** On the convergence region
`ζ(s) = 1_Sᵀ adj(1 − r^s M) γ(s) / det(1 − r^s M)`. -/
theorem graphDirectedZeta_eq_div (M : Matrix σ σ ℕ) (S : Finset σ) {r : ℝ} {gap : σ → ℝ}
    (hr : 0 ≤ r) (hgap : ∀ j, 0 ≤ gap j) {C : ℕ} (hC : ∀ i, ∑ j, M i j ≤ C) {s : ℂ}
    (hs : ‖(r : ℂ) ^ s‖ * C < 1) :
    graphDirectedZeta M S r gap s = scaleNumerator M S r gap s / scaleDet M r s :=
  (hasSum_depthFace M S hr hgap hC hs).tsum_eq

/-! ## Continuation: where the poles can be -/

section Continuation

/-- [proved-standard; formal-checked] `s ↦ r^s` is entire for `r > 0`. -/
theorem differentiable_ofReal_cpow {r : ℝ} (hr : 0 < r) :
    Differentiable ℂ fun s : ℂ => (r : ℂ) ^ s :=
  differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.2 hr.ne'))

/-- [proved-standard; formal-checked] **`D` is entire** for `r > 0`: a polynomial in `r^s`. -/
theorem differentiable_scaleDet (M : Matrix σ σ ℕ) {r : ℝ} (hr : 0 < r) :
    Differentiable ℂ (scaleDet M r) := by
  have h : scaleDet M r =
      fun s => (M.map (Nat.cast : ℕ → ℂ)).charpolyRev.eval ((r : ℂ) ^ s) :=
    funext (scaleDet_eq_eval M r)
  rw [h]
  exact (Polynomial.differentiable _).comp (differentiable_ofReal_cpow hr)

/-- [proved-standard; formal-checked] **`N` is entire** for `r > 0` and `gap > 0`: a finite sum
of polynomials in `r^s` times the powers `gap_j^s`. -/
theorem differentiable_scaleNumerator (M : Matrix σ σ ℕ) (S : Finset σ) {r : ℝ} {gap : σ → ℝ}
    (hr : 0 < r) (hgap : ∀ j, 0 < gap j) : Differentiable ℂ (scaleNumerator M S r gap) := by
  have h : scaleNumerator M S r gap = fun s => ∑ i, ∑ j, (if i ∈ S then (1 : ℂ) else 0) *
      ((1 - (Polynomial.X : Polynomial ℂ) •
        (M.map (Nat.cast : ℕ → ℂ)).map Polynomial.C).adjugate i j).eval ((r : ℂ) ^ s) *
      (gap j : ℂ) ^ s :=
    funext fun s => by
      simp only [scaleNumerator]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [adjugate_eval (M.map (Nat.cast : ℕ → ℂ)) ((r : ℂ) ^ s)]
  rw [h]
  refine Differentiable.fun_sum fun i _ => Differentiable.fun_sum fun j _ => ?_
  exact ((differentiable_const _).mul
    ((Polynomial.differentiable _).comp (differentiable_ofReal_cpow hr))).mul
    (differentiable_ofReal_cpow (hgap j))

/-- [proved-standard; formal-checked] **The continuation is differentiable off the zeros of `D`**:
`N/D` is differentiable at every `s₀` with `det(1 − r^(s₀) M) ≠ 0`. -/
theorem differentiableAt_continuation (M : Matrix σ σ ℕ) (S : Finset σ) {r : ℝ} {gap : σ → ℝ}
    (hr : 0 < r) (hgap : ∀ j, 0 < gap j) {s₀ : ℂ} (hD : scaleDet M r s₀ ≠ 0) :
    DifferentiableAt ℂ (fun s => scaleNumerator M S r gap s / scaleDet M r s) s₀ :=
  ((differentiable_scaleNumerator M S hr hgap) s₀).div ((differentiable_scaleDet M hr) s₀) hD

/-- [proved-standard; formal-checked] **The complex dimensions lie among the zeros of the transfer
determinant**: a point where the continuation `N/D` fails to be differentiable is a zero of
`det(1 − r^s M)`. -/
theorem scaleDet_eq_zero_of_not_differentiableAt (M : Matrix σ σ ℕ) (S : Finset σ) {r : ℝ}
    {gap : σ → ℝ} (hr : 0 < r) (hgap : ∀ j, 0 < gap j) {s₀ : ℂ}
    (h : ¬ DifferentiableAt ℂ (fun s => scaleNumerator M S r gap s / scaleDet M r s) s₀) :
    scaleDet M r s₀ = 0 := by
  by_contra hD
  exact h (differentiableAt_continuation M S hr hgap hD)

/-- [proved-standard; formal-checked] **The convergence region is open** for `r > 0`. -/
theorem isOpen_convergence {r : ℝ} (hr : 0 < r) (C : ℕ) :
    IsOpen {s : ℂ | ‖(r : ℂ) ^ s‖ * C < 1} :=
  isOpen_lt ((differentiable_ofReal_cpow hr).continuous.norm.mul continuous_const)
    continuous_const

/-- [proved-standard; formal-checked] **Agreement**: on the convergence region the zeta is its
continuation, `ζ = N/D`. -/
theorem graphDirectedZeta_eqOn (M : Matrix σ σ ℕ) (S : Finset σ) {r : ℝ} {gap : σ → ℝ}
    (hr : 0 ≤ r) (hgap : ∀ j, 0 ≤ gap j) {C : ℕ} (hC : ∀ i, ∑ j, M i j ≤ C) :
    Set.EqOn (graphDirectedZeta M S r gap)
      (fun s => scaleNumerator M S r gap s / scaleDet M r s) {s : ℂ | ‖(r : ℂ) ^ s‖ * C < 1} :=
  fun _ hs => graphDirectedZeta_eq_div M S hr hgap hC hs

/-- [proved-standard; formal-checked] **The zeta is differentiable on its convergence region**
for `r > 0` and `gap > 0`: it agrees there, on an open set, with `N/D`, and `D ≠ 0` there. -/
theorem differentiableOn_graphDirectedZeta (M : Matrix σ σ ℕ) (S : Finset σ) {r : ℝ}
    {gap : σ → ℝ} (hr : 0 < r) (hgap : ∀ j, 0 < gap j) {C : ℕ} (hC : ∀ i, ∑ j, M i j ≤ C) :
    DifferentiableOn ℂ (graphDirectedZeta M S r gap) {s : ℂ | ‖(r : ℂ) ^ s‖ * C < 1} := by
  intro s hs
  have hev : graphDirectedZeta M S r gap =ᶠ[𝓝 s]
      fun t => scaleNumerator M S r gap t / scaleDet M r t :=
    Filter.eventually_of_mem ((isOpen_convergence hr C).mem_nhds hs) fun t ht =>
      graphDirectedZeta_eq_div M S hr.le (fun j => (hgap j).le) hC ht
  exact ((differentiableAt_continuation M S hr hgap
    (scaleDet_ne_zero M r hC hs)).congr_of_eventuallyEq hev).differentiableWithinAt

/-- [counterexample; formal-checked] **A zero of `D` need not be a pole.** With no start state
`N ≡ 0`, so `N/D` is differentiable everywhere, while `D` vanishes at `s = 1` for the map `[2]` at
`r = ½`. -/
theorem zero_of_scaleDet_not_pole :
    scaleDet (!![2] : Matrix (Fin 1) (Fin 1) ℕ) (1 / 2) 1 = 0 ∧
      Differentiable ℂ (fun s => scaleNumerator (!![2] : Matrix (Fin 1) (Fin 1) ℕ) ∅ (1 / 2)
        (fun _ => 1) s / scaleDet (!![2] : Matrix (Fin 1) (Fin 1) ℕ) (1 / 2) s) := by
  constructor
  · rw [scaleDet, Complex.cpow_one, Matrix.det_unique]
    simp
  · have h0 : ∀ s, scaleNumerator (!![2] : Matrix (Fin 1) (Fin 1) ℕ) ∅ (1 / 2) (fun _ => 1) s =
        0 := fun s => by simp [scaleNumerator]
    simp only [h0, zero_div]
    exact differentiable_const 0

end Continuation

/-! ## Instances: the one-state map, the Cantor string and the golden-mean shift -/

section Instances

/-- [proved-derived; formal-checked] The one-state map `[N]` read over `ℂ` is `[N]`. -/
theorem oneState_map (N : ℕ) :
    (!![N] : Matrix (Fin 1) (Fin 1) ℕ).map (Nat.cast : ℕ → ℂ) = !![(N : ℂ)] := by
  ext i j
  fin_cases i
  fin_cases j
  rfl

/-- [proved-derived; formal-checked] **The one-state transfer determinant in the scale chart**:
`D(s) = 1 − N r^s` for the map `[N]`. -/
theorem oneState_scaleDet (N : ℕ) (r : ℝ) (s : ℂ) :
    scaleDet (!![N] : Matrix (Fin 1) (Fin 1) ℕ) r s = 1 - N * (r : ℂ) ^ s := by
  rw [scaleDet_eq_eval, oneState_map, eval_charpolyRev_oneState]

/-- [proved-derived; formal-checked] **The one-state adjugate face**: `N(s) = g^s` for the map
`[N]`, its one start state and gap `g` (the adjugate of a `1 × 1` matrix is `1`). -/
theorem oneState_scaleNumerator (N : ℕ) (r g : ℝ) (s : ℂ) :
    scaleNumerator (!![N] : Matrix (Fin 1) (Fin 1) ℕ) univ r (fun _ => g) s = (g : ℂ) ^ s := by
  simp [scaleNumerator, Matrix.adjugate_fin_one]

/-- [proved-derived; formal-checked] **The one-state map reads back the equal-ratio string.** For
`‖r^s‖·N < 1` the graph-directed zeta of `[N]` is `g^s / (1 − N r^s)` and equals the self-similar
zeta of `N` equal ratios `r` (`FractalString.equalRatioZeta_eq_transfer`). -/
theorem oneState_graphDirectedZeta (N : ℕ) {r g : ℝ} (hr : 0 ≤ r) (hg : 0 ≤ g) {s : ℂ}
    (hs : ‖(r : ℂ) ^ s‖ * N < 1) :
    graphDirectedZeta (!![N] : Matrix (Fin 1) (Fin 1) ℕ) univ r (fun _ => g) s =
        (g : ℂ) ^ s / (1 - N * (r : ℂ) ^ s) ∧
      graphDirectedZeta (!![N] : Matrix (Fin 1) (Fin 1) ℕ) univ r (fun _ => g) s =
        ∑' n : ℕ, ∑ w : Fin n → Fin N, (selfSimilarLength (fun _ => r) g w : ℂ) ^ s := by
  have hC : ∀ i, ∑ j, (!![N] : Matrix (Fin 1) (Fin 1) ℕ) i j ≤ N := fun i => by
    fin_cases i
    simp
  have h1 : graphDirectedZeta (!![N] : Matrix (Fin 1) (Fin 1) ℕ) univ r (fun _ => g) s =
      (g : ℂ) ^ s / (1 - N * (r : ℂ) ^ s) := by
    rw [graphDirectedZeta_eq_div _ _ hr (fun _ => hg) hC hs, oneState_scaleNumerator,
      oneState_scaleDet]
  refine ⟨h1, ?_⟩
  have hs' : ‖(N : ℂ) * (r : ℂ) ^ s‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast, mul_comm]
    exact hs
  rw [h1, equalRatioZeta_eq_transfer N r g hr hg hs', eval_charpolyRev_oneState]

/-- [proved-standard; formal-checked] `(⅓)^s = 3^(−s)`. -/
theorem third_cpow (s : ℂ) : ((1 / 3 : ℝ) : ℂ) ^ s = (3 : ℂ) ^ (-s) := by
  have harg : (3 : ℂ).arg ≠ π := by
    rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by push_cast; rfl,
      Complex.arg_ofReal_of_nonneg (by norm_num)]
    exact Real.pi_ne_zero.symm
  rw [Complex.cpow_neg, ← Complex.inv_cpow _ _ harg]
  push_cast
  rw [one_div]

/-- [proved-derived; formal-checked] **The Cantor string's transfer determinant**: the map `[2]`
at `r = ⅓` has `D(s) = 1 − 2·3^(−s)`. -/
theorem cantor_scaleDet (s : ℂ) :
    scaleDet (!![2] : Matrix (Fin 1) (Fin 1) ℕ) (1 / 3) s = 1 - 2 * (3 : ℂ) ^ (-s) := by
  rw [oneState_scaleDet, third_cpow]
  norm_num

/-- [proved-derived; formal-checked] **The Cantor string read back**: for `Re s > log 2/log 3` the
graph-directed zeta of `[2]` at `r = g = ⅓` is the Cantor string's zeta
(`FractalString.cantorStringZeta_eq`), `3^(−s) / (1 − 2·3^(−s))`. -/
theorem cantor_graphDirectedZeta {s : ℂ} (hs : Real.log 2 / Real.log 3 < s.re) :
    graphDirectedZeta (!![2] : Matrix (Fin 1) (Fin 1) ℕ) univ (1 / 3) (fun _ => 1 / 3) s =
      ∑' n : ℕ, ((Holonics.Foundation.FractalPacking.words n).map
        fun w => ((cantorGap w : ℝ) : ℂ) ^ s).sum := by
  have hnorm : ‖((1 / 3 : ℝ) : ℂ) ^ s‖ * ((2 : ℕ) : ℝ) < 1 := by
    have h := norm_two_mul_three_cpow_neg_lt_one_iff.2 hs
    rw [norm_mul, Complex.norm_two] at h
    rw [third_cpow]
    push_cast
    linarith
  rw [(oneState_graphDirectedZeta 2 (by norm_num) (by norm_num) hnorm).1, cantorStringZeta_eq hs,
    third_cpow]
  norm_num

/-- [proved-derived; formal-checked] **The Cantor string's complex dimensions**: a point where the
continuation `N/D` of the graph-directed zeta of `[2]` at `r = g = ⅓` fails to be differentiable
is `log 2/log 3 + 2πik/log 3` for some `k ∈ ℤ` (`FractalString.cantor_complex_dimensions`). -/
theorem cantor_dimensions_of_not_differentiableAt {s₀ : ℂ}
    (h : ¬ DifferentiableAt ℂ (fun s =>
      scaleNumerator (!![2] : Matrix (Fin 1) (Fin 1) ℕ) univ (1 / 3) (fun _ => 1 / 3) s /
        scaleDet (!![2] : Matrix (Fin 1) (Fin 1) ℕ) (1 / 3) s) s₀) :
    ∃ k : ℤ, s₀ = Real.log 2 / Real.log 3 + 2 * π * Complex.I * k / Real.log 3 := by
  have hD := scaleDet_eq_zero_of_not_differentiableAt _ _ (by norm_num) (fun _ => by norm_num) h
  rw [cantor_scaleDet] at hD
  exact (cantor_complex_dimensions s₀).1 hD

/-- [proved-derived; formal-checked] **A two-state instance, the golden-mean shift**: for the
return map `[[1,1],[1,0]]`, `D(s) = 1 − r^s − r^(2s)`. -/
theorem goldenShift_scaleDet (r : ℝ) (s : ℂ) :
    scaleDet (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) r s =
      1 - (r : ℂ) ^ s - ((r : ℂ) ^ s) ^ 2 := by
  rw [scaleDet, Matrix.det_fin_two]
  simp
  ring

end Instances

end Holonics.Zeta.GraphDirectedDimensions

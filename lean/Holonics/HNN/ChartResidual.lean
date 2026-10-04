import Holonics.HNN.ReceivingPrior
import Holonics.HNN.LatticeWord

/-!
# HNN.ChartResidual: the receiving prior's bounds through the executed chart and the certified step

[definition] Rebuild step 4 (#73); #62, the receiving prior's owed items (receipt 5973559786,
item 3): the certified step `η` (the second-order bound was stated at `η = 1`) and the chart's
lattice residual (`SolvedChart` is a certified inverse on `2^(−L_s)ℤ`, not `H⁻¹`). The record is
`research/records/2026-10-02_THE_READINGS_LOCATE_THE_RECEIVING_PRIOR_BY_THE_PREQUENTIAL_CERTIFICATE.md`
§6. The Rust owners are `hnn::constitution::{SolvedChart, NormalLaw::prepare,
Constitution::deposited}`: the chart carries its block `X̂` and its exact certificate
`δ = ‖1 − X̂H‖∞` (`SolvedChart::certificate`), and each deposit moves the map by the certified
step times its unit step. That step is the largest power of two `η` with `ηC ≤ a` and
`η max(osc, 1) ≤ 1` (`holon::deposition::CertifiedStep`), halved with the other loci until the joint
certificate holds, so `0 ≤ η ≤ min(a/C, 1/max(osc, 1)) ≤ 1`.

[proved-derived; formal-checked] What is proved.

1. **The pair read through the executed chart** (§1). The executed map reads a pair of readings as
   `⟨X̂ u, z⟩`, the `1/s` reading as `⟨s⁻¹ u, z⟩`. With `H = s I + G`, `G` symmetric,
   `0 ⪯ G ⪯ λ I`, and the chart's certificate `‖1 − X̂H‖∞ ≤ δ < 1`, the exact inverse is within
   `‖X̂‖∞ δ/(1 − δ)` of the chart (`inverse_chart_deviation_left`, the left residual the Rust
   certifies), so the pair departs by at most
   `ρ + ‖X̂‖∞ δ/(1 − δ) · μ · ‖z‖₁`, where `ρ ≥ 0` bounds the exact solve's departure
   (`ρ² ≥ (λ/(s + λ))² |s⁻¹ u|² |z|²`, `ReceivingPrior.departure_pair_sq_le`) and `μ` bounds `u`'s
   entries (`chart_pair_departure_le`, through `matrix_pair_le`). The lattice residual is a
   second term beside the exact solve's, read from the executed chart and its certificate alone.
   A class's departure `E_t c = Σ_u w_u q_u` is then at most `Σ_u |w_u| (ρ_u + β_u)`
   (`chart_class_departure_le`), and the prequential code along the executed map carries it as
   `ReceivingPrior.prequential_code_departure_le`'s remainder (`prequential_code_chart_le`).
2. **The certified step** (§2). Under the prior `s/φ` the unit step scales by `φ`, its alignment
   by `φ`, its curvature by `φ²` and its oscillation by `φ`
   (`ReceivingPrior.cap_and_prior_one_constant`), so the certified step's cap is
   `min(a/(φ C), 1/max(φ osc, 1))`, at most `1`, and at that cap `ψ = φη` lies in `[0, φ]` with
   `ψ = φ` exactly when `η = 1` (`certified_move_scaled`). The executed `η` is a power of two at
   most the cap, so each deposit moves the map by `ψ = φη ≤ φ` times its unit-prior move, which is
   the only bound on `ψ` the code uses. Along the executed move
   `Σ_u ψ_u m_u − E_t`, with `|E_t c| ≤ r_t` and `|m_u t c| ≤ μ_u t`, the prequential code is at
   most the face's less `φ a`, plus `φ² (ln 2) 2^ω Σ_t Var_(p_t)(M_t)`, plus the remainder at
   `r′_t = r_t + Σ_u (φ − ψ_u) μ_u t` (`prequential_code_certified_step_le`): the certified step's
   shortfall from `φ` enters as one more departure, zero at `η = 1`.

[definition; agent-inferred] `μ` bounds the read's entries (`|u_j| ≤ μ`) and `‖z‖₁` is `l1`, the
norms the chart's `‖·‖∞` certificate pairs with. The deposits' unit-prior moves `m_u t c` and their
classwise bounds `μ_u t` are the map's own reads (`M_t = Σ_u m_u t`).

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.ChartResidual

open Matrix
open Holonics.HNN.LatticeWord (rowNorm rowNorm_nonneg row_sum_le_rowNorm rowNorm_mul_le
  rowNorm_add_le l1)
open Holonics.HNN.ReceivingPrior (departure_pair_sq_le prequential_code_departure_le)
open Holonics.HNN.Ratio (codeLength)
open Holonics.HNN.Ratio.Certificate (faceVariance)

/-! ## 1. The pair read through the executed chart -/

section Chart

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- [proved-derived; formal-checked] **A certified chart is near the exact inverse, on the left
residual the chart certifies.** If `AY = 1` and `‖1 − X̂A‖∞ ≤ δ < 1`, then
`‖Y − X̂‖∞ ≤ ‖X̂‖∞ δ/(1 − δ)`: `Y − X̂ = (1 − X̂A) Y`. -/
theorem inverse_chart_deviation_left {A X Y : Matrix n n ℚ} (hY : A * Y = 1) {δ : ℚ}
    (hR : rowNorm (1 - X * A) ≤ δ) (hδ : δ < 1) :
    rowNorm (Y - X) ≤ rowNorm X * δ / (1 - δ) := by
  have hYX : Y - X = (1 - X * A) * Y := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hY, Matrix.mul_one]
  have hdev : rowNorm (Y - X) ≤ δ * rowNorm Y := by
    rw [hYX]
    exact (rowNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hR (rowNorm_nonneg Y))
  have hY' : rowNorm Y ≤ rowNorm X + δ * rowNorm Y := by
    calc rowNorm Y = rowNorm (X + (Y - X)) := by rw [add_sub_cancel]
      _ ≤ rowNorm X + rowNorm (Y - X) := rowNorm_add_le _ _
      _ ≤ rowNorm X + δ * rowNorm Y := add_le_add le_rfl hdev
  have h1 : 0 < 1 - δ := sub_pos.mpr hδ
  rw [le_div_iff₀ h1]
  have hYn := rowNorm_nonneg Y
  have hδ0 : 0 ≤ δ := (rowNorm_nonneg _).trans hR
  nlinarith

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] **A pair read through a matrix** is at most its row norm times
the read's entry bound times the reader's `ℓ1` norm: `|⟨D u, z⟩| ≤ ‖D‖∞ μ ‖z‖₁` for `|u_j| ≤ μ`. -/
theorem matrix_pair_le (D : Matrix n n ℚ) (u z : n → ℚ) {μ : ℚ} (hu : ∀ j, |u j| ≤ μ) :
    |(D *ᵥ u) ⬝ᵥ z| ≤ rowNorm D * μ * l1 z := by
  have hμ : ∀ i, |(D *ᵥ u) i| ≤ rowNorm D * μ := fun i => by
    calc |(D *ᵥ u) i| = |∑ j, D i j * u j| := rfl
      _ ≤ ∑ j, |D i j| * |u j| := (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (by
          simp only [abs_mul]))
      _ ≤ ∑ j, |D i j| * μ :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hu j) (abs_nonneg _)
      _ = (∑ j, |D i j|) * μ := by rw [Finset.sum_mul]
      _ ≤ rowNorm D * μ :=
          mul_le_mul_of_nonneg_right (row_sum_le_rowNorm D i) ((abs_nonneg _).trans (hu i))
  calc |(D *ᵥ u) ⬝ᵥ z| = |∑ i, (D *ᵥ u) i * z i| := rfl
    _ ≤ ∑ i, |(D *ᵥ u) i| * |z i| := (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (by
        simp only [abs_mul]))
    _ ≤ ∑ i, rowNorm D * μ * |z i| :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hμ i) (abs_nonneg _)
    _ = rowNorm D * μ * l1 z := by rw [← Finset.mul_sum]; rfl

/-- [proved-derived; formal-checked] **The pair read through the executed chart.** With
`H = s I + G` (`G` symmetric, `0 ⪯ G ⪯ λ I`, `H` invertible), the chart `X̂` certified by
`‖1 − X̂H‖∞ ≤ δ < 1`, a bound `ρ ≥ 0` of the exact solve's departure
(`(λ/(s + λ))² |s⁻¹ u|² |z|² ≤ ρ²`) and `|u_j| ≤ μ`, the executed pair read departs from the
`1/s` reading by at most `ρ + ‖X̂‖∞ δ/(1 − δ) μ ‖z‖₁`. -/
theorem chart_pair_departure_le (s lam : ℚ) (hs : 0 < s) (hlam : 0 < lam) (G Xh : Matrix n n ℚ)
    (hGt : Gᵀ = G) (h0 : ∀ x, 0 ≤ x ⬝ᵥ (G *ᵥ x)) (h1 : ∀ x, x ⬝ᵥ (G *ᵥ x) ≤ lam * (x ⬝ᵥ x))
    (hH : IsUnit (s • (1 : Matrix n n ℚ) + G).det) {δ : ℚ}
    (hR : rowNorm (1 - Xh * (s • (1 : Matrix n n ℚ) + G)) ≤ δ) (hδ : δ < 1)
    (u z : n → ℚ) {ρ μ : ℚ} (hρ0 : 0 ≤ ρ)
    (hρ : (lam / (s + lam)) ^ 2 * ((s⁻¹ • u) ⬝ᵥ (s⁻¹ • u)) * (z ⬝ᵥ z) ≤ ρ ^ 2)
    (hμ : 0 ≤ μ) (hu : ∀ j, |u j| ≤ μ) :
    |(s⁻¹ • u - Xh *ᵥ u) ⬝ᵥ z| ≤ ρ + rowNorm Xh * δ / (1 - δ) * μ * l1 z := by
  set H := s • (1 : Matrix n n ℚ) + G
  have hY : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv _ hH
  have hsplit : (s⁻¹ • u - Xh *ᵥ u) ⬝ᵥ z =
      (s⁻¹ • u - H⁻¹ *ᵥ u) ⬝ᵥ z + ((H⁻¹ - Xh) *ᵥ u) ⬝ᵥ z := by
    rw [Matrix.sub_mulVec, ← add_dotProduct]
    congr 1
    abel
  have hexact : |(s⁻¹ • u - H⁻¹ *ᵥ u) ⬝ᵥ z| ≤ ρ :=
    abs_le_of_sq_le_sq ((departure_pair_sq_le s lam hs hlam G hGt h0 h1 hH u z).trans hρ) hρ0
  have hdev := inverse_chart_deviation_left hY hR hδ
  have hlat : |((H⁻¹ - Xh) *ᵥ u) ⬝ᵥ z| ≤ rowNorm Xh * δ / (1 - δ) * μ * l1 z := by
    refine (matrix_pair_le _ u z hu).trans ?_
    have hl1 : 0 ≤ l1 z := Finset.sum_nonneg fun i _ => abs_nonneg (z i)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdev hμ) hl1
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hexact hlat)

/-- [proved-derived; formal-checked] **A class's departure through the executed chart.** If
`E = Σ_u w_u q_u` with `|q_u| ≤ ρ_u + β_u` (the exact solve's part and the chart's), then
`|E| ≤ Σ_u |w_u| (ρ_u + β_u)`. -/
theorem chart_class_departure_le {U : Type*} (S : Finset U) (w q ρ β : U → ℚ)
    (hq : ∀ u, |q u| ≤ ρ u + β u) :
    |∑ u ∈ S, w u * q u| ≤ ∑ u ∈ S, |w u| * (ρ u + β u) :=
  (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hq u) (abs_nonneg _))

end Chart

/-- [proved-derived; formal-checked] **The prequential code along the executed map, through the
executed chart.** With the departures read exactly in `ℚ` and bounded classwise there by `r_t`
(from `chart_class_departure_le`), the code along `φ M_t − E_t` is
`ReceivingPrior.prequential_code_departure_le`'s bound at those `r_t`. -/
theorem prequential_code_chart_le {ι T : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Fintype T] (f M p : T → ι → ℝ) (E : T → ι → ℚ)
    (hp : ∀ t c, p t c = (2 : ℝ) ^ f t c / ∑ d, (2 : ℝ) ^ f t d) (target : T → ι) (φ ω : ℝ)
    (r : T → ℚ) (hosc : ∀ t c d, (φ * M t c - E t c) - (φ * M t d - E t d) ≤ ω)
    (hE : ∀ t c, |E t c| ≤ r t) :
    ∑ t, codeLength (fun c => f t c + (φ * M t c - E t c)) (target t) ≤
      ∑ t, codeLength (f t) (target t)
        - φ * ∑ t, ∑ c, ((Pi.single (target t) (1 : ℝ) : ι → ℝ) c - p t c) * M t c
        + φ ^ 2 * (Real.log 2 * (2 : ℝ) ^ ω * ∑ t, faceVariance (p t) (M t))
        + (Real.log 2 * (2 : ℝ) ^ ω * ∑ t, ((r t : ℚ) : ℝ) ^ 2 + 2 * ∑ t, ((r t : ℚ) : ℝ)) :=
  prequential_code_departure_le f M (fun t c => (E t c : ℝ)) p hp target φ ω (fun t => (r t : ℝ))
    hosc (fun t c => by exact_mod_cast hE t c)

/-! ## 2. The certified step -/

section Step

/-- [proved-derived; formal-checked] **The certified move under a scaled prior.** At the prior
`s/φ` (`φ > 0`) the reads along the unit step scale as the alignment `φ a`, the curvature `φ² C`
and the oscillation `φ osc` (`ReceivingPrior.cap_and_prior_one_constant`), so the certified step's
cap is `η = min(a/(φ C), 1/max(φ osc, 1))` and a deposit at the cap moves by `ψ = φ η` times its
unit-prior move. For `a ≥ 0`, `C > 0`: `0 ≤ ψ ≤ φ`, and `ψ = φ` exactly when `η = 1`. The executed
step is the largest power of two at most the cap, halved with the joint certificate
(`holon::deposition::CertifiedStep`), so it too moves by at most `φ`. -/
theorem certified_move_scaled (φ a C o : ℝ) (hφ : 0 < φ) (ha : 0 ≤ a) (hC : 0 < C) :
    let η := min ((φ * a) / (φ ^ 2 * C)) (1 / max (φ * o) 1)
    η = min (a / (φ * C)) (1 / max (φ * o) 1) ∧ 0 ≤ φ * η ∧ φ * η ≤ φ ∧
      (φ * η = φ ↔ η = 1) := by
  intro η
  have he : (φ * a) / (φ ^ 2 * C) = a / (φ * C) := by
    field_simp
  have hη1 : η ≤ 1 := (min_le_right _ _).trans (by
    rw [div_le_one (lt_of_lt_of_le one_pos (le_max_right _ _))]
    exact le_max_right _ _)
  have hη0 : 0 ≤ η := le_min (by positivity)
    (by have := lt_of_lt_of_le one_pos (le_max_right (φ * o) 1); positivity)
  refine ⟨show min ((φ * a) / (φ ^ 2 * C)) (1 / max (φ * o) 1) = _ by rw [he], mul_nonneg hφ.le hη0, ?_, ?_⟩
  · calc φ * η ≤ φ * 1 := mul_le_mul_of_nonneg_left hη1 hφ.le
      _ = φ := mul_one φ
  · constructor
    · intro h
      have := mul_left_cancel₀ hφ.ne' (h.trans (mul_one φ).symm)
      exact this
    · intro h; rw [h, mul_one]

variable {ι T U : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype T] [Fintype U]

/-- [proved-derived; formal-checked] **The prequential code at the certified step.** Each
deposit `u` moves the map by `ψ_u` times its unit-prior move `m_u`, `ψ_u ≤ φ` (the executed step
is a power of two at most `certified_move_scaled`'s cap), and the unit-prior map is
`M_t = Σ_u m_u t`. Along the executed move
`Σ_u ψ_u m_u t − E_t`, with `|E_t c| ≤ r_t` and `|m_u t c| ≤ μ_u t`, the prequential code is at most
the face's less `φ a`, plus `φ² (ln 2) 2^ω Σ_t Var_(p_t)(M_t)`, plus the remainder at
`r′_t = r_t + Σ_u (φ − ψ_u) μ_u t`. At `ψ = φ` (`η = 1`) it is
`ReceivingPrior.prequential_code_departure_le`. -/
theorem prequential_code_certified_step_le (f p : T → ι → ℝ) (m : U → T → ι → ℝ)
    (E : T → ι → ℝ) (hp : ∀ t c, p t c = (2 : ℝ) ^ f t c / ∑ d, (2 : ℝ) ^ f t d)
    (target : T → ι) (φ ω : ℝ) (ψ : U → ℝ) (hψ : ∀ u, ψ u ≤ φ) (r : T → ℝ)
    (μ : U → T → ℝ) (hm : ∀ u t c, |m u t c| ≤ μ u t) (hE : ∀ t c, |E t c| ≤ r t)
    (hosc : ∀ t c d, (∑ u, ψ u * m u t c - E t c) - (∑ u, ψ u * m u t d - E t d) ≤ ω) :
    ∑ t, codeLength (fun c => f t c + (∑ u, ψ u * m u t c - E t c)) (target t) ≤
      ∑ t, codeLength (f t) (target t)
        - φ * ∑ t, ∑ c, ((Pi.single (target t) (1 : ℝ) : ι → ℝ) c - p t c) *
            (∑ u, m u t c)
        + φ ^ 2 * (Real.log 2 * (2 : ℝ) ^ ω * ∑ t, faceVariance (p t) (fun c => ∑ u, m u t c))
        + (Real.log 2 * (2 : ℝ) ^ ω * ∑ t, (r t + ∑ u, (φ - ψ u) * μ u t) ^ 2
            + 2 * ∑ t, (r t + ∑ u, (φ - ψ u) * μ u t)) := by
  set E' : T → ι → ℝ := fun t c => E t c + ∑ u, (φ - ψ u) * m u t c with hE'
  have hmove : ∀ t c, ∑ u, ψ u * m u t c - E t c = φ * (∑ u, m u t c) - E' t c := fun t c => by
    simp only [hE', Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]
    ring
  have hbound : ∀ t c, |E' t c| ≤ r t + ∑ u, (φ - ψ u) * μ u t := fun t c => by
    refine (abs_add_le _ _).trans (add_le_add (hE t c) ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => ?_)
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hψ u))]
    exact mul_le_mul_of_nonneg_left (hm u t c) (sub_nonneg.mpr (hψ u))
  have h := prequential_code_departure_le f (fun t c => ∑ u, m u t c) E' p hp target φ ω
    (fun t => r t + ∑ u, (φ - ψ u) * μ u t)
    (fun t c d => by rw [← hmove, ← hmove]; exact hosc t c d) hbound
  simp only [hmove]
  exact h

end Step

section Audit

#print axioms inverse_chart_deviation_left
#print axioms matrix_pair_le
#print axioms chart_pair_departure_le
#print axioms chart_class_departure_le
#print axioms prequential_code_chart_le
#print axioms certified_move_scaled
#print axioms prequential_code_certified_step_le

end Audit

end Holonics.HNN.ChartResidual

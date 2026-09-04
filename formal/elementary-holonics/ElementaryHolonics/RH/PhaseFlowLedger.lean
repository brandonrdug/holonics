import Mathlib

/-!
# The phase-flow ledger of the zero comb

Under the de Bruijn--Newman deformation `H_t(z) = ∫₀^∞ e^{tu²} Φ(u) cos(zu) du` the zeros of
`H_t` move by the backward-heat zero dynamics (Csordas--Smith--Varga; Rodgers--Tao,
arXiv:1801.05914): each zero is pushed by every other with flux `2/(z_j − z_k)`.  This owner
transports the Navier--Stokes Fourier ledger onto that comb.  On a finite comb of real zeros the
flux is pairwise antisymmetric, so the centre is conserved (Kirchhoff) and the second moment
grows linearly at the configuration-independent flux `2N(N−1)`.  For one conjugate pair above a
real comb the height `y` obeys `ẏ ≤ −1/y`, so `y² + 2t` is nonincreasing: every off-seam pair
collides with the seam in time at most `y₀²/2`.  This is the mechanism of de Bruijn's bound
`Λ ≤ 1/2`.  RH is the claim that the pair population at `t = 0` is empty; the flux annihilates
pairs forward in time and cannot decide that face, which is why the realizer population (the
primes, through the explicit formula) is the missing half.
-/

noncomputable section

namespace Soma.Holonics.RH.PhaseFlowLedger

open Finset Set

/-- The zero-comb flux on a real comb: the velocity of zero `j`.  The diagonal term is `2/0 = 0`
in Lean's convention, so no erasure is needed. -/
def zeroFlux {N : ℕ} (x : Fin N → ℝ) (j : Fin N) : ℝ :=
  ∑ k, 2 / (x j - x k)

/-- **Kirchhoff on the comb**: the total flux vanishes, by pairwise antisymmetry. -/
theorem sum_zeroFlux {N : ℕ} (x : Fin N → ℝ) : ∑ j, zeroFlux x j = 0 := by
  unfold zeroFlux
  have hswap : ∑ j, ∑ k, (2 : ℝ) / (x j - x k) = ∑ j, ∑ k, (2 : ℝ) / (x k - x j) :=
    Finset.sum_comm
  have hneg : ∑ j, ∑ k, (2 : ℝ) / (x k - x j) = -∑ j, ∑ k, (2 : ℝ) / (x j - x k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [← neg_sub, div_neg]
  linarith

/-- **The second-moment flux is configuration-independent**: `Σ_j 2 x_j · flux_j = 2N(N−1)` on
an injective comb. -/
theorem sum_mul_zeroFlux {N : ℕ} (x : Fin N → ℝ) (hx : Function.Injective x) :
    ∑ j, 2 * x j * zeroFlux x j = 2 * (N : ℝ) * ((N : ℝ) - 1) := by
  unfold zeroFlux
  have hexp : ∑ j, 2 * x j * ∑ k, (2 : ℝ) / (x j - x k) =
      ∑ j, ∑ k, 4 * x j / (x j - x k) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hexp]
  set S := ∑ j, ∑ k, 4 * x j / (x j - x k) with hS
  have hswap : S = ∑ j, ∑ k, 4 * x k / (x k - x j) := by
    rw [hS]
    exact Finset.sum_comm
  have hdiag : ∀ j k : Fin N, 4 * x j / (x j - x k) + 4 * x k / (x k - x j) =
      if j = k then 0 else 4 := by
    intro j k
    by_cases hjk : j = k
    · subst hjk
      simp
    · rw [if_neg hjk]
      have hne : x j - x k ≠ 0 := sub_ne_zero.mpr (fun h => hjk (hx h))
      rw [← neg_sub (x j) (x k), div_neg]
      field_simp
      ring
  have h2S : S + S = ∑ j : Fin N, ∑ k : Fin N, (if j = k then (0 : ℝ) else 4) := by
    have h1 : S + S = (∑ j, ∑ k, 4 * x j / (x j - x k)) + ∑ j, ∑ k, 4 * x k / (x k - x j) := by
      rw [← hS, ← hswap]
    rw [h1, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    exact hdiag j k
  have hcount : ∑ j : Fin N, ∑ k : Fin N, (if j = k then (0 : ℝ) else 4) =
      4 * (N : ℝ) * ((N : ℝ) - 1) := by
    have hrow : ∀ j : Fin N, ∑ k : Fin N, (if j = k then (0 : ℝ) else 4) = 4 * ((N : ℝ) - 1) := by
      intro j
      have h1 : ∀ k : Fin N, (if j = k then (0 : ℝ) else 4) = 4 - (if j = k then (4 : ℝ) else 0) := by
        intro k
        split_ifs <;> simp
      rw [Finset.sum_congr rfl (fun k _ => h1 k), Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq, if_pos (Finset.mem_univ j),
        nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hrow j), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  linarith [h2S, hcount]

/-- **Along the flow the centre is conserved and the second moment grows linearly.** -/
theorem hasDerivAt_centre {N : ℕ} (x : ℝ → Fin N → ℝ) (t : ℝ)
    (hx : ∀ j, HasDerivAt (fun τ => x τ j) (zeroFlux (x t) j) t) :
    HasDerivAt (fun τ => ∑ j, x τ j) 0 t := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun j _ => hx j)
  rw [sum_zeroFlux] at h
  have key : (fun τ => ∑ j, x τ j) = ∑ j, fun τ => x τ j := by
    funext τ
    simp [Finset.sum_apply]
  rw [key]
  exact h

theorem hasDerivAt_secondMoment {N : ℕ} (x : ℝ → Fin N → ℝ) (t : ℝ)
    (hx : ∀ j, HasDerivAt (fun τ => x τ j) (zeroFlux (x t) j) t)
    (hinj : Function.Injective (x t)) :
    HasDerivAt (fun τ => ∑ j, x τ j ^ 2) (2 * (N : ℝ) * ((N : ℝ) - 1)) t := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun j _ => (hx j).pow 2)
  rw [← sum_mul_zeroFlux (x t) hinj]
  have key : (fun τ => ∑ j, x τ j ^ 2) = ∑ j, (fun τ => x τ j) ^ 2 := by
    funext τ
    simp [Finset.sum_apply]
  rw [key]
  refine h.congr_deriv ?_
  apply Finset.sum_congr rfl
  intro j _
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]

/-- The height flux of a conjugate pair `a ± i y` above a real comb `x`: the imaginary part of
`2/(z − z̄) + Σ_k 2/(z − x_k)`. -/
def heightFlux {N : ℕ} (a y : ℝ) (x : Fin N → ℝ) : ℝ :=
  -1 / y - ∑ k, 2 * y / ((a - x k) ^ 2 + y ^ 2)

/-- **The crowd only helps the collision**: for `y > 0`, `heightFlux ≤ −1/y`. -/
theorem heightFlux_le {N : ℕ} (a y : ℝ) (x : Fin N → ℝ) (hy : 0 < y) :
    heightFlux a y x ≤ -1 / y := by
  unfold heightFlux
  have hsum : 0 ≤ ∑ k, 2 * y / ((a - x k) ^ 2 + y ^ 2) :=
    Finset.sum_nonneg fun k _ => div_nonneg (by positivity) (by positivity)
  linarith

/-- **The null-cone event is inevitable.** If the height of a pair above a real comb follows the
height flux and stays positive on `[0, T]`, then `y(T)² + 2T ≤ y(0)²`; in particular
`2T ≤ y(0)²`, so the pair meets the seam within time `y(0)²/2`. -/
theorem sq_add_two_mul_le {N : ℕ} (a y : ℝ → ℝ) (x : ℝ → Fin N → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hy : ∀ t, HasDerivAt y (heightFlux (a t) (y t) (x t)) t)
    (hpos : ∀ t ∈ Icc 0 T, 0 < y t) :
    y T ^ 2 + 2 * T ≤ y 0 ^ 2 := by
  have hgd : ∀ t, HasDerivAt (fun t => y t ^ 2 + 2 * t)
      (2 * y t * heightFlux (a t) (y t) (x t) + 2) t := by
    intro t
    have h1 := (hy t).pow 2
    have h2 : HasDerivAt (fun t : ℝ => 2 * t) 2 t := by
      simpa using (hasDerivAt_id t).const_mul 2
    have h := h1.add h2
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  have hanti : AntitoneOn (fun t => y t ^ 2 + 2 * t) (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · exact fun t _ => (hgd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hgd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hgd t).deriv]
      have hyt : 0 < y t := hpos t ⟨ht.1.le, ht.2.le⟩
      have hflux := heightFlux_le (a t) (y t) (x t) hyt
      have : 2 * y t * heightFlux (a t) (y t) (x t) ≤ 2 * y t * (-1 / y t) :=
        mul_le_mul_of_nonneg_left hflux (by positivity)
      have hcancel : 2 * y t * (-1 / y t) = -2 := by
        field_simp
      linarith
  have := hanti (left_mem_Icc.mpr hT) (right_mem_Icc.mpr hT) hT
  simpa using this

theorem two_mul_le_sq {N : ℕ} (a y : ℝ → ℝ) (x : ℝ → Fin N → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hy : ∀ t, HasDerivAt y (heightFlux (a t) (y t) (x t)) t)
    (hpos : ∀ t ∈ Icc 0 T, 0 < y t) :
    2 * T ≤ y 0 ^ 2 := by
  have := sq_add_two_mul_le a y x hT hy hpos
  nlinarith [sq_nonneg (y T)]

/-- [open; project-postulate] **The Rodgers--Tao zero dynamics at the entire face**, the RT3 port.
Along every `C¹` curve `z` of zeros of `H s` that is simple at time `t`, the velocity is the
principal-value comb flux: twice the limit, over centred discs of growing radius, of the
multiplicity-weighted sum of `1/(z − w)` over the other zeros `w` of `H t` in the disc.  At the
polynomial face this is the theorem `HeatFlowOfPolynomials.zero_curve_flux`; at the entire face
`ZeroDynamicsEntire.zero_curve_velocity` returns `ż = H″/H′`, and the expansion of `H″/H′` over the
other zeros in principal-value order (the Hadamard product) is the open half this port names.  No
theorem of this owner consumes it.  Falsifier: a computed velocity of a simple zero of `H t` that
disagrees with the finite comb flux on a declared truncation.  Until 2026-09-03 this port's only
field was `True`; it now states the law it was named for.  *Amended by FT3, 2026-09-03:* the discs
are centred at `½`, the centre of the reflection `z ↦ 1 − z` that pairs the comb, and the curve is
`C¹` (`z′` continuous), the hypothesis `ZeroDynamicsEntire.zero_curve_velocity` carries.  For
`H t = heatE t ξ` the field is the theorem `CombFlux.flux_time_zero` at `t = 0`; at `t ≠ 0` it
waits on the centre value `heatE t ξ (½) ≠ 0` and the growth of `heatE t ξ`, which FT4 returns
through the kernel `Φ`. -/
structure RodgersTaoZeroDynamics (H : ℝ → ℂ → ℂ) : Prop where
  flux : ∀ (t : ℝ) (z z' : ℝ → ℂ), (∀ s, HasDerivAt z (z' s) s) → Continuous z' →
    (∀ s, H s (z s) = 0) → deriv (H t) (z t) ≠ 0 →
    Filter.Tendsto
      (fun R : ℝ => 2 * ∑ᶠ u, if u = z t then (0 : ℂ) else
        (MeromorphicOn.divisor (H t) (Metric.closedBall (1 / 2 : ℂ) R) u : ℂ) / (z t - u))
      Filter.atTop (nhds (z' t))

end Soma.Holonics.RH.PhaseFlowLedger

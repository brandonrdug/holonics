import HolonicsResearch.Zeta.ZeroPairLock
import HolonicsResearch.Zeta.DeBruijnNewmanPolynomial
import Holonics.Compression.Landmark.SiteKind
import Holonics.Compression.Landmark.FixedPoint

/-!
# The reflected zero pair is a site: null on the seam, a boost off it in the strip, and the collision is its fold

[definition] Rebuild step 3 (#145), the null-cone record §4. The reflected pair of `ρ = σ + iγ` is
`(ρ, 1 − ρ̄)`, the helical pair of `Zeta/ZeroPairLock` with advances `σ` and `1 − σ` and one angular
rate `γ`. It is read as a navigator site (`Compression/Landmark/SiteKind`: trace face, determinant
face and discriminant face `a² − 4q`) in three charts. Every classification below states its
determinant sign explicitly: a kind is claimed only at a positive determinant, a negative
determinant is a reflection, and a zero determinant is degenerate.

```text
advance chart   companion(1, σ(1−σ))      roots σ, 1−σ         disc = (2σ−1)² = P(σ,γ)
tank chart      companion(0, −ρ′²)        roots ±ρ′, ρ′=ρ−½    det = 1/(L_F·C_F),  tank = log-derivative
heat chart      companion(2γ, γ²+(σ−½)²)  roots γ ∓ i(σ−½)     disc = −P(σ,γ)      (s = ½ + i z)
```

[proved-derived; formal-checked] What is proved.

1. **The advance site is the pair's velocity.** Its factor's roots are the two generators'
   advances (`advanceSite_factor`), and its discriminant face is the pair power `(2σ − 1)²` of
   `ZeroPairLock` (`advance_discriminant`). Its faces are half those of the velocity-addition
   navigator `[[1, β], [β, 1]]` of `Landmark/FixedPoint` at `β = 2σ − 1`
   (`advanceSite_is_half_velocity`), so its projective Lorentz faces are `γ_L² = tr²/(4 det) =
   1/(1 − β²)`, `(γ_Lβ)² = disc/(4 det)`, `γ_L² − (γ_Lβ)² = 1`, and `β² = disc/tr² = P`
   (`advance_lorentz_faces`). **The critical strip is the interior of the velocity cone:**
   `0 < σ < 1 ⇔ β² < 1 ⇔ det > 0` (`strip_iff_subluminal`, `strip_iff_det_pos`), and its edges are
   the light cone `β² = 1`, where the determinant vanishes (`strip_edge_iff_lightlike`).
2. **Null on the seam, a boost off it inside the strip.** The discriminant face `(2σ − 1)²` is
   zero exactly on the seam (`advance_null_iff_seam`) and positive exactly off it
   (`advance_disc_pos_iff_off_seam`), for every `σ`; the kind also reads the determinant face
   `σ(1 − σ)` (`advance_siteKind`). Outside the closed strip (`σ < 0` or `1 < σ`) the site is a
   **reflection**, on its edges `σ ∈ {0, 1}` it is **degenerate**, and in the open strip, where
   its determinant is positive, it is null (a double root, a nonzero nilpotent traceless part: a
   shear) exactly on the seam (`advance_seam_is_shear`) and a **boost** exactly off it
   (`advance_boost_iff_off_seam`). It is never a rotation (`advance_not_rotation`). With `γ ≠ 0`
   the null seam is exactly the lossless Foster tank (`advance_null_iff_foster`).
3. **The tank is a site.** The Foster tank of `ρ′ = ρ − ½` is the traceless site whose determinant
   face is `1/(L_F C_F)` (`tankSite_det_eq_inv_LC`) and whose characteristic polynomial is the pair's
   quadratic `w² − ρ′²`; the tank impedance is that polynomial's logarithmic derivative
   (`tank_eq_logDeriv_charpoly`). **Foster lossless ⇔ the tank is a real site of positive
   determinant** (`foster_iff_tank_det_pos`), and a traceless site of positive determinant is a
   rotation (`traceless_positive_is_rotation`). Real faces occur only on the seam or on the real
   axis: on the seam the tank is a rotation or (at the centre) degenerate (`tank_seam_iff`); on the
   real axis off the centre it is a reflection, with negative inductance (`tank_reflection_iff`).
   For a zero of nonzero height off the seam the tank is **not a real site at all**
   (`off_seam_tank_not_real`).
4. **The join.** For a rational generator with `γ ≠ 0`: seam ⇔ advance site null ⇔ tank site
   positive (a rotation at the height `γ`); off the seam the advance site's discriminant face is
   positive (a boost inside the strip, a reflection or degenerate site outside it) and the tank
   has no real faces (`reflected_pair_sites`).
5. **The finite fold: the collision is the null event.** In the heat chart `s = ½ + iz` the
   reflected pair is the real quadratic `(z − γ)² + (σ − ½)²` (`pairQuadratic_map`), whose
   discriminant face is `−P`, the quarter-turn of the advance chart's (`heat_discriminant`). Under
   the backward heat flow of `Zeta/PairDescent.heatR` (the finite face of the de Bruijn–Newman flow)
   it is `(z − γ)² + (σ − ½)² − 2t` exactly (`heatR_pairQuadratic`), with discriminant face
   `8t − P` (`flowed_discriminant`). Before `t = P/8` the pair is conjugate (off the seam), at
   `t = P/8` it is the double root `(z − γ)²` (`collision_is_a_double_root`), a positive-determinant
   null site when `γ ≠ 0` (`collision_site`), and after it the two roots are real (on the seam).
   The real-rooted times of the pair are exactly `[P/8, ∞)` (`realRootedTimes_pairQuadratic`), so
   the polynomial de Bruijn–Newman threshold of `Zeta/DeBruijnNewmanPolynomial` is
   **`λ(pair) = P/8 = (2σ − 1)²/8`** (`lambda_pairQuadratic`), which is at most zero exactly on the
   seam (`lambda_pair_nonpos_iff_seam`). For one pair the collision time equals the height bound
   `y₀²/2` of `Zeta/PairDescent` (`y₀ = |σ − ½|`), which a crowd of other roots only shortens.

[counterexample; formal-checked] The tank of the rational zero `ρ′ = ½ + i` (off the seam, off the
axis) has no real determinant face (`tank_off_axis_not_real`), so the ordered trichotomy cannot be
applied to the tank chart without the seam; the advance chart is the one that classifies every
generator of the strip. The height hypothesis `γ ≠ 0` of the join is load-bearing: the real zero
`ρ = 1` has a real tank, a reflection of determinant `−¼` (`tank_real_zero_is_reflection`).

[established-bounded; formal-checked] Scope: one reflected pair of rational generators, and the
algebraic locus only. Nothing here locates a zero of any function, and nothing is claimed about
`Λ_DN` beyond the existing owners (`Zeta/DeBruijnSeal`). No `axiom`, no `sorry`.
-/

noncomputable section

namespace Holonics.Landmarks.ZeroPairSite

open Matrix Polynomial Complex
open Holonics.Geometry.LocalFactor
open Holonics.Zeta.ZeroPairLock
open Holonics.Compression.Landmark.SiteKind (discriminant traceless_sq Kind siteKind
  siteKind_eq_reflection_iff siteKind_eq_degenerate_iff siteKind_eq_null_iff siteKind_eq_boost_iff
  siteKind_eq_rotation_iff)

/-! ## 1. The advance site: the pair's velocity -/

/-- [definition] **The advance site** of the reflected pair of `ρ = σ + iγ`: the site whose factor's
roots are the two members' advances `σ` and `1 − σ`. -/
def advanceSite (σ : ℚ) : Matrix (Fin 2) (Fin 2) ℚ := companion 1 (σ * (1 - σ))

theorem advanceSite_trace (σ : ℚ) : (advanceSite σ).trace = 1 :=
  (theCompanionHasTraceAndDeterminant _ _).1

theorem advanceSite_det (σ : ℚ) : (advanceSite σ).det = σ * (1 - σ) :=
  (theCompanionHasTraceAndDeterminant _ _).2

/-- [proved-derived; formal-checked] **The factor's roots are the members' advances**: the
characteristic form of the advance site splits through the advance of `ZeroPairLock.zeroGenerator`
and of `ZeroPairLock.reflectedGenerator`. -/
theorem advanceSite_factor (σ γ x : ℚ) :
    x ^ 2 - (advanceSite σ).trace * x + (advanceSite σ).det =
      (x - zeroGenerator σ γ 0) * (x - reflectedGenerator σ γ 0) := by
  rw [advanceSite_trace, advanceSite_det]
  simp [zeroGenerator, reflectedGenerator]
  ring

/-- [proved-derived; formal-checked] **The discriminant face of the advance site is the pair
power** `(2σ − 1)²` of `ZeroPairLock`. -/
theorem advance_discriminant (σ γ : ℚ) :
    discriminant (advanceSite σ).trace (advanceSite σ).det = reflectedPairPower σ γ := by
  rw [advanceSite_trace, advanceSite_det, reflectedPairPower_eq, discriminant]
  ring

open Holonics.Compression.Landmark.FixedPoint in
/-- [proved-derived; formal-checked] **The advance site is half the velocity navigator** at
`β = 2σ − 1`: its trace face is half and its determinant face a quarter of those of
`FixedPoint.velocityNavigator (2σ − 1)`, so the two share their projective faces `tr²/det`. -/
theorem advanceSite_is_half_velocity (σ : ℚ) :
    (advanceSite σ).trace = (velocityNavigator (2 * σ - 1)).trace / 2 ∧
      (advanceSite σ).det = (velocityNavigator (2 * σ - 1)).det / 4 := by
  rw [advanceSite_trace, advanceSite_det]
  refine ⟨?_, ?_⟩
  · norm_num [velocityNavigator, Mobius.trace]
  · simp only [velocityNavigator, Mobius.det]
    ring

/-- [proved-derived; formal-checked] **The projective Lorentz faces of the advance site.** In the
open strip, `γ_L² = tr²/(4 det) = 1/(1 − β²)`, `(γ_Lβ)² = disc/(4 det) = P/(1 − β²)`,
`γ_L² − (γ_Lβ)² = 1`, and the velocity squared is the pair power, `β² = disc/tr² = P`, with
`β = 2σ − 1`. -/
theorem advance_lorentz_faces (σ γ : ℚ) (h0 : 0 < σ) (h1 : σ < 1) :
    (advanceSite σ).trace ^ 2 / (4 * (advanceSite σ).det) = 1 / (1 - (2 * σ - 1) ^ 2) ∧
      discriminant (advanceSite σ).trace (advanceSite σ).det / (4 * (advanceSite σ).det) =
        reflectedPairPower σ γ / (1 - (2 * σ - 1) ^ 2) ∧
      (advanceSite σ).trace ^ 2 / (4 * (advanceSite σ).det) -
          discriminant (advanceSite σ).trace (advanceSite σ).det / (4 * (advanceSite σ).det) = 1 ∧
      discriminant (advanceSite σ).trace (advanceSite σ).det / (advanceSite σ).trace ^ 2 =
        reflectedPairPower σ γ ∧
      reflectedPairPower σ γ = (2 * σ - 1) ^ 2 := by
  have hdet : 4 * (σ * (1 - σ)) = 1 - (2 * σ - 1) ^ 2 := by ring
  have hpos : 0 < σ * (1 - σ) := mul_pos h0 (by linarith)
  have hβ : (1 : ℚ) - (2 * σ - 1) ^ 2 ≠ 0 := by rw [← hdet]; positivity
  rw [advance_discriminant σ γ, advanceSite_trace, advanceSite_det, hdet, reflectedPairPower_eq]
  refine ⟨by ring, rfl, ?_, by ring, rfl⟩
  field_simp

/-- [proved-derived; formal-checked] **The critical strip is the interior of the velocity cone**:
`0 < σ < 1 ⇔ β² = P < 1`. -/
theorem strip_iff_subluminal (σ γ : ℚ) : (0 < σ ∧ σ < 1) ↔ reflectedPairPower σ γ < 1 := by
  rw [reflectedPairPower_eq]
  constructor
  · rintro ⟨h0, h1⟩
    nlinarith
  · intro h
    constructor <;> nlinarith [sq_nonneg (2 * σ - 1)]

/-- [proved-derived; formal-checked] **The strip is where the advance site has positive
determinant.** -/
theorem strip_iff_det_pos (σ : ℚ) : (0 < σ ∧ σ < 1) ↔ 0 < (advanceSite σ).det := by
  rw [advanceSite_det]
  constructor
  · rintro ⟨h0, h1⟩
    exact mul_pos h0 (by linarith)
  · intro h
    by_contra hc
    rcases not_and_or.mp hc with h0 | h1
    · have : σ ≤ 0 := not_lt.mp h0
      nlinarith
    · have : 1 ≤ σ := not_lt.mp h1
      nlinarith

/-- [proved-derived; formal-checked] **The strip's edges are the light cone**: `σ ∈ {0, 1} ⇔ β² = 1
⇔ det = 0`. -/
theorem strip_edge_iff_lightlike (σ γ : ℚ) :
    ((σ = 0 ∨ σ = 1) ↔ reflectedPairPower σ γ = 1) ∧
      ((σ = 0 ∨ σ = 1) ↔ (advanceSite σ).det = 0) := by
  rw [reflectedPairPower_eq, advanceSite_det]
  constructor
  · constructor
    · rintro (rfl | rfl) <;> norm_num
    · intro h
      have : σ * (σ - 1) = 0 := by linear_combination h / 4
      rcases mul_eq_zero.mp this with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (by linarith)
  · constructor
    · rintro (rfl | rfl) <;> norm_num
    · intro h
      rcases mul_eq_zero.mp h with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (by linarith)

/-! ## 2. Null on the seam, a boost off it inside the strip -/

/-- [proved-derived; formal-checked] **The advance site is null exactly on the seam**, which is
exactly where the pair locks (`ZeroPairLock.reflected_pair_locked_iff_on_seam`). -/
theorem advance_null_iff_seam (σ γ : ℚ) :
    discriminant (advanceSite σ).trace (advanceSite σ).det = 0 ↔ σ = 1 / 2 := by
  rw [advance_discriminant σ γ]
  exact reflected_pair_locked_iff_on_seam σ γ

/-- [proved-derived; formal-checked] **The discriminant face is positive off the seam**: two
distinct real roots, for every `σ`. Inside the strip that is a boost (`advance_boost_iff_off_seam`);
outside it the determinant face is not positive and the site is a reflection or degenerate
(`advance_siteKind`). -/
theorem advance_disc_pos_iff_off_seam (σ γ : ℚ) :
    0 < discriminant (advanceSite σ).trace (advanceSite σ).det ↔ σ ≠ 1 / 2 := by
  rw [← not_iff_not, not_lt, not_ne_iff, ← advance_null_iff_seam σ γ, advance_discriminant σ γ,
    reflectedPairPower_eq]
  constructor
  · intro h
    exact le_antisymm h (sq_nonneg _)
  · intro h
    exact h.le

/-- [proved-derived; formal-checked] **The advance site's kind by `σ`**, read from its determinant
face `σ(1 − σ)` first (`SiteKind.siteKind`): a reflection outside the closed strip, degenerate on
its edges, null exactly on the seam, a boost exactly in the open strip off the seam, and never a
rotation. -/
theorem advance_siteKind (σ : ℚ) :
    (siteKind (advanceSite σ).trace (advanceSite σ).det = .reflection ↔ σ < 0 ∨ 1 < σ) ∧
      (siteKind (advanceSite σ).trace (advanceSite σ).det = .degenerate ↔ σ = 0 ∨ σ = 1) ∧
      (siteKind (advanceSite σ).trace (advanceSite σ).det = .null ↔ σ = 1 / 2) ∧
      (siteKind (advanceSite σ).trace (advanceSite σ).det = .boost ↔
        (0 < σ ∧ σ < 1) ∧ σ ≠ 1 / 2) ∧
      siteKind (advanceSite σ).trace (advanceSite σ).det ≠ .rotation := by
  rw [advanceSite_trace, advanceSite_det]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [siteKind_eq_reflection_iff]
    constructor
    · intro h
      by_contra hc
      push Not at hc
      nlinarith [hc.1, hc.2]
    · rintro (h | h) <;> nlinarith
  · rw [siteKind_eq_degenerate_iff]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (by linarith)
    · rintro (rfl | rfl) <;> norm_num
  · rw [siteKind_eq_null_iff]
    constructor
    · rintro ⟨-, h⟩
      nlinarith [sq_nonneg (2 * σ - 1)]
    · rintro rfl
      norm_num
  · rw [siteKind_eq_boost_iff]
    constructor
    · rintro ⟨hq, hd⟩
      refine ⟨(strip_iff_det_pos σ).mpr (by rwa [advanceSite_det]), fun h => ?_⟩
      subst h
      norm_num at hd
    · rintro ⟨⟨h0, h1⟩, hσ⟩
      have hs : 2 * σ - 1 ≠ 0 := fun h => hσ (by linarith)
      exact ⟨mul_pos h0 (by linarith), by nlinarith [sq_pos_of_ne_zero hs]⟩
  · rw [Ne, siteKind_eq_rotation_iff, not_lt]
    nlinarith [sq_nonneg (2 * σ - 1)]

/-- [proved-derived; formal-checked] **Inside the strip the advance site is a boost exactly off the
seam** (`SiteKind.siteKind`). Outside the strip `σ ≠ ½` still holds, but the site is a reflection
or degenerate there (`advance_siteKind`). -/
theorem advance_boost_iff_off_seam (σ : ℚ) (h0 : 0 < σ) (h1 : σ < 1) :
    siteKind (advanceSite σ).trace (advanceSite σ).det = .boost ↔ σ ≠ 1 / 2 := by
  rw [(advance_siteKind σ).2.2.2.1]
  exact ⟨fun h => h.2, fun h => ⟨⟨h0, h1⟩, h⟩⟩

/-- [proved-derived; formal-checked] **The advance site's kinds in the strip, with the determinant
stated**: in the open strip it has positive determinant, is null exactly on the seam and a boost
exactly off it. -/
theorem advance_site_in_strip (σ γ : ℚ) (h0 : 0 < σ) (h1 : σ < 1) :
    0 < (advanceSite σ).det ∧
      (discriminant (advanceSite σ).trace (advanceSite σ).det = 0 ↔ σ = 1 / 2) ∧
      (0 < discriminant (advanceSite σ).trace (advanceSite σ).det ↔ σ ≠ 1 / 2) ∧
      (siteKind (advanceSite σ).trace (advanceSite σ).det = .null ↔ σ = 1 / 2) ∧
      (siteKind (advanceSite σ).trace (advanceSite σ).det = .boost ↔ σ ≠ 1 / 2) :=
  ⟨(strip_iff_det_pos σ).mp ⟨h0, h1⟩, advance_null_iff_seam σ γ, advance_disc_pos_iff_off_seam σ γ,
    (advance_siteKind σ).2.2.1, advance_boost_iff_off_seam σ h0 h1⟩

/-- [proved-derived; formal-checked] **The advance site is never a rotation.** -/
theorem advance_not_rotation (σ γ : ℚ) :
    ¬ discriminant (advanceSite σ).trace (advanceSite σ).det < 0 := by
  rw [advance_discriminant σ γ, reflectedPairPower_eq]
  exact not_lt.mpr (sq_nonneg _)

/-- [proved-derived; formal-checked] **On the seam the advance site is a shear**: its traceless part
squares to zero (`SiteKind.traceless_sq`) and is not zero. The two advances collide at `½`. -/
theorem advance_seam_is_shear :
    (advanceSite (1 / 2) - ((advanceSite (1 / 2)).trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℚ)) ^ 2
        = 0 ∧
      advanceSite (1 / 2) - ((advanceSite (1 / 2)).trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℚ)
        ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [traceless_sq, (advance_null_iff_seam (1 / 2) 0).mpr rfl]
    simp
  · intro h
    have h10 := congrFun (congrFun h 1) 0
    simp [advanceSite, companion] at h10

/-- [proved-derived; formal-checked] **The null seam is the lossless Foster tank**: for `γ ≠ 0`,
the advance site is null exactly when the tank of `ρ′ = (σ − ½) + iγ` has positive inductance
(`ZeroPairLock.locked_iff_foster_inductance_positive`). -/
theorem advance_null_iff_foster (σ γ : ℚ) (hγ : γ ≠ 0) :
    discriminant (advanceSite σ).trace (advanceSite σ).det = 0 ↔
      ∃ L : ℝ, 0 < L ∧
        Holonics.Zeta.FosterTanks.inductance
          (((σ - 1 / 2 : ℚ) : ℂ) + ((γ : ℚ) : ℂ) * Complex.I) = (L : ℂ) := by
  rw [advance_discriminant σ γ]
  exact locked_iff_foster_inductance_positive σ γ hγ

/-! ## 3. The tank is a site -/

/-- [definition] **The tank site** of the centred zero `ρ′`: the traceless site whose
characteristic polynomial is the pair's quadratic `w² − ρ′²`. -/
def tankSite (ρ' : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := companion 0 (-ρ' ^ 2)

theorem tankSite_trace (ρ' : ℂ) : (tankSite ρ').trace = 0 :=
  (theCompanionHasTraceAndDeterminant _ _).1

theorem tankSite_det (ρ' : ℂ) : (tankSite ρ').det = -ρ' ^ 2 :=
  (theCompanionHasTraceAndDeterminant _ _).2

/-- [proved-derived; formal-checked] **The tank site's determinant face is `1/(L_F C_F)`**, the
squared resonance of the parallel LC tank of `Zeta/FosterTanks`. -/
theorem tankSite_det_eq_inv_LC (ρ' : ℂ) (hρ : ρ' ≠ 0) :
    (tankSite ρ').det =
      1 / (Holonics.Zeta.FosterTanks.inductance ρ' * Holonics.Zeta.FosterTanks.capacitance) := by
  rw [tankSite_det, Holonics.Zeta.FosterTanks.inductance, Holonics.Zeta.FosterTanks.capacitance]
  have h2 : ρ' ^ 2 ≠ 0 := pow_ne_zero 2 hρ
  field_simp

/-- [proved-derived; formal-checked] The characteristic polynomial of the tank site is the pair's
quadratic `w² − ρ′²`. -/
theorem tankSite_charpoly (ρ' : ℂ) : (tankSite ρ').charpoly = X ^ 2 - C (ρ' ^ 2) := by
  rw [charpoly_fin_two, tankSite_trace, tankSite_det]
  simp [sub_eq_add_neg]

/-- [proved-derived; formal-checked] **The tank impedance is the logarithmic derivative of the
tank site's characteristic polynomial**: `2w/(w² − ρ′²) = χ′(w)/χ(w)`. -/
theorem tank_eq_logDeriv_charpoly (ρ' w : ℂ) :
    Holonics.Zeta.FosterTanks.tank ρ' w =
      (derivative (tankSite ρ').charpoly).eval w / ((tankSite ρ').charpoly).eval w := by
  rw [tankSite_charpoly, Holonics.Zeta.FosterTanks.tank, derivative_sub, derivative_C,
    derivative_X_pow]
  simp

/-- [proved-derived; formal-checked] **Foster lossless ⇔ the tank is a real site of positive
determinant.** -/
theorem foster_iff_tank_det_pos (ρ' : ℂ) :
    (∃ L : ℝ, 0 < L ∧ Holonics.Zeta.FosterTanks.inductance ρ' = (L : ℂ)) ↔
      ∃ q : ℝ, 0 < q ∧ (tankSite ρ').det = (q : ℂ) := by
  rw [Holonics.Zeta.FosterTanks.inductance_pos_real_iff, ← Holonics.Zeta.FosterTanks.sq_eq_neg_real_iff,
    tankSite_det]
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨-c, by linarith, by rw [h]; push_cast; ring⟩
  · rintro ⟨q, hq, h⟩
    exact ⟨-q, by linarith, by push_cast; linear_combination -h⟩

/-- [proved-derived; formal-checked] **A traceless site of positive determinant is a rotation**:
its discriminant face `−4q` is negative. -/
theorem traceless_positive_is_rotation (q : ℝ) (hq : 0 < q) : discriminant (0 : ℝ) q < 0 := by
  rw [discriminant]
  linarith

/-- [proved-derived; formal-checked] **On the seam the tank has real faces of nonnegative
determinant** (a rotation, or degenerate at the centre), and conversely. -/
theorem tank_seam_iff (ρ' : ℂ) : (∃ q : ℝ, 0 ≤ q ∧ (tankSite ρ').det = (q : ℂ)) ↔ ρ'.re = 0 := by
  rw [tankSite_det]
  constructor
  · rintro ⟨q, hq, h⟩
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp [sq, Complex.mul_re, Complex.mul_im] at hre him
    rcases mul_eq_zero.mp (show 2 * ρ'.re * ρ'.im = 0 by linarith) with h1 | h1
    · linarith
    · rw [h1] at hre
      nlinarith [sq_nonneg ρ'.re]
  · intro h
    refine ⟨ρ'.im ^ 2, sq_nonneg _, ?_⟩
    apply Complex.ext <;> simp [sq, Complex.mul_re, Complex.mul_im, h]

/-- [proved-derived; formal-checked] **On the real axis off the centre the tank is a reflection**:
its determinant face is a negative real (a negative inductance). -/
theorem tank_reflection_iff (ρ' : ℂ) :
    (∃ q : ℝ, q < 0 ∧ (tankSite ρ').det = (q : ℂ)) ↔ ρ'.im = 0 ∧ ρ' ≠ 0 := by
  rw [tankSite_det]
  constructor
  · rintro ⟨q, hq, h⟩
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp [sq, Complex.mul_re, Complex.mul_im] at hre him
    rcases mul_eq_zero.mp (show 2 * ρ'.re * ρ'.im = 0 by linarith) with h1 | h1
    · have h1' : ρ'.re = 0 := by linarith
      rw [h1'] at hre
      nlinarith [sq_nonneg ρ'.im]
    · refine ⟨h1, fun h0 => ?_⟩
      rw [h0] at hre
      simp at hre
      linarith
  · rintro ⟨him, hne⟩
    have hre : ρ'.re ≠ 0 := fun h => hne (Complex.ext h him)
    refine ⟨-(ρ'.re ^ 2), by nlinarith [sq_pos_of_ne_zero hre], ?_⟩
    apply Complex.ext <;> simp [sq, Complex.mul_re, Complex.mul_im, him]

/-- [proved-derived; formal-checked] **Off the seam, a zero of nonzero height has no real tank.** -/
theorem off_seam_tank_not_real (ρ' : ℂ) (hre : ρ'.re ≠ 0) (him : ρ'.im ≠ 0) :
    ¬ ∃ q : ℝ, (tankSite ρ').det = (q : ℂ) := by
  rintro ⟨q, h⟩
  rw [tankSite_det] at h
  have h' := congrArg Complex.im h
  simp [sq, Complex.mul_im] at h'
  rcases mul_eq_zero.mp (show 2 * ρ'.re * ρ'.im = 0 by linarith) with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · norm_num at h2
    · exact hre h2
  · exact him h1

/-- [counterexample; formal-checked] **The tank of `ρ′ = ½ + i` has no real determinant face**: off
the seam and off the axis the tank chart does not classify. -/
theorem tank_off_axis_not_real : ¬ ∃ q : ℝ, (tankSite (1 / 2 + Complex.I)).det = (q : ℂ) :=
  off_seam_tank_not_real _ (by simp) (by simp)

/-- [counterexample; formal-checked] **The height hypothesis is load-bearing**: the real zero
`ρ = 1` (`ρ′ = ½`, off the seam, zero height) has a real tank, a reflection of determinant `−¼`. -/
theorem tank_real_zero_is_reflection :
    (tankSite ((1 / 2 : ℝ) : ℂ)).det = ((-1 / 4 : ℝ) : ℂ) ∧ (-1 / 4 : ℝ) < 0 := by
  refine ⟨?_, by norm_num⟩
  rw [tankSite_det]
  push_cast
  ring

/-! ## 4. The join -/

/-- [proved-derived; formal-checked] **The reflected pair's sites.** For a rational generator of
nonzero height: the seam is exactly where the advance site is null and exactly where the tank is a
real site of positive determinant (a rotation, the lossless Foster tank). Off the seam the advance
site's discriminant face is positive, which inside the strip is a boost (outside it the site is a
reflection or degenerate, `advance_siteKind`), and the tank has no real faces. -/
theorem reflected_pair_sites (σ γ : ℚ) (hγ : γ ≠ 0) :
    (σ = 1 / 2 ↔ discriminant (advanceSite σ).trace (advanceSite σ).det = 0) ∧
      (σ = 1 / 2 ↔ ∃ q : ℝ, 0 < q ∧
        (tankSite (((σ - 1 / 2 : ℚ) : ℂ) + ((γ : ℚ) : ℂ) * Complex.I)).det = (q : ℂ)) ∧
      (σ ≠ 1 / 2 ↔ 0 < discriminant (advanceSite σ).trace (advanceSite σ).det) ∧
      (0 < σ → σ < 1 →
        (σ ≠ 1 / 2 ↔ siteKind (advanceSite σ).trace (advanceSite σ).det = .boost)) ∧
      (σ ≠ 1 / 2 → ¬ ∃ q : ℝ,
        (tankSite (((σ - 1 / 2 : ℚ) : ℂ) + ((γ : ℚ) : ℂ) * Complex.I)).det = (q : ℂ)) := by
  refine ⟨(advance_null_iff_seam σ γ).symm, ?_, (advance_disc_pos_iff_off_seam σ γ).symm,
    fun h0 h1 => (advance_boost_iff_off_seam σ h0 h1).symm, ?_⟩
  · rw [← foster_iff_tank_det_pos, ← locked_iff_foster_inductance_positive σ γ hγ]
    exact (reflected_pair_locked_iff_on_seam σ γ).symm
  · intro hσ
    apply off_seam_tank_not_real
    · intro h
      apply hσ
      have h' : (σ : ℝ) - 1 / 2 = 0 := by simpa using h
      have h'' : ((σ - 1 / 2 : ℚ) : ℝ) = 0 := by push_cast; exact h'
      have : (σ - 1 / 2 : ℚ) = 0 := by exact_mod_cast h''
      linarith
    · simpa using hγ

/-! ## 5. The heat chart and the finite fold -/

/-- [definition] A monic real quadratic `z² − bz + c`, the characteristic form of
`companion b c`. -/
def quad (b c : ℝ) : ℝ[X] := X ^ 2 - C b * X + C c

theorem quad_natDegree (b c : ℝ) : (quad b c).natDegree = 2 := by
  have : quad b c = C 1 * X ^ 2 + C (-b) * X + C c := by
    simp [quad, sub_eq_add_neg]
  rw [this]
  exact natDegree_quadratic one_ne_zero

theorem quad_ne_zero (b c : ℝ) : quad b c ≠ 0 := by
  intro h
  have := quad_natDegree b c
  rw [h] at this
  simp at this

/-- [proved-derived; formal-checked] **A monic real quadratic is real-rooted exactly when its
discriminant face is nonnegative**: its count of non-real roots (`PolyaStep.nonreal`) is zero
exactly when `4c ≤ b²`. -/
theorem nonreal_quad_eq_zero_iff (b c : ℝ) :
    Holonics.Zeta.PolyaStep.nonreal (quad b c) = 0 ↔ 0 ≤ discriminant b c := by
  unfold Holonics.Zeta.PolyaStep.nonreal
  rw [quad_natDegree, discriminant]
  constructor
  · intro h
    by_contra hneg
    push Not at hneg
    have hroots : (quad b c).roots = 0 := by
      apply Multiset.eq_zero_of_forall_notMem
      intro x hx
      rw [mem_roots (quad_ne_zero b c), IsRoot, quad] at hx
      simp at hx
      nlinarith [sq_nonneg (x - b / 2)]
    rw [hroots] at h
    simp at h
  · intro hd
    set r := Real.sqrt (b ^ 2 - 4 * c) with hr
    have hrr : r * r = b ^ 2 - 4 * c := Real.mul_self_sqrt hd
    have hfac : quad b c = (X - C ((b + r) / 2)) * (X - C ((b - r) / 2)) := by
      have e1 : (b + r) / 2 + (b - r) / 2 = b := by ring
      have e2 : (b + r) / 2 * ((b - r) / 2) = c := by nlinarith
      rw [quad]
      calc X ^ 2 - C b * X + C c
          = X ^ 2 - C ((b + r) / 2 + (b - r) / 2) * X + C ((b + r) / 2 * ((b - r) / 2)) := by
            rw [e1, e2]
        _ = _ := by simp only [C_add, C_mul]; ring
    have hcard : Multiset.card (quad b c).roots = 2 := by
      rw [hfac, roots_mul (by rw [← hfac]; exact quad_ne_zero b c), roots_X_sub_C, roots_X_sub_C]
      simp
    omega

/-- [definition] **The reflected pair in the heat chart** `s = ½ + iz`: the quadratic
`(z − γ)² + (σ − ½)²`. -/
def pairQuadratic (σ γ : ℚ) : ℝ[X] :=
  quad (2 * (γ : ℝ)) ((γ : ℝ) ^ 2 + ((σ : ℝ) - 1 / 2) ^ 2)

/-- [proved-derived; formal-checked] **The heat chart carries the reflected pair**: over `ℂ` the
quadratic splits at `γ − i(σ − ½)` and `γ + i(σ − ½)`, which are `ρ = σ + iγ` and `1 − ρ̄` read
through `s = ½ + iz`. -/
theorem pairQuadratic_map (σ γ : ℚ) :
    (pairQuadratic σ γ).map (algebraMap ℝ ℂ) =
        (X - C ((γ : ℂ) - ((σ : ℂ) - 1 / 2) * Complex.I)) *
          (X - C ((γ : ℂ) + ((σ : ℂ) - 1 / 2) * Complex.I)) ∧
      1 / 2 + Complex.I * ((γ : ℂ) - ((σ : ℂ) - 1 / 2) * Complex.I) = (σ : ℂ) + (γ : ℂ) * Complex.I ∧
      1 / 2 + Complex.I * ((γ : ℂ) + ((σ : ℂ) - 1 / 2) * Complex.I) =
        1 - ((σ : ℂ) - (γ : ℂ) * Complex.I) := by
  refine ⟨?_, ?_, ?_⟩
  · have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    have e1 : C ((γ : ℂ) ^ 2 + ((σ : ℂ) - 1 / 2) ^ 2) =
        C ((γ : ℂ) - ((σ : ℂ) - 1 / 2) * Complex.I) *
          C ((γ : ℂ) + ((σ : ℂ) - 1 / 2) * Complex.I) := by
      rw [← C_mul]
      congr 1
      linear_combination ((σ : ℂ) - 1 / 2) ^ 2 * hI
    have e2 : C (2 * (γ : ℂ)) =
        C ((γ : ℂ) - ((σ : ℂ) - 1 / 2) * Complex.I) +
          C ((γ : ℂ) + ((σ : ℂ) - 1 / 2) * Complex.I) := by
      rw [← C_add]
      congr 1
      ring
    have hmap : (pairQuadratic σ γ).map (algebraMap ℝ ℂ) =
        X ^ 2 - C (2 * (γ : ℂ)) * X + C ((γ : ℂ) ^ 2 + ((σ : ℂ) - 1 / 2) ^ 2) := by
      simp only [pairQuadratic, quad, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
        Polynomial.map_pow, map_X, map_C]
      congr 3 <;> simp
    rw [hmap, e1, e2]
    ring
  · linear_combination (-((σ : ℂ) - 1 / 2)) * Complex.I_sq
  · linear_combination ((σ : ℂ) - 1 / 2) * Complex.I_sq

/-- [proved-derived; formal-checked] **The heat chart is the quarter-turn of the advance chart**:
its discriminant face is minus the pair power. -/
theorem heat_discriminant (σ γ : ℚ) :
    discriminant (2 * (γ : ℝ)) ((γ : ℝ) ^ 2 + ((σ : ℝ) - 1 / 2) ^ 2) =
      -((reflectedPairPower σ γ : ℚ) : ℝ) := by
  rw [reflectedPairPower_eq, discriminant]
  push_cast
  ring

/-- [proved-derived; formal-checked] **The backward heat flow of the pair**: `heatR t` of
`Zeta/PairDescent` lowers the constant face by `2t`, exactly. -/
theorem heatR_quad (b c t : ℝ) :
    Holonics.Zeta.PairDescent.heatR t (quad b c) = quad b (c - 2 * t) := by
  rw [Holonics.Zeta.HeatSemigroup.heatR_eq_sum_of_le (quad_natDegree b c).le]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h4 : derivative^[2 * 2] (quad b c) = 0 :=
    iterate_derivative_eq_zero (by rw [quad_natDegree]; norm_num)
  have h2 : derivative^[2 * 1] (quad b c) = C 2 := by
    simp [quad, Function.iterate_succ_apply']
    rw [← C_1, ← C_add]
    norm_num
  rw [h4, h2]
  simp [quad, smul_eq_C_mul]
  ring

theorem heatR_pairQuadratic (σ γ : ℚ) (t : ℝ) :
    Holonics.Zeta.PairDescent.heatR t (pairQuadratic σ γ) =
      quad (2 * (γ : ℝ)) ((γ : ℝ) ^ 2 + ((σ : ℝ) - 1 / 2) ^ 2 - 2 * t) :=
  heatR_quad _ _ t

/-- [proved-derived; formal-checked] **The flowed discriminant face is `8t − P`.** -/
theorem flowed_discriminant (σ γ : ℚ) (t : ℝ) :
    discriminant (2 * (γ : ℝ)) ((γ : ℝ) ^ 2 + ((σ : ℝ) - 1 / 2) ^ 2 - 2 * t) =
      8 * t - ((reflectedPairPower σ γ : ℚ) : ℝ) := by
  rw [reflectedPairPower_eq, discriminant]
  push_cast
  ring

/-- [proved-derived; formal-checked] **The collision is a double root**: at `t = P/8` the flowed
pair is `(z − γ)²`, the fold where the discriminant face vanishes. -/
theorem collision_is_a_double_root (σ γ : ℚ) :
    Holonics.Zeta.PairDescent.heatR (((reflectedPairPower σ γ : ℚ) : ℝ) / 8) (pairQuadratic σ γ) =
      (X - C (γ : ℝ)) ^ 2 := by
  rw [heatR_pairQuadratic, reflectedPairPower_eq, quad]
  push_cast
  rw [show (γ : ℝ) ^ 2 + ((σ : ℝ) - 1 / 2) ^ 2 - 2 * ((2 * (σ : ℝ) - 1) ^ 2 / 8) = (γ : ℝ) ^ 2 by
    ring]
  simp only [C_mul, C_pow]
  rw [show (C 2 : ℝ[X]) = 2 from map_ofNat C 2]
  ring

/-- [proved-derived; formal-checked] **The collision site is a positive-determinant null site** for
a pair of nonzero height. -/
theorem collision_site (σ γ : ℚ) (hγ : γ ≠ 0) :
    0 < (γ : ℝ) ^ 2 + ((σ : ℝ) - 1 / 2) ^ 2 - 2 * (((reflectedPairPower σ γ : ℚ) : ℝ) / 8) ∧
      discriminant (2 * (γ : ℝ))
        ((γ : ℝ) ^ 2 + ((σ : ℝ) - 1 / 2) ^ 2 - 2 * (((reflectedPairPower σ γ : ℚ) : ℝ) / 8)) = 0 := by
  have hγ' : (γ : ℝ) ≠ 0 := by exact_mod_cast hγ
  rw [flowed_discriminant, reflectedPairPower_eq]
  push_cast
  constructor
  · nlinarith [sq_pos_of_ne_zero hγ']
  · ring

/-- [proved-derived; formal-checked] **The real-rooted times of the pair are `[P/8, ∞)`**: before
the collision the pair is conjugate, from it on both roots are real. -/
theorem realRootedTimes_pairQuadratic (σ γ : ℚ) :
    Holonics.Zeta.DeBruijnNewmanPolynomial.realRootedTimes (pairQuadratic σ γ) =
      Set.Ici (((reflectedPairPower σ γ : ℚ) : ℝ) / 8) := by
  ext t
  rw [Holonics.Zeta.DeBruijnNewmanPolynomial.mem_realRootedTimes, heatR_pairQuadratic,
    nonreal_quad_eq_zero_iff, flowed_discriminant, Set.mem_Ici]
  constructor <;> intro h <;> linarith

/-- [proved-derived; formal-checked] **The polynomial de Bruijn–Newman threshold of the reflected
pair is `P/8 = (2σ − 1)²/8`**, `Zeta/DeBruijnNewmanPolynomial.lambda` read exactly. -/
theorem lambda_pairQuadratic (σ γ : ℚ) :
    Holonics.Zeta.DeBruijnNewmanPolynomial.lambda (pairQuadratic σ γ) =
      ((reflectedPairPower σ γ : ℚ) : ℝ) / 8 := by
  rw [Holonics.Zeta.DeBruijnNewmanPolynomial.lambda, realRootedTimes_pairQuadratic, csInf_Ici]

/-- [proved-derived; formal-checked] **The pair's threshold is at most zero exactly on the seam**,
where it is zero: the finite face of `RH ⇔ Λ ≤ 0 ⇔ Λ = 0` for one reflected pair. -/
theorem lambda_pair_nonpos_iff_seam (σ γ : ℚ) :
    (Holonics.Zeta.DeBruijnNewmanPolynomial.lambda (pairQuadratic σ γ) ≤ 0 ↔ σ = 1 / 2) ∧
      0 ≤ Holonics.Zeta.DeBruijnNewmanPolynomial.lambda (pairQuadratic σ γ) := by
  rw [lambda_pairQuadratic, ← reflected_pair_locked_iff_on_seam σ γ, reflectedPairPower_eq]
  push_cast
  constructor
  · constructor
    · intro h
      have h0 : (2 * (σ : ℝ) - 1) ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
      exact_mod_cast h0
    · intro h
      have h0 : (2 * (σ : ℝ) - 1) ^ 2 = 0 := by exact_mod_cast h
      rw [h0]; norm_num
  · positivity

section Audit
#print axioms advanceSite_factor
#print axioms advance_discriminant
#print axioms advanceSite_is_half_velocity
#print axioms advance_lorentz_faces
#print axioms strip_iff_subluminal
#print axioms strip_iff_det_pos
#print axioms strip_edge_iff_lightlike
#print axioms advance_null_iff_seam
#print axioms advance_disc_pos_iff_off_seam
#print axioms advance_siteKind
#print axioms advance_boost_iff_off_seam
#print axioms advance_site_in_strip
#print axioms advance_not_rotation
#print axioms advance_seam_is_shear
#print axioms advance_null_iff_foster
#print axioms tankSite_det_eq_inv_LC
#print axioms tank_eq_logDeriv_charpoly
#print axioms foster_iff_tank_det_pos
#print axioms tank_seam_iff
#print axioms tank_reflection_iff
#print axioms off_seam_tank_not_real
#print axioms tank_off_axis_not_real
#print axioms tank_real_zero_is_reflection
#print axioms reflected_pair_sites
#print axioms nonreal_quad_eq_zero_iff
#print axioms pairQuadratic_map
#print axioms heat_discriminant
#print axioms heatR_quad
#print axioms flowed_discriminant
#print axioms collision_is_a_double_root
#print axioms collision_site
#print axioms realRootedTimes_pairQuadratic
#print axioms lambda_pairQuadratic
#print axioms lambda_pair_nonpos_iff_seam
end Audit

end Holonics.Landmarks.ZeroPairSite

import Holonics.Compression.Landmark.FixedPoint
import Holonics.Objects.Ratio
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Fluid.Singularity: planar point-singularity flows are one-parameter Möbius navigators

[definition] The egg record §4 (`research/records/2026-09-24_THE_EGG_IS_A_TORUS_WHOSE_SHAPE_IS_A_BOOST_AND_ITS_NECK_IS_THE_NULL_CONE.md`)
for rebuild step 6, K3 (#74). A planar singularity pair of strength `c = m + iΓ` (source `m`;
`Γ` the **clockwise** circulation, so the counterclockwise circulation is `−Γ`,
`circulation_flux_jump`) at `z₁`, with the opposite singularity at `z₂`, has the complex potential

```text
F(z) = (c / 2π) · ℓ,        ℓ ∈ logFibre (z − z₁ : z − z₂)
```

the logarithm of the **undivided ratio** `(z − z₁ : z − z₂)` carried as a lift with its winding
(`Objects/Ratio.logFibre`, the loss chart `ℓ = log R`). The velocity is `u = conj F′`.

[proved-derived; formal-checked]

* **The velocity is a Möbius field.** In the principal chart `F′ = c / (2π W)` with
  `W = (z − z₁)(z − z₂)/(z₁ − z₂)` (`hasDerivAt_potential`), so
  `2π |W|² · u = conj(c) · W` (`velocity_is_mobius_field`): the velocity is a positive multiple of
  the vector field `λ W`, `λ = conj c`, and the streamlines are its orbits.
* **That field is a one-parameter Möbius navigator.** A block `X` moves `z` along its field
  `b + (a − d) z − c z²`, the derivative at `t = 0` of `(1 + tX)·z` (`hasDerivAt_act`). The pair's
  generator (`generator λ z₁ z₂`) is traceless, has field `λ W` (`generator_field`), vanishes at
  `z₁`, `z₂` (`generator_fixes`) and has discriminant `λ²` (`generator_discriminant`).
* **The site kinds are those of `Compression/Landmark/SiteKind`.** For a real traceless generator
  the Cayley block `(1 − det X/4)·1 + X` (the Cayley element up to scale, rational: no `exp`) has
  the generator's fixed points (`cayleyBlock_fixed_iff`) and discriminant (`cayleyBlock_discriminant`),
  and off the pole `det X = −4` its `siteKind` is the sign of that discriminant
  (`cayley_siteKind_boost`, `_rotation`, `_null`, `cayley_siteKind_eq`).
* **Classification by site kind.** A flow kind is a real site kind of `SiteKind` or loxodromic
  (`FlowKind`). `flowKind D` is loxodromic for `D ∉ ℝ`, and for real `D` the `siteKind` of the
  Cayley block of the real generator of discriminant `D` at the clock rescaled off the pole
  (`siteGenerator`, `offPole`; Rust `cayley_site`): boost for `D > 0`, rotation for `D < 0`,
  null for `D = 0` (`flowKind_eq`), and for every real generator it is the site kind of its own
  Cayley block (`cayley_flowKind`). The pair's generator at rate `conj c` has discriminant
  `conj(c)²`, whatever its two sites, so the **source–sink pair** is a boost, the **vortex pair** a
  rotation and the **spiral pair** loxodromic (`pair_kind_boost`, `pair_kind_rotation`,
  `pair_kind_loxodromic`); the **doublet** (the pair merged, `F = μ/(z − z₀)`) has a nilpotent
  generator and is null (`doublet_velocity_is_mobius_field`, `doublet_null`). The source–sink pair
  on `±1` and the vortex pair on `±i` have real generators whose Cayley blocks are a boost and a
  rotation (`sourceSink_is_boost_site`, `vortexPair_is_rotation_site`); the source–sink block is
  the velocity-addition navigator fixing `±1` (`sourceSink_fixes_one`).
* **Circulation and flux are winding readings.** Two lifts of the ratio differ by whole turns, so
  the potential jumps by `i c n` over a loop of winding `n` (`potential_jump`): the
  counterclockwise circulation (the jump of `Re F`) is `−Γ n` and the flux (the jump of `Im F`) is
  `m n` (`circulation_flux_jump`). The log is never evaluated.
* **The potential chart is a lift, and the log is the navigator's clock.** The principal chart
  `log((z − z₁)/(z − z₂))` lies in `logFibre (z − z₁ : z − z₂)` (`principal_mem_logFibre`), and
  along every orbit of the generator at rate `λ` it advances at the constant rate `λ`
  (`logRatio_is_clock`): `d/dz` of the chart is `1/W`.

[counterexample; formal-checked] **A loxodromic flow has no real site.** A real generator has a
real discriminant (`real_generator_not_loxodromic`), so the spiral pair's kind lies outside the
five real site kinds; the classification needs the complex discriminant. The kind is unchanged by a
positive rescaling of the clock (`flowKind_smul`) and by reversing it (`λ ↦ −λ` keeps `D`), but not
by a complex one: `iλ` exchanges boost and rotation (`quarter_turn_exchanges`).

[open] The streamline orbits are identified through the positive rescaling; the time
reparametrization `dt = 2π|W|² dτ` and the Norbury torus-to-sphere family are not formalized.
-/

noncomputable section

namespace Holonics.Physics.Fluid.Singularity

open Complex ComplexConjugate
open Holonics.Compression.Landmark.FixedPoint Holonics.Compression.Landmark.SiteKind
open Holonics.Objects.Ratio Holonics.Geometry

/-! ## 1. The potential and its velocity -/

/-- [definition] `W = (z − z₁)(z − z₂)/(z₁ − z₂)`, the pair's quadratic. -/
def W (z₁ z₂ z : ℂ) : ℂ := (z - z₁) * (z - z₂) / (z₁ - z₂)

/-- [definition] The pair's potential in the principal chart of the ratio. -/
def potential (c z₁ z₂ z : ℂ) : ℂ := c / (2 * Real.pi) * Complex.log ((z - z₁) / (z - z₂))

theorem two_pi_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 := by
  have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)

/-- [proved-derived; formal-checked] **The derivative of the potential** is `c / (2π W)`. -/
theorem hasDerivAt_potential (c : ℂ) {z₁ z₂ z : ℂ} (h12 : z₁ ≠ z₂) (h1 : z ≠ z₁) (h2 : z ≠ z₂)
    (hslit : (z - z₁) / (z - z₂) ∈ slitPlane) :
    HasDerivAt (potential c z₁ z₂) (c / (2 * Real.pi * W z₁ z₂ z)) z := by
  have hz2 : z - z₂ ≠ 0 := sub_ne_zero.mpr h2
  have hz1 : z - z₁ ≠ 0 := sub_ne_zero.mpr h1
  have h12' : z₁ - z₂ ≠ 0 := sub_ne_zero.mpr h12
  have hratio : HasDerivAt (fun t => (t - z₁) / (t - z₂))
      ((1 * (z - z₂) - (z - z₁) * 1) / (z - z₂) ^ 2) z :=
    ((hasDerivAt_id z).sub_const z₁).div ((hasDerivAt_id z).sub_const z₂) hz2
  have hlog := (HasDerivAt.clog hratio hslit).const_mul (c / (2 * Real.pi))
  unfold potential
  refine hlog.congr_deriv ?_
  simp only [W]
  field_simp
  ring

/-- [proved-derived; formal-checked] **The velocity is a positive multiple of the Möbius field**:
`2π |W|² · conj(F′) = conj(c) · W`. -/
theorem velocity_is_mobius_field (c : ℂ) {z₁ z₂ z : ℂ} (hW : W z₁ z₂ z ≠ 0) :
    conj (c / (2 * Real.pi * W z₁ z₂ z)) * (2 * Real.pi * (Complex.normSq (W z₁ z₂ z) : ℂ)) =
      conj c * W z₁ z₂ z := by
  have hconj : conj (c / (2 * Real.pi * W z₁ z₂ z)) = conj c / (2 * Real.pi * conj (W z₁ z₂ z)) := by
    simp [map_div₀, map_mul, map_ofNat]
  have hc : conj (W z₁ z₂ z) ≠ 0 := (map_ne_zero _).mpr hW
  have := two_pi_ne_zero
  rw [hconj, ← Complex.mul_conj]
  field_simp

/-! ## 2. The Möbius field of a block and the pair's generator -/

/-- [definition] **The vector field of a block** `X = [[a,b],[c,d]]`: `b + (a − d) z − c z²`. -/
def mobiusField (X : Mobius ℂ) (z : ℂ) : ℂ := X.b + (X.a - X.d) * z - X.c * z ^ 2

/-- [proved-derived; formal-checked] **The field is the Möbius motion at `t = 0`**: the derivative
of `(1 + tX)·z` at `t = 0`. -/
theorem hasDerivAt_act (X : Mobius ℂ) (z : ℂ) :
    HasDerivAt (fun t : ℂ => (⟨1 + t * X.a, t * X.b, t * X.c, 1 + t * X.d⟩ : Mobius ℂ).act z)
      (mobiusField X z) 0 := by
  have hN : HasDerivAt (fun t : ℂ => z + t * (X.a * z + X.b)) (X.a * z + X.b) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (X.a * z + X.b)).const_add z
  have hD : HasDerivAt (fun t : ℂ => 1 + t * (X.c * z + X.d)) (X.c * z + X.d) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (X.c * z + X.d)).const_add 1
  have hfun : (fun t : ℂ => (⟨1 + t * X.a, t * X.b, t * X.c, 1 + t * X.d⟩ : Mobius ℂ).act z) =
      fun t => (z + t * (X.a * z + X.b)) / (1 + t * (X.c * z + X.d)) := by
    funext t
    simp only [Mobius.act]
    congr 1 <;> ring
  rw [hfun]
  refine (hN.div hD (by simp)).congr_deriv ?_
  simp only [mobiusField]
  field_simp
  ring

/-- [definition] **The pair's generator** with rate `λ` fixing `z₁`, `z₂`. -/
def generator (lam z₁ z₂ : ℂ) : Mobius ℂ where
  a := -lam * (z₁ + z₂) / (2 * (z₁ - z₂))
  b := lam * z₁ * z₂ / (z₁ - z₂)
  c := -lam / (z₁ - z₂)
  d := lam * (z₁ + z₂) / (2 * (z₁ - z₂))

theorem generator_trace (lam z₁ z₂ : ℂ) : (generator lam z₁ z₂).trace = 0 := by
  simp [generator, Mobius.trace]; ring

/-- [proved-derived; formal-checked] **The pair's generator moves `z` along `λ W`.** -/
theorem generator_field (lam : ℂ) {z₁ z₂ : ℂ} (h12 : z₁ ≠ z₂) (z : ℂ) :
    mobiusField (generator lam z₁ z₂) z = lam * W z₁ z₂ z := by
  have h : z₁ - z₂ ≠ 0 := sub_ne_zero.mpr h12
  simp only [mobiusField, generator, W]
  field_simp
  ring

/-- [proved-derived; formal-checked] Its field vanishes at the two singularities. -/
theorem generator_fixes (lam : ℂ) {z₁ z₂ : ℂ} (h12 : z₁ ≠ z₂) :
    mobiusField (generator lam z₁ z₂) z₁ = 0 ∧ mobiusField (generator lam z₁ z₂) z₂ = 0 := by
  simp [generator_field lam h12, W]

/-- [definition] The discriminant face `tr² − 4 det` of a block. -/
def discriminant (X : Mobius ℂ) : ℂ := X.trace ^ 2 - 4 * X.det

/-- [proved-derived; formal-checked] **The generator's discriminant is `λ²`**, whatever the
positions. -/
theorem generator_discriminant (lam : ℂ) {z₁ z₂ : ℂ} (h12 : z₁ ≠ z₂) :
    discriminant (generator lam z₁ z₂) = lam ^ 2 := by
  have h : z₁ - z₂ ≠ 0 := sub_ne_zero.mpr h12
  simp only [discriminant, Mobius.trace, Mobius.det, generator]
  field_simp
  ring

/-! ## 3. The Cayley block: the real site kinds -/

section Cayley

variable {K : Type*} [Field K] [CharZero K]

/-- [definition] **The Cayley block** of a traceless generator: `(1 − det X/4)·1 + X`, the Cayley
element `(1 + X/2)(1 − X/2)⁻¹` times `1 + det X/4`, with no inversion and no exponential. -/
def cayleyBlock (X : Mobius K) : Mobius K :=
  ⟨X.a + (1 - X.det / 4), X.b, X.c, X.d + (1 - X.det / 4)⟩

/-- [proved-derived; formal-checked] **The Cayley block fixes the generator's fixed points.** -/
theorem cayleyBlock_fixed_iff (X : Mobius K) (z : K) :
    (cayleyBlock X).Fixed z ↔ X.b + (X.a - X.d) * z - X.c * z ^ 2 = 0 := by
  simp only [Mobius.Fixed, cayleyBlock]
  constructor <;> intro h <;> linear_combination h

theorem cayleyBlock_trace {X : Mobius K} (hX : X.trace = 0) :
    (cayleyBlock X).trace = 2 * (1 - X.det / 4) := by
  simp only [Mobius.trace, cayleyBlock] at *
  linear_combination hX

theorem cayleyBlock_det {X : Mobius K} (hX : X.trace = 0) :
    (cayleyBlock X).det = (1 + X.det / 4) ^ 2 := by
  have hd : X.d = -X.a := by simp only [Mobius.trace] at hX; linear_combination hX
  simp only [Mobius.det, cayleyBlock, hd]
  field_simp
  ring

/-- [proved-derived; formal-checked] **The Cayley block keeps the discriminant**:
`tr² − 4 det = −4 det X = tr X² − 4 det X`. -/
theorem cayleyBlock_discriminant {X : Mobius K} (hX : X.trace = 0) :
    (cayleyBlock X).trace ^ 2 - 4 * (cayleyBlock X).det = X.trace ^ 2 - 4 * X.det := by
  rw [cayleyBlock_trace hX, cayleyBlock_det hX, hX]
  field_simp
  ring

end Cayley

section RealCayley

theorem cayleyBlock_det_pos {X : Mobius ℝ} (hX : X.trace = 0) (hpole : X.det ≠ -4) :
    0 < (cayleyBlock X).det := by
  rw [cayleyBlock_det hX]
  have : 1 + X.det / 4 ≠ 0 := by
    intro h; apply hpole; linarith
  positivity

/-- [proved-derived; formal-checked] **A real generator with positive discriminant has a boost
site.** -/
theorem cayley_siteKind_boost {X : Mobius ℝ} (hX : X.trace = 0) (hpole : X.det ≠ -4) :
    siteKind (cayleyBlock X).trace (cayleyBlock X).det = .boost ↔ 0 < X.trace ^ 2 - 4 * X.det := by
  rw [siteKind_eq_boost_iff, ← cayleyBlock_discriminant hX]
  constructor
  · rintro ⟨_, h⟩; linarith
  · intro h; exact ⟨cayleyBlock_det_pos hX hpole, by linarith⟩

/-- [proved-derived; formal-checked] **A real generator with negative discriminant has a rotation
site.** -/
theorem cayley_siteKind_rotation {X : Mobius ℝ} (hX : X.trace = 0) :
    siteKind (cayleyBlock X).trace (cayleyBlock X).det = .rotation ↔
      X.trace ^ 2 - 4 * X.det < 0 := by
  rw [siteKind_eq_rotation_iff, ← cayleyBlock_discriminant hX]
  constructor <;> intro h <;> linarith

/-- [proved-derived; formal-checked] **A real generator with zero discriminant has a null site.** -/
theorem cayley_siteKind_null {X : Mobius ℝ} (hX : X.trace = 0) (hpole : X.det ≠ -4) :
    siteKind (cayleyBlock X).trace (cayleyBlock X).det = .null ↔
      X.trace ^ 2 - 4 * X.det = 0 := by
  rw [siteKind_eq_null_iff, ← cayleyBlock_discriminant hX]
  constructor
  · rintro ⟨_, h⟩; linarith
  · intro h; exact ⟨cayleyBlock_det_pos hX hpole, by linarith⟩

/-- [proved-derived; formal-checked] **The site kind of a real traceless generator off the Cayley
pole is the sign of its discriminant.** -/
theorem cayley_siteKind_eq {X : Mobius ℝ} (hX : X.trace = 0) (hpole : X.det ≠ -4) :
    siteKind (cayleyBlock X).trace (cayleyBlock X).det =
      if 0 < X.trace ^ 2 - 4 * X.det then .boost
      else if X.trace ^ 2 - 4 * X.det < 0 then .rotation else .null := by
  rcases lt_trichotomy (X.trace ^ 2 - 4 * X.det) 0 with h | h | h
  · rw [if_neg (by linarith), if_pos h]
    exact (cayley_siteKind_rotation hX).mpr h
  · rw [h, if_neg (lt_irrefl 0), if_neg (lt_irrefl 0)]
    exact (cayley_siteKind_null hX hpole).mpr h
  · rw [if_pos h]
    exact (cayley_siteKind_boost hX hpole).mpr h

/-- [definition] **The real site generator of a discriminant** `D`: the traceless block
`[[0, 1],[D/4, 0]]`, of discriminant `D`. -/
def siteGenerator (D : ℝ) : Mobius ℝ := ⟨0, 1, D / 4, 0⟩

/-- [definition] **The clock rescaling off the Cayley pole**, `D ↦ D/(1 + D²)`: the discriminant
of the generator run at clock rate `s` with `s² = 1/(1 + D²)` (`flowKind_smul`); it keeps the sign
of `D` and stays within `[−½, ½]`, away from the pole `D = 16`. The Rust owner is
`holonics::physics::fluid::singularity::cayley_site`. -/
def offPole (D : ℝ) : ℝ := D / (1 + D ^ 2)

theorem siteGenerator_trace (D : ℝ) : (siteGenerator D).trace = 0 := by
  simp [siteGenerator, Mobius.trace]

theorem siteGenerator_discriminant (D : ℝ) :
    (siteGenerator D).trace ^ 2 - 4 * (siteGenerator D).det = D := by
  simp only [siteGenerator, Mobius.trace, Mobius.det]; ring

theorem offPole_pos_iff (D : ℝ) : 0 < offPole D ↔ 0 < D := by
  have h : 0 < 1 + D ^ 2 := by positivity
  rw [offPole, lt_div_iff₀ h, zero_mul]

theorem offPole_neg_iff (D : ℝ) : offPole D < 0 ↔ D < 0 := by
  have h : 0 < 1 + D ^ 2 := by positivity
  rw [offPole, div_lt_iff₀ h, zero_mul]

theorem siteGenerator_offPole_ne_pole (D : ℝ) : (siteGenerator (offPole D)).det ≠ -4 := by
  have h1 : 0 < 1 + D ^ 2 := by positivity
  simp only [siteGenerator, Mobius.det, offPole]
  intro h
  have h16 : D = 16 * (1 + D ^ 2) := by
    field_simp at h
    linarith
  nlinarith [sq_nonneg (D - 1 / 32)]

end RealCayley

/-! ## 4. The flow kinds -/

/-- [definition] **The kind of a one-parameter Möbius navigator**, read from its generator's
discriminant `D`: a real site kind of `Compression/Landmark/SiteKind` (`site`), or loxodromic off
the real line. The Rust owner is `FlowKind::{Site(SiteKind), Loxodromic}`. -/
inductive FlowKind
  | site (k : Kind)
  | loxodromic
deriving DecidableEq, Repr

/-- [definition] **The flow kind of a discriminant**: loxodromic off the real line; on it, the
`siteKind` of the Cayley block of the real site generator at the rescaled clock (`offPole`). -/
def flowKind (D : ℂ) : FlowKind :=
  if D.im ≠ 0 then .loxodromic
  else .site (siteKind (cayleyBlock (siteGenerator (offPole D.re))).trace
    (cayleyBlock (siteGenerator (offPole D.re))).det)

/-- [proved-derived; formal-checked] **The flow kind is the sign of a real discriminant**: boost for
`D > 0`, rotation for `D < 0`, null for `D = 0` (`cayley_siteKind_{boost,rotation,null}`),
loxodromic off the real line. -/
theorem flowKind_eq (D : ℂ) :
    flowKind D = if D.im ≠ 0 then .loxodromic
      else .site (if 0 < D.re then .boost else if D.re < 0 then .rotation else .null) := by
  unfold flowKind
  rw [cayley_siteKind_eq (siteGenerator_trace _) (siteGenerator_offPole_ne_pole _),
    siteGenerator_discriminant]
  split_ifs <;> simp_all [offPole_pos_iff, offPole_neg_iff]

/-- [proved-derived; formal-checked] **A real generator's flow kind is the site kind of its own
Cayley block**: `cayley_siteKind_{boost,rotation,null}` read through `flowKind`. -/
theorem cayley_flowKind {X : Mobius ℝ} (hX : X.trace = 0) (hpole : X.det ≠ -4) :
    flowKind (discriminant ⟨(X.a : ℂ), X.b, X.c, X.d⟩) =
      .site (siteKind (cayleyBlock X).trace (cayleyBlock X).det) := by
  have hD : discriminant ⟨(X.a : ℂ), X.b, X.c, X.d⟩ = ((X.trace ^ 2 - 4 * X.det : ℝ) : ℂ) := by
    simp only [discriminant, Mobius.trace, Mobius.det]; push_cast; ring
  rw [hD, flowKind_eq, Complex.ofReal_im, Complex.ofReal_re, if_neg (not_not.mpr rfl),
    cayley_siteKind_eq hX hpole]

/-- [proved-derived; formal-checked] **The kind is a class up to positive rescaling of time**:
scaling the generator by `s > 0` scales `D` by `s²`. -/
theorem flowKind_smul (D : ℂ) {s : ℝ} (hs : 0 < s) : flowKind ((s : ℂ) ^ 2 * D) = flowKind D := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hre : ((s : ℂ) ^ 2 * D).re = s ^ 2 * D.re := by simp [sq]
  have him : ((s : ℂ) ^ 2 * D).im = s ^ 2 * D.im := by simp [sq]
  have e1 : (s ^ 2 * D.im ≠ 0) ↔ (D.im ≠ 0) := by
    constructor
    · intro h h'; exact h (by rw [h', mul_zero])
    · intro h; exact mul_ne_zero hs2.ne' h
  have e2 : 0 < s ^ 2 * D.re ↔ 0 < D.re := mul_pos_iff_of_pos_left hs2
  have e3 : s ^ 2 * D.re < 0 ↔ D.re < 0 := by
    constructor
    · intro h; by_contra h'; have h'' := not_lt.mp h'; nlinarith
    · intro h; exact mul_neg_of_pos_of_neg hs2 h
  rw [flowKind_eq, flowKind_eq, hre, him]
  simp only [e1, e2, e3]

theorem pair_discriminant_re (m Γ : ℝ) : ((conj ((m : ℂ) + Γ * I)) ^ 2).re = m ^ 2 - Γ ^ 2 := by
  simp [sq]

theorem pair_discriminant_im (m Γ : ℝ) : ((conj ((m : ℂ) + Γ * I)) ^ 2).im = -2 * m * Γ := by
  simp [sq]; ring

/-- [proved-derived; formal-checked] **The source–sink pair is a boost**: the pair's generator at
rate `conj(m + iΓ)` with `Γ = 0` has a boost flow kind, wherever its two distinct sites sit
(`generator_discriminant`). -/
theorem pair_kind_boost {m Γ : ℝ} {z₁ z₂ : ℂ} (h12 : z₁ ≠ z₂) (hm : m ≠ 0) (hΓ : Γ = 0) :
    flowKind (discriminant (generator (conj ((m : ℂ) + Γ * I)) z₁ z₂)) = .site .boost := by
  have hpos : 0 < m ^ 2 := by positivity
  rw [generator_discriminant _ h12, flowKind_eq, pair_discriminant_im, pair_discriminant_re, hΓ,
    if_neg (by simp), if_pos (by linarith)]

/-- [proved-derived; formal-checked] **The vortex pair is a rotation**: the pair's generator with
`m = 0`, `Γ ≠ 0` has a rotation flow kind. -/
theorem pair_kind_rotation {m Γ : ℝ} {z₁ z₂ : ℂ} (h12 : z₁ ≠ z₂) (hm : m = 0) (hΓ : Γ ≠ 0) :
    flowKind (discriminant (generator (conj ((m : ℂ) + Γ * I)) z₁ z₂)) = .site .rotation := by
  have hpos : 0 < Γ ^ 2 := by positivity
  rw [generator_discriminant _ h12, flowKind_eq, pair_discriminant_im, pair_discriminant_re, hm,
    if_neg (by simp), if_neg (by linarith), if_pos (by linarith)]

/-- [proved-derived; formal-checked] **The spiral pair is loxodromic**: the pair's generator with
`m ≠ 0`, `Γ ≠ 0` has a loxodromic flow kind. -/
theorem pair_kind_loxodromic {m Γ : ℝ} {z₁ z₂ : ℂ} (h12 : z₁ ≠ z₂) (hm : m ≠ 0) (hΓ : Γ ≠ 0) :
    flowKind (discriminant (generator (conj ((m : ℂ) + Γ * I)) z₁ z₂)) = .loxodromic := by
  rw [generator_discriminant _ h12, flowKind_eq, pair_discriminant_im, if_pos (by simp [hm, hΓ])]

/-- [counterexample; formal-checked] **A quarter turn of the rate exchanges boost and rotation**:
`D(iλ) = −D(λ)`, so a real rate `r ≠ 0` is a boost and `ir` a rotation. -/
theorem quarter_turn_exchanges {r : ℝ} (hr : r ≠ 0) :
    flowKind ((r : ℂ) ^ 2) = .site .boost ∧ flowKind ((I * r) ^ 2) = .site .rotation := by
  have hpos : 0 < r ^ 2 := by positivity
  have h1 : ((r : ℂ) ^ 2) = ((r ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have h2 : ((I * r) ^ 2) = ((-(r ^ 2) : ℝ) : ℂ) := by rw [mul_pow, I_sq]; push_cast; ring
  constructor
  · rw [flowKind_eq, h1, Complex.ofReal_im, Complex.ofReal_re, if_neg (not_not.mpr rfl),
      if_pos hpos]
  · rw [flowKind_eq, h2, Complex.ofReal_im, Complex.ofReal_re, if_neg (not_not.mpr rfl),
      if_neg (by linarith), if_pos (by linarith)]

/-- [counterexample; formal-checked] **No real generator is loxodromic**: a block with real entries
has a real discriminant, so its flow kind is one of the three real site kinds; the spiral pair's
loxodromic kind needs a complex generator. -/
theorem real_generator_not_loxodromic (X : Mobius ℝ) :
    flowKind (discriminant ⟨(X.a : ℂ), X.b, X.c, X.d⟩) ≠ .loxodromic := by
  have him : (discriminant ⟨(X.a : ℂ), X.b, X.c, X.d⟩).im = 0 := by
    have : discriminant ⟨(X.a : ℂ), X.b, X.c, X.d⟩ = ((X.trace ^ 2 - 4 * X.det : ℝ) : ℂ) := by
      simp only [discriminant, Mobius.trace, Mobius.det]; push_cast; ring
    rw [this, Complex.ofReal_im]
  rw [flowKind_eq, if_neg (not_not.mpr him)]
  simp

/-! ## 5. The doublet -/

/-- [definition] The parabolic generator `κ [[z₀, −z₀²],[1, −z₀]]`, nilpotent, fixing `z₀`. -/
def parabolic (κ z₀ : ℂ) : Mobius ℂ := ⟨κ * z₀, -κ * z₀ ^ 2, κ, -κ * z₀⟩

theorem parabolic_field (κ z₀ z : ℂ) : mobiusField (parabolic κ z₀) z = -κ * (z - z₀) ^ 2 := by
  simp [mobiusField, parabolic]; ring

/-- [proved-derived; formal-checked] **The doublet's velocity is a positive multiple of the
parabolic field**: for `F = μ/(z − z₀)`, `|z − z₀|⁴ · conj(F′) = mobiusField (parabolic (conj μ) z₀)`. -/
theorem doublet_velocity_is_mobius_field (μ z₀ z : ℂ) (hz : z ≠ z₀) :
    conj (-μ / (z - z₀) ^ 2) * ((Complex.normSq (z - z₀) : ℂ) ^ 2) =
      mobiusField (parabolic (conj μ) z₀) z := by
  have h : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
  have hc : conj (z - z₀) ≠ 0 := (map_ne_zero _).mpr h
  rw [parabolic_field, ← Complex.mul_conj, map_div₀, map_neg, map_pow]
  field_simp

/-- [proved-derived; formal-checked] **The doublet is null**: its generator is nonzero with
discriminant `0`. -/
theorem doublet_null {κ : ℂ} (hκ : κ ≠ 0) (z₀ : ℂ) :
    discriminant (parabolic κ z₀) = 0 ∧ (parabolic κ z₀).c ≠ 0 ∧
      flowKind (discriminant (parabolic κ z₀)) = .site .null := by
  have hD : discriminant (parabolic κ z₀) = 0 := by
    simp [discriminant, Mobius.trace, Mobius.det, parabolic]; ring
  refine ⟨hD, hκ, ?_⟩
  rw [hD, flowKind_eq]; simp

/-! ## 6. The source–sink and vortex pairs as real sites -/

section RealSite

/-- [definition] The source–sink generator on `±1` at real rate `m` (`generator m (−1) 1`, real). -/
def sourceSinkGenerator (m : ℝ) : Mobius ℝ := ⟨0, m / 2, m / 2, 0⟩

/-- [definition] The vortex-pair generator on `±i` at clockwise circulation `Γ`
(`generator (−iΓ) i (−i)`, real). -/
def vortexGenerator (Γ : ℝ) : Mobius ℝ := ⟨0, -Γ / 2, Γ / 2, 0⟩

/-- [proved-derived; formal-checked] The complex pair generators on `±1` and `±i` are these real
blocks. -/
theorem generators_are_real (m Γ : ℝ) :
    generator (m : ℂ) (-1) 1 = ⟨0, (m / 2 : ℝ), (m / 2 : ℝ), 0⟩ ∧
      generator (-(Γ : ℂ) * I) I (-I) = ⟨0, (-Γ / 2 : ℝ), (Γ / 2 : ℝ), 0⟩ := by
  have hI : (I - -I) = 2 * I := by ring
  constructor
  · simp only [generator, Mobius.mk.injEq]
    push_cast
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ring
  · simp only [generator, Mobius.mk.injEq, hI]
    push_cast
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals field_simp
    all_goals ring_nf
    all_goals simp [I_sq]

/-- [proved-derived; formal-checked] **The source–sink pair on `±1` is a boost site.** -/
theorem sourceSink_is_boost_site {m : ℝ} (hm : m ≠ 0) (hpole : m ^ 2 ≠ 16) :
    siteKind (cayleyBlock (sourceSinkGenerator m)).trace
      (cayleyBlock (sourceSinkGenerator m)).det = .boost := by
  have hX : (sourceSinkGenerator m).trace = 0 := by simp [sourceSinkGenerator, Mobius.trace]
  have hdet : (sourceSinkGenerator m).det = -(m ^ 2 / 4) := by
    simp [sourceSinkGenerator, Mobius.det]; ring
  rw [cayley_siteKind_boost hX (by rw [hdet]; intro h; apply hpole; linarith), hX, hdet]
  have := sq_pos_of_ne_zero hm
  linarith

/-- [proved-derived; formal-checked] **The vortex pair on `±i` is a rotation site.** -/
theorem vortexPair_is_rotation_site {Γ : ℝ} (hΓ : Γ ≠ 0) :
    siteKind (cayleyBlock (vortexGenerator Γ)).trace
      (cayleyBlock (vortexGenerator Γ)).det = .rotation := by
  have hX : (vortexGenerator Γ).trace = 0 := by simp [vortexGenerator, Mobius.trace]
  have hdet : (vortexGenerator Γ).det = Γ ^ 2 / 4 := by
    simp [vortexGenerator, Mobius.det]; ring
  have hpos := sq_pos_of_ne_zero hΓ
  rw [cayley_siteKind_rotation hX, hX, hdet]
  linarith

/-- [proved-derived; formal-checked] **The source–sink Cayley block fixes `±1`**: it is the
velocity-addition navigator's shape `[[s, m/2],[m/2, s]]`, whose landmarks are `±1`
(`Compression/Landmark/FixedPoint.vadd_fixes_one`). -/
theorem sourceSink_fixes_one (m : ℝ) :
    (cayleyBlock (sourceSinkGenerator m)).Fixed 1 ∧ (cayleyBlock (sourceSinkGenerator m)).Fixed (-1) := by
  constructor <;> rw [cayleyBlock_fixed_iff] <;> simp [sourceSinkGenerator]

end RealSite

/-! ## 7. Circulation and flux are winding readings of the ratio -/

/-- [proved-derived; formal-checked] **The potential jumps by `i c n` over a loop of winding `n`**:
two lifts of the ratio `(z − z₁ : z − z₂)` differ by `2πi n` (`Objects/Ratio.logFibre_torsor`). -/
theorem potential_jump (c : ℂ) {num den ℓ ℓ' : ℂ} (hden : den ≠ 0)
    (hℓ : ℓ ∈ logFibre (holonRatio num den)) (hℓ' : ℓ' ∈ logFibre (holonRatio num den)) :
    ∃ n : ℤ, c / (2 * Real.pi) * ℓ' - c / (2 * Real.pi) * ℓ = I * c * n := by
  obtain ⟨n, hn⟩ := (logFibre_torsor (r := holonRatio num den) hden hℓ).mp hℓ'
  refine ⟨n, ?_⟩
  rw [hn]
  have := two_pi_ne_zero
  field_simp
  ring

/-- [proved-derived; formal-checked] **The counterclockwise circulation is `−Γ n` and the flux is
`m n`**: `Γ` is the clockwise circulation (the standard vortex is `F = −(iΓ/2π) log z`). -/
theorem circulation_flux_jump (m Γ : ℝ) (n : ℤ) :
    (I * ((m : ℂ) + Γ * I) * n).re = -Γ * n ∧ (I * ((m : ℂ) + Γ * I) * n).im = m * n := by
  constructor <;> simp

/-! ## 8. The potential chart is a lift of the ratio, and the navigator's clock -/

/-- [proved-derived; formal-checked] **The principal potential chart is a lift of the undivided
ratio**: off the two singularities, `log((z − z₁)/(z − z₂)) ∈ logFibre (z − z₁ : z − z₂)`, so
`potential` is `F = (c/2π) ℓ` at one lift `ℓ` (`Objects/Ratio.logFibre`), and every other lift
differs by whole turns (`potential_jump`). -/
theorem principal_mem_logFibre {z₁ z₂ z : ℂ} (h1 : z ≠ z₁) (h2 : z ≠ z₂) :
    Complex.log ((z - z₁) / (z - z₂)) ∈ logFibre (holonRatio (z - z₁) (z - z₂)) := by
  change Complex.exp (Complex.log ((z - z₁) / (z - z₂))) * (z - z₂) = z - z₁
  rw [Complex.exp_log (div_ne_zero (sub_ne_zero.mpr h1) (sub_ne_zero.mpr h2)),
    div_mul_cancel₀ _ (sub_ne_zero.mpr h2)]

/-- [proved-derived; formal-checked] **The log of the ratio is the navigator's clock**: along an
orbit `z(t)` of the pair's generator at rate `λ` (`ż = mobiusField (generator λ z₁ z₂) z = λ W`),
the principal chart advances at the constant rate `λ`,
`d/dt log((z − z₁)/(z − z₂)) = λ`, because its derivative in `z` is `1/W`. -/
theorem logRatio_is_clock (lam : ℂ) {z₁ z₂ : ℂ} (h12 : z₁ ≠ z₂) {z : ℝ → ℂ} {t : ℝ}
    (hflow : HasDerivAt z (mobiusField (generator lam z₁ z₂) (z t)) t)
    (h1 : z t ≠ z₁) (h2 : z t ≠ z₂) (hslit : (z t - z₁) / (z t - z₂) ∈ slitPlane) :
    HasDerivAt (fun s => Complex.log ((z s - z₁) / (z s - z₂))) lam t := by
  rw [generator_field lam h12] at hflow
  have hz1 : z t - z₁ ≠ 0 := sub_ne_zero.mpr h1
  have hz2 : z t - z₂ ≠ 0 := sub_ne_zero.mpr h2
  have h12' : z₁ - z₂ ≠ 0 := sub_ne_zero.mpr h12
  have hratio : HasDerivAt (fun s => (z s - z₁) / (z s - z₂))
      ((lam * W z₁ z₂ (z t) * (z t - z₂) - (z t - z₁) * (lam * W z₁ z₂ (z t))) / (z t - z₂) ^ 2)
      t :=
    (hflow.sub_const z₁).div (hflow.sub_const z₂) hz2
  refine (hratio.clog_real hslit).congr_deriv ?_
  simp only [W]
  field_simp
  ring

section Audit

#print axioms generator_discriminant
#print axioms flowKind_eq
#print axioms cayley_flowKind
#print axioms pair_kind_boost
#print axioms pair_kind_rotation
#print axioms pair_kind_loxodromic
#print axioms doublet_null
#print axioms sourceSink_is_boost_site
#print axioms vortexPair_is_rotation_site
#print axioms circulation_flux_jump
#print axioms principal_mem_logFibre
#print axioms logRatio_is_clock

end Audit

end Holonics.Physics.Fluid.Singularity

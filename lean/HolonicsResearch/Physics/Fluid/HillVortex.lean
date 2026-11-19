import Holonics.Physics.Fluid.Singularity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Fluid.HillVortex: a streamline orbit re-timed by `dt = 2π|W|² dτ` is a particle path, and Hill's sphere is steady

[proved-derived; formal-checked] for the clock (§1) and the core's site kind (§8);
[proved-standard; formal-checked] for Hill's spherical vortex (Hill 1894, §2 to §8); [definition] for the charts.
Sources: the #410 box "Norbury's vortex-ring family, from a torus to Hill's sphere (`Physics/Fluid/Singularity`)";
the owner's `[open]` paragraph ("The streamline orbits are identified through the positive rescaling; the time
reparametrization `dt = 2π|W|² dτ` and the Norbury torus-to-sphere family are not formalized"); the egg record
`research/records/2026-09-24_THE_EGG_IS_A_TORUS_WHOSE_SHAPE_IS_A_BOOST_AND_ITS_NECK_IS_THE_NULL_CONE.md` §4 ("In
three dimensions. Norbury's family of steady vortex rings runs from a thin-cored torus to Hill's spherical vortex as
the ring's hole closes") and its obligations; the atlas rows `fluid.singularity-site-kinds` (the pair's site kinds,
read here at the ring's core), `fluid.kelvin-holonomy` (circulation as a holonomy pairing), `fluid.closed-body-net-zero`
and `fluid.rankine-oval-closes` (the planar closed bodies). No atlas row names Hill's vortex or Norbury's family
(`rg -n -i 'hill|norbury|vortex ring' docs/atlas/`: the `hill` hits are other names, G. W. Hill's periodic equation in
`parametron.hill-floquet-kinds`, Lighthill, Myhill, Greenhill and T. Hill's Benford law, and "a vortex ring" is a
lens named in `CHARTS.md`). Norbury's family between its ends is computed numerically; this module takes its sphere
end as a built steady solution, and the owner's time reparametrization. The box stays part done.

[definition] **The clock.** An orbit of the pair's generator at rate `λ = conj c` moves by `dz/dτ = λ W(z)`
(`Singularity.generator_field`); the clock `t(τ)` runs at `clockRate = 2π|W|²`, positive off the two sites.

[definition] **Hill's vortex in its own frame.** Cylindrical coordinates `(s, z)` on the meridian half-plane `s > 0`,
`r = √(s² + z²)` (`rad`), radius `a > 0`, the stream `−U` along `z` at infinity (`U > 0`). Stokes' stream function
`ψ` gives the velocity by

```text
u_s = −(1/s) ∂_z ψ,        u_z = (1/s) ∂_s ψ
ψ_in  = (3U/4) s² (1 − r²/a²)        r ≤ a     (streamIn)
ψ_out = −(U/2) s² (1 − a³/r³)        r ≥ a     (streamOut)
```

so that `u_in = (3U/2a²) (s z, a² − 2s² − z²)` (`velSIn`, `velZIn`) and
`u_out = (3Ua³ s z / 2r⁵, −U (1 − a³/r³) − 3Ua³ s² / 2r⁵)` (`velSOut`, `velZOut`). A partial derivative is Mathlib's
derivative along a coordinate line, `s ↦ f s z` or `z ↦ f s z`. The azimuthal vorticity is `ω = ∂_z u_s − ∂_s u_z`
(`vorticity`), Stokes' operator `E²ψ = ∂²_s ψ − (1/s) ∂_s ψ + ∂²_z ψ` (`stokesOperator`), and in this convention
`ω = −E²ψ / s`. The pressure at unit density is Bernoulli's, `p = H − (ω/s) ψ − ½|u|²` (`bernoulliPressure`), with
`H = p∞ + U²/2` on both sides (`pressureIn`, `pressureOut`). The one flow (`hillStream`, `hillVelS`, `hillVelZ`,
`hillPressure`) takes the inner chart on `r ≤ a` and the outer one beyond (`hillSide`).

What is proved.

1. **The streamline orbits are the particle paths** (§1). Through a local inverse `σ` of the clock, the path
   `z ∘ σ` has velocity `conj(c / 2πW) = conj F′` (`particle_velocity`, by `HasDerivAt.of_local_left_inverse`;
   `F′ = c/2πW` is `Singularity.hasDerivAt_potential`): the rescaled field is `conj F′` (`clock_rescales_field`).
   Along a whole orbit that avoids the sites the clock is strictly increasing and has a left inverse that is
   continuous at each reading (`exists_left_inverse`), so the re-timed orbit is a particle path at every point
   (`orbit_is_particle_path`).
2. **The stream function gives the velocity** (§2): `∂_s ψ = s u_z` and `∂_z ψ = −s u_s` on each side
   (`hasDerivAt_streamIn_s`, `hasDerivAt_streamIn_z`, `hasDerivAt_streamOut_s`, `hasDerivAt_streamOut_z`), with
   `∂_s r = s/r`, `∂_z r = z/r` (`hasDerivAt_rad_s`, `hasDerivAt_rad_z`), and the eight velocity gradients
   (`hasDerivAt_velSIn_s` to `hasDerivAt_velZOut_z`).
3. **Continuity and vorticity** (§3). `∂_s(s u_s) + s ∂_z u_z = 0` on each side (`continuity_in`,
   `continuity_out`); `ω = (15U/2a²) s` inside, so `ω/s` is constant, and `ω = 0` outside (`vorticity_in`,
   `vorticity_out`); `E²ψ = −15U s²/(2a²)` inside and `0` outside (`stokesOperator_in`, `stokesOperator_out`);
   `ω/s` is carried along the flow, `u·∇(ω/s) = 0` (`vorticity_transported_in`, `vorticity_transported_out`).
4. **The steady momentum balance** (§4). For any meridian flow whose vorticity is `A s`, Bernoulli's pressure
   balances the advection, `∂p = −(u·∇)u` along both lines, so `∂H = −A ∂ψ` (`momentum_balance`); Hill's flow
   meets it with `A = 15U/2a²` inside and `A = 0` outside (`euler_in`, `euler_out`).
5. **The sphere is the dividing stream surface** (§5). On `r = a` both stream functions vanish (`streamIn_sphere`,
   `streamOut_sphere`), both velocity components match (`velocity_match_sphere`: no vortex sheet), the velocity is
   tangent to the sphere from both sides (`velocity_tangent_sphere`) and the pressure matches
   (`pressure_match_sphere`); `ψ > 0` strictly inside and `ψ < 0` strictly outside (`streamIn_pos`,
   `streamOut_neg`).
6. **The far field is a stream and a dipole** (§6). `ψ_out = −(U/2) s² + (Ua³/2) s²/r³`
   (`streamOut_eq_uniform_add_dipole`); the outer velocity is the gradient of `φ = −U z − (Ua³/2) z/r³`, the uniform
   stream plus a dipole of strength `Ua³/2` (`hasDerivAt_potentialOut_s`, `hasDerivAt_potentialOut_z`); and
   `|ψ_out + (U/2)s²| ≤ Ua³/2r`, `|u_s| ≤ 3Ua³/4r³`, `|u_z + U| ≤ Ua³/r³` (`far_field`).
7. **One flow across the sphere** (§7). A function that agrees with one of two charts on each side, where the
   charts share a value and a derivative, has that derivative (`hasDerivAt_ite_of_eq`, `hillSide_hasDerivAt_s`,
   `hillSide_hasDerivAt_z`); so the one stream function has `∂_s ψ = s u_z`, `∂_z ψ = −s u_s` at every point of the
   half-plane, the sphere included (`hillStream_hasDerivAt`). Its zero set there is the sphere and nothing else
   (`hillStream_sign`, `hillStream_eq_zero_iff`), and its velocity and pressure are continuous across the sphere
   (`hill_continuousAt_sphere`, by `continuousAt_ite_of_eq`).
8. **Readings** (§8). The circulation, the vorticity integrated over the meridian half-disc, is
   `∫_(−a)^a ∫_0^(√(a² − z²)) ω ds dz = 5Ua` (`circulation`); the speed on the sphere at polar angle `θ` is
   `(3/2) U sin θ` (`speed_on_sphere`); the poles are stagnation points (`poles_stagnation`); and the ring's core
   `s₀ = a/√2, z = 0` is a stagnation point at the stream function's maximum `3Ua²/16`, whose velocity gradient is
   traceless with a rotation site (`core_is_rotation_site`, through `Singularity.cayley_siteKind_rotation`).

What is not claimed. Norbury's family between its ends (a numerical family, Norbury 1973): neither its members nor
their passage from the torus to the sphere; the thin ring's Kelvin speed; stability; swirl; uniqueness of Hill's
vortex; the flow's existence from initial data; the vortex's impulse and kinetic energy. The flow is stated on the
meridian half-plane `s > 0` as the axisymmetric reduction (the outer chart is not read on the axis); the one flow's
second derivatives on the sphere are not stated, where `ω/s` jumps from `15U/2a²` to `0`. The flow is inviscid: no
dissipation enters its balances, and its entropy production is not stated. The clock is taken with its rate: its
construction as the integral of `2π|W|²` along the orbit is not made, and the orbit is assumed for every `τ`.

The computational object is the helical pair interaction, read on a vortex ring. The owner's planar pair is a
navigator whose log chart is its clock (`Singularity.logRatio_is_clock`), its orbit a helix whose winding reads the
circulation and the flux; §1 re-times that helix by a positive rate, so the navigator's clock and the fluid's time
are two clocks of one orbit. Hill's vortex is a pair in the meridian plane: the ring's core circle meets a plane
through the axis in two counter-rotating cores at `±a/√2`, each a rotation site (`core_is_rotation_site`), the kind
of the owner's vortex pair (`Singularity.vortexPair_is_rotation_site`). The circulation `5Ua` is the cell holonomy of
the meridian half-disc, its face of vorticity (`fluid.kelvin-holonomy`). [interpretation] The sphere is a globe in the
sense of `Physics/Fluid/Body`: `ψ = 0` bounds an interior with persistent closed motion, coupled to the exterior
through the matched velocity and pressure, while the exterior is the potential flow of a stream past a sphere, whose
receiver reads a dipole and not the interior's vorticity. Of the winding guide's six general objects this touches the
helix (the re-timed orbit), the pair (the planar pair's generator and the ring's two cores) and the cell holonomy (the
circulation); faces and placement, the tube and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.Fluid.HillVortex

open Filter Topology Set

/-! ## 1. The clock: a streamline orbit re-timed by `dt = 2π|W|² dτ` is a particle path -/

section Clock

open Complex ComplexConjugate Holonics.Physics.Fluid.Singularity

/-- [definition] **The clock's rate** `2π |W|²` at a point, the factor between the orbit's and the fluid's time. -/
def clockRate (z₁ z₂ w : ℂ) : ℝ := 2 * Real.pi * Complex.normSq (W z₁ z₂ w)

/-- [proved-derived; formal-checked] The clock's rate is positive off the two sites. -/
theorem clockRate_pos {z₁ z₂ w : ℂ} (hW : W z₁ z₂ w ≠ 0) : 0 < clockRate z₁ z₂ w := by
  have := Real.pi_pos
  have := Complex.normSq_pos.mpr hW
  unfold clockRate
  positivity

/-- [proved-derived; formal-checked] **The rescaled field is the velocity**: `(2π|W|²)⁻¹ · conj c · W = conj F′`. -/
theorem clock_rescales_field (c : ℂ) {z₁ z₂ w : ℂ} (hW : W z₁ z₂ w ≠ 0) :
    (clockRate z₁ z₂ w)⁻¹ • (conj c * W z₁ z₂ w) = conj (c / (2 * Real.pi * W z₁ z₂ w)) := by
  have hr : ((clockRate z₁ z₂ w : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (clockRate_pos hW).ne'
  rw [Complex.real_smul, ← velocity_is_mobius_field c hW]
  have e : (2 * Real.pi * (Complex.normSq (W z₁ z₂ w) : ℂ)) = ((clockRate z₁ z₂ w : ℝ) : ℂ) := by
    simp [clockRate]
  rw [e]
  push_cast
  field_simp

/-- [proved-derived; formal-checked] **Through a local inverse of the clock, an orbit moves at `conj F′`.** -/
theorem particle_velocity (c : ℂ) {z₁ z₂ : ℂ} (h12 : z₁ ≠ z₂) {z : ℝ → ℂ} {T σ : ℝ → ℝ} {t : ℝ}
    (hflow : HasDerivAt z (mobiusField (generator (conj c) z₁ z₂) (z (σ t))) (σ t))
    (hW : W z₁ z₂ (z (σ t)) ≠ 0) (hclock : HasDerivAt T (clockRate z₁ z₂ (z (σ t))) (σ t))
    (hσ : ContinuousAt σ t) (hinv : ∀ᶠ y in 𝓝 t, T (σ y) = y) :
    HasDerivAt (fun y => z (σ y)) (conj (c / (2 * Real.pi * W z₁ z₂ (z (σ t))))) t := by
  have hσd := hclock.of_local_left_inverse hσ (clockRate_pos hW).ne' hinv
  rw [generator_field _ h12] at hflow
  have h := hflow.scomp t hσd
  rw [clock_rescales_field c hW] at h
  exact h

/-- [proved-standard; formal-checked] A continuous strictly increasing clock has a left inverse, continuous at each
reading and a right inverse near it. -/
theorem exists_left_inverse {T : ℝ → ℝ} (hT : StrictMono T) (hc : Continuous T) :
    ∃ σ : ℝ → ℝ, ∀ τ, σ (T τ) = τ ∧ ContinuousAt σ (T τ) ∧ ∀ᶠ y in 𝓝 (T τ), T (σ y) = y := by
  refine ⟨Function.invFun T, fun τ => ?_⟩
  have hleft : ∀ x, Function.invFun T (T x) = x := Function.leftInverse_invFun hT.injective
  have hlo : T (τ - 1) < T τ := hT (by linarith)
  have hhi : T τ < T (τ + 1) := hT (by linarith)
  have hS : Ioo (T (τ - 1)) (T (τ + 1)) ∈ 𝓝 (T τ) := Ioo_mem_nhds hlo hhi
  have hrange : ∀ y ∈ Ioo (T (τ - 1)) (T (τ + 1)), T (Function.invFun T y) = y := by
    intro y hy
    obtain ⟨x, -, hx⟩ := intermediate_value_Icc (by linarith : τ - 1 ≤ τ + 1) hc.continuousOn
      (Ioo_subset_Icc_self hy)
    exact Function.invFun_eq ⟨x, hx⟩
  refine ⟨hleft τ, ?_, Filter.mem_of_superset hS hrange⟩
  have hmono : StrictMonoOn (Function.invFun T) (Ioo (T (τ - 1)) (T (τ + 1))) := by
    intro y₁ hy₁ y₂ hy₂ h
    by_contra hle
    have := hT.monotone (not_lt.mp hle)
    rw [hrange y₁ hy₁, hrange y₂ hy₂] at this
    linarith
  refine hmono.continuousAt_of_image_mem_nhds hS ?_
  rw [hleft τ]
  refine Filter.mem_of_superset (Ioo_mem_nhds (by linarith : τ - 1 < τ) (by linarith : τ < τ + 1)) ?_
  intro x hx
  exact ⟨T x, ⟨hT hx.1, hT hx.2⟩, hleft x⟩

/-- [proved-derived; formal-checked] **The streamline orbits are the particle paths**: re-timed by its clock, an
orbit that avoids the sites moves at `u = conj F′` at every point. -/
theorem orbit_is_particle_path (c : ℂ) {z₁ z₂ : ℂ} (h12 : z₁ ≠ z₂) {z : ℝ → ℂ} {T : ℝ → ℝ}
    (hflow : ∀ τ, HasDerivAt z (mobiusField (generator (conj c) z₁ z₂) (z τ)) τ)
    (hW : ∀ τ, W z₁ z₂ (z τ) ≠ 0) (hclock : ∀ τ, HasDerivAt T (clockRate z₁ z₂ (z τ)) τ) :
    StrictMono T ∧ ∃ σ : ℝ → ℝ, ∀ τ, σ (T τ) = τ ∧
      HasDerivAt (fun t => z (σ t)) (conj (c / (2 * Real.pi * W z₁ z₂ (z τ)))) (T τ) := by
  have hT : StrictMono T := strictMono_of_hasDerivAt_pos hclock fun τ => clockRate_pos (hW τ)
  have hc : Continuous T := continuous_iff_continuousAt.mpr fun τ => (hclock τ).continuousAt
  obtain ⟨σ, hσ⟩ := exists_left_inverse hT hc
  refine ⟨hT, σ, fun τ => ⟨(hσ τ).1, ?_⟩⟩
  have e := (hσ τ).1
  have h := particle_velocity c h12 (t := T τ) (σ := σ) (T := T) (by rw [e]; exact hflow τ)
    (by rw [e]; exact hW τ) (by rw [e]; exact hclock τ) (hσ τ).2.1 (hσ τ).2.2
  rw [e] at h
  exact h

end Clock

/-! ## 2. Hill's spherical vortex: the stream functions and their velocities -/

/-- [definition] The distance `r = √(s² + z²)` from the vortex's centre. -/
def rad (s z : ℝ) : ℝ := √(s ^ 2 + z ^ 2)

/-- [proved-standard; formal-checked] `r² = s² + z²`. -/
theorem rad_sq (s z : ℝ) : rad s z ^ 2 = s ^ 2 + z ^ 2 := Real.sq_sqrt (by positivity)

/-- [proved-standard; formal-checked] `r > 0` off the axis. -/
theorem rad_pos {s z : ℝ} (hs : 0 < s) : 0 < rad s z := Real.sqrt_pos.mpr (by positivity)

/-- [proved-standard; formal-checked] `∂_s r = s / r` off the axis. -/
theorem hasDerivAt_rad_s {s : ℝ} (z : ℝ) (hs : 0 < s) :
    HasDerivAt (fun s => rad s z) (s / rad s z) s := by
  have hne : s ^ 2 + z ^ 2 ≠ 0 := by positivity
  have h := ((hasDerivAt_pow 2 s).add_const (z ^ 2)).sqrt hne
  refine h.congr_deriv ?_
  have : 0 < √(s ^ 2 + z ^ 2) := Real.sqrt_pos.mpr (by positivity)
  simp only [rad]
  field_simp
  ring

/-- [proved-standard; formal-checked] `∂_z r = z / r` off the axis. -/
theorem hasDerivAt_rad_z (s : ℝ) {z : ℝ} (hs : 0 < s) :
    HasDerivAt (fun z => rad s z) (z / rad s z) z := by
  have hne : s ^ 2 + z ^ 2 ≠ 0 := by positivity
  have h := ((hasDerivAt_pow 2 z).const_add (s ^ 2)).sqrt hne
  refine h.congr_deriv ?_
  have : 0 < √(s ^ 2 + z ^ 2) := Real.sqrt_pos.mpr (by positivity)
  simp only [rad]
  field_simp
  ring

/-- [definition] Stokes' stream function inside the sphere, `ψ_in = (3U/4) s² (1 − r²/a²)`. -/
def streamIn (U a s z : ℝ) : ℝ := 3 * U / 4 * s ^ 2 * (1 - (s ^ 2 + z ^ 2) / a ^ 2)

/-- [definition] Stokes' stream function outside the sphere, `ψ_out = −(U/2) s² (1 − a³/r³)`. -/
def streamOut (U a s z : ℝ) : ℝ := -(U / 2) * s ^ 2 * (1 - a ^ 3 / rad s z ^ 3)

/-- [definition] The radial velocity inside, `u_s = (3U/2a²) s z`. -/
def velSIn (U a s z : ℝ) : ℝ := 3 * U / (2 * a ^ 2) * s * z

/-- [definition] The axial velocity inside, `u_z = (3U/2a²) (a² − 2s² − z²)`. -/
def velZIn (U a s z : ℝ) : ℝ := 3 * U / (2 * a ^ 2) * (a ^ 2 - 2 * s ^ 2 - z ^ 2)

/-- [definition] The radial velocity outside, `u_s = 3Ua³ s z / 2r⁵`. -/
def velSOut (U a s z : ℝ) : ℝ := 3 * U * a ^ 3 * s * z / (2 * rad s z ^ 5)

/-- [definition] The axial velocity outside, `u_z = −U (1 − a³/r³) − 3Ua³ s² / 2r⁵`. -/
def velZOut (U a s z : ℝ) : ℝ :=
  -U * (1 - a ^ 3 / rad s z ^ 3) - 3 * U * a ^ 3 * s ^ 2 / (2 * rad s z ^ 5)

/-- [proved-standard; formal-checked] Inside, `∂_s ψ = s u_z`. -/
theorem hasDerivAt_streamIn_s (U a s z : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun s => streamIn U a s z) (s * velZIn U a s z) s := by
  have h := ((hasDerivAt_pow 2 s).const_mul (3 * U / 4)).mul
    ((((hasDerivAt_pow 2 s).add_const (z ^ 2)).div_const (a ^ 2)).const_sub 1)
  refine h.congr_deriv ?_
  simp only [velZIn]
  field_simp
  ring

/-- [proved-standard; formal-checked] Inside, `∂_z ψ = −s u_s`. -/
theorem hasDerivAt_streamIn_z (U a s z : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun z => streamIn U a s z) (-(s * velSIn U a s z)) z := by
  have h := ((((hasDerivAt_pow 2 z).const_add (s ^ 2)).div_const (a ^ 2)).const_sub 1).const_mul
    (3 * U / 4 * s ^ 2)
  refine h.congr_deriv ?_
  simp only [velSIn]
  field_simp
  ring

/-- [proved-standard; formal-checked] Outside, `∂_s ψ = s u_z`. -/
theorem hasDerivAt_streamOut_s (U a : ℝ) {s : ℝ} (z : ℝ) (hs : 0 < s) :
    HasDerivAt (fun s => streamOut U a s z) (s * velZOut U a s z) s := by
  have hr := rad_pos (z := z) hs
  have h := ((hasDerivAt_pow 2 s).const_mul (-(U / 2))).fun_mul
    (((hasDerivAt_const s (a ^ 3)).fun_div ((hasDerivAt_rad_s z hs).fun_pow 3)
      (by positivity)).const_sub 1)
  refine h.congr_deriv ?_
  simp only [velZOut]
  field_simp
  ring

/-- [proved-standard; formal-checked] Outside, `∂_z ψ = −s u_s`. -/
theorem hasDerivAt_streamOut_z (U a : ℝ) {s : ℝ} (z : ℝ) (hs : 0 < s) :
    HasDerivAt (fun z => streamOut U a s z) (-(s * velSOut U a s z)) z := by
  have hr := rad_pos (z := z) hs
  have h := (((hasDerivAt_const z (a ^ 3)).fun_div ((hasDerivAt_rad_z s hs).fun_pow 3)
    (by positivity)).const_sub 1).const_mul (-(U / 2) * s ^ 2)
  refine h.congr_deriv ?_
  simp only [velSOut]
  field_simp
  ring

/-- [proved-standard; formal-checked] Inside, `∂_s u_s = (3U/2a²) z`. -/
theorem hasDerivAt_velSIn_s (U a s z : ℝ) :
    HasDerivAt (fun s => velSIn U a s z) (3 * U / (2 * a ^ 2) * z) s := by
  refine (((hasDerivAt_id' s).const_mul (3 * U / (2 * a ^ 2))).mul_const z).congr_deriv ?_
  ring

/-- [proved-standard; formal-checked] Inside, `∂_z u_s = (3U/2a²) s`. -/
theorem hasDerivAt_velSIn_z (U a s z : ℝ) :
    HasDerivAt (fun z => velSIn U a s z) (3 * U / (2 * a ^ 2) * s) z := by
  refine ((hasDerivAt_id' z).const_mul (3 * U / (2 * a ^ 2) * s)).congr_deriv ?_
  ring

/-- [proved-standard; formal-checked] Inside, `∂_s u_z = (3U/2a²)(−4s)`. -/
theorem hasDerivAt_velZIn_s (U a s z : ℝ) :
    HasDerivAt (fun s => velZIn U a s z) (3 * U / (2 * a ^ 2) * (-4 * s)) s := by
  refine (((((hasDerivAt_pow 2 s).const_mul 2).const_sub (a ^ 2)).sub_const (z ^ 2)).const_mul
    (3 * U / (2 * a ^ 2))).congr_deriv ?_
  ring

/-- [proved-standard; formal-checked] Inside, `∂_z u_z = (3U/2a²)(−2z)`. -/
theorem hasDerivAt_velZIn_z (U a s z : ℝ) :
    HasDerivAt (fun z => velZIn U a s z) (3 * U / (2 * a ^ 2) * (-2 * z)) z := by
  refine (((hasDerivAt_pow 2 z).const_sub (a ^ 2 - 2 * s ^ 2)).const_mul
    (3 * U / (2 * a ^ 2))).congr_deriv ?_
  ring

/-- [proved-standard; formal-checked] Outside, `∂_s u_s = 3Ua³ z (r² − 5s²) / 2r⁷`. -/
theorem hasDerivAt_velSOut_s (U a : ℝ) {s : ℝ} (z : ℝ) (hs : 0 < s) :
    HasDerivAt (fun s => velSOut U a s z)
      (3 * U * a ^ 3 * z * (rad s z ^ 2 - 5 * s ^ 2) / (2 * rad s z ^ 7)) s := by
  have hr := rad_pos (z := z) hs
  have h := (((hasDerivAt_id' s).const_mul (3 * U * a ^ 3)).mul_const z).fun_div
    (((hasDerivAt_rad_s z hs).fun_pow 5).const_mul 2) (by positivity)
  refine h.congr_deriv ?_
  field_simp
  ring

/-- [proved-standard; formal-checked] Outside, `∂_z u_s = 3Ua³ s (r² − 5z²) / 2r⁷`. -/
theorem hasDerivAt_velSOut_z (U a : ℝ) {s : ℝ} (z : ℝ) (hs : 0 < s) :
    HasDerivAt (fun z => velSOut U a s z)
      (3 * U * a ^ 3 * s * (rad s z ^ 2 - 5 * z ^ 2) / (2 * rad s z ^ 7)) z := by
  have hr := rad_pos (z := z) hs
  have h := ((hasDerivAt_id' z).const_mul (3 * U * a ^ 3 * s)).fun_div
    (((hasDerivAt_rad_z s hs).fun_pow 5).const_mul 2) (by positivity)
  refine h.congr_deriv ?_
  field_simp
  ring

/-- [proved-standard; formal-checked] Outside, `∂_s u_z = 3Ua³ s (5s² − 4r²) / 2r⁷`. -/
theorem hasDerivAt_velZOut_s (U a : ℝ) {s : ℝ} (z : ℝ) (hs : 0 < s) :
    HasDerivAt (fun s => velZOut U a s z)
      (3 * U * a ^ 3 * s * (5 * s ^ 2 - 4 * rad s z ^ 2) / (2 * rad s z ^ 7)) s := by
  have hr := rad_pos (z := z) hs
  have h1 := (((hasDerivAt_const s (a ^ 3)).fun_div ((hasDerivAt_rad_s z hs).fun_pow 3)
    (by positivity)).const_sub 1).const_mul (-U)
  have h2 := ((hasDerivAt_pow 2 s).const_mul (3 * U * a ^ 3)).fun_div
    (((hasDerivAt_rad_s z hs).fun_pow 5).const_mul 2) (by positivity)
  refine (h1.sub h2).congr_deriv ?_
  field_simp
  ring

/-- [proved-standard; formal-checked] Outside, `∂_z u_z = 3Ua³ z (5s² − 2r²) / 2r⁷`. -/
theorem hasDerivAt_velZOut_z (U a : ℝ) {s : ℝ} (z : ℝ) (hs : 0 < s) :
    HasDerivAt (fun z => velZOut U a s z)
      (3 * U * a ^ 3 * z * (5 * s ^ 2 - 2 * rad s z ^ 2) / (2 * rad s z ^ 7)) z := by
  have hr := rad_pos (z := z) hs
  have h1 := (((hasDerivAt_const z (a ^ 3)).fun_div ((hasDerivAt_rad_z s hs).fun_pow 3)
    (by positivity)).const_sub 1).const_mul (-U)
  have h2 := (hasDerivAt_const z (3 * U * a ^ 3 * s ^ 2)).fun_div
    (((hasDerivAt_rad_z s hs).fun_pow 5).const_mul 2) (by positivity)
  refine (h1.sub h2).congr_deriv ?_
  field_simp
  ring

/-! ## 3. Continuity, vorticity and Stokes' operator -/

/-- [definition] **The azimuthal vorticity** `ω = ∂_z u_s − ∂_s u_z`, read along the coordinate lines. -/
def vorticity (us uz : ℝ → ℝ → ℝ) (s z : ℝ) : ℝ :=
  deriv (fun z => us s z) z - deriv (fun s => uz s z) s

/-- [definition] **Stokes' operator** `E²ψ = ∂²_s ψ − (1/s) ∂_s ψ + ∂²_z ψ`. -/
def stokesOperator (ψ : ℝ → ℝ → ℝ) (s z : ℝ) : ℝ :=
  deriv (fun s => deriv (fun s => ψ s z) s) s - deriv (fun s => ψ s z) s / s +
    deriv (fun z => deriv (fun z => ψ s z) z) z

/-- [proved-standard; formal-checked] **Inside, the flow is divergence-free**: `∂_s(s u_s) + s ∂_z u_z = 0`. -/
theorem continuity_in (U a s z : ℝ) :
    deriv (fun s => s * velSIn U a s z) s + s * deriv (fun z => velZIn U a s z) z = 0 := by
  rw [((hasDerivAt_id' s).fun_mul (hasDerivAt_velSIn_s U a s z)).deriv,
    (hasDerivAt_velZIn_z U a s z).deriv]
  simp only [velSIn]
  ring

/-- [proved-standard; formal-checked] **Outside, the flow is divergence-free**: `∂_s(s u_s) + s ∂_z u_z = 0`. -/
theorem continuity_out (U a : ℝ) {s : ℝ} (z : ℝ) (hs : 0 < s) :
    deriv (fun s => s * velSOut U a s z) s + s * deriv (fun z => velZOut U a s z) z = 0 := by
  have hr := rad_pos (z := z) hs
  rw [((hasDerivAt_id' s).fun_mul (hasDerivAt_velSOut_s U a z hs)).deriv,
    (hasDerivAt_velZOut_z U a z hs).deriv]
  simp only [velSOut]
  field_simp
  ring

/-- [proved-standard; formal-checked] **Inside, `ω = (15U/2a²) s`**, so `ω/s` is constant. -/
theorem vorticity_in (U a s z : ℝ) :
    vorticity (velSIn U a) (velZIn U a) s z = 15 * U / (2 * a ^ 2) * s := by
  rw [vorticity, (hasDerivAt_velSIn_z U a s z).deriv, (hasDerivAt_velZIn_s U a s z).deriv]
  ring

/-- [proved-standard; formal-checked] **Outside, the flow is irrotational**, `ω = 0`. -/
theorem vorticity_out (U a : ℝ) {s : ℝ} (z : ℝ) (hs : 0 < s) :
    vorticity (velSOut U a) (velZOut U a) s z = 0 := by
  rw [vorticity, (hasDerivAt_velSOut_z U a z hs).deriv, (hasDerivAt_velZOut_s U a z hs).deriv,
    div_sub_div_same, div_eq_zero_iff]
  left
  linear_combination (15 * U * a ^ 3 * s) * rad_sq s z

/-- [proved-standard; formal-checked] **Inside, `E²ψ = −15U s² / 2a²`.** -/
theorem stokesOperator_in (U a s z : ℝ) (ha : a ≠ 0) (hs : s ≠ 0) :
    stokesOperator (streamIn U a) s z = -(15 * U * s ^ 2 / (2 * a ^ 2)) := by
  have e1 : (fun s => deriv (fun s => streamIn U a s z) s) = fun s => s * velZIn U a s z :=
    funext fun s => (hasDerivAt_streamIn_s U a s z ha).deriv
  have e2 : (fun z => deriv (fun z => streamIn U a s z) z) = fun z => -(s * velSIn U a s z) :=
    funext fun z => (hasDerivAt_streamIn_z U a s z ha).deriv
  rw [stokesOperator, e1, e2, ((hasDerivAt_id' s).fun_mul (hasDerivAt_velZIn_s U a s z)).deriv,
    (((hasDerivAt_velSIn_z U a s z).const_mul s).fun_neg).deriv, (hasDerivAt_streamIn_s U a s z ha).deriv]
  simp only [velZIn]
  field_simp
  ring

/-- [proved-standard; formal-checked] **Outside, `E²ψ = 0`.** -/
theorem stokesOperator_out (U a : ℝ) {s : ℝ} (z : ℝ) (hs : 0 < s) :
    stokesOperator (streamOut U a) s z = 0 := by
  have e1 : (fun s => deriv (fun s => streamOut U a s z) s) =ᶠ[𝓝 s] fun s => s * velZOut U a s z := by
    filter_upwards [lt_mem_nhds hs] with s' hs' using (hasDerivAt_streamOut_s U a z hs').deriv
  have e2 : (fun z => deriv (fun z => streamOut U a s z) z) = fun z => -(s * velSOut U a s z) :=
    funext fun z => (hasDerivAt_streamOut_z U a z hs).deriv
  have hω := vorticity_out U a z hs
  rw [vorticity, (hasDerivAt_velSOut_z U a z hs).deriv, (hasDerivAt_velZOut_s U a z hs).deriv] at hω
  rw [stokesOperator, e1.deriv_eq, e2, ((hasDerivAt_id' s).fun_mul (hasDerivAt_velZOut_s U a z hs)).deriv,
    (((hasDerivAt_velSOut_z U a z hs).const_mul s).fun_neg).deriv, (hasDerivAt_streamOut_s U a z hs).deriv,
    mul_div_cancel_left₀ _ hs.ne']
  linear_combination (-s) * hω

/-- [proved-standard; formal-checked] **Inside, `ω/s` is carried along the flow**, `u·∇(ω/s) = 0`. -/
theorem vorticity_transported_in (U a : ℝ) {s : ℝ} (z : ℝ) (hs : s ≠ 0) :
    velSIn U a s z * deriv (fun s => vorticity (velSIn U a) (velZIn U a) s z / s) s +
      velZIn U a s z * deriv (fun z => vorticity (velSIn U a) (velZIn U a) s z / s) z = 0 := by
  have e1 : (fun s => vorticity (velSIn U a) (velZIn U a) s z / s) =ᶠ[𝓝 s]
      fun _ => 15 * U / (2 * a ^ 2) := by
    filter_upwards [isOpen_ne.mem_nhds hs] with s' hs'
    rw [vorticity_in]
    field_simp
  have e2 : (fun z => vorticity (velSIn U a) (velZIn U a) s z / s) = fun _ => 15 * U / (2 * a ^ 2) :=
    funext fun z => by rw [vorticity_in]; field_simp
  rw [e1.deriv_eq, e2]
  simp

/-- [proved-standard; formal-checked] **Outside, `ω/s = 0` is carried along the flow**, `u·∇(ω/s) = 0`. -/
theorem vorticity_transported_out (U a : ℝ) {s : ℝ} (z : ℝ) (hs : 0 < s) :
    velSOut U a s z * deriv (fun s => vorticity (velSOut U a) (velZOut U a) s z / s) s +
      velZOut U a s z * deriv (fun z => vorticity (velSOut U a) (velZOut U a) s z / s) z = 0 := by
  have e1 : (fun s => vorticity (velSOut U a) (velZOut U a) s z / s) =ᶠ[𝓝 s] fun _ => 0 := by
    filter_upwards [lt_mem_nhds hs] with s' hs'
    rw [vorticity_out U a z hs', zero_div]
  have e2 : (fun z => vorticity (velSOut U a) (velZOut U a) s z / s) = fun _ => 0 :=
    funext fun z => by rw [vorticity_out U a z hs, zero_div]
  rw [e1.deriv_eq, e2]
  simp

/-! ## 4. The steady momentum balance -/

/-- [definition] **Bernoulli's pressure** `p = H − A ψ − ½|u|²` of a meridian flow whose vorticity is `A s`. -/
def bernoulliPressure (H A : ℝ) (ψ us uz : ℝ → ℝ → ℝ) (s z : ℝ) : ℝ :=
  H - A * ψ s z - (us s z ^ 2 + uz s z ^ 2) / 2

/-- [proved-standard; formal-checked] **Vorticity `A s` balances Bernoulli's pressure**: `∂p = −(u·∇)u` along both
coordinate lines, so the Bernoulli head `H − Aψ` has gradient `−A ∇ψ`, the vortex force. -/
theorem momentum_balance {ψ us uz : ℝ → ℝ → ℝ} {H A s z us_s us_z uz_s uz_z : ℝ}
    (hψs : HasDerivAt (fun s => ψ s z) (s * uz s z) s)
    (hψz : HasDerivAt (fun z => ψ s z) (-(s * us s z)) z)
    (hus_s : HasDerivAt (fun s => us s z) us_s s) (hus_z : HasDerivAt (fun z => us s z) us_z z)
    (huz_s : HasDerivAt (fun s => uz s z) uz_s s) (huz_z : HasDerivAt (fun z => uz s z) uz_z z)
    (hω : us_z - uz_s = A * s) :
    HasDerivAt (fun s => bernoulliPressure H A ψ us uz s z) (-(us s z * us_s + uz s z * us_z)) s ∧
      HasDerivAt (fun z => bernoulliPressure H A ψ us uz s z)
        (-(us s z * uz_s + uz s z * uz_z)) z := by
  constructor
  · refine ((((hψs.const_mul A).const_sub H).sub
      (((hus_s.fun_pow 2).add (huz_s.fun_pow 2)).div_const 2))).congr_deriv ?_
    push_cast
    linear_combination (uz s z) * hω
  · refine ((((hψz.const_mul A).const_sub H).sub
      (((hus_z.fun_pow 2).add (huz_z.fun_pow 2)).div_const 2))).congr_deriv ?_
    push_cast
    linear_combination (-us s z) * hω

/-- [definition] The pressure inside, Bernoulli's with `A = 15U/2a²` and `H = p∞ + U²/2`. -/
def pressureIn (U a pinf : ℝ) : ℝ → ℝ → ℝ :=
  bernoulliPressure (pinf + U ^ 2 / 2) (15 * U / (2 * a ^ 2)) (streamIn U a) (velSIn U a) (velZIn U a)

/-- [definition] The pressure outside, Bernoulli's with `A = 0` and `H = p∞ + U²/2`. -/
def pressureOut (U a pinf : ℝ) : ℝ → ℝ → ℝ :=
  bernoulliPressure (pinf + U ^ 2 / 2) 0 (streamOut U a) (velSOut U a) (velZOut U a)

/-- [proved-standard; formal-checked] **Inside, Hill's flow is a steady Euler flow** with its explicit pressure. -/
theorem euler_in (U a pinf s z : ℝ) (ha : a ≠ 0) :
    velSIn U a s z * deriv (fun s => velSIn U a s z) s + velZIn U a s z * deriv (fun z => velSIn U a s z) z +
        deriv (fun s => pressureIn U a pinf s z) s = 0 ∧
      velSIn U a s z * deriv (fun s => velZIn U a s z) s + velZIn U a s z * deriv (fun z => velZIn U a s z) z +
        deriv (fun z => pressureIn U a pinf s z) z = 0 := by
  have hω : 3 * U / (2 * a ^ 2) * s - 3 * U / (2 * a ^ 2) * (-4 * s) = 15 * U / (2 * a ^ 2) * s := by ring
  obtain ⟨hs, hz⟩ := momentum_balance (H := pinf + U ^ 2 / 2) (hasDerivAt_streamIn_s U a s z ha)
    (hasDerivAt_streamIn_z U a s z ha) (hasDerivAt_velSIn_s U a s z) (hasDerivAt_velSIn_z U a s z)
    (hasDerivAt_velZIn_s U a s z) (hasDerivAt_velZIn_z U a s z) hω
  rw [(hasDerivAt_velSIn_s U a s z).deriv, (hasDerivAt_velSIn_z U a s z).deriv,
    (hasDerivAt_velZIn_s U a s z).deriv, (hasDerivAt_velZIn_z U a s z).deriv]
  exact ⟨by rw [pressureIn, hs.deriv]; ring, by rw [pressureIn, hz.deriv]; ring⟩

/-- [proved-standard; formal-checked] **Outside, Hill's flow is a steady Euler flow** with its explicit pressure. -/
theorem euler_out (U a pinf : ℝ) {s : ℝ} (z : ℝ) (hs : 0 < s) :
    velSOut U a s z * deriv (fun s => velSOut U a s z) s +
        velZOut U a s z * deriv (fun z => velSOut U a s z) z + deriv (fun s => pressureOut U a pinf s z) s = 0 ∧
      velSOut U a s z * deriv (fun s => velZOut U a s z) s +
        velZOut U a s z * deriv (fun z => velZOut U a s z) z + deriv (fun z => pressureOut U a pinf s z) z = 0 := by
  have hω := vorticity_out U a z hs
  rw [vorticity, (hasDerivAt_velSOut_z U a z hs).deriv, (hasDerivAt_velZOut_s U a z hs).deriv] at hω
  obtain ⟨h1, h2⟩ := momentum_balance (H := pinf + U ^ 2 / 2) (A := 0) (hasDerivAt_streamOut_s U a z hs)
    (hasDerivAt_streamOut_z U a z hs) (hasDerivAt_velSOut_s U a z hs) (hasDerivAt_velSOut_z U a z hs)
    (hasDerivAt_velZOut_s U a z hs) (hasDerivAt_velZOut_z U a z hs) (by rw [hω]; ring)
  rw [(hasDerivAt_velSOut_s U a z hs).deriv, (hasDerivAt_velSOut_z U a z hs).deriv,
    (hasDerivAt_velZOut_s U a z hs).deriv, (hasDerivAt_velZOut_z U a z hs).deriv]
  exact ⟨by rw [pressureOut, h1.deriv]; ring, by rw [pressureOut, h2.deriv]; ring⟩

/-! ## 5. The dividing sphere -/

/-- [proved-standard; formal-checked] On the sphere `r = a`. -/
theorem rad_sphere {s z a : ℝ} (ha : 0 < a) (h : s ^ 2 + z ^ 2 = a ^ 2) : rad s z = a := by
  rw [rad, h, Real.sqrt_sq ha.le]

/-- [proved-standard; formal-checked] The inner stream function vanishes on the sphere. -/
theorem streamIn_sphere (U : ℝ) {a s z : ℝ} (ha : a ≠ 0) (h : s ^ 2 + z ^ 2 = a ^ 2) :
    streamIn U a s z = 0 := by
  rw [streamIn, h, div_self (pow_ne_zero 2 ha), sub_self, mul_zero]

/-- [proved-standard; formal-checked] The outer stream function vanishes on the sphere. -/
theorem streamOut_sphere (U : ℝ) {a s z : ℝ} (ha : 0 < a) (h : s ^ 2 + z ^ 2 = a ^ 2) :
    streamOut U a s z = 0 := by
  rw [streamOut, rad_sphere ha h, div_self (pow_ne_zero 3 ha.ne'), sub_self, mul_zero]

/-- [proved-standard; formal-checked] **Both velocity components match on the sphere**: no vortex sheet. -/
theorem velocity_match_sphere (U : ℝ) {a s z : ℝ} (ha : 0 < a) (h : s ^ 2 + z ^ 2 = a ^ 2) :
    velSIn U a s z = velSOut U a s z ∧ velZIn U a s z = velZOut U a s z := by
  have ha' := ha.ne'
  simp only [velSIn, velSOut, velZIn, velZOut, rad_sphere ha h]
  constructor
  · field_simp
  · field_simp
    linear_combination (-3 * U) * h

/-- [proved-standard; formal-checked] **The velocity is tangent to the sphere from both sides**: `s u_s + z u_z = 0`. -/
theorem velocity_tangent_sphere (U : ℝ) {a s z : ℝ} (ha : 0 < a) (h : s ^ 2 + z ^ 2 = a ^ 2) :
    s * velSIn U a s z + z * velZIn U a s z = 0 ∧ s * velSOut U a s z + z * velZOut U a s z = 0 := by
  have hin : s * velSIn U a s z + z * velZIn U a s z = 0 := by
    simp only [velSIn, velZIn]
    linear_combination (-(3 * U / (2 * a ^ 2)) * z) * h
  obtain ⟨h1, h2⟩ := velocity_match_sphere U ha h
  exact ⟨hin, by rw [← h1, ← h2]; exact hin⟩

/-- [proved-standard; formal-checked] **The pressure matches on the sphere.** -/
theorem pressure_match_sphere (U pinf : ℝ) {a s z : ℝ} (ha : 0 < a) (h : s ^ 2 + z ^ 2 = a ^ 2) :
    pressureIn U a pinf s z = pressureOut U a pinf s z := by
  obtain ⟨h1, h2⟩ := velocity_match_sphere U ha h
  simp only [pressureIn, pressureOut, bernoulliPressure, streamIn_sphere U ha.ne' h,
    streamOut_sphere U ha h, h1, h2]
  ring

/-- [proved-standard; formal-checked] Strictly inside the sphere, off the axis, `ψ > 0`. -/
theorem streamIn_pos {U a s z : ℝ} (hU : 0 < U) (ha : a ≠ 0) (hs : s ≠ 0) (h : s ^ 2 + z ^ 2 < a ^ 2) :
    0 < streamIn U a s z := by
  have ha2 : 0 < a ^ 2 := by positivity
  have : (s ^ 2 + z ^ 2) / a ^ 2 < 1 := (div_lt_one ha2).mpr h
  unfold streamIn
  have : 0 < s ^ 2 := by positivity
  have : 0 < 1 - (s ^ 2 + z ^ 2) / a ^ 2 := by linarith
  positivity

/-- [proved-standard; formal-checked] Strictly outside the sphere, off the axis, `ψ < 0`. -/
theorem streamOut_neg {U a s z : ℝ} (hU : 0 < U) (ha : 0 < a) (hs : 0 < s) (h : a ^ 2 < s ^ 2 + z ^ 2) :
    streamOut U a s z < 0 := by
  have hr := rad_pos (z := z) hs
  have har : a < rad s z := by
    rw [← rad_sq] at h
    exact (pow_lt_pow_iff_left₀ ha.le hr.le two_ne_zero).mp h
  have : a ^ 3 / rad s z ^ 3 < 1 :=
    (div_lt_one (by positivity)).mpr (pow_lt_pow_left₀ har ha.le three_ne_zero)
  have : 0 < 1 - a ^ 3 / rad s z ^ 3 := by linarith
  unfold streamOut
  have : 0 < U / 2 * s ^ 2 * (1 - a ^ 3 / rad s z ^ 3) := by positivity
  linarith

/-! ## 6. The far field: a uniform stream and a dipole -/

/-- [proved-standard; formal-checked] **The outer stream function is the stream plus a dipole's.** -/
theorem streamOut_eq_uniform_add_dipole (U a s z : ℝ) :
    streamOut U a s z = -(U / 2) * s ^ 2 + U * a ^ 3 / 2 * (s ^ 2 / rad s z ^ 3) := by
  unfold streamOut
  ring

/-- [definition] **The outer velocity potential** `φ = −U z − (Ua³/2) z/r³`: the stream and a dipole of `Ua³/2`. -/
def potentialOut (U a s z : ℝ) : ℝ := -U * z - U * a ^ 3 / 2 * (z / rad s z ^ 3)

/-- [proved-standard; formal-checked] `∂_s φ = u_s` outside. -/
theorem hasDerivAt_potentialOut_s (U a : ℝ) {s : ℝ} (z : ℝ) (hs : 0 < s) :
    HasDerivAt (fun s => potentialOut U a s z) (velSOut U a s z) s := by
  have hr := rad_pos (z := z) hs
  have h := (((hasDerivAt_const s z).fun_div ((hasDerivAt_rad_s z hs).fun_pow 3)
    (by positivity)).const_mul (U * a ^ 3 / 2)).const_sub (-U * z)
  refine h.congr_deriv ?_
  simp only [velSOut]
  field_simp
  ring

/-- [proved-standard; formal-checked] `∂_z φ = u_z` outside. -/
theorem hasDerivAt_potentialOut_z (U a : ℝ) {s : ℝ} (z : ℝ) (hs : 0 < s) :
    HasDerivAt (fun z => potentialOut U a s z) (velZOut U a s z) z := by
  have hr := rad_pos (z := z) hs
  have h := ((hasDerivAt_id' z).const_mul (-U)).sub (((hasDerivAt_id' z).fun_div
    ((hasDerivAt_rad_z s hs).fun_pow 3) (by positivity)).const_mul (U * a ^ 3 / 2))
  refine h.congr_deriv ?_
  simp only [velZOut]
  field_simp
  linear_combination (-3 * U * a ^ 3 * rad s z ^ 2) * rad_sq s z

/-- [proved-standard; formal-checked] **The far field**: the dipole's stream decays as `1/r`, its velocity as `1/r³`. -/
theorem far_field {U a s : ℝ} (z : ℝ) (hU : 0 ≤ U) (ha : 0 ≤ a) (hs : 0 < s) :
    |streamOut U a s z + U / 2 * s ^ 2| ≤ U * a ^ 3 / (2 * rad s z) ∧
      |velSOut U a s z| ≤ 3 * U * a ^ 3 / (4 * rad s z ^ 3) ∧
      |velZOut U a s z + U| ≤ U * a ^ 3 / rad s z ^ 3 := by
  have hr := rad_pos (z := z) hs
  have hr2 := rad_sq s z
  have hUa : 0 ≤ U * a ^ 3 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have e : streamOut U a s z + U / 2 * s ^ 2 = U * a ^ 3 * s ^ 2 / (2 * rad s z ^ 3) := by
      unfold streamOut; field_simp; ring
    rw [e, abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
    have : U * a ^ 3 * (2 * rad s z ^ 3) - U * a ^ 3 * s ^ 2 * (2 * rad s z) =
        2 * (U * a ^ 3) * (rad s z * z ^ 2) := by
      linear_combination (2 * U * a ^ 3 * rad s z) * hr2
    have : 0 ≤ 2 * (U * a ^ 3) * (rad s z * z ^ 2) := by positivity
    linarith
  · have h2 : 2 * s * |z| ≤ rad s z ^ 2 := by
      rw [hr2]; nlinarith [sq_nonneg (s - |z|), sq_abs z]
    rw [velSOut, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * rad s z ^ 5), abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ 3 * U * a ^ 3 * s), div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 3 * U * a ^ 3 * (2 * rad s z ^ 3))
    nlinarith
  · have e : velZOut U a s z + U = U * a ^ 3 * (2 * rad s z ^ 2 - 3 * s ^ 2) / (2 * rad s z ^ 5) := by
      unfold velZOut; field_simp; ring
    have hb : |2 * rad s z ^ 2 - 3 * s ^ 2| ≤ 2 * rad s z ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg z, sq_nonneg s]
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * rad s z ^ 5), abs_mul, abs_of_nonneg hUa,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ U * a ^ 3 * rad s z ^ 3)
    nlinarith

/-! ## 7. One flow across the sphere -/

/-- [proved-standard; formal-checked] **Two charts with one value and one derivative at a point glue there**,
whatever set decides between them. -/
theorem hasDerivAt_ite_of_eq {f g : ℝ → ℝ} {p : ℝ → Prop} [DecidablePred p] {d x : ℝ}
    (hf : HasDerivAt f d x) (hg : HasDerivAt g d x) (hfg : f x = g x) :
    HasDerivAt (fun y => if p y then f y else g y) d x := by
  rw [hasDerivAt_iff_isLittleO] at *
  have hx : (if p x then f x else g x) = g x := by split_ifs <;> simp [hfg]
  refine (Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun y => ?_)).trans_isLittleO
    (hf.norm_left.add hg.norm_left)
  simp only [hx, one_mul]
  refine le_trans ?_ (Real.le_norm_self _)
  split_ifs
  · rw [hfg]; exact le_add_of_nonneg_right (norm_nonneg _)
  · exact le_add_of_nonneg_left (norm_nonneg _)

/-- [proved-standard; formal-checked] **Two charts continuous at a point, with one value there, glue continuously.** -/
theorem continuousAt_ite_of_eq {X : Type*} [TopologicalSpace X] {f g : X → ℝ} {p : X → Prop}
    [DecidablePred p] {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) (hfg : f x = g x) :
    ContinuousAt (fun y => if p y then f y else g y) x := by
  have hx : (if p x then f x else g x) = f x := by split_ifs <;> simp [hfg]
  show Tendsto _ _ (𝓝 (if p x then f x else g x))
  rw [hx]
  exact Filter.Tendsto.if (hf.tendsto.mono_left inf_le_left)
    (by rw [hfg]; exact hg.tendsto.mono_left inf_le_left)

/-- [definition] **The one flow's chart**: the inner chart on the closed ball `r ≤ a`, the outer one beyond. -/
def hillSide (a : ℝ) (f g : ℝ → ℝ → ℝ) (s z : ℝ) : ℝ := if s ^ 2 + z ^ 2 ≤ a ^ 2 then f s z else g s z

/-- [definition] **Hill's stream function**, one function on the meridian half-plane. -/
def hillStream (U a : ℝ) : ℝ → ℝ → ℝ := hillSide a (streamIn U a) (streamOut U a)

/-- [definition] Hill's radial velocity. -/
def hillVelS (U a : ℝ) : ℝ → ℝ → ℝ := hillSide a (velSIn U a) (velSOut U a)

/-- [definition] Hill's axial velocity. -/
def hillVelZ (U a : ℝ) : ℝ → ℝ → ℝ := hillSide a (velZIn U a) (velZOut U a)

/-- [definition] Hill's pressure, with far pressure `p∞`. -/
def hillPressure (U a pinf : ℝ) : ℝ → ℝ → ℝ := hillSide a (pressureIn U a pinf) (pressureOut U a pinf)

/-- [proved-standard; formal-checked] The one flow's chart has the side's derivative along `s`, the sphere included. -/
theorem hillSide_hasDerivAt_s {a s z df dg : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : s ^ 2 + z ^ 2 ≤ a ^ 2 → HasDerivAt (fun s => f s z) df s)
    (hg : a ^ 2 ≤ s ^ 2 + z ^ 2 → HasDerivAt (fun s => g s z) dg s)
    (hsph : s ^ 2 + z ^ 2 = a ^ 2 → f s z = g s z ∧ df = dg) :
    HasDerivAt (fun s => hillSide a f g s z) (if s ^ 2 + z ^ 2 ≤ a ^ 2 then df else dg) s := by
  have hc : Continuous fun s : ℝ => s ^ 2 + z ^ 2 := by fun_prop
  rcases lt_trichotomy (s ^ 2 + z ^ 2) (a ^ 2) with h | h | h
  · rw [if_pos h.le]
    refine (hf h.le).congr_of_eventuallyEq ?_
    filter_upwards [hc.continuousAt.eventually_lt continuousAt_const h] with s' hs'
    simp only [hillSide, if_pos hs'.le]
  · rw [if_pos h.le]
    obtain ⟨hv, hd⟩ := hsph h
    exact hasDerivAt_ite_of_eq (p := fun y => y ^ 2 + z ^ 2 ≤ a ^ 2) (hf h.le) (hd ▸ hg h.ge) hv
  · rw [if_neg (not_le.mpr h)]
    refine (hg h.le).congr_of_eventuallyEq ?_
    filter_upwards [continuousAt_const.eventually_lt hc.continuousAt h] with s' hs'
    simp only [hillSide, if_neg (not_le.mpr hs')]

/-- [proved-standard; formal-checked] The one flow's chart has the side's derivative along `z`, the sphere included. -/
theorem hillSide_hasDerivAt_z {a s z df dg : ℝ} {f g : ℝ → ℝ → ℝ}
    (hf : s ^ 2 + z ^ 2 ≤ a ^ 2 → HasDerivAt (fun z => f s z) df z)
    (hg : a ^ 2 ≤ s ^ 2 + z ^ 2 → HasDerivAt (fun z => g s z) dg z)
    (hsph : s ^ 2 + z ^ 2 = a ^ 2 → f s z = g s z ∧ df = dg) :
    HasDerivAt (fun z => hillSide a f g s z) (if s ^ 2 + z ^ 2 ≤ a ^ 2 then df else dg) z := by
  have hc : Continuous fun z : ℝ => s ^ 2 + z ^ 2 := by fun_prop
  rcases lt_trichotomy (s ^ 2 + z ^ 2) (a ^ 2) with h | h | h
  · rw [if_pos h.le]
    refine (hf h.le).congr_of_eventuallyEq ?_
    filter_upwards [hc.continuousAt.eventually_lt continuousAt_const h] with z' hz'
    simp only [hillSide, if_pos hz'.le]
  · rw [if_pos h.le]
    obtain ⟨hv, hd⟩ := hsph h
    exact hasDerivAt_ite_of_eq (p := fun y => s ^ 2 + y ^ 2 ≤ a ^ 2) (hf h.le) (hd ▸ hg h.ge) hv
  · rw [if_neg (not_le.mpr h)]
    refine (hg h.le).congr_of_eventuallyEq ?_
    filter_upwards [continuousAt_const.eventually_lt hc.continuousAt h] with z' hz'
    simp only [hillSide, if_neg (not_le.mpr hz')]

/-- [proved-standard; formal-checked] **Hill's one stream function gives the one velocity everywhere off the axis.** -/
theorem hillStream_hasDerivAt (U : ℝ) {a s : ℝ} (z : ℝ) (ha : 0 < a) (hs : 0 < s) :
    HasDerivAt (fun s => hillStream U a s z) (s * hillVelZ U a s z) s ∧
      HasDerivAt (fun z => hillStream U a s z) (-(s * hillVelS U a s z)) z := by
  have hv : s ^ 2 + z ^ 2 = a ^ 2 → streamIn U a s z = streamOut U a s z := fun h => by
    rw [streamIn_sphere U ha.ne' h, streamOut_sphere U ha h]
  constructor
  · refine (hillSide_hasDerivAt_s (fun _ => hasDerivAt_streamIn_s U a s z ha.ne')
      (fun _ => hasDerivAt_streamOut_s U a z hs)
      (fun h => ⟨hv h, by rw [(velocity_match_sphere U ha h).2]⟩)).congr_deriv ?_
    simp only [hillVelZ, hillSide]
    split_ifs <;> rfl
  · refine (hillSide_hasDerivAt_z (fun _ => hasDerivAt_streamIn_z U a s z ha.ne')
      (fun _ => hasDerivAt_streamOut_z U a z hs)
      (fun h => ⟨hv h, by rw [(velocity_match_sphere U ha h).1]⟩)).congr_deriv ?_
    simp only [hillVelS, hillSide]
    split_ifs <;> rfl

/-- [proved-standard; formal-checked] **The stream function's sign**: positive inside, zero on, negative outside. -/
theorem hillStream_sign {U a s : ℝ} (z : ℝ) (hU : 0 < U) (ha : 0 < a) (hs : 0 < s) :
    (s ^ 2 + z ^ 2 < a ^ 2 → 0 < hillStream U a s z) ∧
      (s ^ 2 + z ^ 2 = a ^ 2 → hillStream U a s z = 0) ∧
      (a ^ 2 < s ^ 2 + z ^ 2 → hillStream U a s z < 0) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [hillStream, hillSide, if_pos h.le]; exact streamIn_pos hU ha.ne' hs.ne' h
  · rw [hillStream, hillSide, if_pos h.le]; exact streamIn_sphere U ha.ne' h
  · rw [hillStream, hillSide, if_neg (not_le.mpr h)]; exact streamOut_neg hU ha hs h

/-- [proved-standard; formal-checked] **The dividing stream surface is the sphere**: off the axis, `ψ = 0 ⇔ r = a`. -/
theorem hillStream_eq_zero_iff {U a s : ℝ} (z : ℝ) (hU : 0 < U) (ha : 0 < a) (hs : 0 < s) :
    hillStream U a s z = 0 ↔ s ^ 2 + z ^ 2 = a ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := hillStream_sign z hU ha hs
  refine ⟨fun h0 => ?_, h2⟩
  rcases lt_trichotomy (s ^ 2 + z ^ 2) (a ^ 2) with h | h | h
  · linarith [h1 h]
  · exact h
  · linarith [h3 h]

/-- [proved-standard; formal-checked] **The velocity and the pressure are continuous across the sphere.** -/
theorem hill_continuousAt_sphere (U pinf : ℝ) {a s z : ℝ} (ha : 0 < a) (hs : 0 < s)
    (h : s ^ 2 + z ^ 2 = a ^ 2) :
    ContinuousAt (fun q : ℝ × ℝ => hillVelS U a q.1 q.2) (s, z) ∧
      ContinuousAt (fun q : ℝ × ℝ => hillVelZ U a q.1 q.2) (s, z) ∧
      ContinuousAt (fun q : ℝ × ℝ => hillPressure U a pinf q.1 q.2) (s, z) := by
  have hr : 0 < √(s ^ 2 + z ^ 2) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · refine continuousAt_ite_of_eq (p := fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2 ≤ a ^ 2) ?_ ?_
      (velocity_match_sphere U ha h).1
    · unfold velSIn; fun_prop
    · unfold velSOut rad; fun_prop (disch := positivity)
  · refine continuousAt_ite_of_eq (p := fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2 ≤ a ^ 2) ?_ ?_
      (velocity_match_sphere U ha h).2
    · unfold velZIn; fun_prop
    · unfold velZOut rad; fun_prop (disch := positivity)
  · refine continuousAt_ite_of_eq (p := fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2 ≤ a ^ 2) ?_ ?_
      (pressure_match_sphere U pinf ha h)
    · unfold pressureIn bernoulliPressure streamIn velSIn velZIn; fun_prop
    · unfold pressureOut bernoulliPressure streamOut velSOut velZOut rad; fun_prop (disch := positivity)

/-! ## 8. Readings: the circulation, the speed on the sphere, the poles and the core -/

/-- [proved-standard; formal-checked] **The circulation is `5Ua`**: the vorticity over the meridian half-disc. -/
theorem circulation (U : ℝ) {a : ℝ} (ha : 0 < a) :
    ∫ z in (-a)..a, ∫ s in (0 : ℝ)..√(a ^ 2 - z ^ 2), vorticity (velSIn U a) (velZIn U a) s z =
      5 * U * a := by
  have hin : Set.EqOn (fun z => ∫ s in (0 : ℝ)..√(a ^ 2 - z ^ 2), vorticity (velSIn U a) (velZIn U a) s z)
      (fun z => 15 * U / (4 * a ^ 2) * (a ^ 2 - z ^ 2)) (Set.uIcc (-a) a) := by
    intro z hz
    rw [Set.uIcc_of_le (by linarith)] at hz
    have h0 : 0 ≤ a ^ 2 - z ^ 2 := by nlinarith [hz.1, hz.2]
    simp only [vorticity_in]
    rw [intervalIntegral.integral_const_mul, integral_id, Real.sq_sqrt h0]
    ring
  rw [intervalIntegral.integral_congr hin, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegrable_const (intervalIntegral.intervalIntegrable_pow 2),
    integral_pow, intervalIntegral.integral_const]
  have ha' := ha.ne'
  simp only [smul_eq_mul]
  field_simp
  ring

/-- [proved-standard; formal-checked] **The speed on the sphere is `(3/2) U sin θ`** at polar angle `θ`. -/
theorem speed_on_sphere {U a θ : ℝ} (hU : 0 ≤ U) (ha : a ≠ 0) (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    velSIn U a (a * Real.sin θ) (a * Real.cos θ) ^ 2 + velZIn U a (a * Real.sin θ) (a * Real.cos θ) ^ 2 =
      (3 / 2 * U * Real.sin θ) ^ 2 ∧
    √(velSIn U a (a * Real.sin θ) (a * Real.cos θ) ^ 2 + velZIn U a (a * Real.sin θ) (a * Real.cos θ) ^ 2) =
      3 / 2 * U * Real.sin θ := by
  have e1 : velSIn U a (a * Real.sin θ) (a * Real.cos θ) = 3 / 2 * U * Real.sin θ * Real.cos θ := by
    simp only [velSIn]; field_simp
  have e2 : velZIn U a (a * Real.sin θ) (a * Real.cos θ) =
      3 / 2 * U * (1 - 2 * Real.sin θ ^ 2 - Real.cos θ ^ 2) := by
    simp only [velZIn]; field_simp
  have h : velSIn U a (a * Real.sin θ) (a * Real.cos θ) ^ 2 +
      velZIn U a (a * Real.sin θ) (a * Real.cos θ) ^ 2 = (3 / 2 * U * Real.sin θ) ^ 2 := by
    rw [e1, e2]
    linear_combination (9 * U ^ 2 / 4) * (4 * Real.sin θ ^ 2 + Real.cos θ ^ 2 - 1) *
      Real.sin_sq_add_cos_sq θ
  refine ⟨h, ?_⟩
  rw [h, Real.sqrt_sq]
  have := Real.sin_nonneg_of_nonneg_of_le_pi hθ hθπ
  positivity

/-- [proved-standard; formal-checked] **The poles `(0, ±a)` are stagnation points.** -/
theorem poles_stagnation (U a : ℝ) :
    velSIn U a 0 a = 0 ∧ velZIn U a 0 a = 0 ∧ velSIn U a 0 (-a) = 0 ∧ velZIn U a 0 (-a) = 0 := by
  simp only [velSIn, velZIn]
  refine ⟨by ring, by ring, by ring, by ring⟩

section Core

open Holonics.Compression.Landmark.FixedPoint Holonics.Compression.Landmark.SiteKind
  Holonics.Physics.Fluid.Singularity

/-- [definition] **The velocity gradient block** `[[∂_s u_s, ∂_z u_s], [∂_s u_z, ∂_z u_z]]` at a point. -/
def gradientBlock (us uz : ℝ → ℝ → ℝ) (s z : ℝ) : Mobius ℝ :=
  ⟨deriv (fun s => us s z) s, deriv (fun z => us s z) z, deriv (fun s => uz s z) s,
    deriv (fun z => uz s z) z⟩

/-- [proved-derived; formal-checked] **The ring's core is a rotation site**: at `s₀ = a/√2` the flow stagnates at
`ψ = 3Ua²/16`, and its traceless gradient's Cayley block has a rotation site. -/
theorem core_is_rotation_site {U a s₀ : ℝ} (hU : U ≠ 0) (ha : a ≠ 0) (hs₀ : s₀ ≠ 0)
    (hcore : 2 * s₀ ^ 2 = a ^ 2) :
    velSIn U a s₀ 0 = 0 ∧ velZIn U a s₀ 0 = 0 ∧ streamIn U a s₀ 0 = 3 * U * a ^ 2 / 16 ∧
      (gradientBlock (velSIn U a) (velZIn U a) s₀ 0).trace = 0 ∧
      siteKind (cayleyBlock (gradientBlock (velSIn U a) (velZIn U a) s₀ 0)).trace
        (cayleyBlock (gradientBlock (velSIn U a) (velZIn U a) s₀ 0)).det = .rotation := by
  have hX : (gradientBlock (velSIn U a) (velZIn U a) s₀ 0).trace = 0 := by
    simp only [gradientBlock, Mobius.trace, (hasDerivAt_velSIn_s U a s₀ 0).deriv,
      (hasDerivAt_velZIn_z U a s₀ 0).deriv]
    ring
  refine ⟨by simp [velSIn], ?_, ?_, hX, (cayley_siteKind_rotation hX).mpr ?_⟩
  · simp only [velZIn]; rw [← hcore]; ring
  · simp only [streamIn]; field_simp; linear_combination (4 * a ^ 2 - 8 * s₀ ^ 2) * hcore
  · rw [hX]
    simp only [gradientBlock, Mobius.det, (hasDerivAt_velSIn_s U a s₀ 0).deriv,
      (hasDerivAt_velSIn_z U a s₀ 0).deriv, (hasDerivAt_velZIn_s U a s₀ 0).deriv,
      (hasDerivAt_velZIn_z U a s₀ 0).deriv]
    have : 0 < (3 * U / (2 * a ^ 2)) ^ 2 * s₀ ^ 2 := by positivity
    nlinarith

end Core

end Holonics.Physics.Fluid.HillVortex

import HolonicsResearch.Physics.Spacetime.CurvatureJets
import Holonics.Fluid.NavierStokesCurvedTransport
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The flat Friedmann–Lemaître–Robertson–Walker metric: a fluid and its thermal bath solving `G + Λg = κT`

[definition] One box of #410: "Einstein: the continuum realization (Lorentzian metric, connection, a
fluid-plus-thermal constitution solving `G + Λg = κT`), the weak-field limit `R₀₀ = ∇²Φ`, and the Regge
construction (`Physics/Spacetime/Einstein`)", part done in #1032 (`Physics/Spacetime/CurvatureJets`: curvature
from a metric's 2-jet, the weak field, the plane wave), with "a metric field and its constitution solving the
field equation, the full curvature where the first jet does not vanish, and the Regge construction" left. This
module takes the spatially flat Friedmann–Lemaître–Robertson–Walker metric with a perfect fluid and its thermal
constitution: a metric field whose first jet does not vanish, solving `G + Λg = κT`. Sources:
`Physics/Spacetime/Einstein`'s `[open]` paragraph ("A nontrivial continuum realization (a Lorentzian metric,
its connection and curvature, and a fluid-plus-thermal constitution solving `G + Λg = κT`) is owed");
`CurvatureJets`' "What is not claimed" ("The full Riemann tensor of a 2-jet whose first jet does not vanish is
defined and split …, but its symmetries, its Ricci tensor and its tide are not read there"; "a
fluid-plus-thermal constitution solving `G + Λg = κT` … not stated") and its `FirstJet`, `SecondJet`,
`JetSymm`, `christoffel`, `christoffelJet`, `riemann`, `riemannLower`, `ricci`, `tide`,
`hasDerivAt_christoffel` and the plane wave's built-metric pattern; `Fluid/NavierStokesCurvedTransport`'s
`einsteinResidual`, `einsteinResidual_eq_zero_iff` and `conservation_return` (atlas
`gr.einstein-residual-return`); `Physics/ReceiverStressEnergy`'s `perfectFluidTensor` and
`minkowskiMetricComponent` (atlas `gr.stress-energy-observer`, `gr.source-map`); `Raychaudhuri`'s
`deformation`, `expansion`, `shear`, `rotation`, `raychaudhuriRate` and `raychaudhuri` (atlas
`coupling.congruence-kinematic-split`); the record of August 19 in `research/records/`,
`2026-08-19_THE_FILLED_POLYGON_IS_A_TWO_CHAIN_THE_COSMOLOGICAL_FLOW_IS_A_SYMMETRY_QUOTIENT_…`,
§7 ("Friedmann is a symmetry-reduced Einstein–fluid chart", F.2 to F.4) and §8.1 (the continuity law is the
temporal projection of `∇·T = 0`); and atlas `gr.comoving-deformation` (the comoving receiver reads the
pressure work `−p tr G`), `gr.conservation-belongs-to-receiver`, `code.equation-of-state` (`dL = −p dV`),
`heat.loudness-per-nat-temperature` (equilibrium light under a stretch `1 + z`: `T ↦ T/(1 + z)`, the entropy
kept) and `gr.dilation-current` (radiation is traceless). No thermal owner of `ρ = σ𝒯⁴` stands in the tree, so
the Stefan–Boltzmann constitution is stated here.

For a scale factor `a` with rates `a′`, `a″`, the **metric field** on `Fin 4 → ℝ` is
`g(x) = diag(−1, a(x₀)², a(x₀)², a(x₀)²)` (`frwField`). At a point it has the 2-jet `frwMetric A`,
`frwFirstJet A B` (`∂₀g = diag(0, 2AB, 2AB, 2AB)`, the spatial rates zero) and `frwSecondJet A B C`
(`∂₀∂₀g = diag(0, 2(B² + AC), …)`, the rest zero) at `(A, B, C) = (a, a′, a″)(x₀)`. The comoving fluid is
`T_ab = (ρ + p)u_a u_b + p g_ab` with `u_a = (−1, 0, 0, 0)` (`fluidTensor`), the Ricci matrix of a 2-jet is
`ricciOf`, its scalar `scalarCurvature`, the Einstein tensor `einsteinTensor`, and the field equation at the
jet is the owner's zero residual `frwResidual = einsteinResidual G g T Λ κ = 0`. `H = a′/a`.

[proved-standard; formal-checked] What is proved. Everything is over ℝ.

1. **The metric field and its jets** (`frwDiag`, `frwRate`, `frwAccel`, `frwMetric`, `frwFirstJet`,
   `frwSecondJet`, `frwField`, `frwFirstJetField`, `lapse`, `spatial`, `frwMetric_eq_add`,
   `frwFirstJet_eq_smul`, `frwFirstJet_apply`, `frwSecondJet_apply`, `line_time`, `hasDerivAt_shift`,
   `hasDerivAt_frwField`, `hasDerivAt_frwFirstJetField`, `frwSecondJet_symm`, `frwFirstJet_ne_zero`,
   `frw_christoffel_rate`). Along every coordinate line, by Mathlib's derivatives, the field's rate is the first
   jet and the first-jet field's rate is the second jet, at every point where `a` and `a′` have their rates;
   the second jet is symmetric (`JetSymm`); the first jet does not vanish where `a ≠ 0` and `a′ ≠ 0`; and the
   Christoffel symbols of the built field have the rate `christoffelJet` of its jet (through the owner's
   `hasDerivAt_christoffel`).
2. **Connection and curvature with a nonzero first jet** (`inv_diagonal_of_ne`, `diagCombo`,
   `christoffel_diagonal`, `inverseJet_diagonal`, `christoffelJet_diagonal`, `ricci_riemannLower`,
   `frwDiag_ne`, `frwMetric_det`, `frw_christoffel`, `frw_christoffelJet`, `frw_christoffel_time`,
   `frw_christoffel_space`, `frw_christoffel_rest`, `frw_ricci`, `frw_ricci_time`, `frw_ricci_mixed`,
   `frw_ricci_space`, `ricciOf`, `frw_ricciOf`, `scalarCurvature`, `frw_scalar`, `einsteinTensor`,
   `frw_einstein`, `frw_tide`). For any diagonal metric with a diagonal jet the Christoffel symbols and their
   rates are closed forms, and the owner's Ricci contraction of the lowered tensor is `Σ_a R^a_bad`. On this
   jet `Γ⁰_ij = AB δ_ij`, `Γⁱ_0j = Γⁱ_j0 = (B/A) δ_ij`, the rest zero; through the owner's `ricci`,
   `R₀₀ = −3C/A`, `R₀ᵢ = 0`, `R_ij = (AC + 2B²) δ_ij`; the scalar `g^(ab)R_ab = 6(C/A + H²)`; the Einstein
   tensor `G₀₀ = 3H²`, `G₀ᵢ = 0`, `G_ij = −(2AC + B²) δ_ij`; and the tide `R_(i0j0) = −AC δ_ij`.
3. **The fluid and Friedmann's equations** (`comoving`, `fluidTensor`, `frw_comoving_unit`, `frw_fluid`,
   `frwFrame`, `frwFrame_metric`, `frwFrame_fluid`, `frwResidual`, `friedmann_iff`, `friedmann_accel`). The
   comoving covector is a unit timelike covector, `T = diag(ρ, pA², pA², pA²)`, and in the orthonormal frame
   `(e₀, eᵢ/A)` the metric reads `minkowskiMetricComponent` and the fluid reads the owner's
   `perfectFluidTensor ρ p`. The field equation holds at the jet iff `3H² = κρ + Λ` and
   `2C/A + H² = Λ − κp`, and then `C/A = Λ/3 − κ(ρ + 3p)/6`.
4. **Conservation** (`hubble_rate`, `continuity`). Where `a ≠ 0` and the field equation holds near `t`,
   `κ ≠ 0`, and `a`, `a′` have their rates at `t`, `ρ′ = −3H(ρ + p)`: the fluid's energy balance, the content
   on this metric of the owner's conservation return (`∇·T = 0` from the Bianchi port), here derived from the
   two Friedmann equations. It is the first law `d(ρa³) = −p d(a³)` of a comoving cell, whose pressure work
   `−3Hp` is the comoving receiver's `−p tr G` at `G = H·1` (atlas `gr.comoving-deformation`).
5. **The thermal constitution** (`barotropic_rate`, `barotropic_const`, `dust_rate`, `radiation_rate`,
   `radiationEntropy`, `radiationEntropy_euler`, `bath_cools`, `entropy_conserved`). A barotropic fluid
   `p = wρ` keeps `ρ·a^(3(1+w))` (`a > 0`), at each instant and as a constant over an open preconnected span
   of the clock; dust keeps `ρa³` and radiation (`w = ⅓`) keeps `ρa⁴`. Radiation with the Stefan–Boltzmann
   constitution `ρ = σ𝒯⁴` (`σ > 0`, `𝒯 > 0`) keeps `𝒯·a` (the bath cools as `1/a`), its entropy density
   `s = (4/3)σ𝒯³` obeys Euler's relation `s𝒯 = ρ + p`, and `s·a³` is kept: the comoving entropy is
   conserved, the expansion is adiabatic.
6. **Witnesses from built metrics** (`deSitter_rates`, `deSitter_field`, `deSitter_jets`, `radiation_rates`,
   `radiation_field`, `radiation_bath`, `radiation_jets`). De Sitter `a = e^(ht)` solves the field equation
   at every `t` with `Λ = 3h²`, `ρ = p = 0`. The radiation solution `a = √t`, read at each `t > 0`, solves it
   with `Λ = 0`, `κρ = 3/(4t²)`, `p = ρ/3`; with the bath `𝒯 = θ/√t`, `4κσθ⁴ = 3`, its density is `σ𝒯⁴`
   and `𝒯·a = θ`. Both fields' jets are read along every coordinate line from Mathlib's derivatives of
   `exp` and `√`.
7. **The comoving pair and its congruence** (`frameTide`, `frameTide_eq`, `scalar_inv`,
   `comoving_deformation`, `comoving_deviation`, `comoving_rate`, `comoving_raychaudhuri`). Read in the frame,
   the built tide is `R̂ = −(a″/a)·1`; the comoving deviation `J = a·1` obeys `J″ = −R̂J` at that tide, so the
   owner's `raychaudhuri` applies with its deviation hypothesis proved on this congruence: its deformation is
   `H·1` (no shear, no rotation) and the expansion `θ = 3H` has the rate `raychaudhuriRate = 3(a″/a − H²)`,
   the rate `hubble_rate` gives.

What is not claimed. Spatial curvature `k ≠ 0`, perturbations and their growth, viscous or heat-conducting
fluids on this metric, inflation, and the Regge construction are not stated. The Bianchi identity for a general
metric (it needs the 3-jet) is not stated, and the continuity equation is derived from the two Friedmann
equations, not as an instance of `conservation_return`: no covariant divergence of tensor fields is built as a
linear map. The jets are read along coordinate lines of one chart: no manifold, no change of coordinates (the
tensor character of `R`), and the frame join reads components, not a transformation law. The full Riemann
tensor of this jet is used through its Ricci contraction and its tide; its symmetries are not stated. The radiation
witness is read at each `t > 0`, where `√` is smooth; the degenerate section `t = 0` is not treated. The
Stefan–Boltzmann constant `σ` is a parameter and `s = (4/3)σ𝒯³` the constitution's entropy density: neither is
derived from Planck's law or a partition function. No statement is made about horizons, the age of the
expansion or observed values of `Λ`, `κ` or `σ`.

Read on the passage. The thermal instance keeps its constitutive equations (`p = wρ`, `ρ = σ𝒯⁴`,
`s = (4/3)σ𝒯³`), its clock (the comoving time `x₀`, along which `H = a′/a` is the log-rate of the scale), its
heat and entropy balance (`d(ρa³) = −p d(a³)`, and `s·a³` kept: along this passage the bath produces no
entropy), and its participating receiver (the comoving observer `u`, whose frame reads the fluid as
`perfectFluidTensor` and whose deformation `H·1` pays the pressure work). Under a stretch `1 + z` of the scale
the bath's temperature falls by `1 + z` and its entropy is kept (atlas `heat.loudness-per-nat-temperature`).

The computational object is the helical pair interaction read on an expanding metric: two neighbouring comoving
worldlines are a pair, their separation `J = a·1` grows by the deformation `H·1`, a boost with no turn, and the
tide the 2-jet builds, `R̂ = −(a″/a)·1`, is the stiffness of the pair's deviation, its constitution at that
instant. Of the winding guide's six general objects this touches the pair (the comoving deviation, stiffened by
the tide), the tube (the comoving congruence carrying the fluid and its bath from one constant-time section to
the next, with Raychaudhuri's rate along it), faces and placement (the comoving frame's readings of `g`, `T` and
the tide; the Friedmann equations as the residual's `00` and `ii` faces) and the cell holonomy (the curvature
built through the connection's two transports, read here through its Ricci contraction); the helix and the tower
thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.Spacetime.FriedmannFluid

open Matrix
open Holonics.Physics.Spacetime.CurvatureJets
open Holonics.Fluid.NavierStokesCurvedTransport

variable {n : ℕ}

/-! ## 1. Diagonal metrics: the connection in closed form -/

section Diagonal

/-- [proved-standard; formal-checked] A diagonal matrix with nonzero entries has the diagonal inverse. -/
theorem inv_diagonal_of_ne {v : Fin n → ℝ} (hv : ∀ i, v i ≠ 0) :
    (diagonal v)⁻¹ = diagonal fun i => (v i)⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact inv_mul_cancel₀ (hv i)

/-- [definition] The combination `w_ba δ_ac + w_ca δ_ab − w_ab δ_bc` of a diagonal jet `w`. -/
def diagCombo (w : Fin n → Fin n → ℝ) (a b c : Fin n) : ℝ :=
  (if a = c then w b a else 0) + (if a = b then w c a else 0) - (if b = c then w a b else 0)

/-- [proved-standard; formal-checked] **A diagonal metric's connection**: `Γ^a_bc = ½ g^(aa) diagCombo`. -/
theorem christoffel_diagonal {v : Fin n → ℝ} (hv : ∀ i, v i ≠ 0) (dv : Fin n → Fin n → ℝ)
    (a b c : Fin n) :
    christoffel (diagonal v) (fun e => diagonal (dv e)) a b c = 2⁻¹ * (v a)⁻¹ * diagCombo dv a b c := by
  simp only [christoffel, inv_diagonal_of_ne hv, diagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, diagCombo]
  ring

/-- [proved-standard; formal-checked] The inverse's rate on a diagonal jet is diagonal. -/
theorem inverseJet_diagonal {v : Fin n → ℝ} (hv : ∀ i, v i ≠ 0) (dv : Fin n → Fin n → ℝ) (e : Fin n) :
    inverseJet (diagonal v) (fun e => diagonal (dv e)) e
      = diagonal fun i => -((v i)⁻¹ * dv e i * (v i)⁻¹) := by
  simp only [inverseJet, inv_diagonal_of_ne hv, diagonal_mul_diagonal, diagonal_neg]

/-- [proved-standard; formal-checked] **The connection's rate on a diagonal 2-jet** in closed form. -/
theorem christoffelJet_diagonal {v : Fin n → ℝ} (hv : ∀ i, v i ≠ 0) (dv : Fin n → Fin n → ℝ)
    (ddv : Fin n → Fin n → Fin n → ℝ) (e a b c : Fin n) :
    christoffelJet (diagonal v) (fun e => diagonal (dv e)) (fun e f => diagonal (ddv e f)) e a b c
      = 2⁻¹ * -((v a)⁻¹ * dv e a * (v a)⁻¹) * diagCombo dv a b c
        + 2⁻¹ * (v a)⁻¹ * diagCombo (ddv e) a b c := by
  simp only [christoffelJet, inverseJet_diagonal hv, inv_diagonal_of_ne hv, diagonal_apply, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, diagCombo]
  ring

/-- [proved-standard; formal-checked] **The owner's Ricci contraction** of the lowered tensor is `Σ_a R^a_bad`. -/
theorem ricci_riemannLower {g : Matrix (Fin n) (Fin n) ℝ} (hg : IsUnit g.det) (dg : FirstJet n)
    (ddg : SecondJet n) (b d : Fin n) :
    ricci g (riemannLower g dg ddg) b d = ∑ a, riemann g dg ddg a b a d := by
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := congrFun (Matrix.mulVec_mulVec (fun f => riemann g dg ddg f b a d) g⁻¹ g) a
  rw [Matrix.nonsing_inv_mul g hg, Matrix.one_mulVec] at h
  rw [← h]
  simp [riemannLower, Matrix.mulVec, dotProduct]

end Diagonal

/-! ## 2. The metric's 2-jet, its connection and its curvature -/

section Jet

/-- [definition] The metric's diagonal `(−1, A², A², A²)`. -/
def frwDiag (A : ℝ) : Fin 4 → ℝ := fun i => if i = 0 then -1 else A ^ 2

/-- [definition] The first jet's diagonal: `∂_e g_ii = 2AB` for `e = 0`, `i ≠ 0`, else zero. -/
def frwRate (A B : ℝ) : Fin 4 → Fin 4 → ℝ := fun e i => if e = 0 ∧ i ≠ 0 then 2 * A * B else 0

/-- [definition] The second jet's diagonal: `∂_e∂_f g_ii = 2(B² + AC)` for `e = f = 0`, `i ≠ 0`, else zero. -/
def frwAccel (A B C : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun e f i => if e = 0 ∧ f = 0 ∧ i ≠ 0 then 2 * (B ^ 2 + A * C) else 0

/-- [definition] **The metric** `g = diag(−1, A², A², A²)` at a point with scale `A`. -/
def frwMetric (A : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := diagonal (frwDiag A)

/-- [definition] **Its first jet**, with scale rate `B`: `∂₀g = diag(0, 2AB, 2AB, 2AB)`, `∂ᵢg = 0`. -/
def frwFirstJet (A B : ℝ) : FirstJet 4 := fun e => diagonal (frwRate A B e)

/-- [definition] **Its second jet**, with scale acceleration `C`: `∂₀∂₀g = diag(0, 2(B² + AC), …)`, the rest 0. -/
def frwSecondJet (A B C : ℝ) : SecondJet 4 := fun e f => diagonal (frwAccel A B C e f)

/-- [proved-standard; formal-checked] The diagonal has no zero entry where `A ≠ 0`. -/
theorem frwDiag_ne {A : ℝ} (hA : A ≠ 0) (i : Fin 4) : frwDiag A i ≠ 0 := by
  unfold frwDiag
  split_ifs <;> simp [hA]

/-- [proved-standard; formal-checked] The metric is invertible where `A ≠ 0`. -/
theorem frwMetric_det {A : ℝ} (hA : A ≠ 0) : IsUnit (frwMetric A).det := by
  rw [frwMetric, det_diagonal]
  exact (Finset.prod_ne_zero_iff.mpr fun i _ => frwDiag_ne hA i).isUnit

/-- [proved-standard; formal-checked] The metric's Christoffel symbols in closed form. -/
theorem frw_christoffel {A : ℝ} (hA : A ≠ 0) (B : ℝ) (a b c : Fin 4) :
    christoffel (frwMetric A) (frwFirstJet A B) a b c
      = 2⁻¹ * (frwDiag A a)⁻¹ * diagCombo (frwRate A B) a b c :=
  christoffel_diagonal (frwDiag_ne hA) _ a b c

/-- [proved-standard; formal-checked] Their rates in closed form. -/
theorem frw_christoffelJet {A : ℝ} (hA : A ≠ 0) (B C : ℝ) (e a b c : Fin 4) :
    christoffelJet (frwMetric A) (frwFirstJet A B) (frwSecondJet A B C) e a b c
      = 2⁻¹ * -((frwDiag A a)⁻¹ * frwRate A B e a * (frwDiag A a)⁻¹) * diagCombo (frwRate A B) a b c
        + 2⁻¹ * (frwDiag A a)⁻¹ * diagCombo (frwAccel A B C e) a b c :=
  christoffelJet_diagonal (frwDiag_ne hA) _ _ e a b c

/-- [proved-standard; formal-checked] **`Γ⁰_ij = AB δ_ij`** (`aa′δ_ij`). -/
theorem frw_christoffel_time {A : ℝ} (hA : A ≠ 0) (B : ℝ) (i j : Fin 3) :
    christoffel (frwMetric A) (frwFirstJet A B) 0 i.succ j.succ = if i = j then A * B else 0 := by
  rw [frw_christoffel hA]
  fin_cases i <;> fin_cases j <;> simp [diagCombo, frwRate, frwDiag]
  all_goals ring

/-- [proved-standard; formal-checked] **`Γⁱ_0j = Γⁱ_j0 = (B/A) δ_ij`** (`(a′/a)δ_ij`). -/
theorem frw_christoffel_space {A : ℝ} (hA : A ≠ 0) (B : ℝ) (i j : Fin 3) :
    christoffel (frwMetric A) (frwFirstJet A B) i.succ 0 j.succ = (if i = j then B / A else 0) ∧
      christoffel (frwMetric A) (frwFirstJet A B) i.succ j.succ 0 = (if i = j then B / A else 0) := by
  rw [frw_christoffel hA, frw_christoffel hA]
  fin_cases i <;> fin_cases j <;> simp [diagCombo, frwRate, frwDiag]
  all_goals field_simp

/-- [proved-standard; formal-checked] **The rest vanish**: `Γ⁰_00 = Γ⁰_0i = Γ⁰_i0 = Γⁱ_00 = Γⁱ_jk = 0`. -/
theorem frw_christoffel_rest {A : ℝ} (hA : A ≠ 0) (B : ℝ) (i j k : Fin 3) :
    christoffel (frwMetric A) (frwFirstJet A B) 0 0 0 = 0 ∧
      christoffel (frwMetric A) (frwFirstJet A B) 0 0 i.succ = 0 ∧
      christoffel (frwMetric A) (frwFirstJet A B) 0 i.succ 0 = 0 ∧
      christoffel (frwMetric A) (frwFirstJet A B) i.succ 0 0 = 0 ∧
      christoffel (frwMetric A) (frwFirstJet A B) i.succ j.succ k.succ = 0 := by
  simp only [frw_christoffel hA]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [diagCombo, frwRate, Fin.succ_ne_zero]

/-- [proved-standard; formal-checked] **The Ricci tensor through the owner's `ricci`**:
`R₀₀ = −3C/A`, `R₀ᵢ = 0`, `R_ij = (AC + 2B²) δ_ij`. -/
theorem frw_ricci {A : ℝ} (hA : A ≠ 0) (B C : ℝ) (b d : Fin 4) :
    ricci (frwMetric A) (riemannLower (frwMetric A) (frwFirstJet A B) (frwSecondJet A B C)) b d
      = if b = d then (if b = 0 then -3 * (C / A) else A * C + 2 * B ^ 2) else 0 := by
  rw [ricci_riemannLower (frwMetric_det hA)]
  simp only [riemann, frw_christoffel hA, frw_christoffelJet hA, Fin.sum_univ_four]
  fin_cases b <;> fin_cases d <;>
    simp [diagCombo, frwRate, frwAccel, frwDiag]
  all_goals field_simp
  all_goals ring

/-- [proved-standard; formal-checked] **`R₀₀ = −3a″/a`**. -/
theorem frw_ricci_time {A : ℝ} (hA : A ≠ 0) (B C : ℝ) :
    ricci (frwMetric A) (riemannLower (frwMetric A) (frwFirstJet A B) (frwSecondJet A B C)) 0 0
      = -3 * (C / A) := by
  rw [frw_ricci hA]
  simp

/-- [proved-standard; formal-checked] **`R₀ᵢ = Rᵢ₀ = 0`**. -/
theorem frw_ricci_mixed {A : ℝ} (hA : A ≠ 0) (B C : ℝ) (i : Fin 3) :
    ricci (frwMetric A) (riemannLower (frwMetric A) (frwFirstJet A B) (frwSecondJet A B C)) 0 i.succ = 0 ∧
      ricci (frwMetric A) (riemannLower (frwMetric A) (frwFirstJet A B) (frwSecondJet A B C)) i.succ 0 = 0 := by
  rw [frw_ricci hA, frw_ricci hA]
  simp [(Fin.succ_ne_zero i).symm, Fin.succ_ne_zero i]

/-- [proved-standard; formal-checked] **`R_ij = (aa″ + 2a′²) δ_ij`**. -/
theorem frw_ricci_space {A : ℝ} (hA : A ≠ 0) (B C : ℝ) (i j : Fin 3) :
    ricci (frwMetric A) (riemannLower (frwMetric A) (frwFirstJet A B) (frwSecondJet A B C)) i.succ j.succ
      = if i = j then A * C + 2 * B ^ 2 else 0 := by
  rw [frw_ricci hA]
  simp [Fin.succ_ne_zero, Fin.succ_inj]

/-- [definition] **The Ricci matrix** of a 2-jet, `R_bd` through the owner's `ricci`. -/
def ricciOf (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (ddg : SecondJet n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun b d => ricci g (riemannLower g dg ddg) b d

/-- [definition] **The scalar curvature** `R = g^(ab) R_ab`. -/
def scalarCurvature (g Ric : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ a, ∑ b, g⁻¹ a b * Ric a b

/-- [definition] **The Einstein tensor** `G = Ric − ½ R g`. -/
def einsteinTensor (g Ric : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Ric - (2⁻¹ * scalarCurvature g Ric) • g

/-- [proved-standard; formal-checked] The Ricci matrix is `diag(−3C/A, AC + 2B², AC + 2B², AC + 2B²)`. -/
theorem frw_ricciOf {A : ℝ} (hA : A ≠ 0) (B C : ℝ) :
    ricciOf (frwMetric A) (frwFirstJet A B) (frwSecondJet A B C)
      = diagonal fun i => if i = 0 then -3 * (C / A) else A * C + 2 * B ^ 2 := by
  ext b d
  simp only [ricciOf, Matrix.of_apply, frw_ricci hA, diagonal_apply]

/-- [proved-standard; formal-checked] **The scalar curvature** `R = 6(a″/a + H²)`. -/
theorem frw_scalar {A : ℝ} (hA : A ≠ 0) (B C : ℝ) :
    scalarCurvature (frwMetric A) (ricciOf (frwMetric A) (frwFirstJet A B) (frwSecondJet A B C))
      = 6 * (C / A + (B / A) ^ 2) := by
  rw [frw_ricciOf hA, scalarCurvature, frwMetric, inv_diagonal_of_ne (frwDiag_ne hA)]
  simp [diagonal_apply, Fin.sum_univ_four, frwDiag]
  field_simp
  ring

/-- [proved-standard; formal-checked] **The Einstein tensor**: `G₀₀ = 3H²`, `G₀ᵢ = 0`,
`G_ij = −(2aa″ + a′²) δ_ij`. -/
theorem frw_einstein {A : ℝ} (hA : A ≠ 0) (B C : ℝ) :
    einsteinTensor (frwMetric A) (ricciOf (frwMetric A) (frwFirstJet A B) (frwSecondJet A B C))
      = diagonal fun i => if i = 0 then 3 * (B / A) ^ 2 else -(2 * A * C + B ^ 2) := by
  rw [einsteinTensor, frw_scalar hA, frw_ricciOf hA, frwMetric, ← diagonal_smul, diagonal_sub]
  congr 1
  funext i
  by_cases hi : i = 0
  · simp [hi, frwDiag]
    field_simp
    ring
  · simp [hi, frwDiag]
    field_simp
    ring

/-- [proved-standard; formal-checked] **The tide** `R_(i0j0) = −AC δ_ij` (`−aa″δ_ij`), through the owner's `tide`. -/
theorem frw_tide {A : ℝ} (hA : A ≠ 0) (B C : ℝ) (i j : Fin 3) :
    tide (riemannLower (frwMetric A) (frwFirstJet A B) (frwSecondJet A B C)) i j
      = if i = j then -(A * C) else 0 := by
  simp only [tide, riemannLower, riemann, frw_christoffel hA, frw_christoffelJet hA]
  simp only [frwMetric, diagonal_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    simp [diagCombo, frwRate, frwAccel, frwDiag]
  all_goals field_simp
  all_goals ring

end Jet

/-! ## 3. The comoving fluid and Friedmann's equations -/

section Fluid

/-- [definition] **The comoving covector** `u_a = (−1, 0, 0, 0)`. -/
def comoving : Fin 4 → ℝ := fun i => if i = 0 then -1 else 0

/-- [definition] **The perfect fluid** `T_ab = (ρ + p) u_a u_b + p g_ab` of the comoving observer. -/
def fluidTensor (ρ p : ℝ) (g : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun a b => (ρ + p) * comoving a * comoving b + p * g a b

/-- [proved-standard; formal-checked] The comoving covector is a unit timelike covector: `g^(ab) u_a u_b = −1`. -/
theorem frw_comoving_unit {A : ℝ} (hA : A ≠ 0) :
    ∑ a, ∑ b, (frwMetric A)⁻¹ a b * comoving a * comoving b = -1 := by
  rw [frwMetric, inv_diagonal_of_ne (frwDiag_ne hA)]
  simp [diagonal_apply, frwDiag, comoving]

/-- [proved-standard; formal-checked] **The fluid on this metric** is `diag(ρ, pA², pA², pA²)`. -/
theorem frw_fluid (ρ p A : ℝ) :
    fluidTensor ρ p (frwMetric A) = diagonal fun i => if i = 0 then ρ else p * A ^ 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [fluidTensor, frwMetric, frwDiag, comoving]

/-- [definition] **The orthonormal frame** `(e₀, eᵢ/A)`, by its scalings. -/
def frwFrame (A : ℝ) : Fin 4 → ℝ := fun i => if i = 0 then 1 else A⁻¹

/-- [proved-standard; formal-checked] In the frame the metric reads the owner's `η`. -/
theorem frwFrame_metric {A : ℝ} (hA : A ≠ 0) (i j : Fin 4) :
    frwFrame A i * frwFrame A j * frwMetric A i j
      = Holonics.Physics.ReceiverStressEnergy.minkowskiMetricComponent i j := by
  fin_cases i <;> fin_cases j <;>
    simp [frwFrame, frwMetric, frwDiag, Holonics.Physics.ReceiverStressEnergy.minkowskiMetricComponent,
      Holonics.Physics.ReceiverStressEnergy.minkowskiSign]
  all_goals field_simp

/-- [proved-standard; formal-checked] **In the frame the fluid reads the owner's `perfectFluidTensor ρ p`.** -/
theorem frwFrame_fluid {A : ℝ} (hA : A ≠ 0) (ρ p : ℝ) (i j : Fin 4) :
    frwFrame A i * frwFrame A j * fluidTensor ρ p (frwMetric A) i j
      = Holonics.Physics.ReceiverStressEnergy.perfectFluidTensor ρ p i j := by
  rw [frw_fluid]
  fin_cases i <;> fin_cases j <;>
    simp [frwFrame, Holonics.Physics.ReceiverStressEnergy.perfectFluidTensor,
      Holonics.Physics.ReceiverStressEnergy.minkowskiMetricComponent,
      Holonics.Physics.ReceiverStressEnergy.minkowskiSign, Holonics.Physics.ReceiverStressEnergy.restObserver]
  all_goals field_simp

/-- [definition] **The owner's Einstein residual** `G + Λg − κT` at the jet `(A, B, C)` with the fluid `(ρ, p)`. -/
def frwResidual (A B C ρ p Λ κ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  einsteinResidual
    (einsteinTensor (frwMetric A) (ricciOf (frwMetric A) (frwFirstJet A B) (frwSecondJet A B C)))
    (frwMetric A) (fluidTensor ρ p (frwMetric A)) Λ κ

/-- [proved-standard; formal-checked] **Friedmann's equations**: `G + Λg = κT` at the jet iff `3H² = κρ + Λ`
and `2a″/a + H² = Λ − κp`. -/
theorem friedmann_iff {A : ℝ} (hA : A ≠ 0) (B C ρ p Λ κ : ℝ) :
    frwResidual A B C ρ p Λ κ = 0 ↔
      3 * (B / A) ^ 2 = κ * ρ + Λ ∧ 2 * (C / A) + (B / A) ^ 2 = Λ - κ * p := by
  rw [frwResidual, einsteinResidual_eq_zero_iff, frw_einstein hA, frw_fluid, frwMetric,
    ← diagonal_smul, ← diagonal_smul, diagonal_add, diagonal_eq_diagonal_iff]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simp [frwDiag] at h0 h1
    refine ⟨by linarith, ?_⟩
    field_simp
    linear_combination -h1
  · rintro ⟨h0, h1⟩ i
    by_cases hi : i = 0
    · simp [hi, frwDiag]
      linarith
    · simp [hi, frwDiag]
      field_simp at h1
      linear_combination -h1

/-- [proved-standard; formal-checked] **The acceleration equation** `a″/a = Λ/3 − κ(ρ + 3p)/6`. -/
theorem friedmann_accel {A B C ρ p Λ κ : ℝ} (hA : A ≠ 0) (h : frwResidual A B C ρ p Λ κ = 0) :
    C / A = Λ / 3 - κ * (ρ + 3 * p) / 6 := by
  obtain ⟨h0, h1⟩ := (friedmann_iff hA B C ρ p Λ κ).mp h
  linarith

end Fluid

/-! ## 4. The metric field and its jets along the coordinate lines -/

section Field

/-- [definition] The lapse part `diag(−1, 0, 0, 0)`. -/
def lapse : Matrix (Fin 4) (Fin 4) ℝ := diagonal fun i => if i = 0 then -1 else 0

/-- [definition] The spatial projector `diag(0, 1, 1, 1)`. -/
def spatial : Matrix (Fin 4) (Fin 4) ℝ := diagonal fun i => if i = 0 then 0 else 1

/-- [proved-standard; formal-checked] `g = lapse + A²·spatial`. -/
theorem frwMetric_eq_add (A : ℝ) : frwMetric A = lapse + A ^ 2 • spatial := by
  rw [frwMetric, lapse, spatial, ← diagonal_smul, diagonal_add]
  congr 1
  funext i
  by_cases hi : i = 0 <;> simp [frwDiag, hi]

/-- [proved-standard; formal-checked] `∂_e g = δ_e0·2AB·spatial`. -/
theorem frwFirstJet_eq_smul (A B : ℝ) (e : Fin 4) :
    frwFirstJet A B e = (if e = 0 then 2 * A * B else 0) • spatial := by
  rw [frwFirstJet, spatial, ← diagonal_smul]
  congr 1
  funext i
  by_cases he : e = 0 <;> by_cases hi : i = 0 <;> simp [frwRate, he, hi]

/-- [proved-standard; formal-checked] The first jet's entries. -/
theorem frwFirstJet_apply (A B : ℝ) (f b c : Fin 4) :
    frwFirstJet A B f b c = (if f = 0 ∧ b = c ∧ b ≠ 0 then 1 else 0) * (2 * A * B) := by
  by_cases hbc : b = c
  · subst hbc
    by_cases hf : f = 0 <;> by_cases hb : b = 0 <;> simp [frwFirstJet, frwRate, hf, hb]
  · simp [frwFirstJet, hbc]

/-- [proved-standard; formal-checked] The second jet's entries. -/
theorem frwSecondJet_apply (A B C : ℝ) (e f b c : Fin 4) :
    frwSecondJet A B C e f b c
      = if e = 0 then (if f = 0 ∧ b = c ∧ b ≠ 0 then 1 else 0) * (2 * (B ^ 2 + A * C)) else 0 := by
  by_cases hbc : b = c
  · subst hbc
    by_cases he : e = 0 <;> by_cases hf : f = 0 <;> by_cases hb : b = 0 <;>
      simp [frwSecondJet, frwAccel, he, hf, hb]
  · simp [frwSecondJet, hbc]

/-- [proved-standard; formal-checked] **The second jet is symmetric** (`JetSymm`). -/
theorem frwSecondJet_symm (A B C : ℝ) : JetSymm (frwSecondJet A B C) where
  deriv_comm e f a b := by
    rw [frwSecondJet_apply, frwSecondJet_apply]
    by_cases he : e = 0 <;> by_cases hf : f = 0 <;> simp [he, hf]
  metric_symm e f a b := by
    rw [frwSecondJet_apply, frwSecondJet_apply]
    by_cases hab : a = b
    · rw [hab]
    · simp [hab, Ne.symm hab]

/-- [proved-standard; formal-checked] **The first jet does not vanish**: `∂₀g₁₁ = 2AB ≠ 0`. -/
theorem frwFirstJet_ne_zero {A B : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) : frwFirstJet A B 0 1 1 ≠ 0 := by
  rw [frwFirstJet_apply]
  simp [hA, hB]

/-- [definition] **The metric field** `g(x) = diag(−1, a(x₀)², a(x₀)², a(x₀)²)`. -/
def frwField (a : ℝ → ℝ) (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ := frwMetric (a (x 0))

/-- [definition] **Its first-jet field**, with the scale's rate `a′`. -/
def frwFirstJetField (a a' : ℝ → ℝ) (x : Fin 4 → ℝ) : FirstJet 4 := frwFirstJet (a (x 0)) (a' (x 0))

/-- [proved-standard; formal-checked] Along the line `x + t·e`, the time coordinate moves only for `e = 0`. -/
theorem line_time (x : Fin 4 → ℝ) (e : Fin 4) (t : ℝ) :
    (x + t • (Pi.single e 1 : Fin 4 → ℝ)) 0 = x 0 + if e = 0 then t else 0 := by
  by_cases he : e = 0
  · subst he
    simp
  · simp [he]

/-- [proved-standard; formal-checked] A rate at `s` is the shifted function's rate at `0`. -/
theorem hasDerivAt_shift {a a' : ℝ → ℝ} {s : ℝ} (ha : HasDerivAt a (a' s) s) :
    HasDerivAt (fun t => a (s + t)) (a' s) 0 := by
  rw [← add_zero s] at ha
  simpa using ha.comp_const_add s 0

section FieldRates

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- [proved-standard; formal-checked] **The first jet is the field's rate** along every coordinate line. -/
theorem hasDerivAt_frwField {a a' : ℝ → ℝ} (x : Fin 4 → ℝ) (ha : HasDerivAt a (a' (x 0)) (x 0))
    (e : Fin 4) :
    HasDerivAt (fun t : ℝ => frwField a (x + t • Pi.single e 1)) (frwFirstJetField a a' x e) 0 := by
  by_cases he : e = 0
  · subst he
    have h := (((hasDerivAt_shift ha).fun_pow 2).smul_const spatial).const_add lapse
    have hf : (fun t : ℝ => frwField a (x + t • Pi.single 0 1))
        = fun t => lapse + a (x 0 + t) ^ 2 • spatial := by
      funext t
      rw [frwField, line_time, if_pos rfl, frwMetric_eq_add]
    rw [hf, frwFirstJetField, frwFirstJet_eq_smul, if_pos rfl]
    refine h.congr_deriv ?_
    norm_num
  · have hf : (fun t : ℝ => frwField a (x + t • Pi.single e 1)) = fun _ => frwField a x := by
      funext t
      rw [frwField, frwField, line_time, if_neg he, add_zero]
    rw [hf, frwFirstJetField, frwFirstJet_eq_smul, if_neg he, zero_smul]
    exact hasDerivAt_const _ _

/-- [proved-standard; formal-checked] **The second jet is the first-jet field's rate** along every coordinate
line. -/
theorem hasDerivAt_frwFirstJetField {a a' a'' : ℝ → ℝ} (x : Fin 4 → ℝ)
    (ha : HasDerivAt a (a' (x 0)) (x 0)) (ha' : HasDerivAt a' (a'' (x 0)) (x 0)) (e f b c : Fin 4) :
    HasDerivAt (fun t : ℝ => frwFirstJetField a a' (x + t • Pi.single e 1) f b c)
      (frwSecondJet (a (x 0)) (a' (x 0)) (a'' (x 0)) e f b c) 0 := by
  simp only [frwFirstJetField, frwFirstJet_apply, frwSecondJet_apply, line_time]
  by_cases he : e = 0
  · simp only [he, ↓reduceIte]
    have h := (((hasDerivAt_shift ha).fun_mul (hasDerivAt_shift ha')).const_mul 2).const_mul
      (if f = 0 ∧ b = c ∧ b ≠ 0 then (1 : ℝ) else 0)
    have hf : (fun t : ℝ => (if f = 0 ∧ b = c ∧ b ≠ 0 then (1 : ℝ) else 0) * (2 * a (x 0 + t) * a' (x 0 + t)))
        = fun t => (if f = 0 ∧ b = c ∧ b ≠ 0 then (1 : ℝ) else 0) * (2 * (a (x 0 + t) * a' (x 0 + t))) := by
      funext t
      ring
    rw [hf]
    refine h.congr_deriv ?_
    simp only [add_zero]
    ring
  · simp only [he, if_false, add_zero]
    exact hasDerivAt_const _ _

/-- [proved-standard; formal-checked] **The built field's Christoffel symbols** have the rate `christoffelJet`
of its jet, along every coordinate line. -/
theorem frw_christoffel_rate {a a' a'' : ℝ → ℝ} (x : Fin 4 → ℝ) (h0 : a (x 0) ≠ 0)
    (ha : HasDerivAt a (a' (x 0)) (x 0)) (ha' : HasDerivAt a' (a'' (x 0)) (x 0)) (e b c d : Fin 4) :
    HasDerivAt
      (fun t : ℝ => christoffel (frwField a (x + t • Pi.single e 1))
        (frwFirstJetField a a' (x + t • Pi.single e 1)) b c d)
      (christoffelJet (frwMetric (a (x 0))) (frwFirstJet (a (x 0)) (a' (x 0)))
        (frwSecondJet (a (x 0)) (a' (x 0)) (a'' (x 0))) e b c d) 0 := by
  have hG := hasDerivAt_frwField x ha e
  have h := hasDerivAt_christoffel (G := fun t : ℝ => frwField a (x + t • Pi.single e 1))
    (dG := fun t : ℝ => frwFirstJetField a a' (x + t • Pi.single e 1)) (s := 0)
    (by simpa using hG) (by simpa [frwField] using frwMetric_det h0)
    (fun f b c => hasDerivAt_frwFirstJetField x ha ha' e f b c) b c d
  simpa [frwField, frwFirstJetField] using h

end FieldRates

end Field

/-! ## 5. Conservation: the continuity equation -/

section Conservation

/-- [proved-standard; formal-checked] **The Hubble rate's rate** `H′ = a″/a − H²`. -/
theorem hubble_rate {a a' a'' : ℝ → ℝ} {t : ℝ} (h0 : a t ≠ 0) (ha : HasDerivAt a (a' t) t)
    (ha' : HasDerivAt a' (a'' t) t) :
    HasDerivAt (fun s => a' s / a s) (a'' t / a t - (a' t / a t) ^ 2) t := by
  refine (ha'.div ha h0).congr_deriv ?_
  field_simp

/-- [proved-standard; formal-checked] **The continuity equation** `ρ′ = −3H(ρ + p)`, from the two Friedmann
equations near `t`. -/
theorem continuity {a a' a'' ρ p : ℝ → ℝ} {Λ κ t : ℝ} (hκ : κ ≠ 0) (h0 : ∀ᶠ s in nhds t, a s ≠ 0)
    (ha : HasDerivAt a (a' t) t) (ha' : HasDerivAt a' (a'' t) t)
    (field : ∀ᶠ s in nhds t, frwResidual (a s) (a' s) (a'' s) (ρ s) (p s) Λ κ = 0) :
    HasDerivAt ρ (-3 * (a' t / a t) * (ρ t + p t)) t := by
  have hF : ∀ᶠ s in nhds t, 3 * (a' s / a s) ^ 2 = κ * ρ s + Λ ∧
      2 * (a'' s / a s) + (a' s / a s) ^ 2 = Λ - κ * p s :=
    (h0.and field).mono fun s hs => (friedmann_iff hs.1 _ _ _ _ _ _).mp hs.2
  have hρ : ρ =ᶠ[nhds t] fun s => (3 * (a' s / a s) ^ 2 - Λ) / κ :=
    hF.mono fun s hs => by
      show ρ s = (3 * (a' s / a s) ^ 2 - Λ) / κ
      rw [hs.1]
      field_simp
      ring
  have ht := hF.self_of_nhds
  have hH : a'' t / a t - (a' t / a t) ^ 2 = -(κ * (ρ t + p t)) / 2 := by
    linear_combination (1 / 2 : ℝ) * ht.2 - (1 / 2 : ℝ) * ht.1
  have h := ((((hubble_rate h0.self_of_nhds ha ha').fun_pow 2).const_mul 3).sub_const Λ).div_const κ
  refine (h.congr_deriv ?_).congr_of_eventuallyEq hρ
  rw [hH]
  field_simp
  ring

end Conservation

/-! ## 6. The thermal constitution -/

section Thermal

/-- [proved-standard; formal-checked] **A barotropic fluid `p = wρ` keeps `ρ·a^(3(1+w))`** at the instant. -/
theorem barotropic_rate {a a' ρ p : ℝ → ℝ} {w t : ℝ} (hpos : 0 < a t) (ha : HasDerivAt a (a' t) t)
    (hρ : HasDerivAt ρ (-3 * (a' t / a t) * (ρ t + p t)) t) (hp : p t = w * ρ t) :
    HasDerivAt (fun s => ρ s * a s ^ (3 * (1 + w))) 0 t := by
  have h := hρ.mul (ha.rpow_const (p := 3 * (1 + w)) (Or.inl hpos.ne'))
  refine h.congr_deriv ?_
  rw [Real.rpow_sub_one hpos.ne', hp]
  field_simp
  ring

/-- [proved-standard; formal-checked] **`ρ·a^(3(1+w))` is constant** over an open preconnected span of the
clock. -/
theorem barotropic_const {a a' ρ p : ℝ → ℝ} {w : ℝ} {D : Set ℝ} (hD : IsOpen D)
    (hDc : IsPreconnected D) (hpos : ∀ t ∈ D, 0 < a t) (ha : ∀ t ∈ D, HasDerivAt a (a' t) t)
    (hρ : ∀ t ∈ D, HasDerivAt ρ (-3 * (a' t / a t) * (ρ t + p t)) t) (hp : ∀ t ∈ D, p t = w * ρ t)
    {t₁ t₂ : ℝ} (h₁ : t₁ ∈ D) (h₂ : t₂ ∈ D) :
    ρ t₁ * a t₁ ^ (3 * (1 + w)) = ρ t₂ * a t₂ ^ (3 * (1 + w)) := by
  have hr := fun t (ht : t ∈ D) => barotropic_rate (hpos t ht) (ha t ht) (hρ t ht) (hp t ht)
  exact hD.is_const_of_deriv_eq_zero hDc
    (fun t ht => (hr t ht).differentiableAt.differentiableWithinAt) (fun t ht => (hr t ht).deriv) h₁ h₂

/-- [proved-standard; formal-checked] **Dust keeps `ρa³`.** -/
theorem dust_rate {a a' ρ p : ℝ → ℝ} {t : ℝ} (ha : HasDerivAt a (a' t) t)
    (hρ : HasDerivAt ρ (-3 * (a' t / a t) * (ρ t + p t)) t) (hp : p t = 0) :
    HasDerivAt (fun s => ρ s * a s ^ 3) 0 t := by
  refine (hρ.fun_mul (ha.fun_pow 3)).congr_deriv ?_
  rw [hp]
  field_simp
  ring

/-- [proved-standard; formal-checked] **Radiation (`p = ρ/3`) keeps `ρa⁴`.** -/
theorem radiation_rate {a a' ρ p : ℝ → ℝ} {t : ℝ} (ha : HasDerivAt a (a' t) t)
    (hρ : HasDerivAt ρ (-3 * (a' t / a t) * (ρ t + p t)) t) (hp : p t = ρ t / 3) :
    HasDerivAt (fun s => ρ s * a s ^ 4) 0 t := by
  refine (hρ.fun_mul (ha.fun_pow 4)).congr_deriv ?_
  rw [hp]
  field_simp
  ring

/-- [definition] **The radiation bath's entropy density** `s = (4/3)σ𝒯³`. -/
def radiationEntropy (σ 𝒯 : ℝ) : ℝ := 4 / 3 * σ * 𝒯 ^ 3

/-- [proved-standard; formal-checked] **Euler's relation** `s𝒯 = ρ + p` for `ρ = σ𝒯⁴`, `p = ρ/3`. -/
theorem radiationEntropy_euler (σ 𝒯 : ℝ) :
    radiationEntropy σ 𝒯 * 𝒯 = σ * 𝒯 ^ 4 + σ * 𝒯 ^ 4 / 3 := by
  rw [radiationEntropy]
  ring

/-- [proved-standard; formal-checked] **The Stefan–Boltzmann bath cools as `1/a`**: `𝒯·a` is kept. -/
theorem bath_cools {a a' ρ p 𝒯 : ℝ → ℝ} {σ 𝒯' t : ℝ} (hσ : 0 < σ) (h𝒯 : 0 < 𝒯 t) (h0 : a t ≠ 0)
    (ha : HasDerivAt a (a' t) t) (h𝒯' : HasDerivAt 𝒯 𝒯' t) (hsb : ∀ s, ρ s = σ * 𝒯 s ^ 4)
    (hρ : HasDerivAt ρ (-3 * (a' t / a t) * (ρ t + p t)) t) (hp : p t = ρ t / 3) :
    HasDerivAt (fun s => 𝒯 s * a s) 0 t := by
  have hsbf : ρ = fun s => σ * 𝒯 s ^ 4 := funext hsb
  have h1 : HasDerivAt ρ (σ * (↑4 * 𝒯 t ^ (4 - 1) * 𝒯')) t := by
    rw [hsbf]
    exact (h𝒯'.fun_pow 4).const_mul σ
  have heq := h1.unique hρ
  rw [hp, hsb t] at heq
  norm_num at heq
  have hk : 4 * σ * 𝒯 t ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero four_ne_zero hσ.ne') (pow_ne_zero 3 h𝒯.ne')
  have h𝒯eq : 𝒯' = -(a' t / a t) * 𝒯 t := by
    apply mul_left_cancel₀ hk
    linear_combination heq
  refine (h𝒯'.fun_mul ha).congr_deriv ?_
  rw [h𝒯eq]
  field_simp
  ring

/-- [proved-standard; formal-checked] **The comoving entropy `s·a³` is kept** wherever `𝒯·a` is: the expansion is
adiabatic. -/
theorem entropy_conserved {a 𝒯 : ℝ → ℝ} {σ t : ℝ} (h : HasDerivAt (fun s => 𝒯 s * a s) 0 t) :
    HasDerivAt (fun s => radiationEntropy σ (𝒯 s) * a s ^ 3) 0 t := by
  have hf : (fun s => radiationEntropy σ (𝒯 s) * a s ^ 3) = fun s => 4 / 3 * σ * (𝒯 s * a s) ^ 3 := by
    funext s
    rw [radiationEntropy]
    ring
  rw [hf]
  simpa using (h.fun_pow 3).const_mul (4 / 3 * σ)

end Thermal

/-! ## 7. Witnesses from built metrics -/

section Witnesses

/-- [proved-standard; formal-checked] **De Sitter's rates**: `a = e^(ht)`, `a′ = h e^(ht)`, `a″ = h² e^(ht)`. -/
theorem deSitter_rates (h t : ℝ) :
    HasDerivAt (fun s => Real.exp (h * s)) (h * Real.exp (h * t)) t ∧
      HasDerivAt (fun s => h * Real.exp (h * s)) (h ^ 2 * Real.exp (h * t)) t := by
  have he : HasDerivAt (fun s => Real.exp (h * s)) (h * Real.exp (h * t)) t := by
    refine (((hasDerivAt_id t).const_mul h).exp).congr_deriv ?_
    simp [mul_comm]
  refine ⟨he, (he.const_mul h).congr_deriv ?_⟩
  ring

/-- [proved-standard; formal-checked] **De Sitter solves the field equation** with `Λ = 3h²`, `ρ = p = 0`. -/
theorem deSitter_field (h κ t : ℝ) :
    frwResidual (Real.exp (h * t)) (h * Real.exp (h * t)) (h ^ 2 * Real.exp (h * t)) 0 0 (3 * h ^ 2) κ
      = 0 := by
  rw [friedmann_iff (Real.exp_pos _).ne']
  have he := (Real.exp_pos (h * t)).ne'
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- [proved-standard; formal-checked] **The radiation scale's rates** at `t > 0`: `a = √t`, `a′ = 1/(2√t)`,
`a″ = −1/(4t√t)`. -/
theorem radiation_rates {t : ℝ} (ht : 0 < t) :
    HasDerivAt Real.sqrt (1 / (2 * √t)) t ∧
      HasDerivAt (fun s => 1 / (2 * √s)) (-(1 / (4 * t * √t))) t := by
  have hs := Real.hasDerivAt_sqrt ht.ne'
  have hpos : 0 < √t := Real.sqrt_pos.mpr ht
  refine ⟨hs, ?_⟩
  have h := (hasDerivAt_const t (1 : ℝ)).div (hs.const_mul 2) (by positivity)
  refine h.congr_deriv ?_
  have hsq : √t ^ 2 = t := Real.sq_sqrt ht.le
  field_simp
  rw [hsq]
  ring

/-- [proved-standard; formal-checked] **The radiation solution** `a = √t` at `t > 0`: `Λ = 0`, `κρ = 3/(4t²)`,
`p = ρ/3`. -/
theorem radiation_field {κ t : ℝ} (hκ : κ ≠ 0) (ht : 0 < t) :
    frwResidual (√t) (1 / (2 * √t)) (-(1 / (4 * t * √t))) (3 / (4 * κ * t ^ 2)) (1 / (4 * κ * t ^ 2)) 0 κ
      = 0 := by
  have hpos : 0 < √t := Real.sqrt_pos.mpr ht
  have h4 : √t ^ 4 = t ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt ht.le]
  rw [friedmann_iff hpos.ne']
  constructor
  · field_simp
    rw [h4]
    ring
  · field_simp
    rw [Real.sq_sqrt ht.le, h4]
    ring

/-- [proved-standard; formal-checked] **Its Stefan–Boltzmann bath** `𝒯 = θ/√t` (`4κσθ⁴ = 3`): `ρ = σ𝒯⁴` solves
the field equation, and `𝒯·a = θ`. -/
theorem radiation_bath {κ σ θ t : ℝ} (hb : 4 * κ * σ * θ ^ 4 = 3) (ht : 0 < t) :
    frwResidual (√t) (1 / (2 * √t)) (-(1 / (4 * t * √t))) (σ * (θ / √t) ^ 4) (σ * (θ / √t) ^ 4 / 3) 0 κ
        = 0 ∧ θ / √t * √t = θ := by
  have hpos : 0 < √t := Real.sqrt_pos.mpr ht
  have hsq : √t ^ 2 = t := Real.sq_sqrt ht.le
  have hκ : κ ≠ 0 := by
    rintro rfl
    norm_num at hb
  have hρ : σ * (θ / √t) ^ 4 = 3 / (4 * κ * t ^ 2) := by
    have h4 : √t ^ 4 = t ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]
    rw [div_pow, h4]
    field_simp
    linear_combination hb
  refine ⟨?_, by field_simp⟩
  rw [hρ, show 3 / (4 * κ * t ^ 2) / 3 = 1 / (4 * κ * t ^ 2) by ring]
  exact radiation_field hκ ht

section WitnessRates

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- [proved-standard; formal-checked] **De Sitter's built field**: its jets are read along every coordinate line
at every point. -/
theorem deSitter_jets (h : ℝ) (x : Fin 4 → ℝ) (e f b c : Fin 4) :
    HasDerivAt (fun t : ℝ => frwField (fun s => Real.exp (h * s)) (x + t • Pi.single e 1))
        (frwFirstJetField (fun s => Real.exp (h * s)) (fun s => h * Real.exp (h * s)) x e) 0 ∧
      HasDerivAt (fun t : ℝ => frwFirstJetField (fun s => Real.exp (h * s)) (fun s => h * Real.exp (h * s))
          (x + t • Pi.single e 1) f b c)
        (frwSecondJet (Real.exp (h * x 0)) (h * Real.exp (h * x 0)) (h ^ 2 * Real.exp (h * x 0)) e f b c) 0 :=
  ⟨hasDerivAt_frwField x (deSitter_rates h (x 0)).1 e,
    hasDerivAt_frwFirstJetField (a'' := fun s => h ^ 2 * Real.exp (h * s)) x (deSitter_rates h (x 0)).1
      (deSitter_rates h (x 0)).2 e f b c⟩

/-- [proved-standard; formal-checked] **The radiation field's jets** are read along every coordinate line at every
point with `x₀ > 0`. -/
theorem radiation_jets (x : Fin 4 → ℝ) (hx : 0 < x 0) (e f b c : Fin 4) :
    HasDerivAt (fun t : ℝ => frwField Real.sqrt (x + t • Pi.single e 1))
        (frwFirstJetField Real.sqrt (fun s => 1 / (2 * √s)) x e) 0 ∧
      HasDerivAt (fun t : ℝ => frwFirstJetField Real.sqrt (fun s => 1 / (2 * √s)) (x + t • Pi.single e 1) f b c)
        (frwSecondJet (√(x 0)) (1 / (2 * √(x 0))) (-(1 / (4 * x 0 * √(x 0)))) e f b c) 0 :=
  ⟨hasDerivAt_frwField x (radiation_rates hx).1 e,
    hasDerivAt_frwFirstJetField (a'' := fun s => -(1 / (4 * s * √s))) x (radiation_rates hx).1
      (radiation_rates hx).2 e f b c⟩

end WitnessRates

end Witnesses

/-! ## 8. The comoving pair and its congruence -/

section Congruence

open Holonics.Physics.Spacetime.Raychaudhuri

/-- [definition] **The tide in the frame** `(e₀, eᵢ/A)`: `R̂_ij = R_(i0j0)/A²`. -/
def frameTide (A B C : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (A ^ 2)⁻¹ • Matrix.of (tide (riemannLower (frwMetric A) (frwFirstJet A B) (frwSecondJet A B C)))

/-- [proved-standard; formal-checked] **The frame tide is isotropic**: `R̂ = −(a″/a)·1`. -/
theorem frameTide_eq {A : ℝ} (hA : A ≠ 0) (B C : ℝ) : frameTide A B C = (-(C / A)) • 1 := by
  ext i j
  by_cases hij : i = j
  · simp [frameTide, frw_tide hA, hij]
    field_simp
  · simp [frameTide, frw_tide hA, hij]

/-- [proved-standard; formal-checked] `(A·1)⁻¹ = A⁻¹·1`. -/
theorem scalar_inv {A : ℝ} (hA : A ≠ 0) : (A • (1 : Matrix (Fin 3) (Fin 3) ℝ))⁻¹ = A⁻¹ • 1 := by
  apply Matrix.inv_eq_left_inv
  rw [smul_one_mul, smul_smul, inv_mul_cancel₀ hA, one_smul]

/-- [proved-standard; formal-checked] **The comoving deformation** is `H·1`: no shear, no rotation. -/
theorem comoving_deformation {a a' : ℝ → ℝ} {t : ℝ} (h0 : a t ≠ 0) :
    deformation (fun s => a s • (1 : Matrix (Fin 3) (Fin 3) ℝ)) (fun s => a' s • 1) t = (a' t / a t) • 1 := by
  rw [deformation, scalar_inv h0, smul_one_mul, smul_smul, div_eq_mul_inv]

/-- [proved-standard; formal-checked] **Raychaudhuri's rate at `H·1` and the frame tide** is `3(a″/a − H²)`. -/
theorem comoving_rate (A B C : ℝ) :
    raychaudhuriRate ((B / A) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) ((-(C / A)) • 1)
      = 3 * (C / A - (B / A) ^ 2) := by
  have hs : shear ((B / A) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 0 := by
    ext i j
    by_cases hij : i = j <;> simp [shear, expansion, hij]
    ring
  have hr : rotation ((B / A) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 0 := by
    simp [rotation]
  rw [raychaudhuriRate, hs, hr]
  simp [Raychaudhuri.frobenius, expansion, Matrix.trace_smul]
  ring

section CongruenceRates

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- [proved-standard; formal-checked] **The comoving pair obeys the deviation equation** `J″ = −R̂J`, `J = a·1`, at
the built tide. -/
theorem comoving_deviation {a a' a'' : ℝ → ℝ} {t : ℝ} (h0 : a t ≠ 0) (ha' : HasDerivAt a' (a'' t) t) :
    HasDerivAt (fun s => a' s • (1 : Matrix (Fin 3) (Fin 3) ℝ))
      (-(frameTide (a t) (a' t) (a'' t) * (a t • 1))) t := by
  refine (ha'.smul_const (1 : Matrix (Fin 3) (Fin 3) ℝ)).congr_deriv ?_
  rw [frameTide_eq h0, smul_one_mul, smul_smul, ← neg_smul]
  congr 1
  field_simp

/-- [proved-standard; formal-checked] **The comoving congruence obeys Raychaudhuri's equation** at the built tide,
through the owner's `raychaudhuri`. -/
theorem comoving_raychaudhuri {a a' a'' : ℝ → ℝ} {t : ℝ} (h0 : a t ≠ 0) (ha : HasDerivAt a (a' t) t)
    (ha' : HasDerivAt a' (a'' t) t) :
    HasDerivAt (fun s => expansion (deformation (fun s => a s • (1 : Matrix (Fin 3) (Fin 3) ℝ))
        (fun s => a' s • 1) s))
      (raychaudhuriRate (deformation (fun s => a s • (1 : Matrix (Fin 3) (Fin 3) ℝ)) (fun s => a' s • 1) t)
        (frameTide (a t) (a' t) (a'' t))) t := by
  have hJ : HasDerivAt (fun s => a s • (1 : Matrix (Fin 3) (Fin 3) ℝ)) (a' t • 1) t := ha.smul_const 1
  have hu : IsUnit (a t • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det := by
    rw [Matrix.det_smul, det_one, mul_one]
    exact (pow_ne_zero _ h0).isUnit
  exact raychaudhuri (R := fun s => frameTide (a s) (a' s) (a'' s)) (by norm_num) hJ
    (comoving_deviation h0 ha') hu

end CongruenceRates

end Congruence

end Holonics.Physics.Spacetime.FriedmannFluid

import HolonicsResearch.Physics.Spacetime.FriedmannFluid
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Friedmann–Lemaître–Robertson–Walker with spatial curvature: the slice of curvature `k`, its jet at the centre

[definition] One box of #410: "Einstein: the continuum realization (Lorentzian metric, connection, a
fluid-plus-thermal constitution solving `G + Λg = κT`), the weak-field limit `R₀₀ = ∇²Φ`, and the Regge
construction (`Physics/Spacetime/Einstein`)", part done in #1032 (`Physics/Spacetime/CurvatureJets`) and #1034
(`Physics/Spacetime/FriedmannFluid`), whose note ends "left: spatial curvature, perturbations, the Bianchi
identity in general, and the Regge construction". This module takes the spatial curvature. Sources:
`FriedmannFluid`'s "What is not claimed" ("Spatial curvature `k ≠ 0` … not stated") and its `frwDiag`,
`frwMetric`, `frwFirstJet`, `frwSecondJet`, `frwMetric_det`, `frwMetric_eq_add`, `frwFirstJet_eq_smul`,
`frwFirstJet_apply`, `frwSecondJet_symm`, `inv_diagonal_of_ne`, `diagCombo`, `frw_christoffel`,
`frw_christoffelJet`, `frw_ricci`, `frw_tide`, `ricciOf`, `scalarCurvature`, `einsteinTensor`, `fluidTensor`,
`frw_fluid`, `frwResidual`, `hubble_rate`, `continuity`, `lapse`, `spatial`, `line_time`, `hasDerivAt_shift`,
`frwField` and `frwFirstJetField`; `CurvatureJets`' `FirstJet`, `SecondJet`, `JetSymm`, `christoffel`,
`christoffelJet`, `riemannLower`, `linearCurvature`, `ricci`, `tide`, `riemannLower_eq_add`,
`riemannLower_of_firstJet_zero` and `hasDerivAt_christoffel`; `Fluid/NavierStokesCurvedTransport`'s
`einsteinResidual` and `einsteinResidual_eq_zero_iff` (atlas `gr.einstein-residual-return`); the record of
August 19 in `research/records/`, `2026-08-19_THE_FILLED_POLYGON_IS_A_TWO_CHAIN_THE_COSMOLOGICAL_FLOW_IS_A_…`,
§7.2 (F.2 to F.4: Friedmann's equations with the curvature term `−k/a²` and the continuity law, graded
proved-standard there); and atlas `gr.flrw-fluid-bath` (its limits: "spatially flat (k = 0)", "k ≠ 0 … not stated"),
`coupling.curvature-jets`, `phase.two-sided-pythagoras` (the curvature-`k` half-angle chart, whose denominator
`1 + kt²` is the conformal factor below at `t = r/2`) and `coupling.deviation-focus` (`Geometry/Deviation`: the
sign of a curvature is the sign in the deviation equation, a focus for `K > 0` and none for `K < 0`).

For a scale factor `a` with rates `a′`, `a″` and a curvature `k`, the **metric field** on `Fin 4 → ℝ` is
`g(x) = diag(−1, a(x₀)²ψ(x)⁻², a(x₀)²ψ(x)⁻², a(x₀)²ψ(x)⁻²)` with `ψ(x) = 1 + k(x₁² + x₂² + x₃²)/4`
(`curvedField`, `conformal`): `ψ⁻²δ` is the conformally flat chart of the three-space of constant curvature `k`
(the unit three-sphere's stereographic chart at `k = 1`). On the time axis `x₁ = x₂ = x₃ = 0`, **the centre**,
`ψ = 1` and its first rates vanish, so the metric and its first jet are the owner's `frwMetric A` and
`frwFirstJet A B`, and the second jet is `curvedSecondJet A B C k = frwSecondJet A B C + spaceJet A k`, whose only
new entries are `∂_j∂_l g_ii = −kA² δ_jl` (`j, l, i ≠ 0`), at `(A, B, C) = (a, a′, a″)(x₀)`. The slice at the
centre has the metric `h = A²·1` (`sliceMetric`), the first jet `0` and the second jet
`∂_e∂_f h_ij = −kA² δ_ef δ_ij` (`sliceJet`): the spacetime jet's spatial block. Its extrinsic curvature is
`K_ij = ½∂₀g_ij` (`extrinsic`). `H = B/A`, and the field equation at the jet is the owner's zero residual
`curvedResidual = einsteinResidual G g T Λ κ = 0` with the owner's comoving fluid.

[proved-standard; formal-checked] What is proved. Everything is over ℝ.

1. **An added second jet enters through its linear form** (`jetSymm_add`, `linearCurvature_add`,
   `riemannLower_add`, `ricci_add`). For an invertible `g` and symmetric second jets,
   `R(g, dg, ddg + ddg′) = R(g, dg, ddg) + K(ddg′)`, through the owner's split `riemannLower_eq_add`: where two
   jets share their value and first jet, their curvatures differ by the linear form of the second jets'
   difference.
2. **The 2-jet at the centre** (`spaceAccel`, `spaceJet`, `curvedSecondJet`, `curvedAccelCoef`,
   `curvedSecondJet_eq_smul`, `spaceJet_symm`, `curvedSecondJet_symm`, `spaceJet_zero`, `curvedSecondJet_zero`).
   `∂_e∂_f g = c_ef·diag(0, 1, 1, 1)` with `c_00 = 2(B² + AC)`, `c_jj = −kA²` (`j ≠ 0`) and every other `c_ef`
   zero (so `∂₀∂_j g = 0`); the jet is symmetric (`JetSymm`) and is the owner's at `k = 0`.
3. **Curvature at the centre** (`space_ricci`, `space_tide`, `curved_ricci`, `curved_ricciOf`, `curved_scalar`,
   `curved_einstein`, `curved_tide`, `planeCurvature`, `frw_riemann`, `space_riemann`, `curved_riemann`). Through
   the owner's `frw_ricci` and item 1, `R₀₀ = −3C/A`, `R₀ᵢ = 0`, `R_ij = (AC + 2B² + 2k) δ_ij`; the scalar
   `6(C/A + H² + k/A²)`; `G₀₀ = 3(H² + k/A²)`, `G₀ᵢ = 0`, `G_ij = −(2AC + B² + k) δ_ij`; and the tide is
   unchanged, `R_(i0j0) = −AC δ_ij`. The full Riemann tensor is `R_abcd = κ_ab (g_ac g_bd − g_ad g_bc)`, with the
   plane curvature `κ_ab = C/A` on a plane holding the time axis and `(B² + k)/A²` on a plane of the slice: at
   `k = 0` through the owner's diagonal formulas for all 256 components (the owner's flat jet, whose Riemann
   tensor `FriedmannFluid` reads only through its Ricci contraction and its tide), the spatial curvature through
   item 1.
4. **The slice, read from its own 3-jet** (`sliceMetric`, `sliceJet`, `frwMetric_slice`, `frwFirstJet_slice`,
   `curvedSecondJet_slice`, `sliceMetric_det`, `sliceJet_symm`, `slice_riemann`, `slice_ricci`,
   `slice_sectional`, `extrinsic`, `extrinsic_eq`, `curved_gauss`, `curved_ricci_split`). The slice's metric and
   second jet are the spacetime jet's spatial blocks and its first jet vanishes; through the owner's connection
   its curvature is `R̃_abcd = (k/A²)(h_ac h_bd − h_ad h_bc)`, its Ricci tensor `2k δ_ij = 2(k/A²) h_ij`, and on
   any two vectors `R̃(X, Y, X, Y) = (k/A²)(|X|²|Y|² − ⟨X, Y⟩²)`: the slice at scale `A` has the sectional
   curvature `k/A²`, and the comoving slice (`A = 1`) has `k`. With `K_ij = AB δ_ij`, a plane of the slice curves
   in spacetime by Gauss's equation `R_ijlm = R̃_ijlm + K_il K_jm − K_im K_jl`, which is `(B² + k)/A² =
   k/A² + H²`; and the spacetime Ricci tensor's spatial block is the owner's flat one plus the slice's own.
5. **Friedmann's equations with curvature** (`curvedResidual`, `curvedResidual_zero`, `curved_friedmann_iff`,
   `curved_accel`, `curved_continuity`, `curved_barotropic`, `densityParameter`, `density_excess`,
   `density_sign`). The comoving
   perfect fluid solves the field equation at the jet iff `3(H² + k/A²) = κρ + Λ` and
   `2C/A + H² + k/A² = Λ − κp` (the residual is the owner's `frwResidual` at `k = 0`); then
   `C/A = Λ/3 − κ(ρ + 3p)/6`, unchanged by `k`. Where `a ≠ 0` and the field equation holds near `t`, `κ ≠ 0`,
   and `a`, `a′` have their rates at `t`, `ρ′ = −3H(ρ + p)`: the curvature term enters both equations and drops
   from their combination, so the owner's barotropic and thermal statements, which take this rate as their
   hypothesis, read on the curved metric unchanged (`curved_barotropic`: `p = wρ` keeps `ρ·a^(3(1+w))`). At
   `Λ = 0` and `H ≠ 0` the density parameter `Ω = κρ/(3H²)` has `Ω − 1 = k/(A²H²)`, and `Ω − 1` is positive,
   zero or negative as `k` is.
6. **The metric field and its jets along the coordinate lines** (`conformal`, `curvedField`, `curvedRate`,
   `curvedFirstJetField`, `line_coord`, `conformal_line`, `hasDerivAt_conformal`, `hasDerivAt_scale_line`,
   `hasDerivAt_coord_line`, `curvedField_zero`, `curvedFirstJetField_zero`, `conformal_centre`,
   `curvedField_centre`, `curvedFirstJetField_centre`, `curved_christoffel`, `hasDerivAt_curvedRate`,
   `curvedField_eq_add`, `hasDerivAt_curvedField`, `hasDerivAt_curvedFirstJetField`, `curved_christoffel_rate`).
   By Mathlib's derivatives, along every coordinate line and at every point where `ψ ≠ 0` and `a` has its rate,
   the field's rate is the first-jet field `∂₀g = 2aa′ψ⁻²·diag(0, 1, 1, 1)`, `∂_j g = −ka²x_jψ⁻³·diag(0, 1, 1, 1)`;
   at the centre the first-jet field is the owner's `frwFirstJet`, so the Christoffel symbols there are the flat
   ones (the owner's `frw_christoffel_time`, `frw_christoffel_space`, `frw_christoffel_rest` apply), and the
   first-jet field's rate along every line is `curvedSecondJet`; the built field's Christoffel symbols have the
   rate `christoffelJet` of that jet (through the owner's `hasDerivAt_christoffel`). At `k = 0` the field and its
   first-jet field are the owner's.
7. **Witnesses from built metrics** (`einsteinStatic_field`, `einsteinStatic_riemann`, `milne_field`,
   `milne_flat`, `deSitterClosed_field`, `deSitterClosed_riemann`, `deSitterFlat_riemann`, `einsteinStatic_jets`,
   `milne_jets`, `deSitterClosed_jets`). Einstein's static universe (`k = 1`, `a = A₀`, dust with `κρ = 2/A₀²`,
   `Λ = 1/A₀²`) solves the field equation, with flat time planes and slice planes of curvature `1/A₀²`; Milne's
   (`k = −1`, `a = t`, `t ≠ 0`, `ρ = p = Λ = 0`) solves it, and its whole Riemann tensor vanishes at the centre;
   de Sitter in the closed slicing (`k = 1`, `a = cosh t`, `Λ = 3`, empty) solves it, with
   `R_abcd = g_ac g_bd − g_ad g_bc`, every plane curving by `Λ/3`, as the owner's flat slicing `a = e^(ht)` does
   at `Λ = 3h²` (`h²(g_ac g_bd − g_ad g_bc)`). Each built field's jets are read along every coordinate line at
   the centre, from Mathlib's derivatives of a constant, the identity, `cosh` and `sinh`.

What is not claimed. Homogeneity is not stated: that every point of a slice is the centre of such a chart (the
slice's isometries carrying it to the time axis), so the curvature and the field equation are read on the time
axis only; the field's first rate is read at every point where `ψ ≠ 0`, its second rate only at the centre. The
chart is one chart: for `k < 0` it is a metric only where `ψ > 0` (the ball `x₁² + x₂² + x₃² < −4/k`), for
`k > 0` the stereographic chart misses a point, and no global slice (sphere, flat space, hyperbolic space) is
built. Perturbations and their growth, viscous or heat-conducting fluids, inflation, the Bianchi identity for a
general metric (it needs the 3-jet) and the Regge construction are not stated. As in the owner, the continuity
equation is derived from the two Friedmann equations, not as an instance of `conservation_return`. The full
Riemann tensor is given in closed form at the centre; its symmetries are not stated as the owner's
`CurvatureSymmetries`, and Gauss's equation is read for this jet, not for a general hypersurface (the Codazzi
equation is not stated). The density parameter is read at `Λ = 0`. Milne's chart is shown flat at the centre,
not mapped onto Minkowski space; the static universe's instability and de Sitter's hyperboloid are not stated.
No statement is made about observed values of `k`, `Λ` or `κ`.

Read on the passage. The fluid instance keeps its constitutive equations (the perfect fluid `(ρ, p)`; dust in the
static universe; the empty constitution with `Λ` in Milne's and de Sitter's), its clock (the comoving time `x₀`,
along which `H = a′/a` is the log-rate of the scale), its balance (`ρ′ = −3H(ρ + p)`, the first law
`d(ρa³) = −p d(a³)` of a comoving cell, unchanged by `k`, so the owner's bath and its kept entropy carry over)
and its participating receiver (the comoving observer, whose frame at the centre reads the fluid as the owner's
`perfectFluidTensor`, the metric there being the owner's). That receiver reads the slice's sign from its own
density and rate: `Ω − 1 = k/(A²H²)`.

The computational object is the helical pair interaction read on a curved expanding metric. Two neighbouring
comoving worldlines are a pair whose deviation is stiffened by the tide `C/A`, which `k` does not change, so the
owner's comoving pair and its congruence read at the centre as on the flat metric; two neighbouring geodesics of
the slice are a pair stiffened by the slice's sectional curvature `k/A²`, a converging lens for `k > 0` and a
diverging one for `k < 0` (atlas `coupling.deviation-focus`); and a plane of the slice holds in spacetime its own
curvature plus the product of the slice's stretch `K = AB·1` (Gauss). Of the winding guide's six general objects
this touches the pair (both deviations), the cell holonomy (the curvature built through the connection's two
transports, split into the slice's own holonomy and the extrinsic product), faces and placement (the plane
curvatures as the frame's faces of `R`, the residual's `00` and `ii` faces, and `Ω − 1` as the receiver's face of
`k`), the tube (the comoving congruence carrying the fluid from one constant-time section to the next, with its
continuity law) and the tower thread in its restriction (the spacetime jet restricted to the slice's 3-jet, one
chart and no gluing); the helix stays attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.Spacetime.CurvedFriedmann

open Matrix
open Holonics.Physics.Spacetime.CurvatureJets
open Holonics.Physics.Spacetime.FriedmannFluid
open Holonics.Fluid.NavierStokesCurvedTransport

variable {n : ℕ}

/-! ## 1. A second jet added to a jet enters through its linear form -/

section Split

/-- [proved-standard; formal-checked] A sum of symmetric second jets is symmetric. -/
theorem jetSymm_add {ddg ddg' : SecondJet n} (h : JetSymm ddg) (h' : JetSymm ddg') :
    JetSymm (ddg + ddg') where
  deriv_comm e f a b := by
    simp only [Pi.add_apply, Matrix.add_apply, h.deriv_comm e f a b, h'.deriv_comm e f a b]
  metric_symm e f a b := by
    simp only [Pi.add_apply, Matrix.add_apply, h.metric_symm e f a b, h'.metric_symm e f a b]

/-- [proved-standard; formal-checked] `K` is additive in the second jet. -/
theorem linearCurvature_add (ddg ddg' : SecondJet n) :
    linearCurvature (ddg + ddg') = linearCurvature ddg + linearCurvature ddg' := by
  funext a b c d
  simp only [linearCurvature, Pi.add_apply, Matrix.add_apply]
  ring

/-- [proved-standard; formal-checked] **An added second jet enters through `K` alone**:
`R(g, dg, ddg + ddg′) = R(g, dg, ddg) + K(ddg′)`, through the owner's split. -/
theorem riemannLower_add {g : Matrix (Fin n) (Fin n) ℝ} (hg : IsUnit g.det) (dg : FirstJet n)
    {ddg ddg' : SecondJet n} (h : JetSymm ddg) (h' : JetSymm ddg') :
    riemannLower g dg (ddg + ddg') = riemannLower g dg ddg + linearCurvature ddg' := by
  rw [riemannLower_eq_add hg dg (jetSymm_add h h'), riemannLower_eq_add hg dg h, linearCurvature_add,
    add_right_comm]

/-- [proved-standard; formal-checked] The owner's Ricci contraction is additive in the tensor. -/
theorem ricci_add (g : Matrix (Fin n) (Fin n) ℝ) (R R' : Tensor4 n) (b d : Fin n) :
    ricci g (R + R') b d = ricci g R b d + ricci g R' b d := by
  simp only [ricci, Pi.add_apply, mul_add, Finset.sum_add_distrib]

end Split

/-! ## 2. The 2-jet at the chart's centre -/

section Jet

/-- [definition] The spatial second jet's diagonal: `∂_j∂_l g_ii = −kA² δ_jl` for `j, l, i ≠ 0`, else zero. -/
def spaceAccel (A k : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun e f i => if e = f ∧ e ≠ 0 ∧ i ≠ 0 then -(k * A ^ 2) else 0

/-- [definition] **The spatial curvature's second jet**: `∂_j∂_l g = −kA² δ_jl·diag(0, 1, 1, 1)`. -/
def spaceJet (A k : ℝ) : SecondJet 4 := fun e f => diagonal (spaceAccel A k e f)

/-- [definition] **The second jet at the centre**: the owner's flat one plus the spatial curvature's. -/
def curvedSecondJet (A B C k : ℝ) : SecondJet 4 := frwSecondJet A B C + spaceJet A k

/-- [definition] Its coefficient on `diag(0, 1, 1, 1)`: `2(B² + AC)` at `e = f = 0`, `−kA²` at `e = f ≠ 0`. -/
def curvedAccelCoef (A B C k : ℝ) (e f : Fin 4) : ℝ :=
  if e = 0 ∧ f = 0 then 2 * (B ^ 2 + A * C) else if e = f then -(k * A ^ 2) else 0

/-- [proved-standard; formal-checked] `∂_e∂_f g = curvedAccelCoef·diag(0, 1, 1, 1)` at the centre. -/
theorem curvedSecondJet_eq_smul (A B C k : ℝ) (e f : Fin 4) :
    curvedSecondJet A B C k e f = curvedAccelCoef A B C k e f • spatial := by
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases he : e = 0 <;> by_cases hf : f = 0 <;> by_cases hef : e = f <;> by_cases hi : i = 0 <;>
      simp [curvedSecondJet, frwSecondJet, frwAccel, spaceJet, spaceAccel, curvedAccelCoef, spatial, he, hf,
        hef, hi] <;> simp_all
  · simp [curvedSecondJet, frwSecondJet, spaceJet, spatial, hij]

/-- [proved-standard; formal-checked] The spatial curvature's second jet is symmetric. -/
theorem spaceJet_symm (A k : ℝ) : JetSymm (spaceJet A k) where
  deriv_comm e f a b := by
    by_cases hab : a = b
    · subst hab
      by_cases hef : e = f
      · subst hef
        rfl
      · simp [spaceJet, spaceAccel, hef, Ne.symm hef]
    · simp [spaceJet, hab]
  metric_symm e f a b := by
    by_cases hab : a = b
    · rw [hab]
    · simp [spaceJet, hab, Ne.symm hab]

/-- [proved-standard; formal-checked] **The second jet at the centre is symmetric** (`JetSymm`). -/
theorem curvedSecondJet_symm (A B C k : ℝ) : JetSymm (curvedSecondJet A B C k) :=
  jetSymm_add (frwSecondJet_symm A B C) (spaceJet_symm A k)

/-- [proved-standard; formal-checked] At `k = 0` the spatial second jet vanishes. -/
theorem spaceJet_zero (A : ℝ) : spaceJet A 0 = 0 := by
  funext e f
  ext i j
  simp [spaceJet, spaceAccel, diagonal_apply]

/-- [proved-standard; formal-checked] **At `k = 0` the second jet is the owner's flat one.** -/
theorem curvedSecondJet_zero (A B C : ℝ) : curvedSecondJet A B C 0 = frwSecondJet A B C := by
  rw [curvedSecondJet, spaceJet_zero, add_zero]

end Jet

/-! ## 3. Curvature at the centre -/

section Curvature

/-- [proved-standard; formal-checked] The Ricci contraction of `K(spaceJet)`: `2k δ_ij` on the slice, else 0. -/
theorem space_ricci {A : ℝ} (hA : A ≠ 0) (k : ℝ) (b d : Fin 4) :
    ricci (frwMetric A) (linearCurvature (spaceJet A k)) b d = if b = d ∧ b ≠ 0 then 2 * k else 0 := by
  simp only [ricci, frwMetric, inv_diagonal_of_ne (frwDiag_ne hA), diagonal_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Fin.sum_univ_four]
  fin_cases b <;> fin_cases d <;> simp [linearCurvature, spaceJet, spaceAccel, frwDiag]
  all_goals field_simp
  all_goals ring

/-- [proved-standard; formal-checked] `K(spaceJet)` has no tide. -/
theorem space_tide (A k : ℝ) (i j : Fin 3) : tide (linearCurvature (spaceJet A k)) i j = 0 := by
  simp [tide, linearCurvature, spaceJet, spaceAccel, diagonal_apply, Fin.succ_ne_zero]

/-- [proved-standard; formal-checked] **The Ricci tensor with spatial curvature**, through the owner's `ricci`:
`R₀₀ = −3C/A`, `R₀ᵢ = 0`, `R_ij = (AC + 2B² + 2k) δ_ij`. -/
theorem curved_ricci {A : ℝ} (hA : A ≠ 0) (B C k : ℝ) (b d : Fin 4) :
    ricci (frwMetric A) (riemannLower (frwMetric A) (frwFirstJet A B) (curvedSecondJet A B C k)) b d
      = if b = d then (if b = 0 then -3 * (C / A) else A * C + 2 * B ^ 2 + 2 * k) else 0 := by
  rw [curvedSecondJet, riemannLower_add (frwMetric_det hA) _ (frwSecondJet_symm A B C) (spaceJet_symm A k),
    ricci_add, frw_ricci hA, space_ricci hA]
  by_cases hbd : b = d
  · subst hbd
    by_cases hb : b = 0 <;> simp [hb]
  · simp [hbd]

/-- [proved-standard; formal-checked] The Ricci matrix is `diag(−3C/A, AC + 2B² + 2k, …)`. -/
theorem curved_ricciOf {A : ℝ} (hA : A ≠ 0) (B C k : ℝ) :
    ricciOf (frwMetric A) (frwFirstJet A B) (curvedSecondJet A B C k)
      = diagonal fun i => if i = 0 then -3 * (C / A) else A * C + 2 * B ^ 2 + 2 * k := by
  ext b d
  simp only [ricciOf, Matrix.of_apply, curved_ricci hA, diagonal_apply]

/-- [proved-standard; formal-checked] **The scalar curvature** `R = 6(C/A + H² + k/A²)`. -/
theorem curved_scalar {A : ℝ} (hA : A ≠ 0) (B C k : ℝ) :
    scalarCurvature (frwMetric A) (ricciOf (frwMetric A) (frwFirstJet A B) (curvedSecondJet A B C k))
      = 6 * (C / A + (B / A) ^ 2 + k / A ^ 2) := by
  rw [curved_ricciOf hA, scalarCurvature, frwMetric, inv_diagonal_of_ne (frwDiag_ne hA)]
  simp [diagonal_apply, Fin.sum_univ_four, frwDiag]
  field_simp
  ring

/-- [proved-standard; formal-checked] **The Einstein tensor**: `G₀₀ = 3(H² + k/A²)`, `G₀ᵢ = 0`,
`G_ij = −(2AC + B² + k) δ_ij`. -/
theorem curved_einstein {A : ℝ} (hA : A ≠ 0) (B C k : ℝ) :
    einsteinTensor (frwMetric A) (ricciOf (frwMetric A) (frwFirstJet A B) (curvedSecondJet A B C k))
      = diagonal fun i => if i = 0 then 3 * ((B / A) ^ 2 + k / A ^ 2) else -(2 * A * C + B ^ 2 + k) := by
  rw [einsteinTensor, curved_scalar hA, curved_ricciOf hA, frwMetric, ← diagonal_smul, diagonal_sub]
  congr 1
  funext i
  by_cases hi : i = 0
  · simp [hi, frwDiag]
    field_simp
    ring
  · simp [hi, frwDiag]
    field_simp
    ring

/-- [proved-standard; formal-checked] **The tide is unchanged**: `R_(i0j0) = −AC δ_ij`. -/
theorem curved_tide {A : ℝ} (hA : A ≠ 0) (B C k : ℝ) (i j : Fin 3) :
    tide (riemannLower (frwMetric A) (frwFirstJet A B) (curvedSecondJet A B C k)) i j
      = if i = j then -(A * C) else 0 := by
  rw [curvedSecondJet, riemannLower_add (frwMetric_det hA) _ (frwSecondJet_symm A B C) (spaceJet_symm A k)]
  have h := space_tide A k i j
  simp only [tide] at h ⊢
  simp only [Pi.add_apply, h, add_zero]
  exact frw_tide hA B C i j

/-- [definition] **The curvature of a coordinate plane** at the centre: `C/A` for a plane holding the time
axis, `(B² + k)/A²` for a plane of the slice. -/
def planeCurvature (A B C k : ℝ) (a b : Fin 4) : ℝ := if a = 0 ∨ b = 0 then C / A else (B ^ 2 + k) / A ^ 2

set_option maxHeartbeats 1000000 in
/-- [proved-standard; formal-checked] **The owner's flat jet's full Riemann tensor**:
`R_abcd = planeCurvature(k = 0)·(g_ac g_bd − g_ad g_bc)`, through the owner's diagonal formulas. -/
theorem frw_riemann {A : ℝ} (hA : A ≠ 0) (B C : ℝ) (a b c d : Fin 4) :
    riemannLower (frwMetric A) (frwFirstJet A B) (frwSecondJet A B C) a b c d
      = planeCurvature A B C 0 a b * (frwMetric A a c * frwMetric A b d - frwMetric A a d * frwMetric A b c) := by
  simp only [riemannLower, riemann, frw_christoffel hA, frw_christoffelJet hA]
  simp only [frwMetric, diagonal_apply, Fin.sum_univ_four, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [diagCombo, frwRate, frwAccel, frwDiag, planeCurvature]
  all_goals field_simp
  all_goals ring

/-- [proved-standard; formal-checked] `K(spaceJet) = (k/A²)·(g_ac g_bd − g_ad g_bc)` on the slice's planes. -/
theorem space_riemann {A : ℝ} (hA : A ≠ 0) (k : ℝ) (a b c d : Fin 4) :
    linearCurvature (spaceJet A k) a b c d
      = (if a = 0 ∨ b = 0 then 0 else k / A ^ 2)
        * (frwMetric A a c * frwMetric A b d - frwMetric A a d * frwMetric A b c) := by
  simp only [linearCurvature, spaceJet, spaceAccel, frwMetric, diagonal_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [frwDiag]
  all_goals field_simp
  all_goals ring

/-- [proved-standard; formal-checked] **The full Riemann tensor at the centre**:
`R_abcd = planeCurvature·(g_ac g_bd − g_ad g_bc)`. -/
theorem curved_riemann {A : ℝ} (hA : A ≠ 0) (B C k : ℝ) (a b c d : Fin 4) :
    riemannLower (frwMetric A) (frwFirstJet A B) (curvedSecondJet A B C k) a b c d
      = planeCurvature A B C k a b * (frwMetric A a c * frwMetric A b d - frwMetric A a d * frwMetric A b c) := by
  rw [curvedSecondJet, riemannLower_add (frwMetric_det hA) _ (frwSecondJet_symm A B C) (spaceJet_symm A k)]
  simp only [Pi.add_apply]
  rw [frw_riemann hA, space_riemann hA]
  unfold planeCurvature
  split_ifs <;> ring

end Curvature

/-! ## 4. The spatial slice, read from its own 3-jet -/

section Slice

/-- [definition] **The slice's metric** at the centre, `h = A²·1`. -/
def sliceMetric (A : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := diagonal fun _ => A ^ 2

/-- [definition] **The slice's second jet** at the centre, `∂_e∂_f h_ij = −kA² δ_ef δ_ij`. -/
def sliceJet (A k : ℝ) : SecondJet 3 := fun e f => diagonal fun _ => if e = f then -(k * A ^ 2) else 0

/-- [proved-standard; formal-checked] The slice's metric is the spacetime metric's spatial block. -/
theorem frwMetric_slice (A : ℝ) (i j : Fin 3) : frwMetric A i.succ j.succ = sliceMetric A i j := by
  by_cases hij : i = j
  · subst hij
    simp [frwMetric, sliceMetric, frwDiag, Fin.succ_ne_zero]
  · simp [frwMetric, sliceMetric, hij]

/-- [proved-standard; formal-checked] The slice's first jet at the centre, `∂_e g_ij` (`e, i, j ≠ 0`), vanishes. -/
theorem frwFirstJet_slice (A B : ℝ) (e i j : Fin 3) : frwFirstJet A B e.succ i.succ j.succ = 0 := by
  rw [frwFirstJet_apply]
  simp [Fin.succ_ne_zero]

/-- [proved-standard; formal-checked] The slice's second jet is the spacetime jet's spatial block. -/
theorem curvedSecondJet_slice (A B C k : ℝ) (e f i j : Fin 3) :
    curvedSecondJet A B C k e.succ f.succ i.succ j.succ = sliceJet A k e f i j := by
  by_cases hij : i = j
  · subst hij
    by_cases hef : e = f
    · subst hef
      simp [curvedSecondJet, frwSecondJet, frwAccel, spaceJet, spaceAccel, sliceJet, Fin.succ_ne_zero]
    · simp [curvedSecondJet, frwSecondJet, frwAccel, spaceJet, spaceAccel, sliceJet, Fin.succ_ne_zero, hef]
  · simp [curvedSecondJet, frwSecondJet, spaceJet, sliceJet, hij]

/-- [proved-standard; formal-checked] The slice's metric is invertible where `A ≠ 0`. -/
theorem sliceMetric_det {A : ℝ} (hA : A ≠ 0) : IsUnit (sliceMetric A).det := by
  rw [sliceMetric, det_diagonal]
  exact (Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero 2 hA).isUnit

/-- [proved-standard; formal-checked] The slice's second jet is symmetric. -/
theorem sliceJet_symm (A k : ℝ) : JetSymm (sliceJet A k) where
  deriv_comm e f a b := by
    by_cases hab : a = b
    · subst hab
      by_cases hef : e = f
      · subst hef
        rfl
      · simp [sliceJet, hef, Ne.symm hef]
    · simp [sliceJet, hab]
  metric_symm e f a b := by
    by_cases hab : a = b
    · rw [hab]
    · simp [sliceJet, hab, Ne.symm hab]

/-- [proved-standard; formal-checked] **The slice's curvature** `R_abcd = (k/A²)(h_ac h_bd − h_ad h_bc)`, built
through the owner's connection from the 3-jet alone. -/
theorem slice_riemann {A : ℝ} (hA : A ≠ 0) (k : ℝ) (a b c d : Fin 3) :
    riemannLower (sliceMetric A) 0 (sliceJet A k) a b c d
      = k / A ^ 2 * (sliceMetric A a c * sliceMetric A b d - sliceMetric A a d * sliceMetric A b c) := by
  rw [riemannLower_of_firstJet_zero (sliceMetric_det hA) (sliceJet_symm A k)]
  simp only [linearCurvature, sliceJet, sliceMetric, diagonal_apply]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp
  all_goals field_simp
  all_goals ring

/-- [proved-standard; formal-checked] **The slice's Ricci tensor** at the centre is `2k δ_ij = 2(k/A²) h_ij`. -/
theorem slice_ricci {A : ℝ} (hA : A ≠ 0) (k : ℝ) (b d : Fin 3) :
    ricci (sliceMetric A) (riemannLower (sliceMetric A) 0 (sliceJet A k)) b d = if b = d then 2 * k else 0 := by
  simp only [ricci, slice_riemann hA]
  simp only [sliceMetric, inv_diagonal_of_ne (fun _ => pow_ne_zero 2 hA), diagonal_apply, Fin.sum_univ_three]
  fin_cases b <;> fin_cases d <;> simp
  all_goals field_simp
  all_goals ring

/-- [proved-standard; formal-checked] **`k/A²` is the slice's sectional curvature**: on any two vectors
`R(X, Y, X, Y) = (k/A²)(|X|²|Y|² − ⟨X, Y⟩²)` in the slice's metric. -/
theorem slice_sectional {A : ℝ} (hA : A ≠ 0) (k : ℝ) (X Y : Fin 3 → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ d, riemannLower (sliceMetric A) 0 (sliceJet A k) a b c d * X a * Y b * X c * Y d
      = k / A ^ 2 * ((X ⬝ᵥ (sliceMetric A *ᵥ X)) * (Y ⬝ᵥ (sliceMetric A *ᵥ Y))
        - (X ⬝ᵥ (sliceMetric A *ᵥ Y)) ^ 2) := by
  simp only [slice_riemann hA]
  simp [sliceMetric, Fin.sum_univ_three, dotProduct, mulVec, diagonal_apply]
  ring

/-- [definition] **The slice's extrinsic curvature** at the centre, `K_ij = ½∂₀g_ij`. -/
def extrinsic (A B : ℝ) (i j : Fin 3) : ℝ := 2⁻¹ * frwFirstJet A B 0 i.succ j.succ

/-- [proved-standard; formal-checked] `K_ij = AB δ_ij`. -/
theorem extrinsic_eq (A B : ℝ) (i j : Fin 3) : extrinsic A B i j = if i = j then A * B else 0 := by
  rw [extrinsic, frwFirstJet_apply]
  by_cases hij : i = j
  · subst hij
    simp [Fin.succ_ne_zero]
    ring
  · simp [hij]

/-- [proved-standard; formal-checked] **Gauss's equation at the centre**: a plane of the slice curves in spacetime
by the slice's own curvature plus the extrinsic product, `R_ijlm = R̃_ijlm + K_il K_jm − K_im K_jl`. -/
theorem curved_gauss {A : ℝ} (hA : A ≠ 0) (B C k : ℝ) (i j l m : Fin 3) :
    riemannLower (frwMetric A) (frwFirstJet A B) (curvedSecondJet A B C k) i.succ j.succ l.succ m.succ
      = riemannLower (sliceMetric A) 0 (sliceJet A k) i j l m
        + (extrinsic A B i l * extrinsic A B j m - extrinsic A B i m * extrinsic A B j l) := by
  rw [curved_riemann hA, slice_riemann hA, frwMetric_slice, frwMetric_slice, frwMetric_slice, frwMetric_slice]
  simp only [planeCurvature, Fin.succ_ne_zero, or_self, if_false, extrinsic_eq, sliceMetric, diagonal_apply]
  split_ifs <;> field_simp <;> ring

/-- [proved-standard; formal-checked] **The slice's part of the Ricci tensor**: `R_ij` is the owner's flat
`R_ij` plus the slice's own Ricci tensor `2k δ_ij`. -/
theorem curved_ricci_split {A : ℝ} (hA : A ≠ 0) (B C k : ℝ) (i j : Fin 3) :
    ricci (frwMetric A) (riemannLower (frwMetric A) (frwFirstJet A B) (curvedSecondJet A B C k)) i.succ j.succ
      = ricci (frwMetric A) (riemannLower (frwMetric A) (frwFirstJet A B) (frwSecondJet A B C)) i.succ j.succ
        + ricci (sliceMetric A) (riemannLower (sliceMetric A) 0 (sliceJet A k)) i j := by
  rw [curved_ricci hA, frw_ricci hA, slice_ricci hA]
  by_cases hij : i = j
  · simp [hij, Fin.succ_ne_zero]
  · simp [hij, Fin.succ_inj]

end Slice

/-! ## 5. Friedmann's equations with curvature -/

section Fluid

/-- [definition] **The owner's Einstein residual** `G + Λg − κT` at the curved jet with the comoving fluid. -/
def curvedResidual (A B C k ρ p Λ κ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  einsteinResidual
    (einsteinTensor (frwMetric A) (ricciOf (frwMetric A) (frwFirstJet A B) (curvedSecondJet A B C k)))
    (frwMetric A) (fluidTensor ρ p (frwMetric A)) Λ κ

/-- [proved-standard; formal-checked] At `k = 0` the residual is the owner's `frwResidual`. -/
theorem curvedResidual_zero (A B C ρ p Λ κ : ℝ) : curvedResidual A B C 0 ρ p Λ κ = frwResidual A B C ρ p Λ κ := by
  rw [curvedResidual, curvedSecondJet_zero, frwResidual]

/-- [proved-standard; formal-checked] **Friedmann's equations with curvature**: `G + Λg = κT` at the jet iff
`3(H² + k/A²) = κρ + Λ` and `2C/A + H² + k/A² = Λ − κp`. -/
theorem curved_friedmann_iff {A : ℝ} (hA : A ≠ 0) (B C k ρ p Λ κ : ℝ) :
    curvedResidual A B C k ρ p Λ κ = 0 ↔
      3 * ((B / A) ^ 2 + k / A ^ 2) = κ * ρ + Λ ∧ 2 * (C / A) + (B / A) ^ 2 + k / A ^ 2 = Λ - κ * p := by
  rw [curvedResidual, einsteinResidual_eq_zero_iff, curved_einstein hA, frw_fluid, frwMetric,
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

/-- [proved-standard; formal-checked] **The acceleration equation is unchanged**: `C/A = Λ/3 − κ(ρ + 3p)/6`. -/
theorem curved_accel {A B C k ρ p Λ κ : ℝ} (hA : A ≠ 0) (h : curvedResidual A B C k ρ p Λ κ = 0) :
    C / A = Λ / 3 - κ * (ρ + 3 * p) / 6 := by
  obtain ⟨h0, h1⟩ := (curved_friedmann_iff hA B C k ρ p Λ κ).mp h
  linarith

/-- [proved-standard; formal-checked] **The continuity equation** `ρ′ = −3H(ρ + p)` with curvature, from the two
equations near `t`. -/
theorem curved_continuity {a a' a'' ρ p : ℝ → ℝ} {k Λ κ t : ℝ} (hκ : κ ≠ 0) (h0 : ∀ᶠ s in nhds t, a s ≠ 0)
    (ha : HasDerivAt a (a' t) t) (ha' : HasDerivAt a' (a'' t) t)
    (field : ∀ᶠ s in nhds t, curvedResidual (a s) (a' s) (a'' s) k (ρ s) (p s) Λ κ = 0) :
    HasDerivAt ρ (-3 * (a' t / a t) * (ρ t + p t)) t := by
  have hF : ∀ᶠ s in nhds t, 3 * ((a' s / a s) ^ 2 + k / a s ^ 2) = κ * ρ s + Λ ∧
      2 * (a'' s / a s) + (a' s / a s) ^ 2 + k / a s ^ 2 = Λ - κ * p s :=
    (h0.and field).mono fun s hs => (curved_friedmann_iff hs.1 _ _ _ _ _ _ _).mp hs.2
  have hρ : ρ =ᶠ[nhds t] fun s => (3 * ((a' s / a s) ^ 2 + k / a s ^ 2) - Λ) / κ :=
    hF.mono fun s hs => by
      show ρ s = (3 * ((a' s / a s) ^ 2 + k / a s ^ 2) - Λ) / κ
      rw [hs.1]
      field_simp
      ring
  have ht := hF.self_of_nhds
  have hat := h0.self_of_nhds
  have hH : a'' t / a t - (a' t / a t) ^ 2 - k / a t ^ 2 = -(κ * (ρ t + p t)) / 2 := by
    linear_combination (1 / 2 : ℝ) * ht.2 - (1 / 2 : ℝ) * ht.1
  have hk : HasDerivAt (fun s => k / a s ^ 2) (-(2 * (a' t / a t) * (k / a t ^ 2))) t := by
    refine ((hasDerivAt_const t k).div (ha.fun_pow 2) (pow_ne_zero 2 hat)).congr_deriv ?_
    field_simp
    ring
  have h := (((((hubble_rate hat ha ha').fun_pow 2).add hk).const_mul 3).sub_const Λ).div_const κ
  refine (h.congr_deriv ?_).congr_of_eventuallyEq hρ
  rw [div_eq_iff hκ]
  norm_num
  linear_combination (6 * (a' t / a t)) * hH

/-- [proved-standard; formal-checked] **A barotropic fluid keeps `ρ·a^(3(1+w))` with curvature**, through the
owner's `barotropic_rate`. -/
theorem curved_barotropic {a a' a'' ρ p : ℝ → ℝ} {k w Λ κ t : ℝ} (hκ : κ ≠ 0) (h0 : ∀ᶠ s in nhds t, a s ≠ 0)
    (hpos : 0 < a t) (ha : HasDerivAt a (a' t) t) (ha' : HasDerivAt a' (a'' t) t)
    (field : ∀ᶠ s in nhds t, curvedResidual (a s) (a' s) (a'' s) k (ρ s) (p s) Λ κ = 0) (hp : p t = w * ρ t) :
    HasDerivAt (fun s => ρ s * a s ^ (3 * (1 + w))) 0 t :=
  barotropic_rate hpos ha (curved_continuity hκ h0 ha ha' field) hp

/-- [definition] **The density parameter** `Ω = κρ/(3H²)`. -/
def densityParameter (κ ρ H : ℝ) : ℝ := κ * ρ / (3 * H ^ 2)

/-- [proved-standard; formal-checked] **The critical density reading** at `Λ = 0`: `Ω − 1 = k/(A²H²)`. -/
theorem density_excess {A B C k ρ p κ : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) (h : curvedResidual A B C k ρ p 0 κ = 0) :
    densityParameter κ ρ (B / A) - 1 = k / (A ^ 2 * (B / A) ^ 2) := by
  obtain ⟨h0, -⟩ := (curved_friedmann_iff hA B C k ρ p 0 κ).mp h
  rw [add_zero] at h0
  rw [densityParameter, ← h0]
  field_simp
  ring

/-- [proved-standard; formal-checked] **`Ω − 1` has the sign of `k`** at `Λ = 0`: above, at or below the critical
density as the slice is closed, flat or open. -/
theorem density_sign {A B C k ρ p κ : ℝ} (hA : A ≠ 0) (hB : B ≠ 0) (h : curvedResidual A B C k ρ p 0 κ = 0) :
    (0 < densityParameter κ ρ (B / A) - 1 ↔ 0 < k) ∧ (densityParameter κ ρ (B / A) - 1 = 0 ↔ k = 0) ∧
      (densityParameter κ ρ (B / A) - 1 < 0 ↔ k < 0) := by
  rw [density_excess hA hB h]
  have hpos : 0 < A ^ 2 * (B / A) ^ 2 := by
    have := div_ne_zero hB hA
    positivity
  refine ⟨div_pos_iff_of_pos_right hpos, ?_, ?_⟩
  · rw [div_eq_zero_iff]
    simp [hpos.ne']
  · rw [div_lt_iff₀ hpos, zero_mul]

end Fluid

/-! ## 6. The metric field and its jets along the coordinate lines -/

section Field

/-- [definition] **The conformal factor** `ψ(x) = 1 + k(x₁² + x₂² + x₃²)/4`. -/
def conformal (k : ℝ) (x : Fin 4 → ℝ) : ℝ := 1 + k * (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) / 4

/-- [definition] **The metric field** `g(x) = diag(−1, a(x₀)²ψ(x)⁻², a(x₀)²ψ(x)⁻², a(x₀)²ψ(x)⁻²)`. -/
def curvedField (a : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  frwMetric (a (x 0) / conformal k x)

/-- [definition] The first-jet field's coefficient on `diag(0, 1, 1, 1)`: `∂₀ = 2aa′ψ⁻²`, `∂_j = −ka²x_jψ⁻³`. -/
def curvedRate (a a' : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) (e : Fin 4) : ℝ :=
  if e = 0 then 2 * a (x 0) * a' (x 0) / conformal k x ^ 2 else -(k * a (x 0) ^ 2 * x e / conformal k x ^ 3)

/-- [definition] **Its first-jet field**, with the scale's rate `a′`. -/
def curvedFirstJetField (a a' : ℝ → ℝ) (k : ℝ) (x : Fin 4 → ℝ) : FirstJet 4 :=
  fun e => curvedRate a a' k x e • spatial

/-- [proved-standard; formal-checked] Along the line `x + t·e`, the coordinate `i` moves only for `i = e`. -/
theorem line_coord (x : Fin 4 → ℝ) (e i : Fin 4) (t : ℝ) :
    (x + t • (Pi.single e 1 : Fin 4 → ℝ)) i = x i + if i = e then t else 0 := by
  by_cases h : i = e
  · subst h
    simp
  · simp [h]

/-- [proved-standard; formal-checked] `ψ` along a coordinate line. -/
theorem conformal_line (k : ℝ) (x : Fin 4 → ℝ) (e : Fin 4) (t : ℝ) :
    conformal k (x + t • (Pi.single e 1 : Fin 4 → ℝ))
      = conformal k x + if e = 0 then 0 else k * (2 * x e * t + t ^ 2) / 4 := by
  fin_cases e <;> simp [conformal] <;> ring

/-- [proved-standard; formal-checked] **`ψ`'s rate** along the line `e` is `k x_e/2` (`0` along the time axis). -/
theorem hasDerivAt_conformal (k : ℝ) (x : Fin 4 → ℝ) (e : Fin 4) :
    HasDerivAt (fun t : ℝ => conformal k (x + t • (Pi.single e 1 : Fin 4 → ℝ)))
      (if e = 0 then 0 else k * x e / 2) 0 := by
  simp only [conformal_line]
  by_cases he : e = 0
  · simp only [he, if_true]
    exact hasDerivAt_const _ _
  · simp only [he, if_false]
    have h := ((((hasDerivAt_id (0 : ℝ)).const_mul (2 * x e)).add ((hasDerivAt_id (0 : ℝ)).pow 2)).const_mul
      k).div_const 4
    refine (h.const_add (conformal k x)).congr_deriv ?_
    simp
    ring

/-- [proved-standard; formal-checked] The scale along a coordinate line moves only along the time axis. -/
theorem hasDerivAt_scale_line {a a' : ℝ → ℝ} (x : Fin 4 → ℝ) (ha : HasDerivAt a (a' (x 0)) (x 0))
    (e : Fin 4) :
    HasDerivAt (fun t : ℝ => a ((x + t • (Pi.single e 1 : Fin 4 → ℝ)) 0)) (if e = 0 then a' (x 0) else 0) 0 := by
  simp only [line_time]
  by_cases he : e = 0
  · simp only [he, if_true]
    exact hasDerivAt_shift ha
  · simp only [he, if_false, add_zero]
    exact hasDerivAt_const _ _

/-- [proved-standard; formal-checked] The coordinate `f` along the line `e` has the rate `δ_fe`. -/
theorem hasDerivAt_coord_line (x : Fin 4 → ℝ) (e f : Fin 4) :
    HasDerivAt (fun t : ℝ => (x + t • (Pi.single e 1 : Fin 4 → ℝ)) f) (if f = e then 1 else 0) 0 := by
  simp only [line_coord]
  by_cases h : f = e
  · simp only [h, if_true]
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (x e)
  · simp only [h, if_false, add_zero]
    exact hasDerivAt_const _ _

/-- [proved-standard; formal-checked] At `k = 0` the field is the owner's flat field. -/
theorem curvedField_zero (a : ℝ → ℝ) : curvedField a 0 = frwField a := by
  funext x
  simp [curvedField, frwField, conformal]

/-- [proved-standard; formal-checked] At `k = 0` the first-jet field is the owner's. -/
theorem curvedFirstJetField_zero (a a' : ℝ → ℝ) : curvedFirstJetField a a' 0 = frwFirstJetField a a' := by
  funext x e
  rw [frwFirstJetField, frwFirstJet_eq_smul, curvedFirstJetField, curvedRate]
  by_cases he : e = 0 <;> simp [he, conformal]

section Centre

variable {x : Fin 4 → ℝ}

/-- [proved-standard; formal-checked] On the time axis `ψ = 1`. -/
theorem conformal_centre (k : ℝ) (hx : ∀ i, i ≠ 0 → x i = 0) : conformal k x = 1 := by
  simp [conformal, hx 1 (by decide), hx 2 (by decide), hx 3 (by decide)]

/-- [proved-standard; formal-checked] **The field at the centre** is the owner's `frwMetric (a(x₀))`. -/
theorem curvedField_centre (a : ℝ → ℝ) (k : ℝ) (hx : ∀ i, i ≠ 0 → x i = 0) :
    curvedField a k x = frwMetric (a (x 0)) := by
  simp [curvedField, conformal_centre k hx]

/-- [proved-standard; formal-checked] **The first jet at the centre** is the owner's flat `frwFirstJet`. -/
theorem curvedFirstJetField_centre (a a' : ℝ → ℝ) (k : ℝ) (hx : ∀ i, i ≠ 0 → x i = 0) :
    curvedFirstJetField a a' k x = frwFirstJet (a (x 0)) (a' (x 0)) := by
  funext e
  rw [frwFirstJet_eq_smul, curvedFirstJetField, curvedRate]
  by_cases he : e = 0 <;> simp [he, conformal_centre k hx, hx e]

/-- [proved-standard; formal-checked] **The Christoffel symbols at the centre are the flat ones.** -/
theorem curved_christoffel (a a' : ℝ → ℝ) (k : ℝ) (hx : ∀ i, i ≠ 0 → x i = 0) (b c d : Fin 4) :
    christoffel (curvedField a k x) (curvedFirstJetField a a' k x) b c d
      = christoffel (frwMetric (a (x 0))) (frwFirstJet (a (x 0)) (a' (x 0))) b c d := by
  rw [curvedField_centre a k hx, curvedFirstJetField_centre a a' k hx]

/-- [proved-standard; formal-checked] The first-jet coefficient's rate along every coordinate line at the centre. -/
theorem hasDerivAt_curvedRate {a a' a'' : ℝ → ℝ} {k : ℝ} (hx : ∀ i, i ≠ 0 → x i = 0)
    (ha : HasDerivAt a (a' (x 0)) (x 0)) (ha' : HasDerivAt a' (a'' (x 0)) (x 0)) (e f : Fin 4) :
    HasDerivAt (fun t : ℝ => curvedRate a a' k (x + t • Pi.single e 1) f)
      (curvedAccelCoef (a (x 0)) (a' (x 0)) (a'' (x 0)) k e f) 0 := by
  have hA := hasDerivAt_scale_line x ha e
  have hA' := hasDerivAt_scale_line x ha' e
  have hψ := hasDerivAt_conformal k x e
  have hc := conformal_centre k hx
  by_cases hf : f = 0
  · simp only [curvedRate, hf, if_true]
    have h := ((hA.const_mul 2).mul hA').div (hψ.pow 2) (by simp [hc])
    refine h.congr_deriv ?_
    by_cases he : e = 0 <;> simp [he, hx e, hc, curvedAccelCoef]
    ring
  · simp only [curvedRate, hf, if_false]
    have h := ((((hA.pow 2).const_mul k).mul (hasDerivAt_coord_line x e f)).div (hψ.pow 3)
      (by simp [hc])).neg
    refine h.congr_deriv ?_
    by_cases he : e = 0 <;> by_cases hef : f = e <;> simp [he, hf, hef, hx e, hx f hf, hc, curvedAccelCoef] <;>
      simp_all [eq_comm]

section CentreRates

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- [proved-standard; formal-checked] `g = lapse + (a/ψ)²·spatial`. -/
theorem curvedField_eq_add (a : ℝ → ℝ) (k : ℝ) (y : Fin 4 → ℝ) :
    curvedField a k y = lapse + (a (y 0) / conformal k y) ^ 2 • spatial :=
  frwMetric_eq_add _

/-- [proved-standard; formal-checked] **The first-jet field is the field's rate** along every coordinate line,
at every point where `ψ ≠ 0`. -/
theorem hasDerivAt_curvedField {a a' : ℝ → ℝ} {k : ℝ} (y : Fin 4 → ℝ) (hψ : conformal k y ≠ 0)
    (ha : HasDerivAt a (a' (y 0)) (y 0)) (e : Fin 4) :
    HasDerivAt (fun t : ℝ => curvedField a k (y + t • Pi.single e 1)) (curvedFirstJetField a a' k y e) 0 := by
  simp only [curvedField_eq_add]
  have hd := (hasDerivAt_scale_line y ha e).div (hasDerivAt_conformal k y e) (by simpa using hψ)
  have h := ((hd.fun_pow 2).smul_const spatial).const_add lapse
  refine h.congr_deriv ?_
  simp only [curvedFirstJetField, curvedRate, zero_smul, add_zero]
  congr 1
  by_cases he : e = 0
  · simp [he]
    field_simp
  · simp [he]
    field_simp

/-- [proved-standard; formal-checked] **The curved second jet is the first-jet field's rate** along every
coordinate line at the centre. -/
theorem hasDerivAt_curvedFirstJetField {a a' a'' : ℝ → ℝ} {k : ℝ} (hx : ∀ i, i ≠ 0 → x i = 0)
    (ha : HasDerivAt a (a' (x 0)) (x 0)) (ha' : HasDerivAt a' (a'' (x 0)) (x 0)) (e f b c : Fin 4) :
    HasDerivAt (fun t : ℝ => curvedFirstJetField a a' k (x + t • Pi.single e 1) f b c)
      (curvedSecondJet (a (x 0)) (a' (x 0)) (a'' (x 0)) k e f b c) 0 := by
  simp only [curvedFirstJetField, Matrix.smul_apply, smul_eq_mul, curvedSecondJet_eq_smul]
  exact (hasDerivAt_curvedRate hx ha ha' e f).mul_const _

/-- [proved-standard; formal-checked] **The built field's Christoffel symbols** have the rate `christoffelJet`
of the curved jet, along every coordinate line at the centre. -/
theorem curved_christoffel_rate {a a' a'' : ℝ → ℝ} {k : ℝ} (hx : ∀ i, i ≠ 0 → x i = 0) (h0 : a (x 0) ≠ 0)
    (ha : HasDerivAt a (a' (x 0)) (x 0)) (ha' : HasDerivAt a' (a'' (x 0)) (x 0)) (e b c d : Fin 4) :
    HasDerivAt
      (fun t : ℝ => christoffel (curvedField a k (x + t • Pi.single e 1))
        (curvedFirstJetField a a' k (x + t • Pi.single e 1)) b c d)
      (christoffelJet (frwMetric (a (x 0))) (frwFirstJet (a (x 0)) (a' (x 0)))
        (curvedSecondJet (a (x 0)) (a' (x 0)) (a'' (x 0)) k) e b c d) 0 := by
  have hG := hasDerivAt_curvedField x (by rw [conformal_centre k hx]; exact one_ne_zero) ha e
  have h := hasDerivAt_christoffel (G := fun t : ℝ => curvedField a k (x + t • Pi.single e 1))
    (dG := fun t : ℝ => curvedFirstJetField a a' k (x + t • Pi.single e 1)) (s := 0)
    (by simpa using hG) (by simpa [curvedField_centre a k hx] using frwMetric_det h0)
    (fun f b c => hasDerivAt_curvedFirstJetField hx ha ha' e f b c) b c d
  simpa [curvedField_centre a k hx, curvedFirstJetField_centre a a' k hx] using h

end CentreRates

end Centre

end Field

/-! ## 7. Witnesses from built metrics -/

section Witnesses

/-- [proved-standard; formal-checked] **Einstein's static universe** solves the field equation: `k = 1`, `a = A₀`,
dust with `κρ = 2/A₀²`, `Λ = 1/A₀²`. -/
theorem einsteinStatic_field {A₀ κ ρ : ℝ} (hA : A₀ ≠ 0) (hρ : κ * ρ = 2 / A₀ ^ 2) :
    curvedResidual A₀ 0 0 1 ρ 0 (1 / A₀ ^ 2) κ = 0 := by
  rw [curved_friedmann_iff hA, hρ]
  constructor
  · field_simp
    ring
  · simp

/-- [proved-standard; formal-checked] **Its curvature**: the time planes are flat and the slice's planes curve by
`1/A₀²`, the curvature of a three-sphere of radius `A₀`. -/
theorem einsteinStatic_riemann {A₀ : ℝ} (hA : A₀ ≠ 0) (a b c d : Fin 4) :
    riemannLower (frwMetric A₀) (frwFirstJet A₀ 0) (curvedSecondJet A₀ 0 0 1) a b c d
      = (if a = 0 ∨ b = 0 then 0 else 1 / A₀ ^ 2)
        * (frwMetric A₀ a c * frwMetric A₀ b d - frwMetric A₀ a d * frwMetric A₀ b c) := by
  rw [curved_riemann hA]
  simp [planeCurvature]

/-- [proved-standard; formal-checked] **Milne's universe** solves the field equation: `k = −1`, `a = t`,
`ρ = p = Λ = 0`. -/
theorem milne_field {t : ℝ} (ht : t ≠ 0) (κ : ℝ) : curvedResidual t 1 0 (-1) 0 0 0 κ = 0 := by
  rw [curved_friedmann_iff ht]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- [proved-standard; formal-checked] **Milne's chart is flat**: its whole Riemann tensor vanishes at the centre,
the open slice's curvature `−1/t²` cancelling the expansion's `H² = 1/t²`. -/
theorem milne_flat {t : ℝ} (ht : t ≠ 0) :
    riemannLower (frwMetric t) (frwFirstJet t 1) (curvedSecondJet t 1 0 (-1)) = 0 := by
  funext a b c d
  rw [curved_riemann ht]
  simp [planeCurvature]

/-- [proved-standard; formal-checked] **De Sitter in the closed slicing** solves the field equation: `k = 1`,
`a = cosh t`, `Λ = 3`, `ρ = p = 0`. -/
theorem deSitterClosed_field (κ t : ℝ) :
    curvedResidual (Real.cosh t) (Real.sinh t) (Real.cosh t) 1 0 0 3 κ = 0 := by
  have hc := (Real.cosh_pos t).ne'
  have h := Real.cosh_sq t
  rw [curved_friedmann_iff hc]
  constructor
  · field_simp
    linear_combination -3 * h
  · field_simp
    linear_combination -h

/-- [proved-standard; formal-checked] **Its curvature is `g_ac g_bd − g_ad g_bc`**: every plane curves by
`1 = Λ/3`. -/
theorem deSitterClosed_riemann (t : ℝ) (a b c d : Fin 4) :
    riemannLower (frwMetric (Real.cosh t)) (frwFirstJet (Real.cosh t) (Real.sinh t))
        (curvedSecondJet (Real.cosh t) (Real.sinh t) (Real.cosh t) 1) a b c d
      = frwMetric (Real.cosh t) a c * frwMetric (Real.cosh t) b d
        - frwMetric (Real.cosh t) a d * frwMetric (Real.cosh t) b c := by
  have hc := (Real.cosh_pos t).ne'
  have hp : planeCurvature (Real.cosh t) (Real.sinh t) (Real.cosh t) 1 a b = 1 := by
    unfold planeCurvature
    split_ifs
    · exact div_self hc
    · rw [← Real.cosh_sq]
      exact div_self (pow_ne_zero 2 hc)
  rw [curved_riemann hc, hp, one_mul]

/-- [proved-standard; formal-checked] **The owner's flat slicing of de Sitter curves alike**: `a = e^(ht)` gives
`R_abcd = h²(g_ac g_bd − g_ad g_bc)`, every plane by `h² = Λ/3`. -/
theorem deSitterFlat_riemann (h t : ℝ) (a b c d : Fin 4) :
    riemannLower (frwMetric (Real.exp (h * t))) (frwFirstJet (Real.exp (h * t)) (h * Real.exp (h * t)))
        (frwSecondJet (Real.exp (h * t)) (h * Real.exp (h * t)) (h ^ 2 * Real.exp (h * t))) a b c d
      = h ^ 2 * (frwMetric (Real.exp (h * t)) a c * frwMetric (Real.exp (h * t)) b d
        - frwMetric (Real.exp (h * t)) a d * frwMetric (Real.exp (h * t)) b c) := by
  have he := (Real.exp_pos (h * t)).ne'
  have hp : planeCurvature (Real.exp (h * t)) (h * Real.exp (h * t)) (h ^ 2 * Real.exp (h * t)) 0 a b = h ^ 2 := by
    unfold planeCurvature
    split_ifs
    · field_simp
    · field_simp
      ring
  rw [frw_riemann he, hp]

section WitnessRates

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {x : Fin 4 → ℝ}

/-- [proved-standard; formal-checked] **The static universe's built field**: its jets are read along every
coordinate line at the centre. -/
theorem einsteinStatic_jets (A₀ : ℝ) (hx : ∀ i, i ≠ 0 → x i = 0) (e f b c : Fin 4) :
    HasDerivAt (fun t : ℝ => curvedField (fun _ => A₀) 1 (x + t • Pi.single e 1))
        (curvedFirstJetField (fun _ => A₀) (fun _ => 0) 1 x e) 0 ∧
      HasDerivAt (fun t : ℝ => curvedFirstJetField (fun _ => A₀) (fun _ => 0) 1 (x + t • Pi.single e 1) f b c)
        (curvedSecondJet A₀ 0 0 1 e f b c) 0 :=
  ⟨hasDerivAt_curvedField x (by rw [conformal_centre 1 hx]; exact one_ne_zero) (hasDerivAt_const _ _) e,
    hasDerivAt_curvedFirstJetField (a'' := fun _ => 0) hx (hasDerivAt_const _ _) (hasDerivAt_const _ _) e f b c⟩

/-- [proved-standard; formal-checked] **Milne's built field**: its jets are read along every coordinate line at
the centre. -/
theorem milne_jets (hx : ∀ i, i ≠ 0 → x i = 0) (e f b c : Fin 4) :
    HasDerivAt (fun t : ℝ => curvedField (fun s => s) (-1) (x + t • Pi.single e 1))
        (curvedFirstJetField (fun s => s) (fun _ => 1) (-1) x e) 0 ∧
      HasDerivAt (fun t : ℝ => curvedFirstJetField (fun s => s) (fun _ => 1) (-1) (x + t • Pi.single e 1) f b c)
        (curvedSecondJet (x 0) 1 0 (-1) e f b c) 0 :=
  ⟨hasDerivAt_curvedField x (by rw [conformal_centre (-1) hx]; exact one_ne_zero) (hasDerivAt_id' _) e,
    hasDerivAt_curvedFirstJetField (a'' := fun _ => 0) hx (hasDerivAt_id' _) (hasDerivAt_const _ _) e f b c⟩

/-- [proved-standard; formal-checked] **De Sitter's closed built field**: its jets are read along every coordinate
line at the centre, from Mathlib's derivatives of `cosh` and `sinh`. -/
theorem deSitterClosed_jets (hx : ∀ i, i ≠ 0 → x i = 0) (e f b c : Fin 4) :
    HasDerivAt (fun t : ℝ => curvedField Real.cosh 1 (x + t • Pi.single e 1))
        (curvedFirstJetField Real.cosh Real.sinh 1 x e) 0 ∧
      HasDerivAt (fun t : ℝ => curvedFirstJetField Real.cosh Real.sinh 1 (x + t • Pi.single e 1) f b c)
        (curvedSecondJet (Real.cosh (x 0)) (Real.sinh (x 0)) (Real.cosh (x 0)) 1 e f b c) 0 :=
  ⟨hasDerivAt_curvedField x (by rw [conformal_centre 1 hx]; exact one_ne_zero) (Real.hasDerivAt_cosh _) e,
    hasDerivAt_curvedFirstJetField hx (Real.hasDerivAt_cosh _) (Real.hasDerivAt_sinh _) e f b c⟩

end WitnessRates

end Witnesses

end Holonics.Physics.Spacetime.CurvedFriedmann

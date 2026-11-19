import Holonics.Physics.Fluid.ControlVolume
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Fluid.TimeAdvanceKelvin: the pressure solve as a projection, a tick of the time advance, and Kelvin in time

[proved-standard; formal-checked] The source is #410's box on the fluid time advance (the cell's time advance
with its pressure solve, and Kelvin's theorem in time), which carries the closing `[open]` paragraph of
`Physics/Fluid/ControlVolume` (owed there under #62, whose obligations #410 carries): the time advance of the
cell, "so that the mechanical debit of the viscous heat is computed rather than supplied", "the pressure solve
(incompressibility `tr G = 0` enforced by a projection whose multiplier is `p`)" and "Kelvin's conservation of
circulation along a material loop". It extends the owner's coholon reading (`vorticity`,
`pressure_vorticity_zero`, `pressure_circulation_zero`) and `Objects/Pairing.coordinate_stokes`. Atlas rows:
`fluid.velocity-coholon` (the instantaneous face of Kelvin, "whose conservation along material loops needs the
time advance"), `fluid.kelvin-holonomy` ("Euler conserves Γ on material cycles"), `ns.kelvin-curve` ("source
derivation from the momentum law owed"), `ns.moving-loop-pressure` and `heat.viscous-port` ("the fluid's own
kinetic change over a tick needs the time advance"). The objects guide reads Kelvin circulation as a holonomy
pairing (ELEMENTARY_OBJECTS, "The targets").

What is proved.

1. [proved-standard; formal-checked] **The pressure solve is a projection** (§1). On a finite complex with
   vertex-to-edge incidence `d₀ : Matrix E V ℝ` and a positive definite edge metric `M`, the divergence of an
   edge velocity is `d₀ᵀ M u` (`divergence`). The ranges of `d₀ᵀ M d₀` and `d₀ᵀ M` agree (`range_poissonMap`),
   so every provisional velocity `u*` has a pressure with `d₀ᵀ M d₀ p = d₀ᵀ M u*` (`exists_pressure`,
   `pressure_solves`), unique up to `ker d₀` (`solvesPressure_iff`). The projected velocity
   `P u* = u* − d₀ p` (`project`) is divergence-free (`divergence_project`) and `M`-orthogonal to every
   pressure part (`project_orthogonal`), so the kinetic energy `½⟨u, M u⟩` falls by `½⟨d₀ p, M d₀ p⟩`
   (`kinetic_project`, Pythagoras). It is the divergence-free field nearest `u*` in the metric, the reading of
   `p` as the multiplier of the constraint (`project_nearest`); a divergence-free field that differs from `u*`
   by a pressure part is `P u*` (`project_eq_of`); it fixes divergence-free fields and is idempotent
   (`project_of_divergence_zero`, `project_project`), and it keeps the circulation of every cycle
   (`circulation_project`) and the vorticity `d₁ u` whenever `d₁ d₀ = 0` (`vorticity_project`).
   [proved-derived; formal-checked] On the owner's Holarchy cell complex the last two are the owner's pressure
   silences applied to the solved pressure (`coholon_vorticity_project`, `coholon_circulation_project`).
2. [proved-standard; formal-checked] **One tick of the time advance** (§2). The tick
   `u_(n+1) = P(u_n + Δt (f − D u_n))` (`tick`) obeys the ledger
   `K(u_(n+1)) − K(u_n) = Δt W − Δt Q − L + Δt² K(f − D u_n)` (`tick_ledger`), every term named: the kinetic
   energy `K = ½⟨·, M ·⟩` (`kinetic`), the forcing work `W = ⟨u_n, M f⟩` (`forcingWork`), the viscous debit
   `Q = ⟨u_n, M D u_n⟩` (`viscousDebit`), the projection's loss `L = ½⟨d₀ p, M d₀ p⟩` (`projectionLoss`) and
   the explicit scheme's second-order term. The debit is computed from the tick, not supplied; it is
   nonnegative when `M D` is positive semidefinite (`viscousDebit_nonneg`; at `M = 1`, a symmetric positive
   semidefinite `D`), the loss is nonnegative (`projectionLoss_nonneg`), and the energy is bounded by the ledger
   without the loss (`tick_energy_le`). The advanced velocity is divergence-free (`divergence_tick`): the net
   outflow of every dual cell is zero, so the storage `ρ̇V` that a uniform density reads from the outflow is
   zero. Around a cycle the tick changes the circulation by `Δt` times the circulation of `f − D u_n`, the
   pressure contributing nothing (`tick_circulation`).
3. [proved-standard; formal-checked] **Kelvin's theorem in time** (§3). Let `u : ℝ → E → E` be a velocity on a
   complete real inner product space (any finite-dimensional one), jointly `C¹`, and `C : ℝ → ℝ → E` a flow
   of loops, jointly `C²`, carried by it (`∂ₜC(t, s) = u(t, C(t, s))`) and closed (`C(t, 1) = C(t, 0)`),
   under the momentum law `∂ₜu + (Du) u = −∇Π + F` with each `Π(t, ·)` differentiable and each `F(t, ·)`
   continuous. The circulation
   `Γ_u(t) = ∫₀¹ ⟨u(t, C(t, s)), ∂ₛC(t, s)⟩ ds` (`circulation`) has as derivative the circulation of `F`
   around the same loop (`circulation_hasDerivAt`): the potential and the moving edge are silent. The route:
   the material derivative is the joint derivative along `(1, u)` (`fderiv_uncurry_apply`); the tangent
   advances by `∂ₜ∂ₛC = ∂ₛ(u ∘ C)`, from the symmetry of the second derivative of a `C²` map; the integrand's
   time derivative is the loop derivative of the Bernoulli function `−Π + ½|u|²` plus `⟨F, ∂ₛC⟩`
   (`loopIntegrand_time_deriv`); and the derivative passes under the integral by a Leibniz rule for a jointly
   `C¹` integrand, its domination read from compactness (`hasDerivAt_intervalIntegral_of_contDiff`). For Euler
   with a barotropic potential (`F = 0`) the circulation has derivative zero (`kelvin_hasDerivAt`) and is
   constant (`kelvin`). Beside `HolonicsResearch/Fluid/NavierStokesMovingLoop`, whose
   `hasDerivAt_movingCirculation_eq_momentum` takes the domination receipts and the tangent's mixed transport
   as hypotheses on the house's Navier–Stokes solution, both are derived here from joint regularity, and the
   source is the circulation of the non-potential force.
4. [proved-derived; formal-checked] **A digon** (§4). Two vertices joined by two parallel edges, unit metric:
   the projection of `(1, 0)` removes the pressure part `(½, ½)` and keeps the circulating part `(½, −½)`, the
   circulation around the digon stays `1` and the kinetic energy falls from `½` to `¼` (`digon_projection`).

What is not claimed. The tick carries no advection term: it is the projection step with explicit forcing and
viscosity, and its circulation statement is about a fixed cycle; a discrete material loop and a discrete Kelvin
theorem are not stated. The second-order term is written out, not bounded by a stability condition, and no
convergence of the tick to the continuum is stated. Variable density and its continuity tick are not treated;
only the uniform density's storage reads zero. The continuum theorem assumes the flow of loops and its
regularity; it does not construct the flow from `u`. Closure of the positions suffices and matching end
derivatives are not assumed, because the Bernoulli function reads only the position. The owner's remaining open
items (the discretization defect of a non-affine field, a native source-conforming solver) stay open.

The computational object is the helical pair interaction read on the fluid: the velocity is a coholon on the
contacts (edges), the metric `M` is the contact material that pairs it with flux, the pressure is the vertex
potential whose coboundary the projection removes, and a circulation is the reading of a cycle, which that
potential never reaches. Of the winding guide's six general objects this touches the cell holonomy (circulation
on cycles and vorticity on faces, kept by the projection and conserved along a material loop), faces and
placement (the `M`-orthogonal split of a velocity into its divergence-free and pressure parts, and the energy
ledger of a tick) and the tube (one clocked tick of the advance, and the flow's clock carrying the loop); the
helix, the pair and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.Fluid.TimeAdvanceKelvin

open Matrix

/-! ## 1. The pressure solve as a projection -/

section Projection

variable {V E : Type*} [Fintype V] [Fintype E] (d₀ : Matrix E V ℝ) (M : Matrix E E ℝ)

/-- [definition] **The divergence** of an edge velocity in the edge metric: `d₀ᵀ M u`, the net flux out of
each vertex's dual cell. -/
def divergence (u : E → ℝ) : V → ℝ := d₀ᵀ *ᵥ (M *ᵥ u)

/-- [definition] **The kinetic energy** `½⟨u, M u⟩`. -/
def kinetic (u : E → ℝ) : ℝ := (1 / 2 : ℝ) * (u ⬝ᵥ (M *ᵥ u))

/-- [definition] **The pressure equation** for `u`: `d₀ᵀ M d₀ p = d₀ᵀ M u`. -/
def SolvesPressure (u : E → ℝ) (p : V → ℝ) : Prop :=
  divergence d₀ M (d₀ *ᵥ p) = divergence d₀ M u

open Classical in
/-- [definition] **The solved pressure**: a solution of the pressure equation (one exists for positive definite
`M`, `exists_pressure`). -/
def pressure (u : E → ℝ) : V → ℝ :=
  if h : ∃ p, SolvesPressure d₀ M u p then Classical.choose h else 0

/-- [definition] **The projection** `P u = u − d₀ p` with `p` the solved pressure. -/
def project (u : E → ℝ) : E → ℝ := u - d₀ *ᵥ pressure d₀ M u

/-- [definition] The divergence as a linear map, `d₀ᵀ M`. -/
def divergenceMap : (E → ℝ) →ₗ[ℝ] (V → ℝ) := (mulVecLin d₀ᵀ).comp (mulVecLin M)

/-- [definition] The pressure operator as a linear map, `d₀ᵀ M d₀` (the weighted vertex Laplacian). -/
def poissonMap : (V → ℝ) →ₗ[ℝ] (V → ℝ) := (divergenceMap d₀ M).comp (mulVecLin d₀)

variable {d₀ M}

/-- [proved-standard; formal-checked] A pressure part pairs as its potential: `⟨d₀ q, w⟩ = ⟨q, d₀ᵀ w⟩`. -/
theorem potential_pairing (q : V → ℝ) (w : E → ℝ) : (d₀ *ᵥ q) ⬝ᵥ w = q ⬝ᵥ (d₀ᵀ *ᵥ w) := by
  simpa using Holonics.Objects.Pairing.coordinate_stokes d₀ᵀ q w

omit [Fintype E] in
/-- [proved-standard; formal-checked] A positive definite real metric is symmetric. -/
theorem metric_symm (hM : M.PosDef) : Mᵀ = M :=
  (conjTranspose_eq_transpose_of_trivial M).symm.trans hM.isHermitian

/-- [proved-standard; formal-checked] The metric pairing is symmetric: `⟨x, M y⟩ = ⟨y, M x⟩`. -/
theorem metric_pairing_comm (hM : M.PosDef) (x y : E → ℝ) : x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, metric_symm hM, dotProduct_comm]

/-- [proved-standard; formal-checked] The metric is positive on a nonzero velocity. -/
theorem metric_pos (hM : M.PosDef) {x : E → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ (M *ᵥ x) := by
  simpa using hM.dotProduct_mulVec_pos hx

/-- [proved-standard; formal-checked] The metric is nonnegative. -/
theorem metric_nonneg (hM : M.PosDef) (x : E → ℝ) : 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (metric_pos hM hx).le

/-- [proved-standard; formal-checked] A velocity of zero metric norm is zero. -/
theorem eq_zero_of_metric (hM : M.PosDef) {x : E → ℝ} (h : x ⬝ᵥ (M *ᵥ x) = 0) : x = 0 := by
  by_contra hx
  exact (metric_pos hM hx).ne' h

/-- [proved-standard; formal-checked] The kinetic energy of a sum: `K(x + y) = K x + K y + ⟨x, M y⟩`. -/
theorem kinetic_add (hM : M.PosDef) (x y : E → ℝ) :
    kinetic M (x + y) = kinetic M x + kinetic M y + x ⬝ᵥ (M *ᵥ y) := by
  unfold kinetic
  rw [mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, metric_pairing_comm hM y x]
  ring

/-- [proved-standard; formal-checked] The kinetic energy is quadratic: `K(c x) = c² K x`. -/
theorem kinetic_smul (c : ℝ) (x : E → ℝ) : kinetic M (c • x) = c ^ 2 * kinetic M x := by
  unfold kinetic
  rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

/-- [proved-standard; formal-checked] The kinetic energy is nonnegative. -/
theorem kinetic_nonneg (hM : M.PosDef) (x : E → ℝ) : 0 ≤ kinetic M x := by
  unfold kinetic
  have := metric_nonneg hM x
  positivity

/-- [proved-standard; formal-checked] A pressure part is `M`-orthogonal to every divergence-free velocity. -/
theorem potential_orthogonal (q : V → ℝ) {v : E → ℝ} (hv : divergence d₀ M v = 0) :
    (d₀ *ᵥ q) ⬝ᵥ (M *ᵥ v) = 0 := by
  rw [potential_pairing]
  exact (congrArg (q ⬝ᵥ ·) hv).trans (dotProduct_zero q)

/-- [proved-standard; formal-checked] A divergence-free pressure part is zero. -/
theorem potential_eq_zero (hM : M.PosDef) {r : V → ℝ} (h : divergence d₀ M (d₀ *ᵥ r) = 0) :
    d₀ *ᵥ r = 0 :=
  eq_zero_of_metric hM (potential_orthogonal r h)

omit [Fintype V] in
/-- [proved-standard; formal-checked] The divergence is additive: `div (u − v) = div u − div v`. -/
theorem divergence_sub (u v : E → ℝ) :
    divergence d₀ M (u - v) = divergence d₀ M u - divergence d₀ M v := by
  simp [divergence, mulVec_sub]

/-- [proved-standard; formal-checked] The kernel of the pressure operator is `ker d₀`. -/
theorem ker_poissonMap (hM : M.PosDef) :
    LinearMap.ker (poissonMap d₀ M) = LinearMap.ker (mulVecLin d₀) := by
  ext p
  simp only [LinearMap.mem_ker, poissonMap, divergenceMap, LinearMap.comp_apply, mulVecLin_apply]
  constructor
  · intro h
    exact potential_eq_zero hM h
  · intro h
    rw [h, mulVec_zero, mulVec_zero]

/-- [proved-standard; formal-checked] **The ranges agree**: `range (d₀ᵀ M d₀) = range (d₀ᵀ M)`. -/
theorem range_poissonMap (hM : M.PosDef) :
    LinearMap.range (poissonMap d₀ M) = LinearMap.range (divergenceMap d₀ M) := by
  classical
  have hle : LinearMap.range (poissonMap d₀ M) ≤ LinearMap.range (divergenceMap d₀ M) :=
    LinearMap.range_comp_le_range _ _
  have htop : LinearMap.range (mulVecLin M) = ⊤ :=
    LinearMap.range_eq_top.mpr (mulVec_surjective_iff_isUnit.mpr hM.isUnit)
  have hdiv : LinearMap.range (divergenceMap d₀ M) = LinearMap.range (mulVecLin d₀ᵀ) :=
    LinearMap.range_comp_of_range_eq_top _ htop
  have h1 := LinearMap.finrank_range_add_finrank_ker (poissonMap d₀ M)
  have h2 := LinearMap.finrank_range_add_finrank_ker (mulVecLin d₀)
  rw [ker_poissonMap hM] at h1
  have hrank : Module.finrank ℝ (LinearMap.range (mulVecLin d₀ᵀ)) =
      Module.finrank ℝ (LinearMap.range (mulVecLin d₀)) := rank_transpose d₀
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [hdiv, hrank]
  omega

/-- [proved-standard; formal-checked] **Every velocity has a pressure**: the pressure equation is solvable. -/
theorem exists_pressure (hM : M.PosDef) (u : E → ℝ) : ∃ p, SolvesPressure d₀ M u p := by
  have hu : divergence d₀ M u ∈ LinearMap.range (poissonMap d₀ M) := by
    rw [range_poissonMap hM]
    exact ⟨u, rfl⟩
  obtain ⟨p, hp⟩ := hu
  exact ⟨p, hp⟩

/-- [proved-standard; formal-checked] The solved pressure solves the pressure equation. -/
theorem pressure_solves (hM : M.PosDef) (u : E → ℝ) : SolvesPressure d₀ M u (pressure d₀ M u) := by
  classical
  have h := exists_pressure (d₀ := d₀) hM u
  unfold pressure
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- [proved-standard; formal-checked] **The pressure is unique up to `ker d₀`**: `q` solves iff `d₀ q = d₀ p`. -/
theorem solvesPressure_iff (hM : M.PosDef) {u : E → ℝ} {p : V → ℝ} (hp : SolvesPressure d₀ M u p)
    (q : V → ℝ) : SolvesPressure d₀ M u q ↔ d₀ *ᵥ q = d₀ *ᵥ p := by
  constructor
  · intro hq
    have h : divergence d₀ M (d₀ *ᵥ (q - p)) = 0 := by
      rw [mulVec_sub, divergence_sub, hq, hp, sub_self]
    have := potential_eq_zero hM h
    rwa [mulVec_sub, sub_eq_zero] at this
  · intro h
    unfold SolvesPressure
    rw [h]
    exact hp

/-- [proved-standard; formal-checked] **The projected velocity is divergence-free**. -/
theorem divergence_project (hM : M.PosDef) (u : E → ℝ) : divergence d₀ M (project d₀ M u) = 0 := by
  rw [project, divergence_sub, pressure_solves hM u, sub_self]

/-- [proved-standard; formal-checked] The projected velocity is `M`-orthogonal to every pressure part. -/
theorem project_orthogonal (hM : M.PosDef) (u : E → ℝ) (q : V → ℝ) :
    (d₀ *ᵥ q) ⬝ᵥ (M *ᵥ project d₀ M u) = 0 :=
  potential_orthogonal q (divergence_project hM u)

/-- [proved-standard; formal-checked] **Pythagoras**: `K u = K (P u) + K (d₀ p)`; the projection loses `½|d₀ p|²_M`. -/
theorem kinetic_project (hM : M.PosDef) (u : E → ℝ) :
    kinetic M u = kinetic M (project d₀ M u) + kinetic M (d₀ *ᵥ pressure d₀ M u) := by
  have hu : u = project d₀ M u + d₀ *ᵥ pressure d₀ M u := by rw [project, sub_add_cancel]
  conv_lhs => rw [hu]
  rw [kinetic_add hM, metric_pairing_comm hM, project_orthogonal hM, add_zero]

/-- [proved-standard; formal-checked] A divergence-free `v` with `u − v` a pressure part is the projection of `u`. -/
theorem project_eq_of (hM : M.PosDef) {u v : E → ℝ} (hv : divergence d₀ M v = 0) (q : V → ℝ)
    (h : u = v + d₀ *ᵥ q) : project d₀ M u = v := by
  have hdiff : project d₀ M u = v + d₀ *ᵥ (q - pressure d₀ M u) := by
    rw [project, h, mulVec_sub]
    abel
  have hzero : divergence d₀ M (d₀ *ᵥ (q - pressure d₀ M u)) = 0 := by
    have : d₀ *ᵥ (q - pressure d₀ M u) = project d₀ M u - v := by rw [hdiff]; abel
    rw [this, divergence_sub, divergence_project hM, hv, sub_self]
  rw [hdiff, potential_eq_zero hM hzero, add_zero]

/-- [proved-standard; formal-checked] The projection fixes a divergence-free velocity. -/
theorem project_of_divergence_zero (hM : M.PosDef) {v : E → ℝ} (hv : divergence d₀ M v = 0) :
    project d₀ M v = v :=
  project_eq_of hM hv 0 (by rw [mulVec_zero, add_zero])

/-- [proved-standard; formal-checked] **The projection is idempotent**. -/
theorem project_project (hM : M.PosDef) (u : E → ℝ) :
    project d₀ M (project d₀ M u) = project d₀ M u :=
  project_of_divergence_zero hM (divergence_project hM u)

/-- [proved-standard; formal-checked] **The multiplier reading**: `P u` is the divergence-free field nearest `u`. -/
theorem project_nearest (hM : M.PosDef) (u : E → ℝ) {v : E → ℝ} (hv : divergence d₀ M v = 0) :
    kinetic M (u - project d₀ M u) ≤ kinetic M (u - v) := by
  have hsplit : u - v = (u - project d₀ M u) + (project d₀ M u - v) := by abel
  have hgrad : u - project d₀ M u = d₀ *ᵥ pressure d₀ M u := by rw [project, sub_sub_cancel]
  have hdiv : divergence d₀ M (project d₀ M u - v) = 0 := by
    rw [divergence_sub, divergence_project hM, hv, sub_self]
  rw [hsplit, kinetic_add hM, hgrad, potential_orthogonal _ hdiv, add_zero]
  linarith [kinetic_nonneg hM (project d₀ M u - v)]

/-- [proved-standard; formal-checked] **The projection keeps a cycle's circulation**:
`d₀ᵀ z = 0 ⇒ ⟨P u, z⟩ = ⟨u, z⟩`. -/
theorem circulation_project (u : E → ℝ) {z : E → ℝ} (hz : d₀ᵀ *ᵥ z = 0) :
    project d₀ M u ⬝ᵥ z = u ⬝ᵥ z := by
  rw [project, sub_dotProduct, potential_pairing, hz, dotProduct_zero, sub_zero]

/-- [proved-standard; formal-checked] **The projection keeps the vorticity**: `d₁ d₀ = 0 ⇒ d₁ (P u) = d₁ u`. -/
theorem vorticity_project {F : Type*} [Fintype F] (d₁ : Matrix F E ℝ) (hd : d₁ * d₀ = 0)
    (u : E → ℝ) : d₁ *ᵥ project d₀ M u = d₁ *ᵥ u := by
  rw [project, mulVec_sub, mulVec_mulVec, hd, zero_mulVec, sub_zero]

section Coholon

variable (K : Holonics.HolarchyCore.CellComplex ℝ) (N : Matrix K.C₁ K.C₁ ℝ)

/-- [proved-derived; formal-checked] On the owner's cell complex the projection keeps `ControlVolume.vorticity`. -/
theorem coholon_vorticity_project (u : K.C₁ → ℝ) :
    ControlVolume.vorticity K (project K.d₁ᵀ N u) = ControlVolume.vorticity K u := by
  have h := ControlVolume.pressure_vorticity_zero K (pressure K.d₁ᵀ N u)
  unfold ControlVolume.vorticity ControlVolume.pressurePart at h
  unfold ControlVolume.vorticity project
  rw [mulVec_sub, h, sub_zero]

/-- [proved-derived; formal-checked] On the owner's cell complex the projection keeps a cycle's circulation. -/
theorem coholon_circulation_project (u : K.C₁ → ℝ) {γ : K.C₁ → ℝ} (hγ : K.d₁ *ᵥ γ = 0) :
    ControlVolume.circulation K (project K.d₁ᵀ N u) γ = ControlVolume.circulation K u γ := by
  have h := ControlVolume.pressure_circulation_zero K (pressure K.d₁ᵀ N u) hγ
  unfold ControlVolume.circulation ControlVolume.pressurePart at h
  unfold ControlVolume.circulation project
  rw [sub_dotProduct, h, sub_zero]

end Coholon

end Projection

/-! ## 2. One tick of the time advance -/

section Tick

variable {V E : Type*} [Fintype V] [Fintype E] (d₀ : Matrix E V ℝ) (M : Matrix E E ℝ)

/-- [definition] **One tick**: `u ↦ P(u + Δt (f − D u))`, the forcing `f` and the viscous operator `D` explicit. -/
def tick (D : Matrix E E ℝ) (f : E → ℝ) (Δt : ℝ) (u : E → ℝ) : E → ℝ :=
  project d₀ M (u + Δt • (f - D *ᵥ u))

/-- [definition] **The forcing work** `⟨u, M f⟩`. -/
def forcingWork (u f : E → ℝ) : ℝ := u ⬝ᵥ (M *ᵥ f)

/-- [definition] **The viscous debit** `⟨u, M D u⟩`, the mechanical side of the viscous heat. -/
def viscousDebit (D : Matrix E E ℝ) (u : E → ℝ) : ℝ := u ⬝ᵥ (M *ᵥ (D *ᵥ u))

/-- [definition] **The projection's loss** `½⟨d₀ p, M d₀ p⟩` on the provisional velocity `u`. -/
def projectionLoss (u : E → ℝ) : ℝ := kinetic M (d₀ *ᵥ pressure d₀ M u)

variable {d₀ M}

/-- [proved-standard; formal-checked] **The tick's energy ledger**: `ΔK = Δt W − Δt Q − L + Δt² K(f − D u)`. -/
theorem tick_ledger (hM : M.PosDef) (D : Matrix E E ℝ) (f : E → ℝ) (Δt : ℝ) (u : E → ℝ) :
    kinetic M (tick d₀ M D f Δt u) - kinetic M u =
      Δt * forcingWork M u f - Δt * viscousDebit M D u
        - projectionLoss d₀ M (u + Δt • (f - D *ᵥ u)) + Δt ^ 2 * kinetic M (f - D *ᵥ u) := by
  have hproj := kinetic_project (d₀ := d₀) hM (u + Δt • (f - D *ᵥ u))
  rw [kinetic_add hM, kinetic_smul, mulVec_smul, dotProduct_smul, smul_eq_mul, mulVec_sub,
    dotProduct_sub] at hproj
  unfold tick projectionLoss forcingWork viscousDebit
  linarith

/-- [proved-standard; formal-checked] The viscous debit is nonnegative when `M D` is positive semidefinite. -/
theorem viscousDebit_nonneg {D : Matrix E E ℝ} (hD : (M * D).PosSemidef) (u : E → ℝ) :
    0 ≤ viscousDebit M D u := by
  unfold viscousDebit
  rw [mulVec_mulVec]
  simpa using hD.dotProduct_mulVec_nonneg u

/-- [proved-standard; formal-checked] The projection's loss is nonnegative. -/
theorem projectionLoss_nonneg (hM : M.PosDef) (u : E → ℝ) : 0 ≤ projectionLoss d₀ M u :=
  kinetic_nonneg hM _

/-- [proved-standard; formal-checked] The tick's energy is bounded by the ledger without the projection's loss. -/
theorem tick_energy_le (hM : M.PosDef) (D : Matrix E E ℝ) (f : E → ℝ) (Δt : ℝ) (u : E → ℝ) :
    kinetic M (tick d₀ M D f Δt u) ≤
      kinetic M u + Δt * forcingWork M u f - Δt * viscousDebit M D u
        + Δt ^ 2 * kinetic M (f - D *ᵥ u) := by
  have h := tick_ledger (d₀ := d₀) hM D f Δt u
  have h0 := projectionLoss_nonneg (d₀ := d₀) hM (u + Δt • (f - D *ᵥ u))
  linarith

/-- [proved-standard; formal-checked] **The advanced velocity is divergence-free**: every dual cell's outflow
is zero. -/
theorem divergence_tick (hM : M.PosDef) (D : Matrix E E ℝ) (f : E → ℝ) (Δt : ℝ) (u : E → ℝ) :
    divergence d₀ M (tick d₀ M D f Δt u) = 0 :=
  divergence_project hM _

/-- [proved-standard; formal-checked] Around a cycle the tick adds `Δt ⟨f − D u, z⟩`; the pressure adds nothing. -/
theorem tick_circulation (D : Matrix E E ℝ) (f : E → ℝ) (Δt : ℝ) (u : E → ℝ) {z : E → ℝ}
    (hz : d₀ᵀ *ᵥ z = 0) : tick d₀ M D f Δt u ⬝ᵥ z = u ⬝ᵥ z + Δt * ((f - D *ᵥ u) ⬝ᵥ z) := by
  rw [tick, circulation_project _ hz, add_dotProduct, smul_dotProduct, smul_eq_mul]

end Tick

/-! ## 3. Kelvin's theorem in time -/

section Kelvin

open MeasureTheory Set
open scoped RealInnerProductSpace

/-- [proved-standard; formal-checked] A joint derivative read along the first slot. -/
theorem hasDerivAt_fst_slice {X G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : ℝ × X → G} {L : ℝ × X →L[ℝ] G} {t : ℝ} {x : X}
    (h : HasFDerivAt f L (t, x)) : HasDerivAt (fun τ => f (τ, x)) (L (1, 0)) t := by
  have hp : HasDerivAt (fun τ : ℝ => (τ, x)) ((1 : ℝ), (0 : X)) t :=
    (hasDerivAt_id' t).prodMk (hasDerivAt_const t x)
  exact h.comp_hasDerivAt t hp

/-- [proved-standard; formal-checked] A joint derivative read along the second slot. -/
theorem hasDerivAt_snd_slice {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℝ × ℝ → G} {L : ℝ × ℝ →L[ℝ] G} {t s : ℝ}
    (h : HasFDerivAt f L (t, s)) : HasDerivAt (fun σ => f (t, σ)) (L (0, 1)) s := by
  have hp : HasDerivAt (fun σ : ℝ => (t, σ)) ((0 : ℝ), (1 : ℝ)) s :=
    (hasDerivAt_const s t).prodMk (hasDerivAt_id' s)
  exact h.comp_hasDerivAt s hp

/-- [proved-standard; formal-checked] **Leibniz's rule** for a jointly `C¹` integrand on `[a, b]`. -/
theorem hasDerivAt_intervalIntegral_of_contDiff {g : ℝ → ℝ → ℝ}
    (hg : ContDiff ℝ 1 (Function.uncurry g)) (a b t : ℝ) :
    HasDerivAt (fun τ => ∫ s in a..b, g τ s)
      (∫ s in a..b, fderiv ℝ (Function.uncurry g) (t, s) (1, 0)) t := by
  have hG' : Continuous (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry g) p (1, 0)) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  obtain ⟨K, hK⟩ := ((isCompact_closedBall t 1).prod
    (isCompact_uIcc (a := a) (b := b))).exists_bound_of_continuousOn hG'.continuousOn
  have hdiff : ∀ τ s, HasDerivAt (fun τ => g τ s) (fderiv ℝ (Function.uncurry g) (τ, s) (1, 0)) τ := by
    intro τ s
    exact hasDerivAt_fst_slice ((hg.differentiable one_ne_zero) (τ, s)).hasFDerivAt
  have hcont : ∀ τ, Continuous (fun s => g τ s) := fun τ =>
    hg.continuous.comp (continuous_const.prodMk continuous_id)
  have hcont' : Continuous (fun s => fderiv ℝ (Function.uncurry g) (t, s) (1, 0)) :=
    hG'.comp (continuous_const.prodMk continuous_id)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (bound := fun _ => K) (Metric.ball_mem_nhds t one_pos)
    (Filter.Eventually.of_forall fun τ => (hcont τ).aestronglyMeasurable)
    ((hcont t).intervalIntegrable a b) hcont'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s hs τ hτ =>
      hK (τ, s) ⟨Metric.ball_subset_closedBall hτ, uIoc_subset_uIcc hs⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun s _ τ _ => hdiff τ s)).2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [definition] **The circulation** of `u(t, ·)` around the loop `C(t, ·)`: `∫₀¹ ⟨u(t, C(t, s)), ∂ₛC(t, s)⟩ ds`. -/
def circulation (u : ℝ → E → E) (C : ℝ → ℝ → E) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, ⟪u t (C t s), deriv (C t) s⟫

/-- [definition] The circulation's integrand with `∂ₛC` read from the joint derivative of `C`. -/
def loopIntegrand (u : ℝ → E → E) (C : ℝ → ℝ → E) (t s : ℝ) : ℝ :=
  ⟪u t (C t s), fderiv ℝ (Function.uncurry C) (t, s) (0, 1)⟫

/-- [definition] **The Bernoulli function** along the loop: `−Π(t, C(t, s)) + ½|u(t, C(t, s))|²`. -/
def bernoulli (u : ℝ → E → E) (C : ℝ → ℝ → E) (P : ℝ → E → ℝ) (t s : ℝ) : ℝ :=
  -P t (C t s) + (1 / 2 : ℝ) * ⟪u t (C t s), u t (C t s)⟫

/-- [proved-standard; formal-checked] **The material derivative splits**: `D_(t,x)u (1, v) = ∂ₜu + (Du) v`. -/
theorem fderiv_uncurry_apply {u : ℝ → E → E} {t : ℝ} {x : E}
    (hu : DifferentiableAt ℝ (Function.uncurry u) (t, x)) (v : E) :
    fderiv ℝ (Function.uncurry u) (t, x) (1, v) = deriv (fun τ => u τ x) t + fderiv ℝ (u t) x v := by
  have h1 : HasDerivAt (fun τ => u τ x) (fderiv ℝ (Function.uncurry u) (t, x) (1, 0)) t :=
    hasDerivAt_fst_slice hu.hasFDerivAt
  have h2 : HasFDerivAt (u t)
      ((fderiv ℝ (Function.uncurry u) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x :=
    hu.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  rw [h1.deriv, h2.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply, ← map_add,
    Prod.mk_add_mk, add_zero, zero_add]

/-- [proved-standard; formal-checked] The circulation's integrand is jointly `C¹`. -/
theorem loopIntegrand_contDiff {u : ℝ → E → E} {C : ℝ → ℝ → E}
    (hu : ContDiff ℝ 1 (Function.uncurry u)) (hC : ContDiff ℝ 2 (Function.uncurry C)) :
    ContDiff ℝ 1 (Function.uncurry (loopIntegrand u C)) := by
  have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => u p.1 (C p.1 p.2)) :=
    hu.comp (contDiff_fst.prodMk (hC.of_le (by norm_num)))
  have h2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry C) p (0, 1)) :=
    (hC.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  exact h1.inner ℝ h2

/-- [proved-standard; formal-checked] The loop's tangent `∂ₛC` is the joint derivative along `(0, 1)`. -/
theorem tangent_hasDerivAt {C : ℝ → ℝ → E} (hC : Differentiable ℝ (Function.uncurry C)) (t s : ℝ) :
    HasDerivAt (C t) (fderiv ℝ (Function.uncurry C) (t, s) (0, 1)) s :=
  hasDerivAt_snd_slice (hC (t, s)).hasFDerivAt

/-- [proved-standard; formal-checked] The gradient pairs as the derivative: `⟨∇f x, v⟩ = Df(x) v`. -/
theorem inner_gradient [CompleteSpace E] (f : E → ℝ) (x v : E) : ⟪gradient f x, v⟫ = fderiv ℝ f x v := by
  rw [← InnerProductSpace.toDual_apply_apply, toDual_gradient]

/-- [proved-standard; formal-checked] **The integrand's time derivative is the Bernoulli function's loop
derivative plus `⟨F, ∂ₛC⟩`**. -/
theorem loopIntegrand_time_deriv [CompleteSpace E] {u F : ℝ → E → E} {C : ℝ → ℝ → E}
    {P : ℝ → E → ℝ}
    (hu : ContDiff ℝ 1 (Function.uncurry u)) (hC : ContDiff ℝ 2 (Function.uncurry C))
    (hP : ∀ t, Differentiable ℝ (P t))
    (hflow : ∀ t s, HasDerivAt (fun τ => C τ s) (u t (C t s)) t)
    (hmom : ∀ t x, deriv (fun τ => u τ x) t + fderiv ℝ (u t) x (u t x) = -gradient (P t) x + F t x)
    (t s : ℝ) :
    HasDerivAt (fun σ => bernoulli u C P t σ)
      (fderiv ℝ (Function.uncurry (loopIntegrand u C)) (t, s) (1, 0) -
        ⟪F t (C t s), fderiv ℝ (Function.uncurry C) (t, s) (0, 1)⟫) s := by
  have hCd : Differentiable ℝ (Function.uncurry C) := hC.differentiable (by norm_num)
  have hDCd : Differentiable ℝ (fderiv ℝ (Function.uncurry C)) :=
    (hC.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hud : Differentiable ℝ (Function.uncurry u) := hu.differentiable one_ne_zero
  -- the time partial of the loop is the velocity
  have hvel : ∀ σ, fderiv ℝ (Function.uncurry C) (t, σ) (1, 0) = u t (C t σ) := fun σ =>
    (hasDerivAt_fst_slice (hCd (t, σ)).hasFDerivAt).unique (hflow t σ)
  -- the mixed partials commute
  have hsymm := (hC.contDiffAt (x := (t, s))).isSymmSndFDerivAt (by simp) ((1 : ℝ), (0 : ℝ))
    ((0 : ℝ), (1 : ℝ))
  -- the material acceleration
  have hw_t : HasDerivAt (fun τ => u τ (C τ s)) (-gradient (P t) (C t s) + F t (C t s)) t := by
    have hp : HasDerivAt (fun τ => (τ, C τ s)) ((1 : ℝ), u t (C t s)) t :=
      (hasDerivAt_id' t).prodMk (hflow t s)
    have h := (hud (t, C t s)).hasFDerivAt.comp_hasDerivAt t hp
    rw [fderiv_uncurry_apply (hud (t, C t s)), hmom] at h
    exact h
  -- the tangent advances by the velocity's stretch along the loop
  have hT_t : HasDerivAt (fun τ => fderiv ℝ (Function.uncurry C) (τ, s) (0, 1))
      (fderiv ℝ (fderiv ℝ (Function.uncurry C)) (t, s) (0, 1) (1, 0)) t := by
    have h := (hasDerivAt_fst_slice (hDCd (t, s)).hasFDerivAt).clm_apply
      (hasDerivAt_const t ((0 : ℝ), (1 : ℝ)))
    rw [map_zero, add_zero, hsymm] at h
    exact h
  have hw_s : HasDerivAt (fun σ => u t (C t σ))
      (fderiv ℝ (fderiv ℝ (Function.uncurry C)) (t, s) (0, 1) (1, 0)) s := by
    have h := (hasDerivAt_snd_slice (hDCd (t, s)).hasFDerivAt).clm_apply
      (hasDerivAt_const s ((1 : ℝ), (0 : ℝ)))
    rw [map_zero, add_zero] at h
    have hfun : (fun σ => fderiv ℝ (Function.uncurry C) (t, σ) (1, 0)) = fun σ => u t (C t σ) :=
      funext hvel
    exact hfun ▸ h
  -- the integrand's time derivative, computed and read from the joint derivative
  have hg_t := hw_t.inner ℝ hT_t
  have hpart : HasDerivAt (fun τ => loopIntegrand u C τ s)
      (fderiv ℝ (Function.uncurry (loopIntegrand u C)) (t, s) (1, 0)) t :=
    hasDerivAt_fst_slice (((loopIntegrand_contDiff hu hC).differentiable one_ne_zero) (t, s)).hasFDerivAt
  have heq := hpart.unique hg_t
  -- the Bernoulli function's loop derivative
  have hP_s : HasDerivAt (fun σ => P t (C t σ))
      (fderiv ℝ (P t) (C t s) (fderiv ℝ (Function.uncurry C) (t, s) (0, 1))) s :=
    (hP t (C t s)).hasFDerivAt.comp_hasDerivAt s (tangent_hasDerivAt hCd t s)
  have hk := hw_s.inner ℝ hw_s
  refine (hP_s.neg.add (hk.const_mul (1 / 2 : ℝ))).congr_deriv ?_
  rw [heq, inner_add_left, inner_neg_left, inner_gradient, real_inner_comm
    (fderiv ℝ (fderiv ℝ (Function.uncurry C)) (t, s) (0, 1) (1, 0)) (u t (C t s))]
  ring

/-- [proved-standard; formal-checked] **The circulation balance**: under `∂ₜu + (Du)u = −∇Π + F`, `Γ_u' = Γ_F`. -/
theorem circulation_hasDerivAt [CompleteSpace E] {u F : ℝ → E → E} {C : ℝ → ℝ → E}
    {P : ℝ → E → ℝ}
    (hu : ContDiff ℝ 1 (Function.uncurry u)) (hC : ContDiff ℝ 2 (Function.uncurry C))
    (hP : ∀ t, Differentiable ℝ (P t)) (hF : ∀ t, Continuous (F t))
    (hflow : ∀ t s, HasDerivAt (fun τ => C τ s) (u t (C t s)) t)
    (hclosed : ∀ t, C t 1 = C t 0)
    (hmom : ∀ t x, deriv (fun τ => u τ x) t + fderiv ℝ (u t) x (u t x) = -gradient (P t) x + F t x)
    (t : ℝ) : HasDerivAt (circulation u C) (circulation F C t) t := by
  have hCd : Differentiable ℝ (Function.uncurry C) := hC.differentiable (by norm_num)
  have hderiv : ∀ τ s, deriv (C τ) s = fderiv ℝ (Function.uncurry C) (τ, s) (0, 1) :=
    fun τ s => (tangent_hasDerivAt hCd τ s).deriv
  have hcirc : circulation u C = fun τ => ∫ s in (0 : ℝ)..1, loopIntegrand u C τ s := by
    funext τ
    simp only [circulation, loopIntegrand, hderiv]
  have hsrc : circulation F C t =
      ∫ s in (0 : ℝ)..1, ⟪F t (C t s), fderiv ℝ (Function.uncurry C) (t, s) (0, 1)⟫ := by
    simp only [circulation, hderiv]
  have hT : Continuous (fun s => fderiv ℝ (Function.uncurry C) (t, s) (0, 1)) :=
    ((hC.continuous_fderiv (by norm_num)).clm_apply continuous_const).comp
      (continuous_const.prodMk continuous_id)
  have hsrc_cont :
      Continuous (fun s => ⟪F t (C t s), fderiv ℝ (Function.uncurry C) (t, s) (0, 1)⟫) :=
    ((hF t).comp (hCd.continuous.comp (continuous_const.prodMk continuous_id))).inner hT
  have hG'_cont :
      Continuous (fun s => fderiv ℝ (Function.uncurry (loopIntegrand u C)) (t, s) (1, 0)) :=
    (((loopIntegrand_contDiff hu hC).continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
      (continuous_const.prodMk continuous_id)
  have hB := loopIntegrand_time_deriv hu hC hP hflow hmom t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hB s)
    ((hG'_cont.sub hsrc_cont).intervalIntegrable 0 1)
  have hzero : bernoulli u C P t 1 - bernoulli u C P t 0 = 0 := by
    simp [bernoulli, hclosed]
  rw [hcirc, hsrc]
  convert hasDerivAt_intervalIntegral_of_contDiff (loopIntegrand_contDiff hu hC) 0 1 t using 1
  rw [intervalIntegral.integral_sub (hG'_cont.intervalIntegrable 0 1)
    (hsrc_cont.intervalIntegrable 0 1), hzero] at hFTC
  linarith

/-- [proved-standard; formal-checked] **Kelvin's theorem**: under Euler with a barotropic potential, `Γ' = 0`. -/
theorem kelvin_hasDerivAt [CompleteSpace E] {u : ℝ → E → E} {C : ℝ → ℝ → E} {P : ℝ → E → ℝ}
    (hu : ContDiff ℝ 1 (Function.uncurry u)) (hC : ContDiff ℝ 2 (Function.uncurry C))
    (hP : ∀ t, Differentiable ℝ (P t))
    (hflow : ∀ t s, HasDerivAt (fun τ => C τ s) (u t (C t s)) t)
    (hclosed : ∀ t, C t 1 = C t 0)
    (heuler : ∀ t x, deriv (fun τ => u τ x) t + fderiv ℝ (u t) x (u t x) = -gradient (P t) x)
    (t : ℝ) : HasDerivAt (circulation u C) 0 t := by
  have h := circulation_hasDerivAt (F := fun _ _ => 0) hu hC hP (fun _ => continuous_const) hflow
    hclosed (fun t x => by rw [heuler, add_zero]) t
  simpa [circulation] using h

/-- [proved-standard; formal-checked] **Kelvin's theorem**: the circulation around a material loop is constant. -/
theorem kelvin [CompleteSpace E] {u : ℝ → E → E} {C : ℝ → ℝ → E} {P : ℝ → E → ℝ}
    (hu : ContDiff ℝ 1 (Function.uncurry u)) (hC : ContDiff ℝ 2 (Function.uncurry C))
    (hP : ∀ t, Differentiable ℝ (P t))
    (hflow : ∀ t s, HasDerivAt (fun τ => C τ s) (u t (C t s)) t)
    (hclosed : ∀ t, C t 1 = C t 0)
    (heuler : ∀ t x, deriv (fun τ => u τ x) t + fderiv ℝ (u t) x (u t x) = -gradient (P t) x)
    (t₁ t₂ : ℝ) : circulation u C t₁ = circulation u C t₂ :=
  is_const_of_deriv_eq_zero
    (fun t => (kelvin_hasDerivAt hu hC hP hflow hclosed heuler t).differentiableAt)
    (fun t => (kelvin_hasDerivAt hu hC hP hflow hclosed heuler t).deriv) t₁ t₂

end Kelvin

/-! ## 4. A digon: the projection removes a pressure part and keeps the circulating part -/

section Digon

/-- [definition] Two vertices `0, 1` and two parallel edges, both oriented `0 → 1`: `d₀ p = (p₁ − p₀, p₁ − p₀)`. -/
def digon : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 1; -1, 1]

/-- [proved-derived; formal-checked] **The digon**: `P(1, 0) = (½, −½)`, the removed part is `d₀(0, ½) = (½, ½)`,
the circulation around the cycle `(1, −1)` stays `1`, and the kinetic energy falls from `½` to `¼`. -/
theorem digon_projection :
    project digon 1 ![1, 0] = ![1 / 2, -1 / 2] ∧
      ![1, 0] - project digon 1 ![1, 0] = digon *ᵥ ![0, 1 / 2] ∧
      project digon 1 ![1, 0] ⬝ᵥ ![1, -1] = ![1, 0] ⬝ᵥ ![1, -1] ∧
      ![1, 0] ⬝ᵥ ![1, -1] = (1 : ℝ) ∧
      kinetic 1 ![1, 0] = (1 / 2 : ℝ) ∧ kinetic 1 (project digon 1 ![1, 0]) = 1 / 4 := by
  have hdiv : divergence digon 1 ![1 / 2, -1 / 2] = 0 := by
    ext i
    fin_cases i <;> simp [divergence, digon, mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  have hgrad : digon *ᵥ ![0, 1 / 2] = ![1 / 2, 1 / 2] := by
    ext i
    fin_cases i <;> simp [digon, mulVec, dotProduct]
  have hP : project digon 1 ![1, 0] = ![1 / 2, -1 / 2] := by
    refine project_eq_of Matrix.PosDef.one hdiv ![0, 1 / 2] ?_
    rw [hgrad]
    ext i
    fin_cases i <;> norm_num
  refine ⟨hP, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hP, hgrad]
    ext i
    fin_cases i <;> norm_num
  · rw [hP]
    simp [dotProduct, Fin.sum_univ_two]
    norm_num
  · simp [dotProduct, Fin.sum_univ_two]
  · simp [kinetic, dotProduct, Fin.sum_univ_two]
  · rw [hP]
    simp [kinetic, dotProduct, Fin.sum_univ_two]
    norm_num

end Digon

end Holonics.Physics.Fluid.TimeAdvanceKelvin

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The Hodge split of a continuum clock

The box of #410: "The Hodge split of a continuum clock (the discrete split is
`Aeon/Production/HodgeTime`)." `Aeon/Production/HodgeTime` splits every time form on a finite cell
complex as `ω = dφ + δβ + h` (state, production, winding) and proves four laws there: state time is
boundary-determined, winding time is a cycle invariant, production time is curvature (on a cell
boundary it reads the flux of `d₁ω`), and a clock has no production. Its last line leaves "the
smooth Hodge theorem and the continuum clock forms of the record" outside it. This module states the
four laws on two continuum carriers, the circle `ℝ/ℤ` and the flat torus `ℝ²/ℤ²`.

Sources: the box above; `Aeon/Production/HodgeTime` (its opening paragraph and its four numbered
laws); the record `research/records/2026-09-24_THE_AEON_EPOCH_AND_CYCLE_STANDARDIZE_THE_PASSAGE_OF_TIME.md`,
§A1 (readings are additive; closed clocks read cycles through `H₁`) and §A2 (Hodge-decomposed time);
atlas rows `aeon.a2-hodge-time`, `aeon.clock-hodge-split`, `aeon.hodge-time-witnesses`,
`holon.face-is-potential-drop`, and `ns.torus-fourier-curl` (the symbol rule `∂_j ↦ 2πi k_j` on the
three-torus, `Fluid/NavierStokesTorusFourier`).

[definition] **Setting.** A continuum clock form is a 1-form on a compact carrier. An aeon is a C¹
path on the carrier's cover over a clock interval `[s, t]`, carried with its velocity
(`Circle.AeonLift`, `Torus.AeonPath`), and its reading is the line integral (`Circle.reading`,
`Torus.reading`). An aeon is closed when its displacement on the cover is a lattice vector, its
winding count. On the torus the split's existence is stated at a declared width, for trigonometric
polynomials on a finite set of modes `S ⊂ ℤ²`, as the precision law reads a continuum form; the
reading laws hold for every C¹ form. Torus forms take values in any real Banach space `E`, so one law
reads real forms (`E = ℝ`) and the complex modes (`E = ℂ`).

[proved-derived; formal-checked] What is proved, Part A, the circle (`ω = f dθ`, `f` continuous and
1-periodic).

1. **The split.** `h = windingRate f = ∫₀¹ f` and `φ = statePotential f`, `φ θ = ∫₀^θ (f − h)`, give
   `f = h + φ′` (`split`, `hasDerivAt_statePotential`), `φ` 1-periodic and C¹
   (`statePotential_periodic`, `contDiff_statePotential`). Among constants plus derivatives of
   periodic functions the split is unique: `h` is unique and `φ` is unique up to a constant
   (`split_unique`).
2. **The reading.** `∫ₛᵗ f(γ τ) γ′ τ dτ = h·(γ t − γ s) + φ(γ t) − φ(γ s)` (`reading_split`, through
   `intervalIntegral.integral_comp_mul_deriv` in `reading_eq_integral` and `integral_eq_split`).
3. **State time is boundary-determined; winding time is a cycle invariant.** The state part reads the
   drop, between the endpoints' phases on `AddCircle 1`, of the lift of `φ`
   (`state_reading_eq_phase_drop`), so it is boundary-determined (`state_boundary_determined`). A
   clock form is boundary-determined if and only if `h = 0` (`boundaryDetermined_iff`), and `h = 0`
   if and only if it is the derivative of a periodic potential (`exact_iff_windingRate_eq_zero`).
   Closed aeons of one winding count read equally (`winding_cycle_invariant`).
4. **No production on the circle.** There are no 2-cells, so every clock form is closed: the reading
   over every closed aeon of winding count `N` is `h · N` (`no_production`), and a contractible
   closed aeon (`N = 0`) reads `0` (`contractible_reads_zero`).

What is proved, Part B, the flat torus (`ω = a dx + b dy`).

5. **The split at declared width** (`a = Σ_(k∈S) A_k e_k`, `b = Σ_(k∈S) B_k e_k`, the modes
   `e_k(p) = exp(2πi(k₁p₁ + k₂p₂))`, `mode`, `trig`). Differentiation is the symbol rule
   `∂ₓ e_k = 2πi k₁ e_k`, `∂ᵧ e_k = 2πi k₂ e_k` (`partialX_trig`, `partialY_trig`). Mode by mode, for
   `k ≠ 0`, the vectors `k` and `k^⊥` are a basis of `ℂ²`: `(A_k, B_k) = φ_k (∂ₓ, ∂ᵧ) + β_k (∂ᵧ, −∂ₓ)`
   with unique coefficients (`mode_split`, `mode_split_unique`, from `normSq_ne_zero`); the mode `0`
   is the harmonic part (`dx_zero`, `dy_zero`). As functions,
   `a = h₁ + ∂ₓφ + ∂ᵧβ`, `b = h₂ + ∂ᵧφ − ∂ₓβ` with `h = (∫∫a, ∫∫b)` (`trig_split`, `mean_trig`), and
   every split of this shape has that `h` and those mode coefficients (`trig_split_unique`, through
   the Fourier coefficients `fourierCoeff_trig`, `fourierCoeff_const_add_trig`, orthogonality
   `mean_sum_mode`). The reality condition `c_(−k) = conj c_k` passes to the parts
   (`stateCoeff_conj`, `prodCoeff_conj`). A form at declared width is closed if and only if its
   production coefficients vanish (`trig_closed_iff`, `curvature_trig`, `curvature_coeff`).
6. **The three readings, for C¹ forms.**
   * State: `dφ = (∂ₓφ, ∂ᵧφ)` reads `φ(γ t) − φ(γ s)` (`state_reading`, the chain rule and the
     fundamental theorem of calculus); for periodic `φ` it depends only on the endpoints' points of
     the torus (`state_boundary_determined`).
   * Winding: the constant form `h` reads `h · (γ t − γ s)` (`winding_reading`), and `h · N` on a
     closed aeon (`winding_closed_reading`). On a closed aeon with periodic state part the reading is
     `production + h · N` (`closed_reading_split`, from `reading_split`).
   * Production: on the boundary of a rectangle `R` (four edge aeons, `cellReading`) the reading of
     `ω` is the iterated integral of its curvature `∂ₓb − ∂ᵧa` over `R` (`green`, from Mathlib's
     `integral2_divergence_prod_of_hasFDerivAt`). The state and winding parts read `0` there
     (`state_cellReading`, `winding_cellReading`), so only the production part reads on a cell
     boundary (`cellReading_split`); the production part `δβ = (∂ᵧβ, −∂ₓβ)` has curvature `−Δβ`
     (`curvature_coexact`, `production_cellReading`, mode-wise `laplacian_trig`), and a closed C¹
     form reads `0` on every cell boundary (`clock_cellReading`).
7. **Witnesses** ([counterexample; formal-checked]).
   * `ω = cos(2πy) dx` (`cosForm`) is coexact, `β = sin(2πy)/(2π)` (`cosForm_coexact`), with harmonic
     part `0` (`mean_cosForm`). Its two horizontal closed aeons at `y = 0` and `y = ½`, both of
     winding vector `(1, 0)`, read `1` and `−1` (`cosForm_reading_zero`, `cosForm_reading_half`)
     where `h · N` is `0`; their difference is the curvature flux `∫₀¹∫₀^½ 2π sin(2πy) = 2` through
     the band between them (`curvature_cosForm`, `cosForm_flux`, `cosForm_cellReading`,
     `cosForm_homologous_loops`).
   * `ω = dx` (`dxForm`, harmonic) reads `1` on the loop `t ↦ (t, 0)` and `0` on the empty aeon, whose
     endpoints are the same points of the torus (`dxForm_winding_not_boundary_determined`), the
     continuum form of `hollowTriangle_winding_not_boundary_determined`. On the circle, the unit
     clock `f = 1` is not boundary-determined (`unit_clock_not_boundaryDetermined`).

What is not claimed. The smooth Hodge theorem for every C¹ form on the torus (the convergence of
Fourier series on `T²` that would carry the declared-width split to every smooth form), the Hodge
theorem on a compact Riemannian manifold, and the Laplace–Beltrami form. Green's theorem is stated
on rectangles only; the reading difference of two homologous closed aeons along a general homotopy,
and the converse that a form reading `0` on every cell boundary is closed, are not stated. The
record's `agent-inferred` reading of relative completeness (an aeon is complete for a clock when
that clock reads on it without remainder, as atlas `aeon.a2-hodge-time` words it) is not stated
here.

Computational object: the helical pair interaction read on a clock. The circle's aeon is a lift
through the helix `ℝ → ℝ/ℤ`, whose displacement carries the whole windings `N` and whose endpoints
carry the residue phases; the torus is the pair of two such clocks, a closed aeon is a cycle of the
pair with its winding vector `N ∈ ℤ²` as address, and the rectangle's boundary reading is the cell
holonomy of the time connection (Green). Of the six objects of the winding guide this module
touches the helix (lift and carry), the pair (the two-clock torus), cell holonomy (curvature flux
through a cell) and the tube (an aeon over its clock interval); faces and placement are touched
only through the declared width, the finite set of Fourier modes a form is read at, and the tower
thread stays attached and is not used here.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Aeon.Production.ContinuumHodgeTime

open Real Set intervalIntegral MeasureTheory

/-! ## Part A. The circle `ℝ/ℤ` -/

namespace Circle

/-- [definition] An aeon on the circle: a C¹ lift `path` over the clock interval `[s, t]`. -/
structure AeonLift where
  /-- The clock instant at which the aeon starts. -/
  s : ℝ
  /-- The clock instant at which the aeon ends. -/
  t : ℝ
  /-- The lift of the aeon to the cover `ℝ`. -/
  path : ℝ → ℝ
  /-- The velocity of the lift. -/
  vel : ℝ → ℝ
  /-- The lift has the velocity as its derivative on the clock interval. -/
  hasDerivAt : ∀ τ ∈ uIcc s t, HasDerivAt path (vel τ) τ
  /-- The velocity is continuous on the clock interval: the lift is C¹. -/
  continuousOn_vel : ContinuousOn vel (uIcc s t)

namespace AeonLift

/-- [definition] The lifted source occurrence. -/
def source (γ : AeonLift) : ℝ := γ.path γ.s

/-- [definition] The lifted target occurrence. -/
def target (γ : AeonLift) : ℝ := γ.path γ.t

/-- [definition] The lifted displacement; on a closed aeon it is the winding count. -/
def displacement (γ : AeonLift) : ℝ := γ.target - γ.source

/-- [definition] The endpoints' phases on the circle `AddCircle 1`: the aeon's boundary. -/
def phases (γ : AeonLift) : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) := (γ.source, γ.target)

/-- [definition] The uniform aeon `τ ↦ θ₀ + v τ` over `[s, t]`. -/
def line (θ₀ v s t : ℝ) : AeonLift where
  s := s
  t := t
  path τ := θ₀ + v * τ
  vel _ := v
  hasDerivAt τ _ := by simpa using ((hasDerivAt_id τ).const_mul v).const_add θ₀
  continuousOn_vel := continuousOn_const

end AeonLift

/-- [definition] The reading `∫ₛᵗ f(γ τ) γ′ τ dτ` of the clock form `f dθ` over an aeon. -/
def reading (f : ℝ → ℝ) (γ : AeonLift) : ℝ := ∫ τ in γ.s..γ.t, f (γ.path τ) * γ.vel τ

/-- [definition] The winding (harmonic) rate `h = ∫₀¹ f`. -/
def windingRate (f : ℝ → ℝ) : ℝ := ∫ θ in (0 : ℝ)..1, f θ

/-- [definition] The state potential `φ θ = ∫₀^θ (f − h)`. -/
def statePotential (f : ℝ → ℝ) (θ : ℝ) : ℝ := ∫ u in (0 : ℝ)..θ, (f u - windingRate f)

/-- [definition] A clock form is **boundary-determined** when aeons with the same endpoint phases
read it equally. -/
def BoundaryDetermined (g : ℝ → ℝ) : Prop :=
  ∀ γ₁ γ₂ : AeonLift, γ₁.phases = γ₂.phases → reading g γ₁ = reading g γ₂

variable {f : ℝ → ℝ}

/-! ### 1. The split -/

/-- [proved-standard; formal-checked] `φ′ = f − h` (the fundamental theorem of calculus). -/
theorem hasDerivAt_statePotential (hf : Continuous f) (θ : ℝ) :
    HasDerivAt (statePotential f) (f θ - windingRate f) θ :=
  ((hf.sub continuous_const).integral_hasStrictDerivAt 0 θ).hasDerivAt

/-- [proved-derived; formal-checked] **The split** `f = h + φ′`: winding rate plus state rate. -/
theorem split (hf : Continuous f) (θ : ℝ) :
    f θ = windingRate f + deriv (statePotential f) θ := by
  rw [(hasDerivAt_statePotential hf θ).deriv]; ring

/-- [proved-standard; formal-checked] The state potential is C¹. -/
theorem contDiff_statePotential (hf : Continuous f) : ContDiff ℝ 1 (statePotential f) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun θ => (hasDerivAt_statePotential hf θ).differentiableAt, ?_⟩
  have : deriv (statePotential f) = fun θ => f θ - windingRate f :=
    funext fun θ => (hasDerivAt_statePotential hf θ).deriv
  rw [this]; exact hf.sub continuous_const

/-- [proved-standard; formal-checked] `∫ᵤᵛ (f − h) = φ v − φ u`. -/
theorem integral_state (hf : Continuous f) (u v : ℝ) :
    ∫ θ in u..v, (f θ - windingRate f) = statePotential f v - statePotential f u :=
  integral_eq_sub_of_hasDerivAt (fun θ _ => hasDerivAt_statePotential hf θ)
    ((hf.sub continuous_const).intervalIntegrable _ _)

/-- [proved-derived; formal-checked] `∫ᵤᵛ f = h (v − u) + φ v − φ u`. -/
theorem integral_eq_split (hf : Continuous f) (u v : ℝ) :
    ∫ θ in u..v, f θ = windingRate f * (v - u) + (statePotential f v - statePotential f u) := by
  rw [← integral_state hf, intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- [proved-derived; formal-checked] The state potential of a 1-periodic clock form is 1-periodic. -/
theorem statePotential_periodic (hf : Continuous f) (hper : Function.Periodic f 1) :
    Function.Periodic (statePotential f) 1 := by
  intro θ
  have hp : Function.Periodic (fun u => f u - windingRate f) 1 := fun u => by
    simp only [hper u]
  have h0 : ∫ u in θ..θ + 1, (f u - windingRate f) = 0 := by
    rw [hp.intervalIntegral_add_eq θ 0, zero_add, intervalIntegral.integral_sub
      (hf.intervalIntegrable _ _) intervalIntegrable_const, intervalIntegral.integral_const]
    simp [windingRate]
  rw [integral_state hf] at h0
  linarith

/-- [proved-standard; formal-checked] The state potential is based at `0`. -/
theorem statePotential_zero : statePotential f 0 = 0 := integral_same

/-- [proved-derived; formal-checked] **The split is unique**: if `f = c + ψ′` with `ψ` periodic, then
`c = h` and `ψ = φ + ψ 0`. -/
theorem split_unique (hf : Continuous f) {c : ℝ} {ψ : ℝ → ℝ} (hψ : Function.Periodic ψ 1)
    (hd : ∀ θ, HasDerivAt ψ (f θ - c) θ) :
    c = windingRate f ∧ ∀ θ, ψ θ = statePotential f θ + ψ 0 := by
  have hc : c = windingRate f := by
    have h := integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
      ((hf.sub continuous_const).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const] at h
    have h1 := hψ 0
    rw [zero_add] at h1
    simp only [sub_zero, smul_eq_mul, one_mul, h1, sub_self] at h
    unfold windingRate; linarith
  refine ⟨hc, fun θ => ?_⟩
  have hd' : ∀ x, HasDerivAt (fun x => ψ x - statePotential f x) 0 x := by
    intro x
    have := (hd x).sub (hasDerivAt_statePotential hf x)
    rwa [hc, sub_self] at this
  have := is_const_of_deriv_eq_zero (fun x => (hd' x).differentiableAt) (fun x => (hd' x).deriv) θ 0
  simp only [statePotential_zero, sub_zero] at this
  linarith

/-! ### 2. The reading -/

/-- [proved-standard; formal-checked] Change of variables: an aeon reads `∫` of `f` between its
lifted endpoints. -/
theorem reading_eq_integral (hf : Continuous f) (γ : AeonLift) :
    reading f γ = ∫ θ in γ.source..γ.target, f θ :=
  integral_comp_mul_deriv γ.hasDerivAt γ.continuousOn_vel hf

/-- [proved-derived; formal-checked] **The reading splits**: `h · displacement + φ(γ t) − φ(γ s)`. -/
theorem reading_split (hf : Continuous f) (γ : AeonLift) :
    reading f γ = windingRate f * γ.displacement +
      (statePotential f γ.target - statePotential f γ.source) := by
  rw [reading_eq_integral hf, integral_eq_split hf]; rfl

/-! ### 3. State time is boundary-determined; winding time is a cycle invariant -/

/-- [proved-derived; formal-checked] The state part `φ′ = f − h` reads the potential drop. -/
theorem state_reading (hf : Continuous f) (γ : AeonLift) :
    reading (fun θ => f θ - windingRate f) γ =
      statePotential f γ.target - statePotential f γ.source := by
  rw [reading_eq_integral (f := fun θ => f θ - windingRate f) (hf.sub continuous_const),
    integral_state hf]

/-- [proved-derived; formal-checked] The state reading is the drop of the potential's lift to the
circle between the endpoints' phases. -/
theorem state_reading_eq_phase_drop (hf : Continuous f) (hper : Function.Periodic f 1)
    (γ : AeonLift) :
    reading (fun θ => f θ - windingRate f) γ =
      (statePotential_periodic hf hper).lift (γ.target : AddCircle (1 : ℝ)) -
        (statePotential_periodic hf hper).lift (γ.source : AddCircle (1 : ℝ)) :=
  state_reading hf γ

/-- [proved-derived; formal-checked] **State time is boundary-determined.** -/
theorem state_boundary_determined (hf : Continuous f) (hper : Function.Periodic f 1) :
    BoundaryDetermined (fun θ => f θ - windingRate f) := by
  intro γ₁ γ₂ h
  simp only [AeonLift.phases, Prod.mk.injEq] at h
  rw [state_reading_eq_phase_drop hf hper, state_reading_eq_phase_drop hf hper, h.1, h.2]

/-- [proved-derived; formal-checked] The unit loop `τ ↦ τ` over `[0, 1]` reads the winding rate. -/
theorem reading_line_loop : reading f (AeonLift.line 0 1 0 1) = windingRate f := by
  simp [reading, AeonLift.line, windingRate]

/-- [proved-standard; formal-checked] The empty aeon (`s = t`) reads `0`. -/
theorem reading_empty (θ₀ v s : ℝ) : reading f (AeonLift.line θ₀ v s s) = 0 := integral_same

/-- [proved-derived; formal-checked] **A clock form is boundary-determined iff `h = 0`**: the continuum
`boundary_determined_iff_exact`. -/
theorem boundaryDetermined_iff (hf : Continuous f) (hper : Function.Periodic f 1) :
    BoundaryDetermined f ↔ windingRate f = 0 := by
  constructor
  · intro h
    have hph : (AeonLift.line 0 1 0 1).phases = (AeonLift.line 0 1 0 0).phases := by
      simp [AeonLift.phases, AeonLift.source, AeonLift.target, AeonLift.line, AddCircle.coe_period]
    have := h _ _ hph
    rwa [reading_line_loop, reading_empty] at this
  · intro h0 γ₁ γ₂ h
    have key : ∀ γ : AeonLift, reading f γ =
        (statePotential_periodic hf hper).lift (γ.target : AddCircle (1 : ℝ)) -
          (statePotential_periodic hf hper).lift (γ.source : AddCircle (1 : ℝ)) := by
      intro γ; rw [reading_split hf, h0, zero_mul, zero_add]; rfl
    simp only [AeonLift.phases, Prod.mk.injEq] at h
    rw [key, key, h.1, h.2]

/-- [proved-derived; formal-checked] A clock form is the derivative of a periodic potential iff
its winding rate is `0`. -/
theorem exact_iff_windingRate_eq_zero (hf : Continuous f) (hper : Function.Periodic f 1) :
    (∃ ψ : ℝ → ℝ, Function.Periodic ψ 1 ∧ ∀ θ, HasDerivAt ψ (f θ) θ) ↔ windingRate f = 0 := by
  constructor
  · rintro ⟨ψ, hψ, hd⟩
    exact (split_unique hf (c := 0) hψ fun θ => by simpa using hd θ).1.symm
  · intro h0
    exact ⟨statePotential f, statePotential_periodic hf hper,
      fun θ => by simpa [h0] using hasDerivAt_statePotential hf θ⟩

/-! ### 4. No production on the circle -/

/-- [proved-derived; formal-checked] **No production on the circle**: every clock form is closed, and
the reading over every closed aeon of winding count `N` is `h · N`. -/
theorem no_production (hf : Continuous f) (hper : Function.Periodic f 1) (γ : AeonLift) (N : ℤ)
    (hγ : γ.displacement = N) : reading f γ = windingRate f * N := by
  rw [reading_split hf, hγ]
  have ht : γ.target = γ.source + N * 1 := by
    rw [mul_one, ← hγ, AeonLift.displacement]; ring
  rw [ht, (statePotential_periodic hf hper).int_mul N γ.source]; ring

/-- [proved-derived; formal-checked] **Winding time is a cycle invariant**: closed aeons of one
winding count read equally. -/
theorem winding_cycle_invariant (hf : Continuous f) (hper : Function.Periodic f 1)
    {γ₁ γ₂ : AeonLift} {N : ℤ} (h₁ : γ₁.displacement = N) (h₂ : γ₂.displacement = N) :
    reading f γ₁ = reading f γ₂ := by
  rw [no_production hf hper γ₁ N h₁, no_production hf hper γ₂ N h₂]

/-- [proved-derived; formal-checked] A contractible closed aeon (winding count `0`) reads `0`. -/
theorem contractible_reads_zero (hf : Continuous f) (hper : Function.Periodic f 1) (γ : AeonLift)
    (hγ : γ.displacement = 0) : reading f γ = 0 := by
  rw [no_production hf hper γ 0 (by rw [hγ, Int.cast_zero]), Int.cast_zero, mul_zero]

/-- [counterexample; formal-checked] The unit clock `f = 1` (winding rate `1`) is not
boundary-determined. -/
theorem unit_clock_not_boundaryDetermined : ¬ BoundaryDetermined (fun _ => (1 : ℝ)) := by
  rw [boundaryDetermined_iff continuous_const (fun _ => rfl)]
  simp [windingRate]

end Circle

/-! ## Part B. The flat torus `ℝ²/ℤ²` -/

namespace Torus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- [definition] An aeon on the torus: a C¹ lift `path` to the plane over the clock interval
`[s, t]`. -/
structure AeonPath where
  /-- The clock instant at which the aeon starts. -/
  s : ℝ
  /-- The clock instant at which the aeon ends. -/
  t : ℝ
  /-- The lift of the aeon to the cover `ℝ²`. -/
  path : ℝ → ℝ × ℝ
  /-- The velocity of the lift. -/
  vel : ℝ → ℝ × ℝ
  /-- The lift has the velocity as its derivative on the clock interval. -/
  hasDerivAt : ∀ τ ∈ uIcc s t, HasDerivAt path (vel τ) τ
  /-- The velocity is continuous on the clock interval: the lift is C¹. -/
  continuousOn_vel : ContinuousOn vel (uIcc s t)

namespace AeonPath

/-- [definition] The lifted source occurrence. -/
def source (γ : AeonPath) : ℝ × ℝ := γ.path γ.s

/-- [definition] The lifted target occurrence. -/
def target (γ : AeonPath) : ℝ × ℝ := γ.path γ.t

/-- [definition] The lifted displacement; on a closed aeon it is the winding vector. -/
def displacement (γ : AeonPath) : ℝ × ℝ := γ.target - γ.source

/-- [proved-standard; formal-checked] The lift is continuous on the clock interval. -/
theorem continuousOn_path (γ : AeonPath) : ContinuousOn γ.path (uIcc γ.s γ.t) :=
  fun τ hτ => (γ.hasDerivAt τ hτ).continuousAt.continuousWithinAt

/-- [definition] The horizontal edge `τ ↦ (τ, y)` over `[u, v]`. -/
def hEdge (y u v : ℝ) : AeonPath where
  s := u
  t := v
  path τ := (τ, y)
  vel _ := (1, 0)
  hasDerivAt τ _ := (hasDerivAt_id τ).prodMk (hasDerivAt_const τ y)
  continuousOn_vel := continuousOn_const

/-- [definition] The vertical edge `τ ↦ (x, τ)` over `[u, v]`. -/
def vEdge (x u v : ℝ) : AeonPath where
  s := u
  t := v
  path τ := (x, τ)
  vel _ := (0, 1)
  hasDerivAt τ _ := (hasDerivAt_const τ x).prodMk (hasDerivAt_id τ)
  continuousOn_vel := continuousOn_const

end AeonPath

open AeonPath

/-- [definition] The reading of `ω = a dx + b dy` over an aeon. -/
def reading (a b : ℝ × ℝ → E) (γ : AeonPath) : E :=
  ∫ τ in γ.s..γ.t, (γ.vel τ).1 • a (γ.path τ) + (γ.vel τ).2 • b (γ.path τ)

/-- [definition] The partial derivative `∂ₓF`. -/
def partialX (F : ℝ × ℝ → E) (p : ℝ × ℝ) : E := fderiv ℝ F p (1, 0)

/-- [definition] The partial derivative `∂ᵧF`. -/
def partialY (F : ℝ × ℝ → E) (p : ℝ × ℝ) : E := fderiv ℝ F p (0, 1)

/-- [definition] The curvature `dω = (∂ₓb − ∂ᵧa) dx ∧ dy` of `ω = a dx + b dy`. -/
def curvature (a b : ℝ × ℝ → E) (p : ℝ × ℝ) : E := partialX b p - partialY a p

/-- [definition] The Laplacian `Δβ = ∂ₓ∂ₓβ + ∂ᵧ∂ᵧβ`. -/
def laplacian (β : ℝ × ℝ → E) (p : ℝ × ℝ) : E := partialX (partialX β) p + partialY (partialY β) p

/-- [definition] The reading over the counterclockwise boundary of `[x₀, x₁] × [y₀, y₁]`: four
edge aeons. -/
def cellReading (a b : ℝ × ℝ → E) (x₀ x₁ y₀ y₁ : ℝ) : E :=
  reading a b (hEdge y₀ x₀ x₁) + reading a b (vEdge x₁ y₀ y₁) + reading a b (hEdge y₁ x₁ x₀) +
    reading a b (vEdge x₀ y₁ y₀)

/-- [definition] The point of the torus `AddCircle 1 × AddCircle 1` under a point of the plane. -/
def toTorus (p : ℝ × ℝ) : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) :=
  ((p.1 : AddCircle (1 : ℝ)), (p.2 : AddCircle (1 : ℝ)))

/-- [definition] `ℤ²`-periodicity. -/
def IsPeriodic {α : Type*} (φ : ℝ × ℝ → α) : Prop :=
  (∀ p : ℝ × ℝ, φ (p.1 + 1, p.2) = φ p) ∧ ∀ p : ℝ × ℝ, φ (p.1, p.2 + 1) = φ p

/-! ### 6. The readings of C¹ forms -/

/-- [proved-standard; formal-checked] A linear map on the plane is read on the two unit vectors. -/
theorem clm_apply_eq (L : ℝ × ℝ →L[ℝ] E) (v : ℝ × ℝ) : L v = v.1 • L (1, 0) + v.2 • L (0, 1) := by
  rw [← map_smul, ← map_smul, ← map_add]; congr 1; ext <;> simp

/-- [proved-standard; formal-checked] A continuous form's reading integrand is integrable. -/
theorem intervalIntegrable_reading {a b : ℝ × ℝ → E} (ha : Continuous a) (hb : Continuous b)
    (γ : AeonPath) :
    IntervalIntegrable (fun τ => (γ.vel τ).1 • a (γ.path τ) + (γ.vel τ).2 • b (γ.path τ))
      volume γ.s γ.t := by
  apply ContinuousOn.intervalIntegrable
  have hv := γ.continuousOn_vel
  have hp := γ.continuousOn_path
  exact ((continuous_fst.comp_continuousOn hv).smul (ha.comp_continuousOn hp)).add
    ((continuous_snd.comp_continuousOn hv).smul (hb.comp_continuousOn hp))

/-- [proved-standard; formal-checked] Readings are additive in the form. -/
theorem reading_add [CompleteSpace E] {a b a' b' : ℝ × ℝ → E} (ha : Continuous a)
    (hb : Continuous b) (ha' : Continuous a') (hb' : Continuous b') (γ : AeonPath) :
    reading (fun p => a p + a' p) (fun p => b p + b' p) γ = reading a b γ + reading a' b' γ := by
  rw [reading, reading, reading, ← intervalIntegral.integral_add
    (intervalIntegrable_reading ha hb γ) (intervalIntegrable_reading ha' hb' γ)]
  congr 1; funext τ; simp only [smul_add]; abel

/-- [proved-derived; formal-checked] **State time reads the potential drop**:
`⟨dφ | γ⟩ = φ(γ t) − φ(γ s)`. -/
theorem state_reading [CompleteSpace E] {φ : ℝ × ℝ → E} (hφ : ContDiff ℝ 1 φ) (γ : AeonPath) :
    reading (partialX φ) (partialY φ) γ = φ γ.target - φ γ.source := by
  have hd : ∀ τ ∈ uIcc γ.s γ.t, HasDerivAt (fun τ => φ (γ.path τ))
      (fderiv ℝ φ (γ.path τ) (γ.vel τ)) τ := fun τ hτ =>
    ((hφ.differentiable one_ne_zero) (γ.path τ)).hasFDerivAt.comp_hasDerivAt τ (γ.hasDerivAt τ hτ)
  have hint : IntervalIntegrable (fun τ => fderiv ℝ φ (γ.path τ) (γ.vel τ)) volume γ.s γ.t := by
    apply ContinuousOn.intervalIntegrable
    exact ((hφ.continuous_fderiv one_ne_zero).comp_continuousOn γ.continuousOn_path).clm_apply
      γ.continuousOn_vel
  have := integral_eq_sub_of_hasDerivAt hd hint
  rw [reading, target, source, ← this]
  congr 1; funext τ
  rw [clm_apply_eq (fderiv ℝ φ (γ.path τ)) (γ.vel τ)]; rfl

/-- [proved-standard; formal-checked] Integer shifts of a `ℤ²`-periodic function. -/
theorem IsPeriodic.add_int {α : Type*} {φ : ℝ × ℝ → α} (hφ : IsPeriodic φ) (p : ℝ × ℝ)
    (m n : ℤ) : φ (p.1 + m, p.2 + n) = φ p := by
  have hx : Function.Periodic (fun x => φ (x, p.2)) 1 := fun x => hφ.1 (x, p.2)
  have hy : Function.Periodic (fun y => φ (p.1 + m, y)) 1 := fun y => hφ.2 (p.1 + m, y)
  have e1 := hy.int_mul n p.2
  have e2 := hx.int_mul m p.1
  simp only [mul_one] at e1 e2
  rw [e1, e2]

/-- [proved-standard; formal-checked] Equal points of the circle differ by an integer. -/
theorem exists_int_of_coe_eq {x y : ℝ} (h : (x : AddCircle (1 : ℝ)) = y) :
    ∃ k : ℤ, y = x + k := by
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp h)
  exact ⟨k, by rw [zsmul_eq_mul, mul_one] at hk; linarith⟩

/-- [proved-standard; formal-checked] A `ℤ²`-periodic function is a function on the torus. -/
theorem IsPeriodic.eq_of_toTorus_eq {α : Type*} {φ : ℝ × ℝ → α} (hφ : IsPeriodic φ)
    {p q : ℝ × ℝ} (h : toTorus p = toTorus q) : φ p = φ q := by
  simp only [toTorus, Prod.mk.injEq] at h
  obtain ⟨m, hm⟩ := exists_int_of_coe_eq h.1
  obtain ⟨n, hn⟩ := exists_int_of_coe_eq h.2
  rw [show q = (q.1, q.2) from rfl, hm, hn, hφ.add_int]

/-- [proved-derived; formal-checked] **State time is boundary-determined** on the torus: for a
periodic potential the reading depends only on the endpoints' points of the torus. -/
theorem state_boundary_determined [CompleteSpace E] {φ : ℝ × ℝ → E} (hφ : ContDiff ℝ 1 φ)
    (hper : IsPeriodic φ) {γ₁ γ₂ : AeonPath} (hs : toTorus γ₁.source = toTorus γ₂.source)
    (ht : toTorus γ₁.target = toTorus γ₂.target) :
    reading (partialX φ) (partialY φ) γ₁ = reading (partialX φ) (partialY φ) γ₂ := by
  rw [state_reading hφ, state_reading hφ, hper.eq_of_toTorus_eq hs, hper.eq_of_toTorus_eq ht]

/-- [proved-derived; formal-checked] **Winding time**: the constant form `h` reads
`h · (γ t − γ s)`. -/
theorem winding_reading [CompleteSpace E] (h₁ h₂ : E) (γ : AeonPath) :
    reading (fun _ => h₁) (fun _ => h₂) γ = γ.displacement.1 • h₁ + γ.displacement.2 • h₂ := by
  let L : ℝ × ℝ →L[ℝ] E :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight h₁ + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight h₂
  have hL : ∀ v, L v = v.1 • h₁ + v.2 • h₂ := fun v => by simp [L]
  have hd : ∀ τ ∈ uIcc γ.s γ.t, HasDerivAt (fun τ => L (γ.path τ)) (L (γ.vel τ)) τ :=
    fun τ hτ => L.hasFDerivAt.comp_hasDerivAt τ (γ.hasDerivAt τ hτ)
  have hint : IntervalIntegrable (fun τ => L (γ.vel τ)) volume γ.s γ.t :=
    (L.continuous.comp_continuousOn γ.continuousOn_vel).intervalIntegrable
  have := integral_eq_sub_of_hasDerivAt hd hint
  rw [← map_sub] at this
  rw [displacement, target, source, ← hL, ← this, reading]
  simp only [hL]

/-- [proved-derived; formal-checked] **Winding time is a cycle invariant**: on a closed aeon of
winding vector `N` the constant form reads `h · N`. -/
theorem winding_closed_reading [CompleteSpace E] (h₁ h₂ : E) (γ : AeonPath) (N : ℤ × ℤ)
    (hN : γ.displacement = ((N.1 : ℝ), (N.2 : ℝ))) :
    reading (fun _ => h₁) (fun _ => h₂) γ = (N.1 : ℝ) • h₁ + (N.2 : ℝ) • h₂ := by
  rw [winding_reading, hN]

/-- [proved-standard; formal-checked] The partials of a C¹ function are continuous. -/
theorem continuous_partialX {φ : ℝ × ℝ → E} (hφ : ContDiff ℝ 1 φ) : Continuous (partialX φ) :=
  (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- [proved-standard; formal-checked] The partials of a C¹ function are continuous. -/
theorem continuous_partialY {φ : ℝ × ℝ → E} (hφ : ContDiff ℝ 1 φ) : Continuous (partialY φ) :=
  (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- [proved-standard; formal-checked] The partials of a C² function are C¹. -/
theorem contDiff_partialX {φ : ℝ × ℝ → E} (hφ : ContDiff ℝ 2 φ) : ContDiff ℝ 1 (partialX φ) :=
  (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- [proved-standard; formal-checked] The partials of a C² function are C¹. -/
theorem contDiff_partialY {φ : ℝ × ℝ → E} (hφ : ContDiff ℝ 2 φ) : ContDiff ℝ 1 (partialY φ) :=
  (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- [proved-derived; formal-checked] **The reading of a split form**:
`⟨dφ + δβ + h | γ⟩ = (φ(γ t) − φ(γ s)) + ⟨δβ | γ⟩ + h · (γ t − γ s)`. -/
theorem reading_split [CompleteSpace E] {φ β : ℝ × ℝ → E} (hφ : ContDiff ℝ 1 φ)
    (hβ : ContDiff ℝ 1 β) (h₁ h₂ : E) (γ : AeonPath) :
    reading (fun p => partialX φ p + partialY β p + h₁) (fun p => partialY φ p - partialX β p + h₂) γ =
      (φ γ.target - φ γ.source) + reading (partialY β) (fun p => -partialX β p) γ +
        (γ.displacement.1 • h₁ + γ.displacement.2 • h₂) := by
  rw [show (fun p => partialY φ p - partialX β p + h₂) =
      fun p => partialY φ p + -partialX β p + h₂ from funext fun p => by rw [sub_eq_add_neg]]
  rw [reading_add (a := fun p => partialX φ p + partialY β p) (a' := fun _ => h₁)
      (b := fun p => partialY φ p + -partialX β p) (b' := fun _ => h₂)
      ((continuous_partialX hφ).add (continuous_partialY hβ))
      ((continuous_partialY hφ).add (continuous_partialX hβ).neg) continuous_const continuous_const,
    reading_add (a := partialX φ) (a' := partialY β) (b := partialY φ)
      (b' := fun p => -partialX β p) (continuous_partialX hφ) (continuous_partialY hφ)
      (continuous_partialY hβ) (continuous_partialX hβ).neg, state_reading hφ, winding_reading]

/-- [proved-derived; formal-checked] On a closed aeon with periodic state part the reading is
`production + h · N`: the continuum `cycle_reading_split`. -/
theorem closed_reading_split [CompleteSpace E] {φ β : ℝ × ℝ → E} (hφ : ContDiff ℝ 1 φ)
    (hper : IsPeriodic φ) (hβ : ContDiff ℝ 1 β) (h₁ h₂ : E) (γ : AeonPath) (N : ℤ × ℤ)
    (hN : γ.displacement = ((N.1 : ℝ), (N.2 : ℝ))) :
    reading (fun p => partialX φ p + partialY β p + h₁) (fun p => partialY φ p - partialX β p + h₂) γ =
      reading (partialY β) (fun p => -partialX β p) γ + ((N.1 : ℝ) • h₁ + (N.2 : ℝ) • h₂) := by
  rw [reading_split hφ hβ, hN]
  have ht : γ.target = (γ.source.1 + N.1, γ.source.2 + N.2) := by
    have := hN; rw [displacement, Prod.ext_iff] at this
    exact Prod.ext (by simp only [Prod.fst_sub] at this; linarith [this.1])
      (by simp only [Prod.snd_sub] at this; linarith [this.2])
  rw [ht, hper.add_int, sub_self, zero_add]

/-- [proved-standard; formal-checked] A horizontal edge reads `∫ a(x, y) dx`. -/
theorem reading_hEdge (a b : ℝ × ℝ → E) (y u v : ℝ) :
    reading a b (hEdge y u v) = ∫ x in u..v, a (x, y) := by
  simp [reading, hEdge]

/-- [proved-standard; formal-checked] A vertical edge reads `∫ b(x, y) dy`. -/
theorem reading_vEdge (a b : ℝ × ℝ → E) (x u v : ℝ) :
    reading a b (vEdge x u v) = ∫ y in u..v, b (x, y) := by
  simp [reading, vEdge]

/-- [proved-standard; formal-checked] The cell boundary reading as four edge integrals. -/
theorem cellReading_eq (a b : ℝ × ℝ → E) (x₀ x₁ y₀ y₁ : ℝ) :
    cellReading a b x₀ x₁ y₀ y₁ = ((∫ x in x₀..x₁, a (x, y₀)) - ∫ x in x₀..x₁, a (x, y₁)) +
      ((∫ y in y₀..y₁, b (x₁, y)) - ∫ y in y₀..y₁, b (x₀, y)) := by
  rw [cellReading, reading_hEdge, reading_vEdge, reading_hEdge, reading_vEdge,
    integral_symm x₀ x₁, integral_symm y₀ y₁]
  abel

/-- [proved-standard; formal-checked] **Green on a rectangle**: the cell boundary reads the iterated
integral of the curvature `∂ₓb − ∂ᵧa`. -/
theorem green [CompleteSpace E] {a b : ℝ × ℝ → E} (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (x₀ x₁ y₀ y₁ : ℝ) :
    cellReading a b x₀ x₁ y₀ y₁ = ∫ x in x₀..x₁, ∫ y in y₀..y₁, curvature a b (x, y) := by
  have hca := ha.continuous_fderiv one_ne_zero
  have hcb := hb.continuous_fderiv one_ne_zero
  have key := integral2_divergence_prod_of_hasFDerivAt b (fun p => -a p) (fderiv ℝ b)
    (fun p => -fderiv ℝ a p) x₀ y₀ x₁ y₁ hb.continuous.continuousOn ha.continuous.neg.continuousOn
    (fun p _ => ((hb.differentiable one_ne_zero) p).hasFDerivAt)
    (fun p _ => ((ha.differentiable one_ne_zero) p).hasFDerivAt.neg)
    (((hcb.clm_apply continuous_const).add
      ((hca.neg).clm_apply continuous_const)).continuousOn.integrableOn_compact
      (isCompact_uIcc.prod isCompact_uIcc))
  have hint : ∀ x y, fderiv ℝ b (x, y) (1, 0) + (-fderiv ℝ a (x, y)) (0, 1) =
      curvature a b (x, y) := by
    intro x y; simp [curvature, partialX, partialY, sub_eq_add_neg]
  simp only [hint, intervalIntegral.integral_neg] at key
  rw [key, cellReading_eq]
  abel

/-- [proved-standard; formal-checked] Cell boundary readings are additive in the form. -/
theorem cellReading_add [CompleteSpace E] {a b a' b' : ℝ × ℝ → E} (ha : Continuous a)
    (hb : Continuous b) (ha' : Continuous a') (hb' : Continuous b') (x₀ x₁ y₀ y₁ : ℝ) :
    cellReading (fun p => a p + a' p) (fun p => b p + b' p) x₀ x₁ y₀ y₁ =
      cellReading a b x₀ x₁ y₀ y₁ + cellReading a' b' x₀ x₁ y₀ y₁ := by
  simp only [cellReading, reading_add ha hb ha' hb']; abel

/-- [proved-derived; formal-checked] State time reads `0` on a cell boundary. -/
theorem state_cellReading [CompleteSpace E] {φ : ℝ × ℝ → E} (hφ : ContDiff ℝ 1 φ)
    (x₀ x₁ y₀ y₁ : ℝ) : cellReading (partialX φ) (partialY φ) x₀ x₁ y₀ y₁ = 0 := by
  simp only [cellReading, state_reading hφ, target, source, hEdge, vEdge]; abel

/-- [proved-derived; formal-checked] Winding time reads `0` on a cell boundary. -/
theorem winding_cellReading [CompleteSpace E] (h₁ h₂ : E) (x₀ x₁ y₀ y₁ : ℝ) :
    cellReading (fun _ => h₁) (fun _ => h₂) x₀ x₁ y₀ y₁ = 0 := by
  simp only [cellReading, winding_reading, displacement, target, source, hEdge, vEdge]
  simp only [Prod.fst_sub, Prod.snd_sub, sub_self, zero_smul, add_zero, zero_add, sub_smul]
  abel

/-- [proved-derived; formal-checked] **Only the production part reads on a cell boundary.** -/
theorem cellReading_split [CompleteSpace E] {φ β : ℝ × ℝ → E} (hφ : ContDiff ℝ 1 φ)
    (hβ : ContDiff ℝ 1 β) (h₁ h₂ : E) (x₀ x₁ y₀ y₁ : ℝ) :
    cellReading (fun p => partialX φ p + partialY β p + h₁)
      (fun p => partialY φ p - partialX β p + h₂) x₀ x₁ y₀ y₁ =
      cellReading (partialY β) (fun p => -partialX β p) x₀ x₁ y₀ y₁ := by
  simp only [sub_eq_add_neg]
  rw [cellReading_add (a := fun p => partialX φ p + partialY β p) (a' := fun _ => h₁)
      (b := fun p => partialY φ p + -partialX β p) (b' := fun _ => h₂)
      ((continuous_partialX hφ).add (continuous_partialY hβ))
      ((continuous_partialY hφ).add (continuous_partialX hβ).neg) continuous_const continuous_const,
    cellReading_add (a := partialX φ) (a' := partialY β) (b := partialY φ)
      (b' := fun p => -partialX β p) (continuous_partialX hφ) (continuous_partialY hφ)
      (continuous_partialY hβ) (continuous_partialX hβ).neg, state_cellReading hφ,
    winding_cellReading]
  abel

/-- [proved-derived; formal-checked] **Production is curvature**: `δβ = (∂ᵧβ, −∂ₓβ)` has curvature
`−Δβ`. -/
theorem curvature_coexact (β : ℝ × ℝ → E) (p : ℝ × ℝ) :
    curvature (partialY β) (fun q => -partialX β q) p = -laplacian β p := by
  have : (fun q => -partialX β q) = -(partialX β) := rfl
  rw [curvature, laplacian, this, partialX, fderiv_neg]
  simp only [neg_apply]
  rw [← partialX]; abel

/-- [proved-derived; formal-checked] The production part reads the flux of `−Δβ` on a cell
boundary. -/
theorem production_cellReading [CompleteSpace E] {β : ℝ × ℝ → E} (hβ : ContDiff ℝ 2 β)
    (x₀ x₁ y₀ y₁ : ℝ) :
    cellReading (partialY β) (fun p => -partialX β p) x₀ x₁ y₀ y₁ =
      ∫ x in x₀..x₁, ∫ y in y₀..y₁, -laplacian β (x, y) := by
  rw [green (contDiff_partialY hβ) (contDiff_partialX hβ).neg]
  simp only [curvature_coexact]

/-- [proved-derived; formal-checked] **A clock has no production**: a closed C¹ form reads `0` on
every cell boundary. -/
theorem clock_cellReading [CompleteSpace E] {a b : ℝ × ℝ → E} (ha : ContDiff ℝ 1 a)
    (hb : ContDiff ℝ 1 b) (hc : ∀ p, curvature a b p = 0) (x₀ x₁ y₀ y₁ : ℝ) :
    cellReading a b x₀ x₁ y₀ y₁ = 0 := by
  rw [green ha hb]; simp [hc]

/-! ### 5. The split at declared width -/

/-- [definition] The symbol `2πi k₁` of `∂ₓ` on the mode `k`. -/
def dx (k : ℤ × ℤ) : ℂ := 2 * π * Complex.I * k.1

/-- [definition] The symbol `2πi k₂` of `∂ᵧ` on the mode `k`. -/
def dy (k : ℤ × ℤ) : ℂ := 2 * π * Complex.I * k.2

/-- [proved-standard; formal-checked] The zero mode carries no `∂ₓ`. -/
theorem dx_zero : dx 0 = 0 := by simp [dx]

/-- [proved-standard; formal-checked] The zero mode carries no `∂ᵧ`. -/
theorem dy_zero : dy 0 = 0 := by simp [dy]

/-- [definition] The Fourier mode `e_k(p) = exp(2πi(k₁ p₁ + k₂ p₂))`. -/
def mode (k : ℤ × ℤ) (p : ℝ × ℝ) : ℂ := Complex.exp (dx k * p.1 + dy k * p.2)

/-- [definition] The phase of the mode `k`, a real-linear map of the plane. -/
def phase (k : ℤ × ℤ) : ℝ × ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (dx k) + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (dy k)

/-- [definition] A trigonometric polynomial at the declared width `S`: `Σ_(k∈S) c_k e_k`. -/
def trig (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (p : ℝ × ℝ) : ℂ := ∑ k ∈ S, c k * mode k p

/-- [definition] The mean `∫₀¹∫₀¹ F` over a fundamental cell of the torus. -/
def mean (F : ℝ × ℝ → E) : E := ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, F (x, y)

/-- [definition] The Fourier coefficient `∫∫ F e_(−j)`. -/
def fourierCoeff (j : ℤ × ℤ) (F : ℝ × ℝ → ℂ) : ℂ := mean (fun p => F p * mode (-j) p)

/-- [definition] The state coefficient `(∂ₓA + ∂ᵧB)/(∂ₓ² + ∂ᵧ²)` of one mode. -/
def stateCoeff (k : ℤ × ℤ) (α β : ℂ) : ℂ := (dx k * α + dy k * β) / (dx k ^ 2 + dy k ^ 2)

/-- [definition] The production coefficient `(∂ᵧA − ∂ₓB)/(∂ₓ² + ∂ᵧ²)` of one mode. -/
def prodCoeff (k : ℤ × ℤ) (α β : ℂ) : ℂ := (dy k * α - dx k * β) / (dx k ^ 2 + dy k ^ 2)

/-- [definition] The state potential at declared width. -/
def stateTrig (S : Finset (ℤ × ℤ)) (A B : ℤ × ℤ → ℂ) : ℝ × ℝ → ℂ :=
  trig S fun k => stateCoeff k (A k) (B k)

/-- [definition] The production potential at declared width. -/
def prodTrig (S : Finset (ℤ × ℤ)) (A B : ℤ × ℤ → ℂ) : ℝ × ℝ → ℂ :=
  trig S fun k => prodCoeff k (A k) (B k)

/-- [proved-standard; formal-checked] The phase map in coordinates. -/
theorem phase_apply (k : ℤ × ℤ) (p : ℝ × ℝ) : phase k p = dx k * p.1 + dy k * p.2 := by
  simp [phase, Complex.real_smul, mul_comm]

/-- [proved-standard; formal-checked] A mode is the exponential of its phase. -/
theorem mode_eq (k : ℤ × ℤ) : mode k = fun p => Complex.exp (phase k p) := by
  funext p; simp [mode, phase_apply]

/-- [proved-standard; formal-checked] The zero mode is the constant `1`. -/
theorem mode_zero (p : ℝ × ℝ) : mode 0 p = 1 := by simp [mode, dx_zero, dy_zero]

/-- [proved-standard; formal-checked] Modes multiply by adding their frequencies. -/
theorem mode_mul (k j : ℤ × ℤ) (p : ℝ × ℝ) : mode k p * mode j p = mode (k + j) p := by
  simp only [mode, ← Complex.exp_add, dx, dy, Prod.fst_add, Prod.snd_add, Int.cast_add]
  congr 1; ring

/-- [proved-standard; formal-checked] A mode is the product of its two circle modes. -/
theorem mode_apply (k : ℤ × ℤ) (x y : ℝ) :
    mode k (x, y) = Complex.exp (dx k * x) * Complex.exp (dy k * y) := by
  rw [mode, Complex.exp_add]

/-- [proved-standard; formal-checked] Modes are continuous. -/
theorem continuous_mode (k : ℤ × ℤ) : Continuous (mode k) := by
  rw [mode_eq]; exact (phase k).continuous.cexp

/-- [proved-standard; formal-checked] The derivative of a mode is its phase times itself. -/
theorem hasFDerivAt_mode (k : ℤ × ℤ) (p : ℝ × ℝ) :
    HasFDerivAt (mode k) (mode k p • phase k) p := by
  rw [mode_eq]; exact (phase k).hasFDerivAt.cexp

/-- [proved-standard; formal-checked] Trigonometric polynomials are smooth. -/
theorem contDiff_trig (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (trig S c) := by
  unfold trig
  refine ContDiff.sum fun k _ => contDiff_const.mul ?_
  rw [mode_eq]; exact (phase k).contDiff.cexp

/-- [proved-standard; formal-checked] The derivative of a trigonometric polynomial. -/
theorem hasFDerivAt_trig (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (p : ℝ × ℝ) :
    HasFDerivAt (trig S c) (∑ k ∈ S, c k • mode k p • phase k) p :=
  HasFDerivAt.fun_sum fun k _ => (hasFDerivAt_mode k p).const_mul (c k)

/-- [proved-standard; formal-checked] **The symbol rule** `∂ₓ e_k = 2πi k₁ e_k`. -/
theorem partialX_trig (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) :
    partialX (trig S c) = trig S (fun k => dx k * c k) := by
  funext p
  rw [partialX, (hasFDerivAt_trig S c p).fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, phase_apply,
    smul_eq_mul, trig]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp; ring

/-- [proved-standard; formal-checked] **The symbol rule** `∂ᵧ e_k = 2πi k₂ e_k`. -/
theorem partialY_trig (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) :
    partialY (trig S c) = trig S (fun k => dy k * c k) := by
  funext p
  rw [partialY, (hasFDerivAt_trig S c p).fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, phase_apply,
    smul_eq_mul, trig]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp; ring

/-- [proved-standard; formal-checked] Mode-wise, `−Δ e_k = 4π²|k|² e_k`: the Laplacian's symbol is
`∂ₓ² + ∂ᵧ²`. -/
theorem laplacian_trig (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) :
    laplacian (trig S c) = trig S (fun k => (dx k ^ 2 + dy k ^ 2) * c k) := by
  funext p
  simp only [laplacian, partialX_trig, partialY_trig, trig, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => by ring

/-- [proved-standard; formal-checked] For `k ≠ 0`, `∂ₓ² + ∂ᵧ² = −4π²|k|² ≠ 0`: `k` and `k^⊥` are a
basis. -/
theorem normSq_ne_zero {k : ℤ × ℤ} (hk : k ≠ 0) : dx k ^ 2 + dy k ^ 2 ≠ 0 := by
  have e : dx k ^ 2 + dy k ^ 2 = -(4 * π ^ 2 : ℂ) * (((k.1 ^ 2 + k.2 ^ 2 : ℤ) : ℂ)) := by
    simp only [dx, dy, Int.cast_add, Int.cast_pow]
    ring_nf; rw [Complex.I_sq]; ring
  have hz : (k.1 ^ 2 + k.2 ^ 2 : ℤ) ≠ 0 := by
    intro h
    apply hk
    have h1 : k.1 ^ 2 = 0 := by nlinarith [sq_nonneg k.1, sq_nonneg k.2]
    have h2 : k.2 ^ 2 = 0 := by nlinarith [sq_nonneg k.1, sq_nonneg k.2]
    exact Prod.ext (pow_eq_zero_iff two_ne_zero |>.mp h1) (pow_eq_zero_iff two_ne_zero |>.mp h2)
  rw [e]
  refine mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (by norm_num) ?_)) (Int.cast_ne_zero.mpr hz)
  exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr pi_ne_zero)

/-- [proved-derived; formal-checked] **The mode split**: for `k ≠ 0`,
`(A, B) = φ_k (∂ₓ, ∂ᵧ) + β_k (∂ᵧ, −∂ₓ)`. -/
theorem mode_split {k : ℤ × ℤ} (hk : k ≠ 0) (α β : ℂ) :
    α = dx k * stateCoeff k α β + dy k * prodCoeff k α β ∧
      β = dy k * stateCoeff k α β - dx k * prodCoeff k α β := by
  have h := normSq_ne_zero hk
  unfold stateCoeff prodCoeff
  constructor
  · field_simp; ring
  · field_simp; ring

/-- [proved-derived; formal-checked] **The mode split is unique.** -/
theorem mode_split_unique {k : ℤ × ℤ} (hk : k ≠ 0) {α β φ' β' : ℂ}
    (h₁ : α = dx k * φ' + dy k * β') (h₂ : β = dy k * φ' - dx k * β') :
    φ' = stateCoeff k α β ∧ β' = prodCoeff k α β := by
  have h := normSq_ne_zero hk
  subst h₁ h₂
  unfold stateCoeff prodCoeff
  constructor
  · field_simp; ring
  · field_simp; ring

/-- [proved-derived; formal-checked] Mode-wise the curvature is the production coefficient times
`−(∂ₓ² + ∂ᵧ²)`. -/
theorem curvature_coeff {k : ℤ × ℤ} (hk : k ≠ 0) (α β : ℂ) :
    dx k * β - dy k * α = -(dx k ^ 2 + dy k ^ 2) * prodCoeff k α β := by
  have h := normSq_ne_zero hk
  unfold prodCoeff; field_simp; ring

/-- [proved-standard; formal-checked] `∫₀¹ exp(2πi n x) dx` is `1` at `n = 0` and `0` otherwise. -/
theorem integral_exp_two_pi_int (n : ℤ) :
    ∫ x in (0 : ℝ)..1, Complex.exp (2 * π * Complex.I * n * x) = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst hn; simp
  · have hc : (2 * π * Complex.I * n : ℂ) ≠ 0 := by simp [hn, pi_ne_zero, Complex.I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.ofReal_one, mul_one,
        show (2 * π * Complex.I * n : ℂ) = n * (2 * π * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [h1]; simp

/-- [proved-standard; formal-checked] **Orthogonality**: the mean of a sum of modes keeps the zero
modes. -/
theorem mean_sum_mode {ι : Type*} (S : Finset ι) (d : ι → ℂ) (g : ι → ℤ × ℤ) :
    mean (fun p => ∑ i ∈ S, d i * mode (g i) p) = ∑ i ∈ S, if g i = 0 then d i else 0 := by
  unfold mean
  have inner : ∀ x : ℝ, ∫ y in (0 : ℝ)..1, ∑ i ∈ S, d i * mode (g i) (x, y) =
      ∑ i ∈ S, (d i * (if (g i).2 = 0 then 1 else 0)) * Complex.exp (dx (g i) * x) := by
    intro x
    have hint : ∀ i ∈ S, IntervalIntegrable (fun y : ℝ => d i * mode (g i) (x, y)) volume 0 1 :=
      fun i _ => Continuous.intervalIntegrable (continuous_const.mul ((continuous_mode (g i)).comp
        (continuous_const.prodMk continuous_id))) _ _
    rw [intervalIntegral.integral_finsetSum hint]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mode_apply]
    rw [show (fun y : ℝ => d i * (Complex.exp (dx (g i) * x) * Complex.exp (dy (g i) * y))) =
        fun y : ℝ => (d i * Complex.exp (dx (g i) * x)) * Complex.exp (dy (g i) * y) by
      funext y; ring, intervalIntegral.integral_const_mul]
    simp only [dy]
    rw [integral_exp_two_pi_int]; ring
  simp only [inner]
  have hint : ∀ i ∈ S, IntervalIntegrable (fun x : ℝ => (d i * (if (g i).2 = 0 then 1 else 0)) *
      Complex.exp (dx (g i) * x)) volume 0 1 :=
    fun i _ => Continuous.intervalIntegrable (continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))) _ _
  rw [intervalIntegral.integral_finsetSum hint]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_const_mul]
  simp only [dx]
  rw [integral_exp_two_pi_int]
  by_cases h1 : (g i).1 = 0 <;> by_cases h2 : (g i).2 = 0 <;> simp [h1, h2, Prod.ext_iff]

/-- [proved-standard; formal-checked] The mean of a trigonometric polynomial is its zero
coefficient. -/
theorem mean_trig (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) :
    mean (trig S c) = if (0 : ℤ × ℤ) ∈ S then c 0 else 0 := by
  have : trig S c = fun p => ∑ k ∈ S, c k * mode (id k) p := rfl
  rw [this, mean_sum_mode]; simp only [id]; exact Finset.sum_ite_eq' S 0 c

/-- [proved-standard; formal-checked] The Fourier coefficient of a sum of modes. -/
theorem fourierCoeff_sum_mode {ι : Type*} (S : Finset ι) (d : ι → ℂ) (g : ι → ℤ × ℤ)
    (j : ℤ × ℤ) :
    fourierCoeff j (fun p => ∑ i ∈ S, d i * mode (g i) p) = ∑ i ∈ S, if g i = j then d i else 0 := by
  have : (fun p => (∑ i ∈ S, d i * mode (g i) p) * mode (-j) p) =
      fun p => ∑ i ∈ S, d i * mode (g i + -j) p := by
    funext p; rw [Finset.sum_mul]; simp only [mul_assoc, mode_mul]
  rw [fourierCoeff, this, mean_sum_mode]
  simp only [add_neg_eq_zero]

/-- [proved-standard; formal-checked] **A trigonometric polynomial determines its coefficients.** -/
theorem fourierCoeff_trig (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (j : ℤ × ℤ) :
    fourierCoeff j (trig S c) = if j ∈ S then c j else 0 := by
  have : trig S c = fun p => ∑ k ∈ S, c k * mode (id k) p := rfl
  rw [this, fourierCoeff_sum_mode]; simp only [id]; exact Finset.sum_ite_eq' S j c

/-- [proved-standard; formal-checked] The Fourier coefficient of a constant plus a trigonometric
polynomial. -/
theorem fourierCoeff_const_add_trig (S : Finset (ℤ × ℤ)) (c₀ : ℂ) (c : ℤ × ℤ → ℂ) (j : ℤ × ℤ) :
    fourierCoeff j (fun p => c₀ + trig S c p) =
      (if j = 0 then c₀ else 0) + if j ∈ S then c j else 0 := by
  have : (fun p => c₀ + trig S c p) = fun p => ∑ i ∈ Finset.insertNone S,
      (Option.elim i c₀ c) * mode (Option.elim i 0 id) p := by
    funext p; rw [Finset.sum_insertNone]; simp [mode_zero, trig]
  rw [this, fourierCoeff_sum_mode, Finset.sum_insertNone]
  have h2 : (∑ x ∈ S, if Option.elim (some x) (0 : ℤ × ℤ) id = j then Option.elim (some x) c₀ c
      else 0) = if j ∈ S then c j else 0 := Finset.sum_ite_eq' S j c
  rw [h2]
  show (if (0 : ℤ × ℤ) = j then c₀ else 0) + _ = _
  by_cases hj : j = 0
  · subst hj; simp
  · simp [Ne.symm hj, hj]

/-- [proved-standard; formal-checked] The mean is the zero Fourier coefficient. -/
theorem mean_eq_fourierCoeff_zero (F : ℝ × ℝ → ℂ) : mean F = fourierCoeff 0 F := by
  simp [fourierCoeff, mode_zero]

/-- [proved-derived; formal-checked] **The split at declared width**: `a = h₁ + ∂ₓφ + ∂ᵧβ` and
`b = h₂ + ∂ᵧφ − ∂ₓβ`, with `h = (∫∫a, ∫∫b)`. -/
theorem trig_split (S : Finset (ℤ × ℤ)) (A B : ℤ × ℤ → ℂ) (p : ℝ × ℝ) :
    trig S A p = mean (trig S A) + partialX (stateTrig S A B) p + partialY (prodTrig S A B) p ∧
      trig S B p = mean (trig S B) + partialY (stateTrig S A B) p - partialX (prodTrig S A B) p := by
  simp only [stateTrig, prodTrig, partialX_trig, partialY_trig, mean_trig]
  rw [← Finset.sum_ite_eq' S 0 A, ← Finset.sum_ite_eq' S 0 B]
  simp only [trig, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  constructor
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = 0
    · subst hk; simp [mode_zero, dx_zero, dy_zero]
    · simp only [hk, if_false, zero_add]
      linear_combination mode k p * (mode_split hk (A k) (B k)).1
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = 0
    · subst hk; simp [mode_zero, dx_zero, dy_zero]
    · simp only [hk, if_false, zero_add]
      linear_combination mode k p * (mode_split hk (A k) (B k)).2

/-- [proved-derived; formal-checked] **The split at declared width is unique**: any split of this
shape has the mean as its harmonic part and the mode coefficients of `trig_split`. -/
theorem trig_split_unique {S : Finset (ℤ × ℤ)} {A B P Q : ℤ × ℤ → ℂ} {c₁ c₂ : ℂ}
    (ha : ∀ p, trig S A p = c₁ + partialX (trig S P) p + partialY (trig S Q) p)
    (hb : ∀ p, trig S B p = c₂ + partialY (trig S P) p - partialX (trig S Q) p) :
    c₁ = mean (trig S A) ∧ c₂ = mean (trig S B) ∧
      ∀ k ∈ S, k ≠ 0 → P k = stateCoeff k (A k) (B k) ∧ Q k = prodCoeff k (A k) (B k) := by
  simp only [partialX_trig, partialY_trig] at ha hb
  have ha' : trig S A = fun p => c₁ + trig S (fun k => dx k * P k + dy k * Q k) p := by
    funext p; rw [ha p]; simp only [trig, add_assoc, ← Finset.sum_add_distrib, add_mul]
  have hb' : trig S B = fun p => c₂ + trig S (fun k => dy k * P k - dx k * Q k) p := by
    funext p; rw [hb p]; simp only [trig, add_sub_assoc, ← Finset.sum_sub_distrib, sub_mul]
  have ca := fun j => congrArg (fourierCoeff j) ha'
  have cb := fun j => congrArg (fourierCoeff j) hb'
  simp only [fourierCoeff_trig, fourierCoeff_const_add_trig] at ca cb
  refine ⟨?_, ?_, fun k hk hk0 => ?_⟩
  · rw [mean_eq_fourierCoeff_zero, ha', fourierCoeff_const_add_trig]; simp [dx_zero, dy_zero]
  · rw [mean_eq_fourierCoeff_zero, hb', fourierCoeff_const_add_trig]; simp [dx_zero, dy_zero]
  · have h1 := ca k
    have h2 := cb k
    simp only [hk, hk0, if_true, if_false, zero_add] at h1 h2
    exact mode_split_unique hk0 h1 h2

/-- [proved-standard; formal-checked] The curvature of a form at declared width, mode by mode. -/
theorem curvature_trig (S : Finset (ℤ × ℤ)) (A B : ℤ × ℤ → ℂ) :
    curvature (trig S A) (trig S B) = trig S (fun k => dx k * B k - dy k * A k) := by
  funext p
  simp only [curvature, partialX_trig, partialY_trig, trig, ← Finset.sum_sub_distrib, sub_mul]

/-- [proved-derived; formal-checked] **A form at declared width is closed iff its production part
vanishes**: the continuum `isClosed_iff_production_zero`. -/
theorem trig_closed_iff (S : Finset (ℤ × ℤ)) (A B : ℤ × ℤ → ℂ) :
    curvature (trig S A) (trig S B) = 0 ↔ ∀ k ∈ S, k ≠ 0 → prodCoeff k (A k) (B k) = 0 := by
  rw [curvature_trig]
  constructor
  · intro h k hk hk0
    have := congrArg (fourierCoeff k) h
    rw [fourierCoeff_trig, if_pos hk] at this
    have h0 : fourierCoeff k (0 : ℝ × ℝ → ℂ) = 0 := by simp [fourierCoeff, mean]
    rw [h0, curvature_coeff hk0] at this
    exact (mul_eq_zero.mp this).resolve_left (neg_ne_zero.mpr (normSq_ne_zero hk0))
  · intro h
    funext p
    refine Finset.sum_eq_zero fun k hk => ?_
    by_cases hk0 : k = 0
    · subst hk0; simp [dx_zero, dy_zero]
    · show (dx k * B k - dy k * A k) * mode k p = 0
      rw [curvature_coeff hk0, h k hk hk0]; ring

/-- [proved-standard; formal-checked] Reversing a mode reverses its symbol. -/
theorem dx_neg (k : ℤ × ℤ) : dx (-k) = -dx k := by simp [dx]

/-- [proved-standard; formal-checked] Reversing a mode reverses its symbol. -/
theorem dy_neg (k : ℤ × ℤ) : dy (-k) = -dy k := by simp [dy]

/-- [proved-standard; formal-checked] The symbol is imaginary. -/
theorem conj_dx (k : ℤ × ℤ) : (starRingEnd ℂ) (dx k) = -dx k := by simp [dx, map_ofNat]

/-- [proved-standard; formal-checked] The symbol is imaginary. -/
theorem conj_dy (k : ℤ × ℤ) : (starRingEnd ℂ) (dy k) = -dy k := by simp [dy, map_ofNat]

/-- [proved-derived; formal-checked] **The reality condition passes to the state part**:
`φ_(−k) = conj φ_k` when `A_(−k) = conj A_k`, `B_(−k) = conj B_k`. -/
theorem stateCoeff_conj (k : ℤ × ℤ) (α β : ℂ) :
    stateCoeff (-k) ((starRingEnd ℂ) α) ((starRingEnd ℂ) β) = (starRingEnd ℂ) (stateCoeff k α β) := by
  simp only [stateCoeff, map_div₀, map_add, map_mul, map_pow, conj_dx, conj_dy, dx_neg, dy_neg]

/-- [proved-derived; formal-checked] **The reality condition passes to the production part.** -/
theorem prodCoeff_conj (k : ℤ × ℤ) (α β : ℂ) :
    prodCoeff (-k) ((starRingEnd ℂ) α) ((starRingEnd ℂ) β) = (starRingEnd ℂ) (prodCoeff k α β) := by
  simp only [prodCoeff, map_div₀, map_sub, map_add, map_mul, map_pow, conj_dx, conj_dy, dx_neg,
    dy_neg]

/-! ### 7. Witnesses -/

/-- [proved-standard; formal-checked] The partials of a function of `y` alone. -/
theorem partials_of_snd {g g' : ℝ → ℝ} (hg : ∀ y, HasDerivAt g (g' y) y) (p : ℝ × ℝ) :
    partialX (fun q : ℝ × ℝ => g q.2) p = 0 ∧ partialY (fun q : ℝ × ℝ => g q.2) p = g' p.2 := by
  have h := (hg p.2).hasFDerivAt.comp p (hasFDerivAt_snd (p := p))
  rw [partialX, partialY, show (fun q : ℝ × ℝ => g q.2) = g ∘ Prod.snd from rfl, h.fderiv]
  simp

/-- [definition] The coexact witness `ω = cos(2πy) dx` (its `dx` coefficient). -/
def cosForm : ℝ × ℝ → ℝ := fun q => cos (2 * π * q.2)

/-- [definition] Its production potential `β = sin(2πy)/(2π)`. -/
def cosPotential : ℝ × ℝ → ℝ := fun q => sin (2 * π * q.2) / (2 * π)

/-- [proved-standard; formal-checked] `(sin(2πy)/(2π))′ = cos(2πy)`. -/
theorem hasDerivAt_sin_div (y : ℝ) :
    HasDerivAt (fun y => sin (2 * π * y) / (2 * π)) (cos (2 * π * y)) y := by
  have h := (((hasDerivAt_id' y).const_mul (2 * π)).sin).div_const (2 * π)
  have e : cos (2 * π * y) * (2 * π * 1) / (2 * π) = cos (2 * π * y) := by field_simp
  rwa [e] at h

/-- [proved-standard; formal-checked] `(cos(2πy))′ = −2π sin(2πy)`. -/
theorem hasDerivAt_cos_mul (y : ℝ) :
    HasDerivAt (fun y => cos (2 * π * y)) (-(2 * π * sin (2 * π * y))) y := by
  have h := ((hasDerivAt_id' y).const_mul (2 * π)).cos
  have e : -sin (2 * π * y) * (2 * π * 1) = -(2 * π * sin (2 * π * y)) := by ring
  rwa [e] at h

/-- [counterexample; formal-checked] `cos(2πy) dx = δβ` for `β = sin(2πy)/(2π)`: a coexact form. -/
theorem cosForm_coexact (p : ℝ × ℝ) :
    cosForm p = partialY cosPotential p ∧ (0 : ℝ) = -partialX cosPotential p := by
  have h := partials_of_snd (g := fun y => sin (2 * π * y) / (2 * π)) hasDerivAt_sin_div p
  exact ⟨h.2.symm, by
    rw [show cosPotential = fun q : ℝ × ℝ => sin (2 * π * q.2) / (2 * π) from rfl, h.1, neg_zero]⟩

/-- [counterexample; formal-checked] Its harmonic part `∫∫ cos(2πy)` is `0`. -/
theorem mean_cosForm : mean cosForm = 0 := by
  simp [mean, cosForm]

/-- [counterexample; formal-checked] Its curvature is `2π sin(2πy)`. -/
theorem curvature_cosForm (p : ℝ × ℝ) :
    curvature cosForm (fun _ => (0 : ℝ)) p = 2 * π * sin (2 * π * p.2) := by
  have h := partials_of_snd (g := fun y => cos (2 * π * y)) hasDerivAt_cos_mul p
  rw [curvature, show cosForm = fun q : ℝ × ℝ => cos (2 * π * q.2) from rfl, h.2]
  simp [partialX]

/-- [counterexample; formal-checked] The horizontal closed aeon at height `y` reads `cos(2πy)`. -/
theorem cosForm_reading_horizontal (y : ℝ) :
    reading cosForm (fun _ => (0 : ℝ)) (hEdge y 0 1) = cos (2 * π * y) := by
  simp [reading_hEdge, cosForm]

/-- [proved-standard; formal-checked] A horizontal edge over `[u, v]` moves by `(v − u, 0)`. -/
theorem displacement_hEdge (y u v : ℝ) : (hEdge y u v).displacement = (v - u, 0) := by
  simp [displacement, target, source, hEdge]

/-- [counterexample; formal-checked] The horizontal closed aeon at `y = 0` reads `1`. -/
theorem cosForm_reading_zero : reading cosForm (fun _ => (0 : ℝ)) (hEdge 0 0 1) = 1 := by
  rw [cosForm_reading_horizontal]; simp

/-- [counterexample; formal-checked] The horizontal closed aeon at `y = ½` reads `−1`. -/
theorem cosForm_reading_half : reading cosForm (fun _ => (0 : ℝ)) (hEdge (1 / 2) 0 1) = -1 := by
  rw [cosForm_reading_horizontal, show 2 * π * (1 / 2 : ℝ) = π by ring, cos_pi]

/-- [counterexample; formal-checked] The boundary of `[0, 1] × [0, ½]` reads `2`. -/
theorem cosForm_cellReading : cellReading cosForm (fun _ => (0 : ℝ)) 0 1 0 (1 / 2) = 2 := by
  rw [cellReading, cosForm_reading_zero, reading_vEdge, reading_hEdge, reading_vEdge,
    integral_symm 0 1]
  have : ∫ x in (0 : ℝ)..1, cosForm (x, 1 / 2) = -1 := by
    rw [← reading_hEdge cosForm (fun _ => (0 : ℝ)), cosForm_reading_half]
  rw [this]; simp; norm_num

/-- [counterexample; formal-checked] The curvature flux through `[0, 1] × [0, ½]` is
`∫₀¹∫₀^½ 2π sin(2πy) = 2`. -/
theorem cosForm_flux :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1 / 2), curvature cosForm (fun _ => (0 : ℝ)) (x, y) = 2 := by
  simp only [curvature_cosForm]
  have : ∫ y in (0 : ℝ)..(1 / 2), 2 * π * sin (2 * π * y) = 2 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun y => sin y) (by positivity : (2 * π : ℝ) ≠ 0)]
    rw [show 2 * π * (1 / 2 : ℝ) = π by ring, integral_sin, cos_pi]
    simp; field_simp; norm_num
  rw [intervalIntegral.integral_congr (g := fun _ => (2 : ℝ)) (fun x _ => this)]
  simp

/-- [counterexample; formal-checked] **Production time on homologous closed aeons**: the loops at
`y = 0` and `y = ½` (both of winding vector `(1, 0)`) differ in reading by the curvature flux through
the band between them. -/
theorem cosForm_homologous_loops :
    (hEdge 0 0 1).displacement = (hEdge (1 / 2) 0 1).displacement ∧
      reading cosForm (fun _ => (0 : ℝ)) (hEdge 0 0 1) -
          reading cosForm (fun _ => (0 : ℝ)) (hEdge (1 / 2) 0 1) =
        ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1 / 2), curvature cosForm (fun _ => (0 : ℝ)) (x, y) := by
  refine ⟨by rw [displacement_hEdge, displacement_hEdge], ?_⟩
  rw [cosForm_reading_zero, cosForm_reading_half, cosForm_flux]; norm_num

/-- [definition] The harmonic witness `ω = dx` (its `dx` coefficient). -/
def dxForm : ℝ × ℝ → ℝ := fun _ => 1

/-- [counterexample; formal-checked] **Winding time is not boundary-determined**: `dx` reads `1` on
the loop `t ↦ (t, 0)` and `0` on the empty aeon, with the same endpoints on the torus. -/
theorem dxForm_winding_not_boundary_determined :
    toTorus (hEdge 0 0 1).source = toTorus (hEdge 0 0 0).source ∧
      toTorus (hEdge 0 0 1).target = toTorus (hEdge 0 0 0).target ∧
      reading dxForm (fun _ => (0 : ℝ)) (hEdge 0 0 1) = 1 ∧
      reading dxForm (fun _ => (0 : ℝ)) (hEdge 0 0 0) = 0 := by
  refine ⟨rfl, ?_, by simp [reading_hEdge, dxForm], by simp [reading_hEdge, dxForm]⟩
  simp [toTorus, target, hEdge, AddCircle.coe_period]

end Torus

end Holonics.Aeon.Production.ContinuumHodgeTime

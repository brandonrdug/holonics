import HolonicsResearch.Physics.Spacetime.CurvatureJets
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Geodesic deviation from a connection: two neighbouring free falls part by the curvature

[definition] The box of #410, "Curvature's strain and rotation: the Weyl tensor's electric/magnetic
split and Petrov's classification; Raychaudhuri's equation from a Lorentzian metric, connection and
congruence", part done in #1024 (`Physics/Spacetime/Raychaudhuri`, which takes the deviation
equation `J″ = −RJ` as its premise), #1031 (`Physics/Spacetime/PetrovTypes`) and #1032
(`Physics/Spacetime/CurvatureJets`, curvature from a metric's 2-jet at a point), with "the deviation
equation along a general geodesic" left: this module derives it from a connection's coefficients
and their first jet, and carries it through a parallel frame to `Raychaudhuri`'s premise. Sources:
`CurvatureJets`' "What is not claimed" ("The deviation equation `J″ = −RJ` along a general geodesic
stays owed: the tide is read at a point, and `Raychaudhuri` takes the deviation equation as a
hypothesis") and its `christoffel`, `christoffelJet`, `riemann`, `riemannLower`, `connection`,
`riemann_eq_commutator`, `tide` and `minkowski`; `Raychaudhuri`'s "What is not claimed" ("neither
`J″ = −RJ` nor `R_ij = R_(i a j b) u^a u^b` is derived from a Lorentzian metric and its
connection") and its `raychaudhuri`, `deformation`, `expansion`, `raychaudhuriRate`,
`hasDerivAt_ringInverse_comp`; `FriedmannFluid.comoving_deviation` (the one congruence where the
premise was proved); the Swing record
(`research/records/2026-09-28_THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_A_GRIP_TURNS_A_PUSH_BOOSTS_AND_A_FREE_BODY_FALLS.md`
§5.6: "Free fall is the geodesic, and gravity the connection"; "A free-falling congruence focuses by
strain and resists by rotation"); and atlas `coupling.curvature-jets`, `gr.curvature-commutator`,
`cell.connection-route-return`, `coupling.raychaudhuri-riccati`, `coupling.deviation-focus`.

Everything is over ℝ in coordinates `Fin n`. A **connection** is its coefficients
`Γ y a b c = Γ^a_bc(y)` (`Coeff`), the lower index `b` the direction; its **first jet** at a point
`p` is `dG e a b c = ∂_eΓ^a_bc(p)` (`CoeffJet`, the index order of the owner's `christoffelJet`),
held as the Fréchet derivative `Σ_e dG e a b c · dx^e` of each coefficient (`HasConnectionJetAt`).
It is **torsion-free** where `Γ^a_bc = Γ^a_cb`. Its **Riemann tensor** is the owner's formula
`R^a_bcd = ∂_cΓ^a_db − ∂_dΓ^a_cb + Γ^a_ce Γ^e_db − Γ^a_de Γ^e_cb` (`riemannOf`). The connection's
**form** is `Γ(v, V)^a = Γ^a_bc v^b V^c` (`gammaForm`), with rate `(∂_zΓ)^a_bc = Σ_e ∂_eΓ^a_bc z^e`
along `z` (`rateAlong`) and matrix `A(v) = (Γ^a_bc v^b)_(ac) = Σ_c v^c A_c` (`connectionAlong`).
Along a curve with velocity `v`, a field `V` whose rate is `V′` has the **covariant derivative**
`D V = V′ + Γ(v, V)` (`covD`); the curve is a **geodesic** where its acceleration `α = u̇` has
`D u = α + Γ(u, u) = 0`. The **curvature operator** is
`R(X, Y)V = (∂_XΓ)(Y, V) − (∂_YΓ)(X, V) + Γ(X, Γ(Y, V)) − Γ(Y, Γ(X, V))` (`curvature`), whose
components are `R^a_bcd V^b X^c Y^d`. A **family** `x(τ, s)` is given at a point by its partials
(`FamilyAt`): `u = ∂_τx`, `ξ = ∂_sx`, `w = ∂_su = ∂_τξ` (one value for both: the second mixed
partials agree), `α = ∂_τu` and `β = ∂_sα = ∂_τw` (the third). The **tidal matrix** is
`(R(·, u)u)^a_c = R^a_bcd u^b u^d` (`tidal`). A matrix whose `i`-th column is `V i` is `cols V`, and
a frame `E` reads the tidal matrix as `𝓡 = E⁻¹ R(·, u)u E` (`frameTidal`), the frame's
`𝓡_ij = (E⁻¹ R(E_j, u)u)_i`. The sign convention is Misner–Thorne–Wheeler's, the owner's.

[proved-standard; formal-checked] What is proved.

1. **The owner's curvature is the connection's** (`riemann_eq_riemannOf`, `connectionAlong_mulVec`,
   `connectionAlong_christoffel`, `tidal_mulVec`, `tidal_single`, `tidal_observer`, `tide_eq_tidal`,
   `tidal_mulVec_self`). At a point the owner's `riemann g dg ddg` is
   `riemannOf (christoffel g dg) (christoffelJet g dg ddg)`, by unfolding; `A(v)` is `Σ_c v^c A_c` of
   the owner's `connection`; the tidal matrix at the observer `e₀` is `R^a_0c0`, the owner's `tide`
   on the spatial indices, and at `g = η` the owner's `tide (riemannLower η dg ddg)` is
   `R^(i+1)_0(j+1)0`. A geodesic's own tangent has no tide: `R(u, u)u = 0`.
2. **The calculus along a curve** (`hasDerivAt_gammaForm`, `hasDerivAt_covD`, `jetForm_apply`,
   `jetForm_apply_swap`, `squareForm_apply`, `squareForm_apply_swap`, `curvature_apply`,
   `riemannOf_anti`, `curvature_deviation`, `gammaForm_add_right`, `gammaForm_zero_right`,
   `gammaForm_comm`). With the connection's first jet, `Γ(x(t))(v(t), V(t))` has the rate
   `(∂_{ẋ}Γ)(v, V) + Γ(v̇, V) + Γ(v, V̇)` (Mathlib's chain rule and product rule), and
   `R(X, Y)V^a = R^a_bcd V^b X^c Y^d` for the owner's formula, which is antisymmetric in `c d`.
3. **The deviation equation along a general geodesic** (`covD_symm`, `covD_commutator`,
   `deviation`, `deviation_tidal`). For any connection and any family with the partial data at a
   point, `D_τ D_s u − D_s D_τ u = R(u, ξ)u` there: the commutator of the two covariant derivatives
   around the family's coordinate cell (no symmetry of `Γ` is used; the coordinate fields commute
   because the mixed partials agree). A torsion-free connection has `D_τ ξ = D_s u`. Where every
   curve of the family is a geodesic near the point along `s`, the deviation obeys
   `(D_τ D_τ ξ)^a = −R^a_bcd u^b ξ^c u^d`, that is `D_τ²ξ = −R(ξ, u)u = −(R(·, u)u) ξ` (the rate `Z`
   of `D_τξ` that the statement names is supplied by `hasDerivAt_covD`).
4. **The parallel frame and Raychaudhuri's premise** (`hasDerivAt_matrix_of_entries`,
   `frame_deviation`, `families_frame_deviation`, `families_raychaudhuri`). With matrices in
   Mathlib's `linftyOp` norm (the owner's local instances): if `E′ = −AE`, `E` is invertible, `X′`
   is the rate of `X` and `Y′` that of `X′ + AX` with `Y′ + A(X′ + AX) = −MX`, then `J = E⁻¹X` has
   `J′ = E⁻¹(X′ + AX)` and `J″ = −(E⁻¹ME)J`. For `n` families of geodesics sharing one base geodesic
   at `s`, with `X` the matrix whose `i`-th column is the `i`-th deviation and a parallel frame `E`
   along the base (`D_τE_i = 0`), the frame components meet the owner's premise
   `HasDerivAt J (J′ τ) τ`, `HasDerivAt J′ (−(R τ * J τ)) τ` with `R(τ) = 𝓡(τ)`, and where `J(τ)` is
   invertible the owner's `raychaudhuri` gives the expansion's rate.
5. **Witnesses** (`hasConnectionJetAt_const`, `riemannOf_zero`, `lines_family`, `lines_deviation`;
   `constΓ`, `constΓ_symm`, `constΓ_tidal`, `constΓ_curved`, `coordFamily`, `constΓ_geodesic`,
   `constΓ_connectionAlong`, `constΓ_deviation`, `constFrame`, `constFrame_rate`, `constFrame_det`,
   `constFrame_parallel`, `constFrame_tidal`, `cols_single`, `constΓ_frame`, `constΓ_raychaudhuri`;
   `sphereF`, `sphereF'`, `sphereΓ`, `sphereJet`, `sphereMetricJet`, `hasDerivAt_sphereMetric`,
   `sphere_christoffel`, `sphereF_symm`, `hasDerivAt_cot`, `hasDerivAt_sphereF`, `sphere_jet`,
   `sphere_geodesic`, `sphere_deviation`). Flat: `Γ = 0`, the lines `x(τ, s) = a(s) + τ·b(s)` (with
   `a`, `b` differentiable) are a geodesic family with `ξ″ = 0` and `R = 0`. The constant connection
   on the plane with `Γ^1_01 = Γ^1_10 = k` (its jet zero): `R^1_010 = −k²`, so it is curved for
   `k ≠ 0`; along the coordinate geodesic `x(τ, s) = τe₀ + se_i`, the deviation `e₁` has
   `D_τ²e₁ = k²e₁` and `−R(e₁, e₀)e₀ = k²e₁`, both computed; the frame `diag(1, e^(−kτ))` is parallel,
   its tidal matrix is `diag(0, −k²)`, and the two families meet the owner's premise and
   Raychaudhuri's equation. The round sphere `dθ² + sin²θ dφ²`: its coefficients
   `Γ^θ_φφ = −sinθ cosθ`, `Γ^φ_θφ = Γ^φ_φθ = cosθ/sinθ` are the owner's `christoffel` of the 2-jet
   `(diag(1, sin²θ), ∂_θ diag(1, sin²θ))`, the metric's rate read by Mathlib's derivatives; their
   jet is read by Mathlib's derivatives at `sinθ ≠ 0`; the meridians `θ = τ`, `φ = s` are a
   geodesic family with `D_τξ = (cosτ/sinτ)e₁`, and `D_τ²ξ = −e₁ = −R(ξ, u)u`, both computed: unit
   curvature (in the metric `|ξ| = sin τ`, the `J = sin τ` of atlas `coupling.deviation-focus`; that
   norm is read, not derived here).

What is not claimed. The existence of geodesics and of a parallel frame is a hypothesis: no
ordinary differential equation is solved. A family is given by its partial derivatives at a point,
with the agreement of mixed partials built into the shared `w` and `β`; it is not derived from a
`C³` family by Schwarz's theorem, and a family whose data hold at every point gives the hypotheses
at each point. No metric enters the derivation: metric compatibility, the symmetries of `R` beyond
`R^a_bcd = −R^a_bdc`, and the symmetry of the frame's tidal matrix `𝓡` (which the owner's
`rotation_law` asks) are not derived; the matrix `J` carries all `n` frame directions, the
geodesic's own included (`R(u, u)u = 0` empties that column), and the reduction to the screen
orthogonal to a timelike `u` with `⟨u, u⟩ = −1` is not made. The derivation holds for any
torsion-free connection, the Levi-Civita connection of a Lorentzian metric among them, but no
Lorentzian instance is built here (`FriedmannFluid` holds the comoving one). Coordinates are those
of `ℝⁿ`: no manifold, no change of coordinates. Conjugate points, the Morse index and the sphere's
focus at the antipode (as an instance of `caustic_of_deviation`) are not stated; the constant
connection is not claimed to be a metric's; the sphere's coefficients and jet are read where
`sinθ ≠ 0`, where the chart is regular. Another sign convention flips the sign of `R`.

Read on the Swing. Free fall is the geodesic and gravity the connection (the Swing record §5.6):
`D_τu = 0` is free fall, the parabolic move (a shear: inertia alone, between grips), read through
the connection's transport. Two
neighbouring free falls part by the curvature: the deviation's second covariant rate is the
commutator of the two transports around the family's cell, `R(u, ξ)u` (atlas
`cell.connection-route-return`: two routes return their curvature), once torsion-freeness has closed
the cell (`D_τξ = D_su`). A parallel frame removes the transport and leaves the stiffness alone,
`J″ = −𝓡J`, the oscillator of atlas `coupling.deviation-focus`: the sphere's unit curvature
(`D_τ²ξ = −ξ`) pulls the pair back toward each other, and the constant connection's `−k²` pushes it
apart.

The computational object is the helical pair interaction read on a family of geodesics: two
neighbouring strands are a pair, the deviation `ξ` is the pair's displacement, and the tidal matrix
`R(·, u)u` is its constitution, the stiffness that the connection's jet builds along the strand. Of
the winding guide's six general objects this touches the pair (the deviation between neighbouring
geodesics), the cell holonomy (`D_τD_s − D_sD_τ` around the family's coordinate cell returns
`R(u, ξ)u`), the tube (the base geodesic along its clock, with the parallel frame carried along it
into `Raychaudhuri`'s congruence) and faces and placement (the frame components `E⁻¹ξ`, the frame's
tidal matrix `𝓡` and the observer `e₀`'s tide); the helix and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.Spacetime.GeodesicDeviation

open Matrix Filter Topology
open Holonics.Physics.Spacetime.Raychaudhuri Holonics.Physics.Spacetime.CurvatureJets

variable {n : ℕ}

/-! ## 1. A connection, its form and its curvature -/

/-- [definition] A connection's coefficients at a point: `G a b c = Γ^a_bc`. -/
abbrev Coeff (n : ℕ) := Fin n → Fin n → Fin n → ℝ

/-- [definition] Their first jet at a point: `dG e a b c = ∂_eΓ^a_bc`. -/
abbrev CoeffJet (n : ℕ) := Fin n → Fin n → Fin n → Fin n → ℝ

/-- [definition] **The Riemann tensor of a connection**
`R^a_bcd = ∂_cΓ^a_db − ∂_dΓ^a_cb + Γ^a_ce Γ^e_db − Γ^a_de Γ^e_cb`, the owner's formula. -/
def riemannOf (G : Coeff n) (dG : CoeffJet n) : Tensor4 n :=
  fun a b c d => dG c a d b - dG d a c b + ∑ e, (G a c e * G e d b - G a d e * G e c b)

/-- [proved-standard; formal-checked] **The owner's curvature is the connection's**:
`riemann g dg ddg = riemannOf Γ ∂Γ` for the Christoffel symbols of the 2-jet. -/
theorem riemann_eq_riemannOf (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (ddg : SecondJet n) :
    riemann g dg ddg = riemannOf (christoffel g dg) (christoffelJet g dg ddg) := rfl

/-- [definition] **The connection's form** `Γ(v, V)^a = Γ^a_bc v^b V^c`. -/
def gammaForm (G : Coeff n) (v V : Fin n → ℝ) : Fin n → ℝ :=
  fun a => ∑ b, ∑ c, G a b c * v b * V c

/-- [definition] **The coefficients' rate along `z`**: `(∂_zΓ)^a_bc = Σ_e ∂_eΓ^a_bc z^e`. -/
def rateAlong (dG : CoeffJet n) (z : Fin n → ℝ) : Coeff n :=
  fun a b c => ∑ e, dG e a b c * z e

/-- [definition] **The covariant derivative** along a velocity `v` of a field `V` with rate `V′`:
`D V = V′ + Γ(v, V)`. -/
def covD (G : Coeff n) (v V V' : Fin n → ℝ) : Fin n → ℝ := V' + gammaForm G v V

/-- [definition] **A connection's first jet at `p`**: each coefficient has the derivative
`Σ_e ∂_eΓ^a_bc dx^e` there. -/
def HasConnectionJetAt (Γ : (Fin n → ℝ) → Coeff n) (dG : CoeffJet n) (p : Fin n → ℝ) : Prop :=
  ∀ a b c, HasFDerivAt (fun y => Γ y a b c)
    (∑ e, dG e a b c • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) e) p

/-- [definition] **The curvature operator**
`R(X, Y)V = (∂_XΓ)(Y, V) − (∂_YΓ)(X, V) + Γ(X, Γ(Y, V)) − Γ(Y, Γ(X, V))`. -/
def curvature (G : Coeff n) (dG : CoeffJet n) (X Y V : Fin n → ℝ) : Fin n → ℝ :=
  gammaForm (rateAlong dG X) Y V - gammaForm (rateAlong dG Y) X V + gammaForm G X (gammaForm G Y V)
    - gammaForm G Y (gammaForm G X V)

/-- [proved-standard; formal-checked] The form is additive in its second slot. -/
theorem gammaForm_add_right (G : Coeff n) (v V W : Fin n → ℝ) :
    gammaForm G v (V + W) = gammaForm G v V + gammaForm G v W := by
  funext a
  simp only [gammaForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- [proved-standard; formal-checked] The form vanishes on a zero second slot. -/
theorem gammaForm_zero_right (G : Coeff n) (v : Fin n → ℝ) : gammaForm G v 0 = 0 := by
  funext a
  simp [gammaForm]

/-- [proved-standard; formal-checked] **A torsion-free form is symmetric**: `Γ(v, V) = Γ(V, v)`. -/
theorem gammaForm_comm {G : Coeff n} (hG : ∀ a b c, G a b c = G a c b) (v V : Fin n → ℝ) :
    gammaForm G v V = gammaForm G V v := by
  funext a
  simp only [gammaForm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [hG a c b]
  ring

/-- [proved-standard; formal-checked] **Torsion-freeness closes the cell**: `D_τξ = D_su` at a point,
`ξ′ + Γ(u, ξ) = ξ′ + Γ(ξ, u)`. -/
theorem covD_symm {G : Coeff n} (hG : ∀ a b c, G a b c = G a c b) (v V V' : Fin n → ℝ) :
    covD G v V V' = covD G V v V' := by
  rw [covD, covD, gammaForm_comm hG]

section Index

variable (G : Coeff n) (dG : CoeffJet n) (X Y V : Fin n → ℝ) (a : Fin n)

/-- [proved-standard; formal-checked] The jet term `(∂_XΓ)(Y, V)^a = Σ ∂_cΓ^a_db V^b X^c Y^d`. -/
theorem jetForm_apply :
    gammaForm (rateAlong dG X) Y V a = ∑ b, ∑ c, ∑ d, dG c a d b * V b * X c * Y d := by
  simp only [gammaForm, rateAlong, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

/-- [proved-standard; formal-checked] The jet term `(∂_YΓ)(X, V)^a = Σ ∂_dΓ^a_cb V^b X^c Y^d`. -/
theorem jetForm_apply_swap :
    gammaForm (rateAlong dG Y) X V a = ∑ b, ∑ c, ∑ d, dG d a c b * V b * X c * Y d := by
  simp only [gammaForm, rateAlong, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

/-- [proved-standard; formal-checked] The square term `Γ(X, Γ(Y, V))^a = Σ Γ^a_ce Γ^e_db V^b X^c Y^d`. -/
theorem squareForm_apply :
    gammaForm G X (gammaForm G Y V) a = ∑ b, ∑ c, ∑ d, ∑ e, G a c e * G e d b * V b * X c * Y d := by
  simp only [gammaForm, Finset.mul_sum]
  conv_lhs => enter [2, x, 2, k]; rw [Finset.sum_comm]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
  ring

/-- [proved-standard; formal-checked] The square term `Γ(Y, Γ(X, V))^a = Σ Γ^a_de Γ^e_cb V^b X^c Y^d`. -/
theorem squareForm_apply_swap :
    gammaForm G Y (gammaForm G X V) a = ∑ b, ∑ c, ∑ d, ∑ e, G a d e * G e c b * V b * X c * Y d := by
  rw [squareForm_apply G Y X V a]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
  ring

/-- [proved-standard; formal-checked] **The curvature operator's components**:
`R(X, Y)V^a = R^a_bcd V^b X^c Y^d`. -/
theorem curvature_apply :
    curvature G dG X Y V a = ∑ b, ∑ c, ∑ d, riemannOf G dG a b c d * V b * X c * Y d := by
  simp only [curvature, Pi.add_apply, Pi.sub_apply]
  rw [jetForm_apply, jetForm_apply_swap, squareForm_apply, squareForm_apply_swap]
  simp only [riemannOf, add_mul, sub_mul, Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- [proved-standard; formal-checked] The owner's formula is antisymmetric in its last pair. -/
theorem riemannOf_anti (b c d : Fin n) : riemannOf G dG a b c d = -riemannOf G dG a b d c := by
  have h : ∑ e, (G a c e * G e d b - G a d e * G e c b)
      = -∑ e, (G a d e * G e c b - G a c e * G e d b) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  simp only [riemannOf, h]
  ring

/-- [proved-standard; formal-checked] **The deviation's side**:
`R(u, ξ)u^a = −R^a_bcd u^b ξ^c u^d`. -/
theorem curvature_deviation (u ξ : Fin n → ℝ) :
    curvature G dG u ξ u a = -∑ b, ∑ c, ∑ d, riemannOf G dG a b c d * u b * ξ c * u d := by
  rw [curvature_apply]
  conv_rhs => enter [1, 2, b]; rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [riemannOf_anti G dG a b d c]
  ring

end Index

/-! ## 2. The tidal matrix and the owner's tide -/

/-- [definition] **The tidal matrix** `(R(·, u)u)^a_c = R^a_bcd u^b u^d`. -/
def tidal (R : Tensor4 n) (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a c => ∑ b, ∑ d, R a b c d * u b * u d

/-- [proved-standard; formal-checked] `(R(·, u)u)ξ^a = R^a_bcd u^b ξ^c u^d`. -/
theorem tidal_mulVec (R : Tensor4 n) (u ξ : Fin n → ℝ) (a : Fin n) :
    (tidal R u).mulVec ξ a = ∑ b, ∑ c, ∑ d, R a b c d * u b * ξ c * u d := by
  simp only [mulVec, dotProduct, tidal, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  ring

/-- [proved-standard; formal-checked] **The tangent has no tide**: `R(u, u)u = 0`. -/
theorem tidal_mulVec_self (G : Coeff n) (dG : CoeffJet n) (u : Fin n → ℝ) :
    (tidal (riemannOf G dG) u).mulVec u = 0 := by
  funext a
  have h := curvature_deviation G dG a u u
  have h0 : curvature G dG u u u a = 0 := by simp [curvature]
  rw [tidal_mulVec, Pi.zero_apply]
  linarith

/-- [proved-standard; formal-checked] At the observer `e_k`, the tidal matrix is `R^a_kck`. -/
theorem tidal_single (R : Tensor4 n) (k a c : Fin n) : tidal R (Pi.single k 1) a c = R a k c k := by
  simp [tidal, Pi.single_apply]

/-- [proved-standard; formal-checked] **The observer `e₀` reads the owner's tide** on the spatial
indices: `R^(i+1)_0(j+1)0 = tide R i j`. -/
theorem tidal_observer (R : Tensor4 4) (i j : Fin 3) :
    tidal R (Pi.single 0 1) i.succ j.succ = tide R i j := by
  rw [tidal_single]
  rfl

/-- [proved-standard; formal-checked] **At `g = η` the owner's lowered tide is the tidal matrix** of
the raised tensor: `tide (riemannLower η dg ddg) i j = R^(i+1)_0(j+1)0`. -/
theorem tide_eq_tidal (dg : FirstJet 4) (ddg : SecondJet 4) (i j : Fin 3) :
    tide (riemannLower minkowski dg ddg) i j
      = tidal (riemann minkowski dg ddg) (Pi.single 0 1) i.succ j.succ := by
  rw [tidal_single]
  have h : minkowskiSign i.succ = 1 := by fin_cases i <;> rfl
  simp [tide, riemannLower, minkowski, diagonal_apply, h]

/-- [definition] **The connection's matrix along `v`**: `A(v) = (Γ^a_bc v^b)_(ac)`. -/
def connectionAlong (G : Coeff n) (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a c => ∑ b, G a b c * v b

/-- [proved-standard; formal-checked] `A(v)V = Γ(v, V)`. -/
theorem connectionAlong_mulVec (G : Coeff n) (v V : Fin n → ℝ) :
    (connectionAlong G v).mulVec V = gammaForm G v V := by
  funext a
  simp only [mulVec, dotProduct, connectionAlong, of_apply, gammaForm, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- [proved-standard; formal-checked] **`A(v)` is `Σ_c v^c A_c`** of the owner's `connection`. -/
theorem connectionAlong_christoffel (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (v : Fin n → ℝ) :
    connectionAlong (christoffel g dg) v = ∑ c, v c • connection g dg c := by
  ext a b
  simp [connectionAlong, connection, Matrix.sum_apply, mul_comm]

/-- [proved-standard; formal-checked] The `i`-th column of `X′ + A(v)X` is `D` of the `i`-th
column. -/
theorem covD_col (G : Coeff n) (v : Fin n → ℝ) (X X' : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (fun a => (X' + connectionAlong G v * X) a i) = covD G v (fun a => X a i) (fun a => X' a i) := by
  rw [covD, ← connectionAlong_mulVec]
  rfl

/-! ## 3. The calculus along a curve -/

/-- [proved-standard; formal-checked] **The form's rate along a curve**:
`(Γ(x)(v, V))′ = (∂_{x′}Γ)(v, V) + Γ(v′, V) + Γ(v, V′)`. -/
theorem hasDerivAt_gammaForm {Γ : (Fin n → ℝ) → Coeff n} {dG : CoeffJet n} {p v V : ℝ → Fin n → ℝ}
    {p' v' V' : Fin n → ℝ} {t : ℝ} (hΓ : HasConnectionJetAt Γ dG (p t)) (hp : HasDerivAt p p' t)
    (hv : HasDerivAt v v' t) (hV : HasDerivAt V V' t) :
    HasDerivAt (fun s => gammaForm (Γ (p s)) (v s) (V s))
      (gammaForm (rateAlong dG p') (v t) (V t) + gammaForm (Γ (p t)) v' (V t)
        + gammaForm (Γ (p t)) (v t) V') t := by
  rw [hasDerivAt_pi]
  intro a
  have hG : ∀ b c, HasDerivAt (fun s => Γ (p s) a b c) (rateAlong dG p' a b c) t := by
    intro b c
    refine ((hΓ a b c).comp_hasDerivAt t hp).congr_deriv ?_
    simp [rateAlong]
  have hv' := hasDerivAt_pi.mp hv
  have hV' := hasDerivAt_pi.mp hV
  have hs := HasDerivAt.fun_sum (u := Finset.univ) fun b _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun c _ => ((hG b c).mul (hv' b)).mul (hV' c)
  refine hs.congr_deriv ?_
  simp only [gammaForm, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [Pi.mul_apply]
  ring

/-- [proved-standard; formal-checked] **The rate of a covariant derivative along a curve.** -/
theorem hasDerivAt_covD {Γ : (Fin n → ℝ) → Coeff n} {dG : CoeffJet n} {p v V W : ℝ → Fin n → ℝ}
    {p' v' V' W' : Fin n → ℝ} {t : ℝ} (hΓ : HasConnectionJetAt Γ dG (p t)) (hp : HasDerivAt p p' t)
    (hv : HasDerivAt v v' t) (hV : HasDerivAt V V' t) (hW : HasDerivAt W W' t) :
    HasDerivAt (fun s => covD (Γ (p s)) (v s) (V s) (W s))
      (W' + (gammaForm (rateAlong dG p') (v t) (V t) + gammaForm (Γ (p t)) v' (V t)
        + gammaForm (Γ (p t)) (v t) V')) t :=
  hW.add (hasDerivAt_gammaForm hΓ hp hv hV)

/-! ## 4. The deviation equation along a general geodesic -/

/-- [definition] **A family `x(τ, s)` at a point**, by its partials: `u = ∂_τx`, `ξ = ∂_sx`,
`w = ∂_su = ∂_τξ`, `α = ∂_τu`, `β = ∂_sα = ∂_τw`. -/
structure FamilyAt (x u ξ w α β : ℝ → ℝ → Fin n → ℝ) (τ s : ℝ) : Prop where
  dx_τ : HasDerivAt (fun t => x t s) (u τ s) τ
  dx_s : HasDerivAt (fun r => x τ r) (ξ τ s) s
  du_τ : HasDerivAt (fun t => u t s) (α τ s) τ
  du_s : HasDerivAt (fun r => u τ r) (w τ s) s
  dξ_τ : HasDerivAt (fun t => ξ t s) (w τ s) τ
  dα_s : HasDerivAt (fun r => α τ r) (β τ s) s
  dw_τ : HasDerivAt (fun t => w t s) (β τ s) τ

/-- [proved-standard; formal-checked] **The commutator of the two transports** around the family's
cell: `D_τD_su − D_sD_τu = R(u, ξ)u`, for any connection. -/
theorem covD_commutator {Γ : (Fin n → ℝ) → Coeff n} {dG : CoeffJet n}
    {x u ξ w α β : ℝ → ℝ → Fin n → ℝ} {τ s : ℝ} (hΓ : HasConnectionJetAt Γ dG (x τ s))
    (hF : FamilyAt x u ξ w α β τ s) {Z₁ Z₂ : Fin n → ℝ}
    (h₁ : HasDerivAt (fun t => covD (Γ (x t s)) (ξ t s) (u t s) (w t s)) Z₁ τ)
    (h₂ : HasDerivAt (fun r => covD (Γ (x τ r)) (u τ r) (u τ r) (α τ r)) Z₂ s) :
    covD (Γ (x τ s)) (u τ s) (covD (Γ (x τ s)) (ξ τ s) (u τ s) (w τ s)) Z₁
      - covD (Γ (x τ s)) (ξ τ s) (covD (Γ (x τ s)) (u τ s) (u τ s) (α τ s)) Z₂
      = curvature (Γ (x τ s)) dG (u τ s) (ξ τ s) (u τ s) := by
  have e₁ := h₁.unique (hasDerivAt_covD (p := fun t => x t s) hΓ hF.dx_τ hF.dξ_τ hF.du_τ hF.dw_τ)
  have e₂ := h₂.unique (hasDerivAt_covD (p := fun r => x τ r) hΓ hF.dx_s hF.du_s hF.du_s hF.dα_s)
  rw [e₁, e₂]
  simp only [covD, curvature, gammaForm_add_right]
  abel

/-- [proved-standard; formal-checked] **The deviation equation along a general geodesic**:
`(D_τD_τξ)^a = −R^a_bcd u^b ξ^c u^d` for a torsion-free connection and a family of geodesics. -/
theorem deviation {Γ : (Fin n → ℝ) → Coeff n} {dG : CoeffJet n} {x u ξ w α β : ℝ → ℝ → Fin n → ℝ}
    {τ s : ℝ} (hsym : ∀ y a b c, Γ y a b c = Γ y a c b) (hΓ : HasConnectionJetAt Γ dG (x τ s))
    (hF : FamilyAt x u ξ w α β τ s)
    (hgeo : ∀ᶠ r in 𝓝 s, covD (Γ (x τ r)) (u τ r) (u τ r) (α τ r) = 0) {Z : Fin n → ℝ}
    (hZ : HasDerivAt (fun t => covD (Γ (x t s)) (u t s) (ξ t s) (w t s)) Z τ) :
    covD (Γ (x τ s)) (u τ s) (covD (Γ (x τ s)) (u τ s) (ξ τ s) (w τ s)) Z
      = fun a => -∑ b, ∑ c, ∑ d, riemannOf (Γ (x τ s)) dG a b c d * u τ s b * ξ τ s c * u τ s d := by
  have hsw : ∀ t, covD (Γ (x t s)) (u t s) (ξ t s) (w t s) = covD (Γ (x t s)) (ξ t s) (u t s) (w t s) :=
    fun t => covD_symm (hsym _) _ _ _
  have h₁ : HasDerivAt (fun t => covD (Γ (x t s)) (ξ t s) (u t s) (w t s)) Z τ := by
    simpa only [hsw] using hZ
  have h₂ : HasDerivAt (fun r => covD (Γ (x τ r)) (u τ r) (u τ r) (α τ r)) 0 s :=
    (hasDerivAt_const s (0 : Fin n → ℝ)).congr_of_eventuallyEq hgeo
  have hc := covD_commutator hΓ hF h₁ h₂
  have h0 : covD (Γ (x τ s)) (ξ τ s) 0 0 = 0 := by simp [covD, gammaForm_zero_right]
  rw [hgeo.self_of_nhds, h0, sub_zero, ← hsw τ] at hc
  rw [hc]
  funext a
  exact curvature_deviation _ _ _ _ _

/-- [proved-standard; formal-checked] **The deviation equation as a matrix**:
`D_τ²ξ = −(R(·, u)u) ξ`. -/
theorem deviation_tidal {Γ : (Fin n → ℝ) → Coeff n} {dG : CoeffJet n}
    {x u ξ w α β : ℝ → ℝ → Fin n → ℝ} {τ s : ℝ} (hsym : ∀ y a b c, Γ y a b c = Γ y a c b)
    (hΓ : HasConnectionJetAt Γ dG (x τ s)) (hF : FamilyAt x u ξ w α β τ s)
    (hgeo : ∀ᶠ r in 𝓝 s, covD (Γ (x τ r)) (u τ r) (u τ r) (α τ r) = 0) {Z : Fin n → ℝ}
    (hZ : HasDerivAt (fun t => covD (Γ (x t s)) (u t s) (ξ t s) (w t s)) Z τ) :
    covD (Γ (x τ s)) (u τ s) (covD (Γ (x τ s)) (u τ s) (ξ τ s) (w τ s)) Z
      = -(tidal (riemannOf (Γ (x τ s)) dG) (u τ s)).mulVec (ξ τ s) := by
  rw [deviation hsym hΓ hF hgeo hZ]
  funext a
  rw [Pi.neg_apply, tidal_mulVec]

/-! ## 5. The parallel frame and Raychaudhuri's premise -/

/-- [definition] The matrix whose `i`-th column is `V i`. -/
def cols (V : Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a i => V i a

/-- [definition] **The frame's tidal matrix** `𝓡 = E⁻¹ R(·, u)u E`, `𝓡_ij = (E⁻¹ R(E_j, u)u)_i`. -/
def frameTidal (E : Matrix (Fin n) (Fin n) ℝ) (G : Coeff n) (dG : CoeffJet n) (u : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  E⁻¹ * tidal (riemannOf G dG) u * E

/-- [proved-standard; formal-checked] The `n` columns of the identity are the coordinate vectors. -/
theorem cols_single : cols (fun i => (Pi.single i 1 : Fin n → ℝ)) = 1 := by
  ext a i
  simp [cols, Pi.single_apply, one_apply]

section Frame

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- [proved-standard; formal-checked] A matrix path whose entries have rates has the matrix of
those rates. -/
theorem hasDerivAt_matrix_of_entries {M : ℝ → Matrix (Fin n) (Fin n) ℝ} {M' : Matrix (Fin n) (Fin n) ℝ}
    {τ : ℝ} (h : ∀ a i, HasDerivAt (fun t => M t a i) (M' a i) τ) : HasDerivAt M M' τ := by
  have hM : M = fun t => ∑ a, ∑ i, M t a i • Matrix.single a i (1 : ℝ) := by
    funext t
    conv_lhs => rw [Matrix.matrix_eq_sum_single (M t)]
    simp [Matrix.smul_single]
  have hM' : M' = ∑ a, ∑ i, M' a i • Matrix.single a i (1 : ℝ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single M']
    simp [Matrix.smul_single]
  have hs : HasDerivAt (fun t => ∑ a, ∑ i, M t a i • Matrix.single a i (1 : ℝ))
      (∑ a, ∑ i, M' a i • Matrix.single a i (1 : ℝ)) τ :=
    HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun i _ => (h a i).smul_const _
  rw [← hM, ← hM'] at hs
  exact hs

/-- [proved-standard; formal-checked] **Frame components of a deviation**: `E′ = −AE` and
`Y′ + A(X′ + AX) = −MX` give `J = E⁻¹X` the rates `J′ = E⁻¹(X′ + AX)` and `J″ = −(E⁻¹ME)J`. -/
theorem frame_deviation {E X X' Y' A M : ℝ → Matrix (Fin n) (Fin n) ℝ} {τ : ℝ}
    (hE : HasDerivAt E (-(A τ * E τ)) τ) (hdet : IsUnit (E τ).det)
    (hX : HasDerivAt X (X' τ) τ) (hY : HasDerivAt (fun t => X' t + A t * X t) (Y' τ) τ)
    (hdev : Y' τ + A τ * (X' τ + A τ * X τ) = -(M τ * X τ)) :
    HasDerivAt (fun t => (E t)⁻¹ * X t) ((E τ)⁻¹ * (X' τ + A τ * X τ)) τ ∧
    HasDerivAt (fun t => (E t)⁻¹ * (X' t + A t * X t))
      (-((E τ)⁻¹ * M τ * E τ * ((E τ)⁻¹ * X τ))) τ := by
  have hEE : E τ * (E τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hinv : HasDerivAt (fun t => (E t)⁻¹) ((E τ)⁻¹ * A τ) τ := by
    have h := hasDerivAt_ringInverse_comp hE ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
    simp only [← Matrix.nonsing_inv_eq_ringInverse] at h
    refine h.congr_deriv ?_
    simp only [mul_neg, neg_mul, neg_neg, mul_assoc, hEE, mul_one]
  constructor
  · refine (hinv.mul hX).congr_deriv ?_
    rw [mul_add, mul_assoc]
    abel
  · refine (hinv.mul hY).congr_deriv ?_
    calc (E τ)⁻¹ * A τ * (X' τ + A τ * X τ) + (E τ)⁻¹ * Y' τ
        = (E τ)⁻¹ * (Y' τ + A τ * (X' τ + A τ * X τ)) := by simp only [mul_add, mul_assoc]; abel
      _ = -((E τ)⁻¹ * M τ * E τ * ((E τ)⁻¹ * X τ)) := by
        rw [hdev]
        simp only [mul_neg, mul_assoc, ← mul_assoc (E τ), hEE, one_mul]

/-- [proved-standard; formal-checked] **`n` families of geodesics in a parallel frame meet
Raychaudhuri's premise**: their frame components `J` obey `J″ = −𝓡J` in the owner's shape. -/
theorem families_frame_deviation {Γ : (Fin n → ℝ) → Coeff n} {dΓ : (Fin n → ℝ) → CoeffJet n}
    {x u ξ w α β : Fin n → ℝ → ℝ → Fin n → ℝ} {xb ub : ℝ → Fin n → ℝ}
    {E : ℝ → Matrix (Fin n) (Fin n) ℝ} {τ s : ℝ} (hsym : ∀ y a b c, Γ y a b c = Γ y a c b)
    (hΓ : HasConnectionJetAt Γ (dΓ (xb τ)) (xb τ))
    (hF : ∀ i, FamilyAt (x i) (u i) (ξ i) (w i) (α i) (β i) τ s)
    (hgeo : ∀ i, ∀ᶠ r in 𝓝 s, covD (Γ (x i τ r)) (u i τ r) (u i τ r) (α i τ r) = 0)
    (hxb : ∀ i t, x i t s = xb t) (hub : ∀ i t, u i t s = ub t)
    (hE : HasDerivAt E (-(connectionAlong (Γ (xb τ)) (ub τ) * E τ)) τ) (hdet : IsUnit (E τ).det) :
    HasDerivAt (fun t => (E t)⁻¹ * cols (fun i => ξ i t s))
      ((E τ)⁻¹ * (cols (fun i => w i τ s) + connectionAlong (Γ (xb τ)) (ub τ) * cols (fun i => ξ i τ s))) τ ∧
    HasDerivAt (fun t => (E t)⁻¹ * (cols (fun i => w i t s)
        + connectionAlong (Γ (xb t)) (ub t) * cols (fun i => ξ i t s)))
      (-(frameTidal (E τ) (Γ (xb τ)) (dΓ (xb τ)) (ub τ) * ((E τ)⁻¹ * cols (fun i => ξ i τ s)))) τ := by
  have hΓi : ∀ i, HasConnectionJetAt Γ (dΓ (xb τ)) (x i τ s) := fun i => by rw [hxb i τ]; exact hΓ
  have hZ : ∀ i, ∃ Z, HasDerivAt (fun t => covD (Γ (x i t s)) (u i t s) (ξ i t s) (w i t s)) Z τ :=
    fun i => ⟨_, hasDerivAt_covD (p := fun t => x i t s) (hΓi i) (hF i).dx_τ (hF i).du_τ (hF i).dξ_τ
      (hF i).dw_τ⟩
  choose Z hZ using hZ
  have hcol : ∀ i t, covD (Γ (x i t s)) (u i t s) (ξ i t s) (w i t s)
      = fun a => (cols (fun i => w i t s) + connectionAlong (Γ (xb t)) (ub t) * cols (fun i => ξ i t s)) a i := by
    intro i t
    rw [hxb i t, hub i t, covD_col]
    rfl
  refine frame_deviation (X := fun t => cols (fun i => ξ i t s)) (X' := fun t => cols (fun i => w i t s))
    (A := fun t => connectionAlong (Γ (xb t)) (ub t)) (Y' := fun _ => cols Z)
    (M := fun t => tidal (riemannOf (Γ (xb t)) (dΓ (xb t))) (ub t)) hE hdet ?_ ?_ ?_
  · exact hasDerivAt_matrix_of_entries fun a i => hasDerivAt_pi.mp (hF i).dξ_τ a
  · refine hasDerivAt_matrix_of_entries fun a i => ?_
    exact (hasDerivAt_pi.mp (hZ i) a).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => (congrFun (hcol i t) a).symm)
  · ext a i
    have hd := deviation_tidal hsym (hΓi i) (hF i) (hgeo i) (hZ i)
    rw [hxb i τ, hub i τ] at hd
    have h1 := congrFun (covD_col (Γ (xb τ)) (ub τ)
      (cols (fun i => w i τ s) + connectionAlong (Γ (xb τ)) (ub τ) * cols (fun i => ξ i τ s)) (cols Z) i) a
    rw [← hcol i τ, hxb i τ, hub i τ] at h1
    rw [h1]
    exact congrFun hd a

/-- [proved-standard; formal-checked] **Raychaudhuri's equation from a connection**: the owner's
`raychaudhuri` on the frame components of `n` families of geodesics. -/
theorem families_raychaudhuri (hn : (n : ℝ) ≠ 0) {Γ : (Fin n → ℝ) → Coeff n}
    {dΓ : (Fin n → ℝ) → CoeffJet n} {x u ξ w α β : Fin n → ℝ → ℝ → Fin n → ℝ} {xb ub : ℝ → Fin n → ℝ}
    {E : ℝ → Matrix (Fin n) (Fin n) ℝ} {τ s : ℝ} (hsym : ∀ y a b c, Γ y a b c = Γ y a c b)
    (hΓ : HasConnectionJetAt Γ (dΓ (xb τ)) (xb τ))
    (hF : ∀ i, FamilyAt (x i) (u i) (ξ i) (w i) (α i) (β i) τ s)
    (hgeo : ∀ i, ∀ᶠ r in 𝓝 s, covD (Γ (x i τ r)) (u i τ r) (u i τ r) (α i τ r) = 0)
    (hxb : ∀ i t, x i t s = xb t) (hub : ∀ i t, u i t s = ub t)
    (hE : HasDerivAt E (-(connectionAlong (Γ (xb τ)) (ub τ) * E τ)) τ) (hdet : IsUnit (E τ).det)
    (hJ : IsUnit ((E τ)⁻¹ * cols (fun i => ξ i τ s)).det) :
    HasDerivAt (fun t => expansion (deformation (fun t => (E t)⁻¹ * cols (fun i => ξ i t s))
        (fun t => (E t)⁻¹ * (cols (fun i => w i t s)
          + connectionAlong (Γ (xb t)) (ub t) * cols (fun i => ξ i t s))) t))
      (raychaudhuriRate (deformation (fun t => (E t)⁻¹ * cols (fun i => ξ i t s))
        (fun t => (E t)⁻¹ * (cols (fun i => w i t s)
          + connectionAlong (Γ (xb t)) (ub t) * cols (fun i => ξ i t s))) τ)
        (frameTidal (E τ) (Γ (xb τ)) (dΓ (xb τ)) (ub τ))) τ :=
  have h := families_frame_deviation hsym hΓ hF hgeo hxb hub hE hdet
  raychaudhuri (R := fun _ => frameTidal (E τ) (Γ (xb τ)) (dΓ (xb τ)) (ub τ)) hn h.1 h.2 hJ

end Frame

/-! ## 6. Witnesses -/

section Witnesses

/-- [proved-standard; formal-checked] A constant connection has the zero jet. -/
theorem hasConnectionJetAt_const (G : Coeff n) (p : Fin n → ℝ) : HasConnectionJetAt (fun _ => G) 0 p := by
  intro a b c
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  exact hasFDerivAt_const _ _

/-- [proved-standard; formal-checked] The flat connection has no curvature. -/
theorem riemannOf_zero : riemannOf (0 : Coeff n) 0 = 0 := by
  funext a b c d
  simp [riemannOf]

/-- [proved-standard; formal-checked] **The lines** `x(τ, s) = a(s) + τ·b(s)` are a family, with
`u = b`, `ξ = a′ + τb′`, `w = b′` and no acceleration. -/
theorem lines_family {a b a' b' : ℝ → Fin n → ℝ} (ha : ∀ s, HasDerivAt a (a' s) s)
    (hb : ∀ s, HasDerivAt b (b' s) s) (τ s : ℝ) :
    FamilyAt (fun (t : ℝ) s => a s + t • b s) (fun _ s => b s) (fun (t : ℝ) s => a' s + t • b' s)
      (fun _ s => b' s) (fun _ _ => 0) (fun _ _ => 0) τ s where
  dx_τ := (((hasDerivAt_id τ).smul_const (b s)).const_add (a s)).congr_deriv (one_smul ℝ _)
  dx_s := (ha s).add ((hb s).const_smul τ)
  du_τ := hasDerivAt_const τ (b s)
  du_s := hb s
  dξ_τ := (((hasDerivAt_id τ).smul_const (b' s)).const_add (a' s)).congr_deriv (one_smul ℝ _)
  dα_s := hasDerivAt_const s 0
  dw_τ := hasDerivAt_const τ (b' s)

/-- [proved-standard; formal-checked] **Flat witness**: the lines have `ξ′ = b′`, `ξ″ = 0`, the
deviation equation holds and `R = 0`. -/
theorem lines_deviation {a b a' b' : ℝ → Fin n → ℝ} (ha : ∀ s, HasDerivAt a (a' s) s)
    (hb : ∀ s, HasDerivAt b (b' s) s) (τ s : ℝ) :
    HasDerivAt (fun t => a' s + t • b' s) (b' s) τ ∧ HasDerivAt (fun _ : ℝ => b' s) 0 τ ∧
    covD (0 : Coeff n) (b s) (covD 0 (b s) (a' s + τ • b' s) (b' s)) 0
      = (fun c => -∑ i, ∑ j, ∑ k, riemannOf (0 : Coeff n) 0 c i j k * b s i * (a' s + τ • b' s) j * b s k) ∧
    riemannOf (0 : Coeff n) 0 = 0 := by
  refine ⟨(lines_family ha hb τ s).dξ_τ, hasDerivAt_const τ _, ?_, riemannOf_zero⟩
  have hZ : HasDerivAt (fun t => covD (0 : Coeff n) (b s) (a' s + t • b' s) (b' s)) 0 τ := by
    have h : ∀ t : ℝ, covD (0 : Coeff n) (b s) (a' s + t • b' s) (b' s) = b' s := fun t => by
      funext c
      simp [covD, gammaForm]
    simp only [h]
    exact hasDerivAt_const τ _
  exact deviation (Γ := fun _ => 0) (fun _ _ _ _ => rfl) (hasConnectionJetAt_const 0 _)
    (lines_family ha hb τ s) (Filter.Eventually.of_forall fun r => by funext c; simp [covD, gammaForm]) hZ

/-- [definition] **The constant connection** on the plane with `Γ^1_01 = Γ^1_10 = k`. -/
def constΓ (k : ℝ) : Coeff 2 := fun a b c => if a = 1 ∧ b ≠ c then k else 0

/-- [proved-standard; formal-checked] It is torsion-free. -/
theorem constΓ_symm (k : ℝ) (a b c : Fin 2) : constΓ k a b c = constΓ k a c b := by
  simp only [constΓ, ne_comm]

/-- [proved-standard; formal-checked] Its tidal matrix along `e₀` is `diag(0, −k²)`. -/
theorem constΓ_tidal (k : ℝ) :
    tidal (riemannOf (constΓ k) 0) (Pi.single 0 1) = diagonal ![0, -k ^ 2] := by
  ext a c
  rw [tidal_single]
  fin_cases a <;> fin_cases c <;> simp [riemannOf, constΓ, sq]

/-- [proved-standard; formal-checked] **It is curved**: `R^1_010 = −k²`. -/
theorem constΓ_curved (k : ℝ) : riemannOf (constΓ k) 0 1 0 1 0 = -k ^ 2 := by
  simp [riemannOf, constΓ, sq]

/-- [proved-standard; formal-checked] **The coordinate family** `x(τ, s) = τe₀ + se_i`: `u = e₀`,
`ξ = e_i`, no rates. -/
theorem coordFamily (i : Fin 2) (τ s : ℝ) :
    FamilyAt (fun (t : ℝ) s => t • (Pi.single 0 1 : Fin 2 → ℝ) + s • Pi.single i 1)
      (fun _ _ => Pi.single 0 1) (fun _ _ => Pi.single i 1) (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ => 0) τ s where
  dx_τ := (((hasDerivAt_id τ).smul_const _).add_const _).congr_deriv (one_smul ℝ _)
  dx_s := (((hasDerivAt_id s).smul_const _).const_add _).congr_deriv (one_smul ℝ _)
  du_τ := hasDerivAt_const τ _
  du_s := hasDerivAt_const s _
  dξ_τ := hasDerivAt_const τ _
  dα_s := hasDerivAt_const s _
  dw_τ := hasDerivAt_const τ _

/-- [proved-standard; formal-checked] The line along `e₀` is a geodesic of the constant connection. -/
theorem constΓ_geodesic (k : ℝ) : covD (constΓ k) (Pi.single 0 1) (Pi.single 0 1) 0 = 0 := by
  funext a
  simp [covD, gammaForm, constΓ, Pi.single_apply]

/-- [proved-standard; formal-checked] Its matrix along `e₀` is `diag(0, k)`. -/
theorem constΓ_connectionAlong (k : ℝ) : connectionAlong (constΓ k) (Pi.single 0 1) = diagonal ![0, k] := by
  ext a c
  fin_cases a <;> fin_cases c <;> simp [connectionAlong, constΓ, Pi.single_apply]

/-- [proved-standard; formal-checked] **Curved witness, both sides computed**: along `e₀`, the
deviation `e₁` has `D_τ²e₁ = k²e₁ = −R(e₁, e₀)e₀`. -/
theorem constΓ_deviation (k τ s : ℝ) :
    HasDerivAt (fun _ : ℝ => covD (constΓ k) (Pi.single 0 1) (Pi.single 1 1) 0) 0 τ ∧
    covD (constΓ k) (Pi.single 0 1) (covD (constΓ k) (Pi.single 0 1) (Pi.single 1 1) 0) 0
      = k ^ 2 • (Pi.single 1 1 : Fin 2 → ℝ) ∧
    -(tidal (riemannOf (constΓ k) 0) (Pi.single 0 1)).mulVec (Pi.single 1 1)
      = k ^ 2 • (Pi.single 1 1 : Fin 2 → ℝ) ∧
    covD (constΓ k) (Pi.single 0 1) (covD (constΓ k) (Pi.single 0 1) (Pi.single 1 1) 0) 0
      = -(tidal (riemannOf (constΓ k) 0) (Pi.single 0 1)).mulVec (Pi.single 1 1) := by
  have hZ : HasDerivAt (fun _ : ℝ => covD (constΓ k) (Pi.single 0 1) (Pi.single 1 1) 0) 0 τ :=
    hasDerivAt_const τ _
  refine ⟨hZ, ?_, ?_, ?_⟩
  · funext a
    fin_cases a <;> simp [covD, gammaForm, constΓ, Pi.single_apply, sq]
  · rw [constΓ_tidal]
    funext a
    fin_cases a <;> simp [diagonal]
  · exact deviation_tidal (Γ := fun _ => constΓ k) (fun _ => constΓ_symm k) (hasConnectionJetAt_const _ _)
      (coordFamily 1 τ s) (Filter.Eventually.of_forall fun r => constΓ_geodesic k) hZ

/-- [definition] **The parallel frame** of the constant connection along `e₀`: `diag(1, e^(−kt))`. -/
def constFrame (k t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![1, Real.exp (-(k * t))]

/-- [proved-standard; formal-checked] `−A(e₀)E = diag(0, −k e^(−kτ))`. -/
theorem constFrame_rate (k τ : ℝ) :
    -(connectionAlong (constΓ k) (Pi.single 0 1) * constFrame k τ)
      = diagonal ![0, -(k * Real.exp (-(k * τ)))] := by
  rw [constΓ_connectionAlong, constFrame, diagonal_mul_diagonal, diagonal_neg]
  congr 1
  funext a
  fin_cases a <;> simp

/-- [proved-standard; formal-checked] The frame is invertible. -/
theorem constFrame_det (k t : ℝ) : IsUnit (constFrame k t).det := by
  simp [constFrame, (Real.exp_pos _).ne']

/-- [proved-standard; formal-checked] The frame's tidal matrix is `diag(0, −k²)`. -/
theorem constFrame_tidal (k τ : ℝ) :
    frameTidal (constFrame k τ) (constΓ k) 0 (Pi.single 0 1) = diagonal ![0, -k ^ 2] := by
  have hu := constFrame_det k τ
  have hc : diagonal ![0, -k ^ 2] * constFrame k τ = constFrame k τ * diagonal ![0, -k ^ 2] := by
    simp only [constFrame, diagonal_mul_diagonal, mul_comm]
  rw [frameTidal, constΓ_tidal, mul_assoc, hc, ← mul_assoc, Matrix.nonsing_inv_mul _ hu, one_mul]

section ConstFrame

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- [proved-standard; formal-checked] **The frame is parallel**: `E′ = −A(e₀)E`. -/
theorem constFrame_parallel (k τ : ℝ) :
    HasDerivAt (constFrame k) (-(connectionAlong (constΓ k) (Pi.single 0 1) * constFrame k τ)) τ := by
  have he : HasDerivAt (fun t => Real.exp (-(k * t))) (-(k * Real.exp (-(k * τ)))) τ :=
    (((hasDerivAt_id τ).const_mul k).neg.exp).congr_deriv (by simp; ring)
  have h : HasDerivAt (constFrame k) (diagonal ![0, -(k * Real.exp (-(k * τ)))]) τ := by
    refine hasDerivAt_matrix_of_entries fun a c => ?_
    fin_cases a <;> fin_cases c <;> simp [constFrame, diagonal, he] <;> exact hasDerivAt_const _ _
  exact h.congr_deriv (constFrame_rate k τ).symm

/-- [proved-standard; formal-checked] **The constant connection meets Raychaudhuri's premise**: the
two coordinate families in the parallel frame obey `J″ = −diag(0, −k²)J`. -/
theorem constΓ_frame (k τ : ℝ) :
    HasDerivAt (fun t => (constFrame k t)⁻¹ * cols (fun i => (Pi.single i 1 : Fin 2 → ℝ)))
      ((constFrame k τ)⁻¹ * (cols (fun _ => 0) + connectionAlong (constΓ k) (Pi.single 0 1)
        * cols (fun i => (Pi.single i 1 : Fin 2 → ℝ)))) τ ∧
    HasDerivAt (fun t => (constFrame k t)⁻¹ * (cols (fun _ => 0) + connectionAlong (constΓ k) (Pi.single 0 1)
        * cols (fun i => (Pi.single i 1 : Fin 2 → ℝ))))
      (-(diagonal ![0, -k ^ 2] * ((constFrame k τ)⁻¹ * cols (fun i => (Pi.single i 1 : Fin 2 → ℝ))))) τ := by
  have h := families_frame_deviation (Γ := fun _ => constΓ k) (dΓ := fun _ => 0)
    (x := fun i (t : ℝ) s => t • (Pi.single 0 1 : Fin 2 → ℝ) + s • Pi.single i 1)
    (u := fun _ _ _ => Pi.single 0 1) (ξ := fun i _ _ => Pi.single i 1) (w := fun _ _ _ => 0)
    (α := fun _ _ _ => 0) (β := fun _ _ _ => 0) (xb := fun t => t • Pi.single 0 1)
    (ub := fun _ => Pi.single 0 1) (s := 0) (fun _ => constΓ_symm k) (hasConnectionJetAt_const _ _)
    (fun i => coordFamily i τ 0) (fun _ => Filter.Eventually.of_forall fun _ => constΓ_geodesic k)
    (fun _ _ => by simp) (fun _ _ => rfl) (constFrame_parallel k τ) (constFrame_det k τ)
  rw [constFrame_tidal] at h
  exact h

/-- [proved-standard; formal-checked] **Raychaudhuri's equation on the constant connection**, at the
frame's tidal matrix `diag(0, −k²)`. -/
theorem constΓ_raychaudhuri (k τ : ℝ) :
    HasDerivAt (fun t => expansion (deformation
        (fun t => (constFrame k t)⁻¹ * cols (fun i => (Pi.single i 1 : Fin 2 → ℝ)))
        (fun t => (constFrame k t)⁻¹ * (cols (fun _ => 0) + connectionAlong (constΓ k) (Pi.single 0 1)
          * cols (fun i => (Pi.single i 1 : Fin 2 → ℝ)))) t))
      (raychaudhuriRate (deformation
        (fun t => (constFrame k t)⁻¹ * cols (fun i => (Pi.single i 1 : Fin 2 → ℝ)))
        (fun t => (constFrame k t)⁻¹ * (cols (fun _ => 0) + connectionAlong (constΓ k) (Pi.single 0 1)
          * cols (fun i => (Pi.single i 1 : Fin 2 → ℝ)))) τ) (diagonal ![0, -k ^ 2])) τ := by
  have h := constΓ_frame k τ
  have hJ : IsUnit ((constFrame k τ)⁻¹ * cols (fun i => (Pi.single i 1 : Fin 2 → ℝ))).det := by
    rw [cols_single, mul_one]
    exact isUnit_nonsing_inv_det _ (constFrame_det k τ)
  exact raychaudhuri (R := fun _ => diagonal ![0, -k ^ 2]) (by norm_num) h.1 h.2 hJ

end ConstFrame

section Sphere

/-- [definition] **The round sphere's coefficients** in `(θ, φ)`, as functions of `θ`:
`Γ^θ_φφ = −sinθ cosθ`, `Γ^φ_θφ = Γ^φ_φθ = cosθ/sinθ`. -/
def sphereF (θ : ℝ) : Coeff 2 :=
  ![![![0, 0], ![0, -(Real.sin θ * Real.cos θ)]],
    ![![0, Real.cos θ / Real.sin θ], ![Real.cos θ / Real.sin θ, 0]]]

/-- [definition] Their rates in `θ`. -/
def sphereF' (θ : ℝ) : Coeff 2 :=
  ![![![0, 0], ![0, Real.sin θ ^ 2 - Real.cos θ ^ 2]], ![![0, -(Real.sin θ ^ 2)⁻¹], ![-(Real.sin θ ^ 2)⁻¹, 0]]]

/-- [definition] The sphere's connection on the chart. -/
def sphereΓ (p : Fin 2 → ℝ) : Coeff 2 := sphereF (p 0)

/-- [definition] Its first jet: the rates in `θ`, none in `φ`. -/
def sphereJet (p : Fin 2 → ℝ) : CoeffJet 2 := fun e => if e = 0 then sphereF' (p 0) else 0

/-- [definition] The metric's first jet at `θ`: `∂_θ diag(1, sin²θ) = diag(0, 2 sinθ cosθ)`. -/
def sphereMetricJet (θ : ℝ) : FirstJet 2 :=
  fun e => if e = 0 then diagonal ![0, 2 * Real.sin θ * Real.cos θ] else 0

/-- [proved-standard; formal-checked] The metric `diag(1, sin²θ)` has the rate `sphereMetricJet` in
`θ`, entry by entry. -/
theorem hasDerivAt_sphereMetric (θ : ℝ) (a b : Fin 2) :
    HasDerivAt (fun t => diagonal ![1, Real.sin t ^ 2] a b) (sphereMetricJet θ 0 a b) θ := by
  have h : HasDerivAt (fun t => Real.sin t ^ 2) (2 * Real.sin θ * Real.cos θ) θ :=
    ((Real.hasDerivAt_sin θ).pow 2).congr_deriv (by ring)
  fin_cases a <;> fin_cases b <;> simp [sphereMetricJet, diagonal, h] <;> exact hasDerivAt_const _ _

/-- [proved-standard; formal-checked] **They are the owner's Christoffel symbols** of the round
metric's 2-jet `(diag(1, sin²θ), ∂_θ diag(1, sin²θ))`. -/
theorem sphere_christoffel {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    christoffel (diagonal ![1, Real.sin θ ^ 2]) (sphereMetricJet θ) = sphereF θ := by
  have hinv : (diagonal ![1, Real.sin θ ^ 2])⁻¹ = diagonal ![1, (Real.sin θ ^ 2)⁻¹] := by
    refine Matrix.inv_eq_right_inv ?_
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hs]
  funext a b c
  rw [christoffel, hinv]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [sphereMetricJet, sphereF, diagonal] <;> field_simp

/-- [proved-standard; formal-checked] The sphere's connection is torsion-free. -/
theorem sphereF_symm (θ : ℝ) (a b c : Fin 2) : sphereF θ a b c = sphereF θ a c b := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

/-- [proved-standard; formal-checked] `(cos/sin)′ = −1/sin²` where `sin ≠ 0`. -/
theorem hasDerivAt_cot {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    HasDerivAt (fun t => Real.cos t / Real.sin t) (-(Real.sin θ ^ 2)⁻¹) θ := by
  refine ((Real.hasDerivAt_cos θ).div (Real.hasDerivAt_sin θ) hs).congr_deriv ?_
  field_simp
  linear_combination -Real.sin_sq_add_cos_sq θ

/-- [proved-standard; formal-checked] Each coefficient has its rate `sphereF'`. -/
theorem hasDerivAt_sphereF {θ : ℝ} (hs : Real.sin θ ≠ 0) (a b c : Fin 2) :
    HasDerivAt (fun t => sphereF t a b c) (sphereF' θ a b c) θ := by
  have h1 : HasDerivAt (fun t => -(Real.sin t * Real.cos t)) (Real.sin θ ^ 2 - Real.cos θ ^ 2) θ :=
    ((Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_cos θ)).neg.congr_deriv (by ring)
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [sphereF, sphereF', h1, hasDerivAt_cot hs] <;>
    exact hasDerivAt_const _ _

/-- [proved-standard; formal-checked] **The sphere's connection has the jet `sphereJet`** where
`sinθ ≠ 0`. -/
theorem sphere_jet {p : Fin 2 → ℝ} (hs : Real.sin (p 0) ≠ 0) : HasConnectionJetAt sphereΓ (sphereJet p) p := by
  intro a b c
  have hp : HasFDerivAt (fun y : Fin 2 → ℝ => y 0) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) p :=
    hasFDerivAt_apply 0 p
  refine ((hasDerivAt_sphereF hs a b c).hasFDerivAt.comp p hp).congr_fderiv ?_
  ext v
  simp [sphereJet, Fin.sum_univ_two, mul_comm]

/-- [proved-standard; formal-checked] **The meridians are geodesics**: `Γ(e₀, e₀) = 0`. -/
theorem sphere_geodesic (p : Fin 2 → ℝ) : covD (sphereΓ p) (Pi.single 0 1) (Pi.single 0 1) 0 = 0 := by
  funext a
  fin_cases a <;> simp [covD, gammaForm, sphereΓ, sphereF, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] **The sphere's deviation, both sides computed**: on the
meridians `θ = τ`, `φ = s`, `D_τξ = cot τ·e₁` and `D_τ²ξ = −e₁ = −R(ξ, u)u`. -/
theorem sphere_deviation (τ s : ℝ) (hs : Real.sin τ ≠ 0) :
    HasDerivAt (fun t => covD (sphereΓ (t • Pi.single 0 1 + s • Pi.single 1 1)) (Pi.single 0 1) (Pi.single 1 1) 0)
      ((-(Real.sin τ ^ 2)⁻¹) • Pi.single 1 1) τ ∧
    covD (sphereΓ (τ • Pi.single 0 1 + s • Pi.single 1 1)) (Pi.single 0 1)
        (covD (sphereΓ (τ • Pi.single 0 1 + s • Pi.single 1 1)) (Pi.single 0 1) (Pi.single 1 1) 0)
        ((-(Real.sin τ ^ 2)⁻¹) • Pi.single 1 1) = -Pi.single 1 1 ∧
    -(tidal (riemannOf (sphereΓ (τ • Pi.single 0 1 + s • Pi.single 1 1))
        (sphereJet (τ • Pi.single 0 1 + s • Pi.single 1 1))) (Pi.single 0 1)).mulVec (Pi.single 1 1)
      = -Pi.single 1 1 ∧
    covD (sphereΓ (τ • Pi.single 0 1 + s • Pi.single 1 1)) (Pi.single 0 1)
        (covD (sphereΓ (τ • Pi.single 0 1 + s • Pi.single 1 1)) (Pi.single 0 1) (Pi.single 1 1) 0)
        ((-(Real.sin τ ^ 2)⁻¹) • Pi.single 1 1)
      = -(tidal (riemannOf (sphereΓ (τ • Pi.single 0 1 + s • Pi.single 1 1))
        (sphereJet (τ • Pi.single 0 1 + s • Pi.single 1 1))) (Pi.single 0 1)).mulVec (Pi.single 1 1) := by
  have hp : ∀ t : ℝ, (t • Pi.single 0 1 + s • Pi.single 1 1 : Fin 2 → ℝ) 0 = t := fun t => by simp
  have hcot : ∀ t : ℝ, covD (sphereΓ (t • Pi.single 0 1 + s • Pi.single 1 1)) (Pi.single 0 1) (Pi.single 1 1) 0
      = (Real.cos t / Real.sin t) • Pi.single 1 1 := fun t => by
    funext a
    fin_cases a <;> simp [covD, gammaForm, sphereΓ, sphereF, Fin.sum_univ_two]
  have hZ : HasDerivAt (fun t => covD (sphereΓ (t • Pi.single 0 1 + s • Pi.single 1 1)) (Pi.single 0 1)
      (Pi.single 1 1) 0) ((-(Real.sin τ ^ 2)⁻¹) • Pi.single 1 1) τ := by
    simp only [hcot]
    exact (hasDerivAt_cot hs).smul_const _
  refine ⟨hZ, ?_, ?_, ?_⟩
  · rw [hcot]
    funext a
    fin_cases a <;> simp [covD, gammaForm, sphereΓ, sphereF, Fin.sum_univ_two]
    field_simp
    linear_combination Real.sin_sq_add_cos_sq τ
  · funext a
    rw [Pi.neg_apply, tidal_mulVec]
    fin_cases a <;> simp [riemannOf, sphereΓ, sphereJet, sphereF, sphereF', Fin.sum_univ_two, Pi.single_apply]
    field_simp
    linear_combination Real.sin_sq_add_cos_sq τ
  · exact deviation_tidal (x := fun (t : ℝ) s => t • (Pi.single 0 1 : Fin 2 → ℝ) + s • Pi.single 1 1)
      (fun y => sphereF_symm (y 0)) (sphere_jet (by rw [hp]; exact hs)) (coordFamily 1 τ s)
      (Filter.Eventually.of_forall fun r => sphere_geodesic _) hZ

end Sphere

end Witnesses

end Holonics.Physics.Spacetime.GeodesicDeviation

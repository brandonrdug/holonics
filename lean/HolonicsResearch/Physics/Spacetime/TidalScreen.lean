import HolonicsResearch.Physics.Spacetime.GeodesicDeviation
import HolonicsResearch.Physics.Spacetime.Raychaudhuri
import HolonicsResearch.Physics.Spacetime.FriedmannFluid
import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-!
# The tidal screen: metric compatibility makes the tide self-adjoint, and free fall deviates on the screen

[definition] The box of #410, "Curvature's strain and rotation: the Weyl tensor's electric/magnetic
split and Petrov's classification; Raychaudhuri's equation from a Lorentzian metric, connection and
congruence", part done in #1024 (`Physics/Spacetime/Raychaudhuri`), #1031 (`Physics/Spacetime/PetrovTypes`),
#1032 (`Physics/Spacetime/CurvatureJets`), #1034 (`Physics/Spacetime/FriedmannFluid`) and #1037
(`Physics/Spacetime/GeodesicDeviation`), with "the screen orthogonal to a timelike velocity and the tide's
symmetry from metric compatibility" left: this module takes both, and with it the box is answered whole. The
Weyl tensor's split stands in `Raychaudhuri` §4, Petrov's classification in `PetrovTypes`, the curvature of a
metric's 2-jet in `CurvatureJets`, the deviation along a geodesic of a torsion-free connection and its parallel
frame in `GeodesicDeviation`, and here the metric's curvature symmetries, the self-adjoint tide and the screen.
Sources: `Raychaudhuri`'s "What is not claimed" ("The reduction to the screen orthogonal to a timelike `u` and
the tidal matrix's symmetry from metric compatibility are not derived, and that symmetry is assumed where it is
used") and its `deformation`, `symPart`, `rotation`, `shear`, `expansion`, `raychaudhuri`, `rotation_law`
(premise `(R τ)ᵀ = R τ`), `shear_law`; `GeodesicDeviation`'s "What is not claimed" ("No metric enters the
derivation: metric compatibility, the symmetries of `R` beyond `R^a_bcd = −R^a_bdc`, and the symmetry of the
frame's tidal matrix `𝓡` (which the owner's `rotation_law` asks) are not derived"; "the reduction to the screen
orthogonal to a timelike `u` with `⟨u, u⟩ = −1` is not made") and its `riemannOf`, `riemann_eq_riemannOf`,
`tidal`, `tidal_mulVec`, `tidal_single`, `tide_eq_tidal`, `cols`, `connectionAlong`, `frameTidal`,
`families_frame_deviation`, `families_raychaudhuri`, `sphereF`, `sphereΓ`, `sphereJet`, `sphereMetricJet`,
`sphere_christoffel`, `sphere_deviation`; `CurvatureJets`' "What is not claimed" ("The full Riemann tensor of a
2-jet whose first jet does not vanish is defined and split (`K` plus a part quadratic in the first jet), but its
symmetries, its Ricci tensor and its tide are not read here") and its `riemannLower_eq_add`, `contract_inv`,
`CurvatureSymmetries`, `linearCurvature_symmetries`, `minkowski`, `minkowski_det`, `tide`, `tide_transpose`,
`tide_eq_electric`, `tide_is_boost`; `FriedmannFluid`'s `frwMetric`, `frwFirstJet`, `frwSecondJet`,
`frwSecondJet_symm`, `frwMetric_det`, `frwFrame`, `frw_tide`; `PetrovTypes`, which reads the electric part as the
tide; the record of November 19 that answers #1037 (its file name opens
`2026-11-19_AN_L_FUNCTION_IS_A_CYCLE_MACHINE`, §2 item 3: "a metric enters only for the symmetric tide read on
the screen orthogonal to a timelike velocity, which is what stays", the matrix of `J″ = −RJ` being
`𝓡 = E⁻¹R(·, u)uE`, with which "the lowered forms agree … in an orthonormal frame"); the Swing record
(`research/records/2026-09-28_THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_A_GRIP_TURNS_A_PUSH_BOOSTS_AND_A_FREE_BODY_FALLS.md`
§5.6: "Tidal curvature is a strain field"; "A free-falling congruence focuses by strain and resists by
rotation", with `dθ/dτ = −θ²/3 − σ² + ω² − R_μν u^μ u^ν`); `Geometry/Motion` (`turn`, `boost`,
`adjointIn_eq_self_of_symm`: against a receiver's metric a rate splits into a skew turn and a self-adjoint
boost); and atlas `coupling.geodesic-deviation`, `coupling.curvature-jets`, `coupling.raychaudhuri-riccati`,
`coupling.weyl-electric-magnetic`, `coupling.congruence-kinematic-split`, `gr.flrw-fluid-bath`,
`motion.turn-boost-split`, `tube.g-self-adjoint-real-spectrum`.

Everything is over ℝ in coordinates `Fin n`, the owners' index conventions and Misner–Thorne–Wheeler's sign. A
first jet is **symmetric** where `∂_e g_ab = ∂_e g_ba` (`FirstJetSymm`). The **lowered Christoffel symbols** are
`Γ_dbc = ½(∂_b g_dc + ∂_c g_db − ∂_d g_bc)` (`christoffelLower`), so that the owner's `Γ^a_bc = g^(ad)Γ_dbc`; their
pairing through `g⁻¹` is `P(xy; zw) = Σ_q Γ_qxy Γ^q_zw` (`connectionPair`). For a tensor `R` with all indices
down the **tidal form** at `u` is `T(ξ, η) = R_abcd ξ^a u^b η^c u^d` (`tidalForm`), whose matrix is the owner's
`tidal R u`. The **screen** of `u` under `g` is `u^⊥ = {ξ | uᵀgξ = 0}`, Mathlib's orthogonal complement of `ℝu`
under the bilinear form of `g` (`screen`). With `Fin (k + 1)` and the index `0` for `u`, the **adapted sign** is
`(σ, 1, …, 1)` (`adaptedSign`), and an **adapted frame** at `u` is a matrix `E` whose first column is `u` and
with `EᵀgE = diag(σ, 1, …, 1)` (`AdaptedFrame`): `σ = −1` for a unit timelike `u` with an orthonormal basis of
its screen, `σ = 1` for a Riemannian metric. The **screen part** of a `(k + 1) × (k + 1)` matrix is its block on
the indices `1..k` (`screenPart`). The frame components of `n` deviations are `J = E⁻¹X` (`frameJ`), with rate
`E⁻¹(X′ + AX)` (`frameJ'`), as in `GeodesicDeviation`.

[proved-standard; formal-checked] What is proved.

1. **Metric compatibility gives every curvature symmetry** (`FirstJetSymm`, `christoffelLower`,
   `christoffel_eq_raise`, `christoffelLower_symm`, `christoffel_symm`, `firstJet_eq_christoffelLower`,
   `lower_christoffel`, `christoffelJet_zero`, `lower_christoffelJet`, `riemannLower_zero_eq`,
   `riemannLower_zero_eq_quadratic`, `connectionPair`, `connectionPair_exchange`, `connectionPair_swap_left`,
   `connectionPair_swap_right`, `riemannLower_zero_eq_pair`, `riemannLower_zero_symmetries`,
   `curvatureSymmetries_add`, `riemannLower_symmetries`, `firstJetSymm_of_transpose`). A symmetric first jet
   gives `Γ^a_bc = Γ^a_cb` and `∂_c g_ab = Γ_acb + Γ_bca`, metric compatibility read on the jet. At a zero second
   jet the owner's `∂Γ`, lowered, is `−Σ_q ∂_c g_aq Γ^q_db` (the inverse's rate through `contract_inv`), and
   compatibility cancels half of it against the owner's `ΓΓ` term:
   `R(g, dg, 0)_abcd = Σ_q (Γ_qda Γ^q_cb − Γ_qca Γ^q_db) = g_ef(Γ^e_bc Γ^f_ad − Γ^e_bd Γ^f_ac)`. As
   `P(da; cb) − P(ca; db)`, with `P` symmetric in each pair and, for symmetric `g`, under the exchange of the pairs,
   it has both antisymmetries, the pair exchange and the cyclic identity. With the owner's split
   `R(g, dg, ddg) = K(ddg) + R(g, dg, 0)` and `linearCurvature_symmetries`, the whole `riemannLower g dg ddg` has
   them for symmetric invertible `g`, a symmetric first jet and a second jet with `JetSymm`.
2. **The tide is self-adjoint and lives on the screen** (`tidalForm`, `tidalForm_apply`, `tidal_transpose`,
   `tidal_mulVec_self_of_symm`, `vecMul_tidal_self`, `tidalForm_symm`, `tidalForm_self_left`,
   `tidalForm_self_right`, `tidal_riemannLower`, `tidal_riemann`, `screen`, `mem_screen`,
   `dotProduct_mulVec_of_symm`, `mem_screen_iff`, `isCompl_screen`, `screen_split`, `timelike_split`,
   `tidalMap_isSymm`, `tidalMap_selfAdjoint`, `tidalMap_mulVec_self`, `tidalMap_mem_screen`, `metric_tidal`). For
   `R` with the curvature symmetries the tidal form is symmetric (the pair exchange), `T(u, ·) = 0` (the first
   antisymmetry) and `T(·, u) = 0` (the second). The owner's tidal matrix of the metric's curvature is that form
   raised, `R(·, u)u = g⁻¹T` (`tidal_riemann`), so for symmetric invertible `g` it is `g`-self-adjoint
   (`g·M = Mᵀ·g`, `⟨Mξ, η⟩_g = ⟨ξ, Mη⟩_g`), kills `u` and maps every vector into `u^⊥`. Where `uᵀgu ≠ 0`, `ℝu`
   and `u^⊥` are complements (Mathlib's `isCompl_span_singleton_orthogonal`), and a vector splits as
   `ξ = cu + (ξ − cu)` with the rest on the screen at `c = uᵀgξ/uᵀgu`; for timelike `u` (`uᵀgu < 0`) that `c` is
   the only coefficient that does so.
3. **The reduction in an adapted frame** (`adaptedSign`, `AdaptedFrame`, `screenPart`, `AdaptedFrame.col_zero`,
   `frame_entry`, `AdaptedFrame.norm`, `AdaptedFrame.mem_screen`, `adaptedSign_mul`, `AdaptedFrame.left_inv`,
   `AdaptedFrame.inv_eq`, `AdaptedFrame.det`, `frame_row_zero`, `frameTidal_eq`, `frameTidal_transpose`,
   `frameTidal_row`, `frameTidal_col`, `frameTidal_apply`, `screenPart_transpose`, `metric_frameTidal`). An
   adapted frame has `uᵀgu = σ`, its other columns on the screen, and, for `σ ≠ 0`,
   `E⁻¹ = diag(σ⁻¹, 1, …, 1)Eᵀg`. Then the owner's `frameTidal E Γ ∂Γ u = E⁻¹R(·, u)uE` of the metric's
   connection is `EᵀTE`, entry by entry `T(E_i, E_j)`, the lowered form in the frame, as the record's reading
   said: symmetric, with zero first row and column, so its screen part, the screen tide, is symmetric.
4. **The deviation on the screen** (`screenPartₗ`, `screenPart_mul`, `screen_deviation`, `screen_raychaudhuri`,
   `shear_of_symm`, `screen_shear_law`, `frameJ`, `frameJ'`, `families_tide`, `families_rotation_law`,
   `families_screen_raychaudhuri`). In Mathlib's `linftyOp` norm (the owners' local instances), where `J″ = −𝓡J`
   and `𝓡`'s first column vanishes, the screen part `J_s` obeys `J_s″ = −𝓡_s J_s` with `𝓡_s = screenPart 𝓡`;
   with `𝓡` symmetric the owner's `raychaudhuri` holds there at `n = k` (`−θ²/k`, so `−θ²/3` at `k = 3`) and so
   does `rotation_law`, whose premise `𝓡_s` symmetric is now met. The owner's `shear_law` takes no symmetry
   premise; with the symmetric tide its tidal term `shear 𝓡_s` is the trace-free screen tide
   `𝓡_s − (tr 𝓡_s/k)·1`. Joined to `GeodesicDeviation`: for `n = k + 1` families of geodesics whose connection at
   the base point is a metric's (`Γ = christoffel g dg`, `∂Γ = christoffelJet g dg ddg` there, the jets
   symmetric), in a parallel frame adapted at `τ`, the frame tide is symmetric with zero first column; so the
   owner's `families_raychaudhuri` holds with a symmetric tide and `rotation_law` holds on the whole frame, and on
   the screen the frame components meet the owner's premise with the screen tide, with Raychaudhuri's equation at
   `−θ²/k` and the rotation law.
5. **Witnesses** (`minkowskiSign_eq`, `minkowski_transpose`, `minkowski_adapted`, `minkowski_screenPart`,
   `minkowski_tide`; `frw_adapted`, `frw_screen`; `sphereSecondJet`, `hasDerivAt_sphereMetricJet`,
   `sphereMetricJet_symm`, `sphereSecondJet_symm`, `sphereMetric_det`, `sphereMetric_inv`,
   `sphere_christoffelJet`, `sphere_quadratic`, `sphere_riemannLower`, `sphere_adapted`, `sphere_tidal`,
   `sphere_frameTidal`, `sphere_screen`). Minkowski's `η` with `u = e₀` and `E = 1` is adapted with `σ = −1`, and
   for any jets the screen part of the frame tide is the owner's `tide` (through `tide_eq_tidal`); for symmetric
   jets with any first jet that tide is symmetric and is the electric part (`CurvatureJets` built the
   symmetries at a zero first jet only). The flat Friedmann–Lemaître–Robertson–Walker jet
   `g = diag(−1, A², A², A²)`, whose first jet `∂₀g = diag(0, 2AB, 2AB, 2AB)` does not vanish for `AB ≠ 0`, with
   the comoving `u = e₀` and the owner's frame `diag(1, 1/A, 1/A, 1/A)`, is adapted with `σ = −1`: its frame
   tide is symmetric and its screen tide is `−(C/A)·1`, the `−a″/a` of the comoving congruence (from the owner's
   `frw_tide`). The round sphere `dθ² + sin²θ dφ²` at `sinθ ≠ 0`: its metric's second jet in `θ`, read by
   Mathlib's derivatives from the owner's `sphereMetricJet`, gives through the owner's `christoffelJet` the
   owner's connection jet `sphereJet`; its curvature's quadratic part `R(g, dg, 0)_φθφθ = cos²θ` vanishes only on
   the equator and the whole `R_φθφθ = sin²θ`, with the curvature symmetries by item 1; the frame
   `diag(1, 1/sinθ)` is adapted with `σ = 1` at `u = e_θ`, the frame tide is `diag(0, 1)` and the screen tide
   `1`, the unit curvature of the owner's `sphere_deviation`.

[proved-derived; formal-checked]

6. **The tide is a boost at the receiver's own metric** (`tidalMap_is_boost`, `metric_tidal_is_boost`). The
   raised tidal map has `Geometry/Motion`'s turn `0` and boost itself at the metric `g`: the owner's
   `tide_is_boost`, read at the comoving metric `1` and a zero first jet, holds at any symmetric invertible `g`
   and any symmetric first jet.

What is not claimed. The null (Sachs) screen, a two-dimensional quotient of `u^⊥` for a null `u` with its
`−θ²/2`, is not stated, nor is an accelerated congruence (`D_τu ≠ 0`). The Bianchi identity's differential form
`∇R = 0` (it needs the 3-jet) is not stated: the cyclic identity here is the algebraic one. There is no manifold:
the metric and its jets live at a point and the families and frames along curves in a chart of `ℝⁿ`, as in the
owners; the symmetry of the jets (Schwarz's theorem) and the connection being the metric's at the base point are
hypotheses. The adapted frame is a hypothesis at the instant `τ`: that a parallel frame stays adapted (the
transport of a metric connection keeps `EᵀgE`, and a geodesic's tangent is parallel) is not derived, and no
parallel adapted frame is built. The signature of `g` enters only through the frame (`σ` is any nonzero number),
and that every unit timelike `u` of a Lorentzian `g` has an adapted frame (Sylvester's law of inertia) is not
stated. The screen part drops the deviations' components along `u` and a deviation along `u`; that the screen
decouples from them is what is proved (the frame tide's first row and column vanish), and the evolution of the
first row is not read. The screen tide's spectrum, its principal tidal axes, is not read (atlas
`tube.g-self-adjoint-real-spectrum` holds the real spectrum of a `G`-self-adjoint map). That a vanishing rotation
stays zero along the congruence needs uniqueness for the rotation's linear law, as in `Raychaudhuri`. The
witnesses are at a point: no family of geodesics through the sphere's or the Friedmann jet's frame is built here
(`GeodesicDeviation.sphere_deviation` and `FriedmannFluid.comoving_deviation` hold their deviations). Another sign
convention flips the sign of `R`.

Read on the Swing. A tide strains a pair of neighbouring falls and does not turn it: against the metric that
its own connection preserves, the tidal map is a self-adjoint boost with no turn (`tidalMap_is_boost`; atlas
`motion.turn-boost-split`), now at any metric's jet and not only at the comoving metric of a zero first jet. It
kills the strand's own direction and lands on the screen, so in a frame adapted to the strand the stiffness acts
only across it, the screen tide `T(E_i, E_j)`, and the rotation law `ω′ = −(Sω + ωS)` holds there: a congruence
of any metric's free falls focuses by strain at `−θ²/k` on its `k`-dimensional screen and resists by rotation.

The computational object is the helical pair interaction read on a congruence's screen: two neighbouring free
falls are a pair, the deviation is the pair's displacement, and the tide `R(·, u)u` is the pair's constitution,
the stiffness that a metric's jet builds. Of the winding guide's six general objects this touches the pair (the
deviation between neighbouring strands, stiffened by the screen tide), the tube (the base geodesic along its
clock, and the congruence on its screen), faces and placement (the observer's adapted frame, in which the frame
tide is the lowered form `T(E_i, E_j)` and the screen part is the face Raychaudhuri reads) and the cell holonomy
(the curvature as the connection's commutator around a cell, whose pair exchange under a metric-preserving
transport makes the tide symmetric); the helix and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.Spacetime.TidalScreen

open Matrix Filter Topology
open Holonics.Physics.Spacetime.Raychaudhuri Holonics.Physics.Spacetime.CurvatureJets
  Holonics.Physics.Spacetime.GeodesicDeviation

variable {n : ℕ}

/-! ## 1. Metric compatibility gives every curvature symmetry -/

section Compatibility

/-- [definition] **A symmetric first jet**: `∂_e g_ab = ∂_e g_ba`. -/
def FirstJetSymm (dg : FirstJet n) : Prop := ∀ e a b, dg e a b = dg e b a

/-- [definition] **The lowered Christoffel symbols** `Γ_dbc = ½(∂_b g_dc + ∂_c g_db − ∂_d g_bc)`. -/
def christoffelLower (dg : FirstJet n) (d b c : Fin n) : ℝ := 2⁻¹ * (dg b d c + dg c d b - dg d b c)

variable {g : Matrix (Fin n) (Fin n) ℝ} {dg : FirstJet n}

/-- [proved-standard; formal-checked] The owner's symbols are the lowered ones raised: `Γ^a_bc = g^(ad)Γ_dbc`. -/
theorem christoffel_eq_raise (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (a b c : Fin n) :
    christoffel g dg a b c = ∑ d, g⁻¹ a d * christoffelLower dg d b c := by
  simp only [christoffel, christoffelLower, Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by ring

/-- [proved-standard; formal-checked] A symmetric first jet gives `Γ_dbc = Γ_dcb`. -/
theorem christoffelLower_symm (hdg : FirstJetSymm dg) (d b c : Fin n) :
    christoffelLower dg d b c = christoffelLower dg d c b := by
  simp only [christoffelLower]
  linarith [hdg d b c]

/-- [proved-standard; formal-checked] **Torsion-free**: a symmetric first jet gives `Γ^a_bc = Γ^a_cb`. -/
theorem christoffel_symm (hdg : FirstJetSymm dg) (a b c : Fin n) :
    christoffel g dg a b c = christoffel g dg a c b := by
  simp only [christoffel_eq_raise, christoffelLower_symm hdg _ b c]

/-- [proved-standard; formal-checked] **Metric compatibility on the jet**: `∂_c g_ab = Γ_acb + Γ_bca`. -/
theorem firstJet_eq_christoffelLower (hdg : FirstJetSymm dg) (c a b : Fin n) :
    dg c a b = christoffelLower dg a c b + christoffelLower dg b c a := by
  simp only [christoffelLower]
  linarith [hdg a c b, hdg b c a, hdg c b a]

/-- [proved-standard; formal-checked] Lowering the owner's symbols: `g_ae Γ^e_bc = Γ_abc`. -/
theorem lower_christoffel (hg : IsUnit g.det) (dg : FirstJet n) (a b c : Fin n) :
    ∑ e, g a e * christoffel g dg e b c = christoffelLower dg a b c := by
  simp only [christoffel_eq_raise]
  exact contract_inv hg (fun d => christoffelLower dg d b c) a

/-- [proved-standard; formal-checked] At a zero second jet, `∂_eΓ^a_bc = −g^(ap) ∂_e g_pq Γ^q_bc`. -/
theorem christoffelJet_zero (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (e a b c : Fin n) :
    christoffelJet g dg 0 e a b c = -∑ p, g⁻¹ a p * ∑ q, dg e p q * christoffel g dg q b c := by
  simp only [christoffelJet, christoffel, inverseJet, Pi.zero_apply, Matrix.zero_apply, add_zero, sub_zero,
    mul_zero, Finset.sum_const_zero, Matrix.neg_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul,
    neg_mul, Finset.sum_neg_distrib, mul_neg]
  congr 1
  rw [Finset.sum_comm]
  refine Eq.trans (Finset.sum_congr rfl fun q _ => Finset.sum_comm) ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun d _ => by ring

/-- [proved-standard; formal-checked] Lowered, the jet term is `g_af ∂_eΓ^f_bc = −∂_e g_aq Γ^q_bc`. -/
theorem lower_christoffelJet (hg : IsUnit g.det) (dg : FirstJet n) (e a b c : Fin n) :
    ∑ f, g a f * christoffelJet g dg 0 e f b c = -∑ q, dg e a q * christoffel g dg q b c := by
  simp only [christoffelJet_zero, mul_neg, Finset.sum_neg_distrib]
  rw [contract_inv hg (fun p => ∑ q, dg e p q * christoffel g dg q b c) a]

/-- [proved-standard; formal-checked] **The first jet's part**: `R(g, dg, 0)_abcd = Γ_qda Γ^q_cb − Γ_qca Γ^q_db`. -/
theorem riemannLower_zero_eq (hg : IsUnit g.det) (hdg : FirstJetSymm dg) (a b c d : Fin n) :
    riemannLower g dg 0 a b c d
      = ∑ q, (christoffelLower dg q d a * christoffel g dg q c b
        - christoffelLower dg q c a * christoffel g dg q d b) := by
  have h1 : riemannLower g dg 0 a b c d = ∑ e, g a e * christoffelJet g dg 0 c e d b
      - ∑ e, g a e * christoffelJet g dg 0 d e c b
      + ∑ f, ((∑ e, g a e * christoffel g dg e c f) * christoffel g dg f d b
        - (∑ e, g a e * christoffel g dg e d f) * christoffel g dg f c b) := by
    simp only [riemannLower, riemann, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.mul_sum, Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm,
      Finset.sum_comm (f := fun x y => g a x * (christoffel g dg x d y * christoffel g dg y c b))]
    simp only [mul_assoc]
  rw [h1, lower_christoffelJet hg, lower_christoffelJet hg]
  simp only [lower_christoffel hg, firstJet_eq_christoffelLower hdg c a, firstJet_eq_christoffelLower hdg d a]
  simp only [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- [proved-standard; formal-checked] **Quadratic part** `R(g,dg,0)_abcd = g_ef(Γ^e_bc Γ^f_ad − Γ^e_bd Γ^f_ac)`. -/
theorem riemannLower_zero_eq_quadratic (hg : IsUnit g.det) (hdg : FirstJetSymm dg) (a b c d : Fin n) :
    riemannLower g dg 0 a b c d = ∑ e, ∑ f, g e f * (christoffel g dg e b c * christoffel g dg f a d
      - christoffel g dg e b d * christoffel g dg f a c) := by
  rw [riemannLower_zero_eq hg hdg]
  simp only [← lower_christoffel hg dg, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  rw [christoffel_symm hdg e b c, christoffel_symm hdg f a d, christoffel_symm hdg e b d,
    christoffel_symm hdg f a c]
  ring

/-- [definition] **The symbols' pairing through `g⁻¹`**: `P(xy; zw) = Σ_q Γ_qxy Γ^q_zw`. -/
def connectionPair (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (x y z w : Fin n) : ℝ :=
  ∑ q, christoffelLower dg q x y * christoffel g dg q z w

/-- [proved-standard; formal-checked] For symmetric `g` the pairing exchanges its pairs: `P(xy; zw) = P(zw; xy)`. -/
theorem connectionPair_exchange (hgs : gᵀ = g) (x y z w : Fin n) :
    connectionPair g dg x y z w = connectionPair g dg z w x y := by
  have hinv : ∀ i j, g⁻¹ i j = g⁻¹ j i := fun i j => by
    rw [← transpose_apply g⁻¹ j i, transpose_nonsing_inv, hgs]
  simp only [connectionPair, christoffel_eq_raise, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun k _ => by rw [hinv k q]; ring

/-- [proved-standard; formal-checked] The pairing is symmetric in its first pair. -/
theorem connectionPair_swap_left (hdg : FirstJetSymm dg) (x y z w : Fin n) :
    connectionPair g dg x y z w = connectionPair g dg y x z w := by
  simp only [connectionPair, christoffelLower_symm hdg _ x y]

/-- [proved-standard; formal-checked] The pairing is symmetric in its second pair. -/
theorem connectionPair_swap_right (hdg : FirstJetSymm dg) (x y z w : Fin n) :
    connectionPair g dg x y z w = connectionPair g dg x y w z := by
  simp only [connectionPair, christoffel_symm hdg _ z w]

/-- [proved-standard; formal-checked] The first jet's part is `P(da; cb) − P(ca; db)`. -/
theorem riemannLower_zero_eq_pair (hg : IsUnit g.det) (hdg : FirstJetSymm dg) (a b c d : Fin n) :
    riemannLower g dg 0 a b c d = connectionPair g dg d a c b - connectionPair g dg c a d b := by
  rw [riemannLower_zero_eq hg hdg, connectionPair, connectionPair, Finset.sum_sub_distrib]

/-- [proved-standard; formal-checked] **The first jet's part has the curvature symmetries.** -/
theorem riemannLower_zero_symmetries (hg : IsUnit g.det) (hgs : gᵀ = g) (hdg : FirstJetSymm dg) :
    CurvatureSymmetries (riemannLower g dg 0) where
  anti_left a b c d := by
    simp only [riemannLower_zero_eq_pair hg hdg]
    rw [connectionPair_exchange hgs d b, connectionPair_exchange hgs c b]
    ring
  anti_right a b c d := by
    simp only [riemannLower_zero_eq_pair hg hdg]
    ring
  pair a b c d := by
    simp only [riemannLower_zero_eq_pair hg hdg]
    rw [connectionPair_exchange hgs b c, connectionPair_swap_left hdg a d, connectionPair_swap_right hdg d a b,
      connectionPair_swap_left hdg a c, connectionPair_swap_right hdg c a b]
  cyclic a b c d := by
    simp only [riemannLower_zero_eq_pair hg hdg]
    rw [connectionPair_swap_right hdg d a b, connectionPair_swap_right hdg c a b,
      connectionPair_swap_right hdg b a d]
    ring

/-- [proved-standard; formal-checked] The curvature symmetries add. -/
theorem curvatureSymmetries_add {R S : Tensor4 n} (hR : CurvatureSymmetries R)
    (hS : CurvatureSymmetries S) : CurvatureSymmetries (R + S) where
  anti_left a b c d := by
    change R b a c d + S b a c d = -(R a b c d + S a b c d)
    rw [hR.anti_left, hS.anti_left]
    ring
  anti_right a b c d := by
    change R a b d c + S a b d c = -(R a b c d + S a b c d)
    rw [hR.anti_right, hS.anti_right]
    ring
  pair a b c d := by
    change R c d a b + S c d a b = R a b c d + S a b c d
    rw [hR.pair, hS.pair]
  cyclic a b c d := by
    simp only [Pi.add_apply]
    linarith [hR.cyclic a b c d, hS.cyclic a b c d]

/-- [proved-standard; formal-checked] **Metric compatibility gives every curvature symmetry** of `R(g, dg, ddg)`. -/
theorem riemannLower_symmetries (hg : IsUnit g.det) (hgs : gᵀ = g) (hdg : FirstJetSymm dg)
    {ddg : SecondJet n} (h : JetSymm ddg) : CurvatureSymmetries (riemannLower g dg ddg) := by
  rw [riemannLower_eq_add hg dg h]
  exact curvatureSymmetries_add (linearCurvature_symmetries h) (riemannLower_zero_symmetries hg hgs hdg)

/-- [proved-standard; formal-checked] A first jet of symmetric matrices is symmetric. -/
theorem firstJetSymm_of_transpose (h : ∀ e, (dg e)ᵀ = dg e) : FirstJetSymm dg :=
  fun e a b => congrFun (congrFun (h e) b) a

end Compatibility

/-! ## 2. The tide is self-adjoint and lives on the screen -/

section Tide

variable {R : Tensor4 n}

/-- [definition] **The lowered tidal form** `T(ξ, η) = ξ · (tidal R u) η`, for `R` with all indices down. -/
def tidalForm (R : Tensor4 n) (u ξ η : Fin n → ℝ) : ℝ := ξ ⬝ᵥ (tidal R u *ᵥ η)

/-- [proved-standard; formal-checked] `T(ξ, η) = R_abcd ξ^a u^b η^c u^d`, the form `R(ξ, u, η, u)`. -/
theorem tidalForm_apply (R : Tensor4 n) (u ξ η : Fin n → ℝ) :
    tidalForm R u ξ η = ∑ a, ∑ b, ∑ c, ∑ d, R a b c d * ξ a * u b * η c * u d := by
  simp only [tidalForm, dotProduct, tidal_mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => by ring

/-- [proved-standard; formal-checked] **The lowered tidal matrix is symmetric** (the pair exchange). -/
theorem tidal_transpose (h : CurvatureSymmetries R) (u : Fin n → ℝ) : (tidal R u)ᵀ = tidal R u := by
  ext a c
  simp only [transpose_apply, tidal, of_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [h.pair a x c y]; ring

/-- [proved-standard; formal-checked] `T(·, u) = 0`: the second antisymmetry. -/
theorem tidal_mulVec_self_of_symm (h : CurvatureSymmetries R) (u : Fin n → ℝ) : tidal R u *ᵥ u = 0 := by
  funext a
  rw [tidal_mulVec, Pi.zero_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  have h2 : ∑ c, ∑ d, R a b c d * u b * u c * u d = -∑ c, ∑ d, R a b c d * u b * u c * u d := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [h.anti_right a b d c]
    ring
  linarith

/-- [proved-standard; formal-checked] `T(u, ·) = 0`: the first antisymmetry, through the symmetry. -/
theorem vecMul_tidal_self (h : CurvatureSymmetries R) (u : Fin n → ℝ) : u ᵥ* tidal R u = 0 := by
  rw [← tidal_transpose h, vecMul_transpose, tidal_mulVec_self_of_symm h]

/-- [proved-standard; formal-checked] **The tidal form is symmetric**: `T(ξ, η) = T(η, ξ)`. -/
theorem tidalForm_symm (h : CurvatureSymmetries R) (u ξ η : Fin n → ℝ) :
    tidalForm R u ξ η = tidalForm R u η ξ := by
  rw [tidalForm, tidalForm, dotProduct_mulVec, ← mulVec_transpose, tidal_transpose h, dotProduct_comm]

/-- [proved-standard; formal-checked] `T(u, η) = 0`. -/
theorem tidalForm_self_left (h : CurvatureSymmetries R) (u η : Fin n → ℝ) : tidalForm R u u η = 0 := by
  rw [tidalForm, dotProduct_mulVec, vecMul_tidal_self h, zero_dotProduct]

/-- [proved-standard; formal-checked] `T(ξ, u) = 0`. -/
theorem tidalForm_self_right (h : CurvatureSymmetries R) (u ξ : Fin n → ℝ) : tidalForm R u ξ u = 0 := by
  rw [tidalForm, tidal_mulVec_self_of_symm h, dotProduct_zero]

/-- [proved-standard; formal-checked] The lowered curvature's tidal matrix is `g` times the owner's. -/
theorem tidal_riemannLower (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (ddg : SecondJet n)
    (u : Fin n → ℝ) : tidal (riemannLower g dg ddg) u = g * tidal (riemann g dg ddg) u := by
  ext a c
  simp only [tidal, riemannLower, of_apply, mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Eq.trans (Finset.sum_congr rfl fun b _ => Finset.sum_comm) ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by ring

/-- [proved-standard; formal-checked] **The owner's tidal matrix is the form raised**: `R(·, u)u = g⁻¹T`. -/
theorem tidal_riemann {g : Matrix (Fin n) (Fin n) ℝ} (hg : IsUnit g.det) (dg : FirstJet n)
    (ddg : SecondJet n) (u : Fin n → ℝ) :
    tidal (riemann g dg ddg) u = g⁻¹ * tidal (riemannLower g dg ddg) u := by
  rw [tidal_riemannLower, ← Matrix.mul_assoc, nonsing_inv_mul _ hg, Matrix.one_mul]

end Tide

section Screen

variable {g : Matrix (Fin n) (Fin n) ℝ} {u : Fin n → ℝ}

/-- [definition] **The screen** `u^⊥ = {ξ | uᵀgξ = 0}`, the orthogonal complement of `ℝu` under `g`. -/
def screen (g : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) : Submodule ℝ (Fin n → ℝ) :=
  (ℝ ∙ u).orthogonalBilin (Matrix.toLinearMap₂' ℝ g)

/-- [proved-standard; formal-checked] `ξ ∈ u^⊥ ↔ uᵀgξ = 0`. -/
theorem mem_screen {ξ : Fin n → ℝ} : ξ ∈ screen g u ↔ u ⬝ᵥ (g *ᵥ ξ) = 0 := by
  rw [screen, LinearMap.orthogonal_span_singleton_eq_to_lin_ker, LinearMap.mem_ker, toLinearMap₂'_apply']

/-- [proved-standard; formal-checked] A symmetric matrix's form is symmetric: `xᵀAy = yᵀAx`. -/
theorem dotProduct_mulVec_of_symm {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) (x y : Fin n → ℝ) :
    x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]

/-- [proved-standard; formal-checked] For symmetric `g`, `ξ ∈ u^⊥ ↔ ξᵀgu = 0`. -/
theorem mem_screen_iff (hgs : gᵀ = g) {ξ : Fin n → ℝ} : ξ ∈ screen g u ↔ ξ ⬝ᵥ (g *ᵥ u) = 0 := by
  rw [mem_screen, dotProduct_mulVec_of_symm hgs]

/-- [proved-standard; formal-checked] **The splitting** `ℝu ⊕ u^⊥` where `uᵀgu ≠ 0`. -/
theorem isCompl_screen (hu : u ⬝ᵥ (g *ᵥ u) ≠ 0) : IsCompl (ℝ ∙ u) (screen g u) :=
  LinearMap.isCompl_span_singleton_orthogonal (by rwa [toLinearMap₂'_apply'])

/-- [proved-standard; formal-checked] **A vector's two parts**: `ξ − (uᵀgξ/uᵀgu)u` lies on the screen. -/
theorem screen_split (hu : u ⬝ᵥ (g *ᵥ u) ≠ 0) (ξ : Fin n → ℝ) :
    ξ - (u ⬝ᵥ (g *ᵥ ξ) / u ⬝ᵥ (g *ᵥ u)) • u ∈ screen g u := by
  rw [mem_screen, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul,
    div_mul_cancel₀ _ hu, sub_self]

/-- [proved-standard; formal-checked] **For timelike `u`** one coefficient `c` leaves `ξ − cu` on the screen. -/
theorem timelike_split (hu : u ⬝ᵥ (g *ᵥ u) < 0) (ξ : Fin n → ℝ) :
    ∃! c : ℝ, ξ - c • u ∈ screen g u := by
  refine ⟨_, screen_split hu.ne ξ, fun c hc => ?_⟩
  change ξ - c • u ∈ screen g u at hc
  rw [mem_screen, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_eq_zero] at hc
  rw [hc, mul_div_cancel_right₀ _ hu.ne]

variable {R : Tensor4 n}

/-- [proved-standard; formal-checked] **The raised tidal map is `g`-self-adjoint**: `g·M = Mᵀ·g`. -/
theorem tidalMap_isSymm (hg : IsUnit g.det) (hgs : gᵀ = g) (h : CurvatureSymmetries R) :
    g * (g⁻¹ * tidal R u) = (g⁻¹ * tidal R u)ᵀ * g := by
  rw [← Matrix.mul_assoc, mul_nonsing_inv _ hg, Matrix.one_mul, transpose_mul, tidal_transpose h,
    transpose_nonsing_inv, hgs, Matrix.mul_assoc, nonsing_inv_mul _ hg, Matrix.mul_one]

/-- [proved-standard; formal-checked] `⟨Mξ, η⟩_g = ⟨ξ, Mη⟩_g` for the raised tidal map `M`. -/
theorem tidalMap_selfAdjoint (hg : IsUnit g.det) (hgs : gᵀ = g) (h : CurvatureSymmetries R)
    (ξ η : Fin n → ℝ) :
    ((g⁻¹ * tidal R u) *ᵥ ξ) ⬝ᵥ (g *ᵥ η) = ξ ⬝ᵥ (g *ᵥ ((g⁻¹ * tidal R u) *ᵥ η)) := by
  have hT : ∀ ζ, g *ᵥ ((g⁻¹ * tidal R u) *ᵥ ζ) = tidal R u *ᵥ ζ := fun ζ => by
    rw [mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hg, Matrix.one_mul]
  rw [dotProduct_mulVec_of_symm hgs, hT, hT, dotProduct_mulVec_of_symm (tidal_transpose h u)]

/-- [proved-derived; formal-checked] **The raised tidal map is a boost** at `g`: Motion's turn is `0`. -/
theorem tidalMap_is_boost (hg : IsUnit g.det) (hgs : gᵀ = g) (h : CurvatureSymmetries R) :
    Holonics.Geometry.Motion.turn g (g⁻¹ * tidal R u) = 0 ∧
      Holonics.Geometry.Motion.boost g (g⁻¹ * tidal R u) = g⁻¹ * tidal R u := by
  have ha := Holonics.Geometry.Motion.adjointIn_eq_self_of_symm hg (tidalMap_isSymm (u := u) hg hgs h)
  refine ⟨?_, ?_⟩
  · rw [Holonics.Geometry.Motion.turn, ha, sub_self, smul_zero]
  · rw [Holonics.Geometry.Motion.boost, ha, ← two_smul ℝ, smul_smul, invOf_mul_self, one_smul]

/-- [proved-standard; formal-checked] **The raised tidal map kills `u`.** -/
theorem tidalMap_mulVec_self (h : CurvatureSymmetries R) : (g⁻¹ * tidal R u) *ᵥ u = 0 := by
  rw [← mulVec_mulVec, tidal_mulVec_self_of_symm h, mulVec_zero]

/-- [proved-standard; formal-checked] **The raised tidal map lands on the screen.** -/
theorem tidalMap_mem_screen (hg : IsUnit g.det) (h : CurvatureSymmetries R) (ξ : Fin n → ℝ) :
    (g⁻¹ * tidal R u) *ᵥ ξ ∈ screen g u := by
  rw [mem_screen, mulVec_mulVec, ← Matrix.mul_assoc, mul_nonsing_inv _ hg, Matrix.one_mul,
    dotProduct_mulVec, vecMul_tidal_self h, zero_dotProduct]

/-- [proved-standard; formal-checked] **A metric's tide** is `g`-self-adjoint, kills `u` and lands on `u^⊥`. -/
theorem metric_tidal {dg : FirstJet n} {ddg : SecondJet n} (hg : IsUnit g.det) (hgs : gᵀ = g)
    (hdg : FirstJetSymm dg) (h : JetSymm ddg) (u : Fin n → ℝ) :
    g * tidal (riemann g dg ddg) u = (tidal (riemann g dg ddg) u)ᵀ * g ∧
      tidal (riemann g dg ddg) u *ᵥ u = 0 ∧
      ∀ ξ, tidal (riemann g dg ddg) u *ᵥ ξ ∈ screen g u := by
  have hR := riemannLower_symmetries hg hgs hdg h
  rw [tidal_riemann hg]
  exact ⟨tidalMap_isSymm hg hgs hR, tidalMap_mulVec_self hR, tidalMap_mem_screen hg hR⟩

/-- [proved-derived; formal-checked] **A metric's tide is a boost** at that metric: Motion's turn is `0`. -/
theorem metric_tidal_is_boost {dg : FirstJet n} {ddg : SecondJet n} (hg : IsUnit g.det) (hgs : gᵀ = g)
    (hdg : FirstJetSymm dg) (h : JetSymm ddg) (u : Fin n → ℝ) :
    Holonics.Geometry.Motion.turn g (tidal (riemann g dg ddg) u) = 0 := by
  rw [tidal_riemann hg]
  exact (tidalMap_is_boost hg hgs (riemannLower_symmetries hg hgs hdg h)).1

end Screen

/-! ## 3. The reduction in an adapted frame -/

section Frame

variable {k : ℕ}

/-- [definition] **The adapted sign** `(σ, 1, …, 1)`. -/
def adaptedSign (σ : ℝ) (k : ℕ) : Fin (k + 1) → ℝ := Fin.cons σ fun _ => 1

/-- [definition] **An adapted frame** at `u`: first column `u`, and `EᵀgE = diag(σ, 1, …, 1)`. -/
structure AdaptedFrame (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (u : Fin (k + 1) → ℝ) (σ : ℝ)
    (E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) : Prop where
  first : ∀ a, E a 0 = u a
  orthonormal : Eᵀ * g * E = diagonal (adaptedSign σ k)

/-- [definition] **The screen part** of a matrix: its block on the indices `1..k`. -/
def screenPart (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  M.submatrix Fin.succ Fin.succ

variable {g E : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} {u : Fin (k + 1) → ℝ} {σ : ℝ}

/-- [proved-standard; formal-checked] The frame's first column is `u`. -/
theorem AdaptedFrame.col_zero (hE : AdaptedFrame g u σ E) : (fun a => E a 0) = u := funext hE.first

/-- [proved-standard; formal-checked] `(EᵀgE)_ij = E_iᵀ g E_j`, the columns paired by `g`. -/
theorem frame_entry (g E : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (Eᵀ * g * E) i j = (fun a => E a i) ⬝ᵥ (g *ᵥ fun a => E a j) := by
  simp only [mul_apply, transpose_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring

/-- [proved-standard; formal-checked] An adapted frame has `uᵀgu = σ`. -/
theorem AdaptedFrame.norm (hE : AdaptedFrame g u σ E) : u ⬝ᵥ (g *ᵥ u) = σ := by
  rw [← hE.col_zero, ← frame_entry, hE.orthonormal, diagonal_apply_eq]
  rfl

/-- [proved-standard; formal-checked] **The frame's other columns lie on the screen.** -/
theorem AdaptedFrame.mem_screen (hE : AdaptedFrame g u σ E) (j : Fin k) :
    (fun a => E a j.succ) ∈ screen g u := by
  rw [TidalScreen.mem_screen, ← hE.col_zero, ← frame_entry, hE.orthonormal,
    diagonal_apply_ne _ (Fin.succ_ne_zero j).symm]

/-- [proved-standard; formal-checked] `diag(σ⁻¹, 1, …, 1)·diag(σ, 1, …, 1) = 1` for `σ ≠ 0`. -/
theorem adaptedSign_mul (hσ : σ ≠ 0) :
    diagonal (adaptedSign σ⁻¹ k) * diagonal (adaptedSign σ k) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [adaptedSign, hσ]
  · simp [adaptedSign]

/-- [proved-standard; formal-checked] `diag(σ⁻¹, 1, …, 1)Eᵀg` is a left inverse of an adapted frame. -/
theorem AdaptedFrame.left_inv (hE : AdaptedFrame g u σ E) (hσ : σ ≠ 0) :
    diagonal (adaptedSign σ⁻¹ k) * Eᵀ * g * E = 1 := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Eᵀ, hE.orthonormal, adaptedSign_mul hσ]

/-- [proved-standard; formal-checked] `E⁻¹ = diag(σ⁻¹, 1, …, 1)Eᵀg`. -/
theorem AdaptedFrame.inv_eq (hE : AdaptedFrame g u σ E) (hσ : σ ≠ 0) :
    E⁻¹ = diagonal (adaptedSign σ⁻¹ k) * Eᵀ * g :=
  Matrix.inv_eq_left_inv (hE.left_inv hσ)

/-- [proved-standard; formal-checked] An adapted frame is invertible. -/
theorem AdaptedFrame.det (hE : AdaptedFrame g u σ E) (hσ : σ ≠ 0) : IsUnit E.det :=
  Matrix.isUnit_det_of_left_inverse (hE.left_inv hσ)

variable {dg : FirstJet (k + 1)} {ddg : SecondJet (k + 1)}

/-- [proved-standard; formal-checked] `EᵀTE` has zero first row: `T(u, ·) = 0`. -/
theorem frame_row_zero (hE : AdaptedFrame g u σ E) (h : CurvatureSymmetries (riemannLower g dg ddg))
    (j : Fin (k + 1)) : (Eᵀ * tidal (riemannLower g dg ddg) u * E) 0 j = 0 := by
  rw [mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  have h0 : (Eᵀ * tidal (riemannLower g dg ddg) u) 0 c = (u ᵥ* tidal (riemannLower g dg ddg) u) c := by
    simp only [mul_apply, transpose_apply, vecMul, dotProduct, hE.first]
  rw [h0, vecMul_tidal_self h, Pi.zero_apply, zero_mul]

/-- [proved-standard; formal-checked] **The frame tide is the lowered form in the frame**: `E⁻¹R(·, u)uE = EᵀTE`. -/
theorem frameTidal_eq (hg : IsUnit g.det) (hE : AdaptedFrame g u σ E) (hσ : σ ≠ 0)
    (h : CurvatureSymmetries (riemannLower g dg ddg)) :
    frameTidal E (christoffel g dg) (christoffelJet g dg ddg) u
      = Eᵀ * tidal (riemannLower g dg ddg) u * E := by
  have h1 : frameTidal E (christoffel g dg) (christoffelJet g dg ddg) u
      = diagonal (adaptedSign σ⁻¹ k) * (Eᵀ * tidal (riemannLower g dg ddg) u * E) := by
    rw [frameTidal, ← riemann_eq_riemannOf, tidal_riemann hg, hE.inv_eq hσ]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc g, mul_nonsing_inv _ hg, Matrix.one_mul]
  rw [h1]
  ext i j
  rw [diagonal_mul]
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [frame_row_zero hE h, mul_zero]
  · simp [adaptedSign]

/-- [proved-standard; formal-checked] **The frame tide is symmetric.** -/
theorem frameTidal_transpose (hg : IsUnit g.det) (hE : AdaptedFrame g u σ E) (hσ : σ ≠ 0)
    (h : CurvatureSymmetries (riemannLower g dg ddg)) :
    (frameTidal E (christoffel g dg) (christoffelJet g dg ddg) u)ᵀ
      = frameTidal E (christoffel g dg) (christoffelJet g dg ddg) u := by
  rw [frameTidal_eq hg hE hσ h, transpose_mul, transpose_mul, transpose_transpose, tidal_transpose h,
    Matrix.mul_assoc]

/-- [proved-standard; formal-checked] The frame tide's first row vanishes. -/
theorem frameTidal_row (hg : IsUnit g.det) (hE : AdaptedFrame g u σ E) (hσ : σ ≠ 0)
    (h : CurvatureSymmetries (riemannLower g dg ddg)) (j : Fin (k + 1)) :
    frameTidal E (christoffel g dg) (christoffelJet g dg ddg) u 0 j = 0 := by
  rw [frameTidal_eq hg hE hσ h, frame_row_zero hE h]

/-- [proved-standard; formal-checked] The frame tide's first column vanishes. -/
theorem frameTidal_col (hg : IsUnit g.det) (hE : AdaptedFrame g u σ E) (hσ : σ ≠ 0)
    (h : CurvatureSymmetries (riemannLower g dg ddg)) (i : Fin (k + 1)) :
    frameTidal E (christoffel g dg) (christoffelJet g dg ddg) u i 0 = 0 := by
  rw [← frameTidal_transpose hg hE hσ h, transpose_apply, frameTidal_row hg hE hσ h]

/-- [proved-standard; formal-checked] **The frame tide's entries**: `𝓡_ij = T(E_i, E_j)`. -/
theorem frameTidal_apply (hg : IsUnit g.det) (hE : AdaptedFrame g u σ E) (hσ : σ ≠ 0)
    (h : CurvatureSymmetries (riemannLower g dg ddg)) (i j : Fin (k + 1)) :
    frameTidal E (christoffel g dg) (christoffelJet g dg ddg) u i j
      = tidalForm (riemannLower g dg ddg) u (fun a => E a i) (fun a => E a j) := by
  rw [frameTidal_eq hg hE hσ h, frame_entry, tidalForm]

/-- [proved-standard; formal-checked] A symmetric matrix has a symmetric screen part. -/
theorem screenPart_transpose {M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} (hM : Mᵀ = M) :
    (screenPart M)ᵀ = screenPart M := by
  rw [screenPart, transpose_submatrix, hM]

/-- [proved-standard; formal-checked] **A metric's frame tide**: symmetric, first row and column zero, symmetric
screen part. -/
theorem metric_frameTidal (hg : IsUnit g.det) (hgs : gᵀ = g) (hdg : FirstJetSymm dg) (h : JetSymm ddg)
    (hE : AdaptedFrame g u σ E) (hσ : σ ≠ 0) :
    (frameTidal E (christoffel g dg) (christoffelJet g dg ddg) u)ᵀ
        = frameTidal E (christoffel g dg) (christoffelJet g dg ddg) u ∧
      (∀ j, frameTidal E (christoffel g dg) (christoffelJet g dg ddg) u 0 j = 0) ∧
      (∀ i, frameTidal E (christoffel g dg) (christoffelJet g dg ddg) u i 0 = 0) ∧
      (screenPart (frameTidal E (christoffel g dg) (christoffelJet g dg ddg) u))ᵀ
        = screenPart (frameTidal E (christoffel g dg) (christoffelJet g dg ddg) u) := by
  have hR := riemannLower_symmetries hg hgs hdg h
  exact ⟨frameTidal_transpose hg hE hσ hR, frameTidal_row hg hE hσ hR, frameTidal_col hg hE hσ hR,
    screenPart_transpose (frameTidal_transpose hg hE hσ hR)⟩

end Frame

/-! ## 4. The deviation on the screen -/

section Deviation

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {k : ℕ}

/-- [definition] The screen part as a linear map. -/
def screenPartₗ (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ →ₗ[ℝ] Matrix (Fin k) (Fin k) ℝ where
  toFun := screenPart
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- [proved-standard; formal-checked] Where `M`'s first column vanishes, `(MJ)_s = M_s J_s`. -/
theorem screenPart_mul {M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} (h0 : ∀ i, M i 0 = 0)
    (J : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) : screenPart (M * J) = screenPart M * screenPart J := by
  ext i j
  simp [screenPart, mul_apply, Fin.sum_univ_succ, h0]

/-- [proved-standard; formal-checked] **The screen's deviation**: `J″ = −𝓡J` gives `J_s″ = −𝓡_s J_s`. -/
theorem screen_deviation {J J' : ℝ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} {τ : ℝ} (hJ : HasDerivAt J (J' τ) τ)
    (hJ' : HasDerivAt J' (-(M * J τ)) τ) (h0 : ∀ i, M i 0 = 0) :
    HasDerivAt (fun t => screenPart (J t)) (screenPart (J' τ)) τ ∧
      HasDerivAt (fun t => screenPart (J' t)) (-(screenPart M * screenPart (J τ))) τ := by
  refine ⟨hasDerivAt_linearMap (screenPartₗ k) hJ, ?_⟩
  have h := hasDerivAt_linearMap (screenPartₗ k) hJ'
  rw [map_neg] at h
  change HasDerivAt (fun t => screenPart (J' t)) (-screenPart (M * J τ)) τ at h
  rwa [screenPart_mul h0] at h

/-- [proved-standard; formal-checked] **Raychaudhuri's equation and the rotation law on the screen.** -/
theorem screen_raychaudhuri (hk : (k : ℝ) ≠ 0) {J J' : ℝ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} {τ : ℝ} (hJ : HasDerivAt J (J' τ) τ)
    (hJ' : HasDerivAt J' (-(M * J τ)) τ) (h0 : ∀ i, M i 0 = 0) (hM : Mᵀ = M)
    (hu : IsUnit (screenPart (J τ)).det) :
    HasDerivAt (fun t => expansion (deformation (fun t => screenPart (J t)) (fun t => screenPart (J' t)) t))
        (raychaudhuriRate (deformation (fun t => screenPart (J t)) (fun t => screenPart (J' t)) τ)
          (screenPart M)) τ ∧
      HasDerivAt (fun t => rotation (deformation (fun t => screenPart (J t)) (fun t => screenPart (J' t)) t))
        (-(symPart (deformation (fun t => screenPart (J t)) (fun t => screenPart (J' t)) τ)
            * rotation (deformation (fun t => screenPart (J t)) (fun t => screenPart (J' t)) τ)
          + rotation (deformation (fun t => screenPart (J t)) (fun t => screenPart (J' t)) τ)
            * symPart (deformation (fun t => screenPart (J t)) (fun t => screenPart (J' t)) τ))) τ := by
  have h := screen_deviation hJ hJ' h0
  exact ⟨raychaudhuri (R := fun _ => screenPart M) hk h.1 h.2 hu,
    rotation_law (R := fun _ => screenPart M) h.1 h.2 hu (screenPart_transpose hM)⟩

/-- [proved-standard; formal-checked] A symmetric tide's shear is its trace-free part `R − (tr R/m)·1`. -/
theorem shear_of_symm {m : ℕ} {M : Matrix (Fin m) (Fin m) ℝ} (hM : Mᵀ = M) :
    shear M = M - (M.trace / m) • (1 : Matrix (Fin m) (Fin m) ℝ) := by
  rw [shear, hM, expansion, ← two_smul ℝ M, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- [proved-standard; formal-checked] **The shear's law on the screen**, driven by the trace-free screen tide. -/
theorem screen_shear_law (hk : (k : ℝ) ≠ 0) {J J' : ℝ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ}
    {M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} {τ : ℝ} (hJ : HasDerivAt J (J' τ) τ)
    (hJ' : HasDerivAt J' (-(M * J τ)) τ) (h0 : ∀ i, M i 0 = 0) (hM : Mᵀ = M)
    (hu : IsUnit (screenPart (J τ)).det) :
    HasDerivAt (fun t => shear (deformation (fun t => screenPart (J t)) (fun t => screenPart (J' t)) t))
      (-((2 * expansion (deformation (fun t => screenPart (J t)) (fun t => screenPart (J' t)) τ) / k)
          • shear (deformation (fun t => screenPart (J t)) (fun t => screenPart (J' t)) τ)
        + (shear (deformation (fun t => screenPart (J t)) (fun t => screenPart (J' t)) τ)
            * shear (deformation (fun t => screenPart (J t)) (fun t => screenPart (J' t)) τ)
          + rotation (deformation (fun t => screenPart (J t)) (fun t => screenPart (J' t)) τ)
            * rotation (deformation (fun t => screenPart (J t)) (fun t => screenPart (J' t)) τ))
        - ((shear (deformation (fun t => screenPart (J t)) (fun t => screenPart (J' t)) τ)
            * shear (deformation (fun t => screenPart (J t)) (fun t => screenPart (J' t)) τ)
          + rotation (deformation (fun t => screenPart (J t)) (fun t => screenPart (J' t)) τ)
            * rotation (deformation (fun t => screenPart (J t)) (fun t => screenPart (J' t)) τ)).trace / k)
          • (1 : Matrix (Fin k) (Fin k) ℝ))
        - (screenPart M - ((screenPart M).trace / k) • (1 : Matrix (Fin k) (Fin k) ℝ))) τ := by
  have h := screen_deviation hJ hJ' h0
  rw [← shear_of_symm (screenPart_transpose hM)]
  exact shear_law (R := fun _ => screenPart M) hk h.1 h.2 hu

/-- [definition] **The frame components** `J = E⁻¹X` of `n` deviations along the base geodesic. -/
def frameJ (E : ℝ → Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ → ℝ → Fin n → ℝ) (s t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (E t)⁻¹ * cols (fun i => ξ i t s)

/-- [definition] **Their rate** `E⁻¹(X′ + A(u)X)`, as in `GeodesicDeviation.families_frame_deviation`. -/
def frameJ' (E : ℝ → Matrix (Fin n) (Fin n) ℝ) (Γ : (Fin n → ℝ) → Coeff n) (xb ub : ℝ → Fin n → ℝ)
    (ξ w : Fin n → ℝ → ℝ → Fin n → ℝ) (s t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (E t)⁻¹ * (cols (fun i => w i t s) + connectionAlong (Γ (xb t)) (ub t) * cols (fun i => ξ i t s))

section Families

variable {g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} {dg : FirstJet (k + 1)} {ddg : SecondJet (k + 1)} {σ : ℝ}
  {Γ : (Fin (k + 1) → ℝ) → Coeff (k + 1)} {dΓ : (Fin (k + 1) → ℝ) → CoeffJet (k + 1)}
  {x u ξ w α β : Fin (k + 1) → ℝ → ℝ → Fin (k + 1) → ℝ} {xb ub : ℝ → Fin (k + 1) → ℝ}
  {E : ℝ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} {τ s : ℝ}

/-- [proved-standard; formal-checked] **A metric connection's frame tide** is symmetric, first column zero. -/
theorem families_tide (hmet : Γ (xb τ) = christoffel g dg) (hmetJ : dΓ (xb τ) = christoffelJet g dg ddg)
    (hg : IsUnit g.det) (hgs : gᵀ = g) (hdg : FirstJetSymm dg) (hddg : JetSymm ddg)
    (hA : AdaptedFrame g (ub τ) σ (E τ)) (hσ : σ ≠ 0) :
    (frameTidal (E τ) (Γ (xb τ)) (dΓ (xb τ)) (ub τ))ᵀ = frameTidal (E τ) (Γ (xb τ)) (dΓ (xb τ)) (ub τ) ∧
      ∀ i, frameTidal (E τ) (Γ (xb τ)) (dΓ (xb τ)) (ub τ) i 0 = 0 := by
  have hR := riemannLower_symmetries hg hgs hdg hddg
  rw [hmet, hmetJ]
  exact ⟨frameTidal_transpose hg hA hσ hR, frameTidal_col hg hA hσ hR⟩

/-- [proved-standard; formal-checked] **`families_raychaudhuri` with the symmetric tide, and the rotation law.** -/
theorem families_rotation_law (hsym : ∀ y a b c, Γ y a b c = Γ y a c b)
    (hΓ : HasConnectionJetAt Γ (dΓ (xb τ)) (xb τ))
    (hF : ∀ i, FamilyAt (x i) (u i) (ξ i) (w i) (α i) (β i) τ s)
    (hgeo : ∀ i, ∀ᶠ r in 𝓝 s, covD (Γ (x i τ r)) (u i τ r) (u i τ r) (α i τ r) = 0)
    (hxb : ∀ i t, x i t s = xb t) (hub : ∀ i t, u i t s = ub t)
    (hE : HasDerivAt E (-(connectionAlong (Γ (xb τ)) (ub τ) * E τ)) τ)
    (hmet : Γ (xb τ) = christoffel g dg) (hmetJ : dΓ (xb τ) = christoffelJet g dg ddg)
    (hg : IsUnit g.det) (hgs : gᵀ = g) (hdg : FirstJetSymm dg) (hddg : JetSymm ddg)
    (hA : AdaptedFrame g (ub τ) σ (E τ)) (hσ : σ ≠ 0) (hJ : IsUnit (frameJ E ξ s τ).det) :
    HasDerivAt (fun t => expansion (deformation (frameJ E ξ s) (frameJ' E Γ xb ub ξ w s) t))
        (raychaudhuriRate (deformation (frameJ E ξ s) (frameJ' E Γ xb ub ξ w s) τ)
          (frameTidal (E τ) (Γ (xb τ)) (dΓ (xb τ)) (ub τ))) τ ∧
      HasDerivAt (fun t => rotation (deformation (frameJ E ξ s) (frameJ' E Γ xb ub ξ w s) t))
        (-(symPart (deformation (frameJ E ξ s) (frameJ' E Γ xb ub ξ w s) τ)
            * rotation (deformation (frameJ E ξ s) (frameJ' E Γ xb ub ξ w s) τ)
          + rotation (deformation (frameJ E ξ s) (frameJ' E Γ xb ub ξ w s) τ)
            * symPart (deformation (frameJ E ξ s) (frameJ' E Γ xb ub ξ w s) τ))) τ := by
  have h := families_frame_deviation hsym hΓ hF hgeo hxb hub hE (hA.det hσ)
  have h1 : HasDerivAt (frameJ E ξ s) (frameJ' E Γ xb ub ξ w s τ) τ := h.1
  have h2 : HasDerivAt (frameJ' E Γ xb ub ξ w s)
      (-(frameTidal (E τ) (Γ (xb τ)) (dΓ (xb τ)) (ub τ) * frameJ E ξ s τ)) τ := h.2
  have hT := (families_tide hmet hmetJ hg hgs hdg hddg hA hσ).1
  exact ⟨raychaudhuri (R := fun _ => frameTidal (E τ) (Γ (xb τ)) (dΓ (xb τ)) (ub τ)) (by positivity) h1 h2 hJ,
    rotation_law (R := fun _ => frameTidal (E τ) (Γ (xb τ)) (dΓ (xb τ)) (ub τ)) h1 h2 hJ hT⟩

/-- [proved-standard; formal-checked] **Free fall on the screen**: its deviation, Raychaudhuri's equation at
`−θ²/k` and the rotation law, for `n = k + 1` families of a metric's geodesics in an adapted parallel frame. -/
theorem families_screen_raychaudhuri (hk : (k : ℝ) ≠ 0) (hsym : ∀ y a b c, Γ y a b c = Γ y a c b)
    (hΓ : HasConnectionJetAt Γ (dΓ (xb τ)) (xb τ))
    (hF : ∀ i, FamilyAt (x i) (u i) (ξ i) (w i) (α i) (β i) τ s)
    (hgeo : ∀ i, ∀ᶠ r in 𝓝 s, covD (Γ (x i τ r)) (u i τ r) (u i τ r) (α i τ r) = 0)
    (hxb : ∀ i t, x i t s = xb t) (hub : ∀ i t, u i t s = ub t)
    (hE : HasDerivAt E (-(connectionAlong (Γ (xb τ)) (ub τ) * E τ)) τ)
    (hmet : Γ (xb τ) = christoffel g dg) (hmetJ : dΓ (xb τ) = christoffelJet g dg ddg)
    (hg : IsUnit g.det) (hgs : gᵀ = g) (hdg : FirstJetSymm dg) (hddg : JetSymm ddg)
    (hA : AdaptedFrame g (ub τ) σ (E τ)) (hσ : σ ≠ 0) (hJ : IsUnit (screenPart (frameJ E ξ s τ)).det) :
    HasDerivAt (fun t => screenPart (frameJ E ξ s t)) (screenPart (frameJ' E Γ xb ub ξ w s τ)) τ ∧
      HasDerivAt (fun t => screenPart (frameJ' E Γ xb ub ξ w s t))
        (-(screenPart (frameTidal (E τ) (Γ (xb τ)) (dΓ (xb τ)) (ub τ)) * screenPart (frameJ E ξ s τ))) τ ∧
      HasDerivAt (fun t => expansion (deformation (fun t => screenPart (frameJ E ξ s t))
          (fun t => screenPart (frameJ' E Γ xb ub ξ w s t)) t))
        (raychaudhuriRate (deformation (fun t => screenPart (frameJ E ξ s t))
          (fun t => screenPart (frameJ' E Γ xb ub ξ w s t)) τ)
          (screenPart (frameTidal (E τ) (Γ (xb τ)) (dΓ (xb τ)) (ub τ)))) τ ∧
      HasDerivAt (fun t => rotation (deformation (fun t => screenPart (frameJ E ξ s t))
          (fun t => screenPart (frameJ' E Γ xb ub ξ w s t)) t))
        (-(symPart (deformation (fun t => screenPart (frameJ E ξ s t))
              (fun t => screenPart (frameJ' E Γ xb ub ξ w s t)) τ)
            * rotation (deformation (fun t => screenPart (frameJ E ξ s t))
              (fun t => screenPart (frameJ' E Γ xb ub ξ w s t)) τ)
          + rotation (deformation (fun t => screenPart (frameJ E ξ s t))
              (fun t => screenPart (frameJ' E Γ xb ub ξ w s t)) τ)
            * symPart (deformation (fun t => screenPart (frameJ E ξ s t))
              (fun t => screenPart (frameJ' E Γ xb ub ξ w s t)) τ))) τ := by
  have h := families_frame_deviation hsym hΓ hF hgeo hxb hub hE (hA.det hσ)
  have h1 : HasDerivAt (frameJ E ξ s) (frameJ' E Γ xb ub ξ w s τ) τ := h.1
  have h2 : HasDerivAt (frameJ' E Γ xb ub ξ w s)
      (-(frameTidal (E τ) (Γ (xb τ)) (dΓ (xb τ)) (ub τ) * frameJ E ξ s τ)) τ := h.2
  have hT := families_tide hmet hmetJ hg hgs hdg hddg hA hσ
  have hs := screen_deviation h1 h2 hT.2
  exact ⟨hs.1, hs.2, screen_raychaudhuri hk h1 h2 hT.2 hT.1 hJ⟩

end Families

end Deviation

/-! ## 5. Witnesses -/

section Witnesses

/-- [proved-standard; formal-checked] Minkowski's signs are the adapted sign `(−1, 1, 1, 1)`. -/
theorem minkowskiSign_eq : minkowskiSign = adaptedSign (-1) 3 := by
  funext i
  fin_cases i <;> rfl

/-- [proved-standard; formal-checked] `η` is symmetric. -/
theorem minkowski_transpose : minkowskiᵀ = minkowski := diagonal_transpose _

/-- [proved-standard; formal-checked] **The observer `e₀` at `η`**: `E = 1` is adapted with `σ = −1`. -/
theorem minkowski_adapted : AdaptedFrame minkowski (Pi.single 0 1) (-1) 1 where
  first a := by simp [one_apply, Pi.single_apply]
  orthonormal := by rw [transpose_one, Matrix.one_mul, Matrix.mul_one, minkowski, minkowskiSign_eq]

/-- [proved-standard; formal-checked] **At `η` the screen tide is the owner's `tide`**, for any jets. -/
theorem minkowski_screenPart (dg : FirstJet 4) (ddg : SecondJet 4) :
    screenPart (frameTidal 1 (christoffel minkowski dg) (christoffelJet minkowski dg ddg) (Pi.single 0 1))
      = Matrix.of (tide (riemannLower minkowski dg ddg)) := by
  ext i j
  simp only [screenPart, submatrix_apply, frameTidal, inv_one, Matrix.one_mul, Matrix.mul_one, of_apply]
  rw [tide_eq_tidal]
  rfl

/-- [proved-standard; formal-checked] **At `η` with any symmetric first jet** the tide is symmetric and is `E`. -/
theorem minkowski_tide {dg : FirstJet 4} {ddg : SecondJet 4} (hdg : FirstJetSymm dg) (h : JetSymm ddg) :
    (Matrix.of (tide (riemannLower minkowski dg ddg)))ᵀ = Matrix.of (tide (riemannLower minkowski dg ddg)) ∧
      tide (riemannLower minkowski dg ddg) = electric (riemannLower minkowski dg ddg) := by
  have hR := riemannLower_symmetries minkowski_det minkowski_transpose hdg h
  exact ⟨tide_transpose hR, tide_eq_electric hR⟩

open Holonics.Physics.Spacetime.FriedmannFluid in
/-- [proved-standard; formal-checked] **The comoving frame of the Friedmann jet** is adapted with `σ = −1`. -/
theorem frw_adapted {A : ℝ} (hA : A ≠ 0) :
    AdaptedFrame (frwMetric A) (Pi.single 0 1) (-1) (diagonal (frwFrame A)) where
  first a := by fin_cases a <;> simp [frwFrame, diagonal]
  orthonormal := by
    rw [diagonal_transpose, frwMetric, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [frwFrame, frwDiag, adaptedSign]
    · simp [frwFrame, frwDiag, adaptedSign, Fin.succ_ne_zero]
      field_simp

open Holonics.Physics.Spacetime.FriedmannFluid in
/-- [proved-standard; formal-checked] **The Friedmann jet's screen tide** is `−(C/A)·1`, its frame tide symmetric. -/
theorem frw_screen {A : ℝ} (hA : A ≠ 0) (B C : ℝ) :
    (frameTidal (diagonal (frwFrame A)) (christoffel (frwMetric A) (frwFirstJet A B))
        (christoffelJet (frwMetric A) (frwFirstJet A B) (frwSecondJet A B C)) (Pi.single 0 1))ᵀ
      = frameTidal (diagonal (frwFrame A)) (christoffel (frwMetric A) (frwFirstJet A B))
        (christoffelJet (frwMetric A) (frwFirstJet A B) (frwSecondJet A B C)) (Pi.single 0 1) ∧
    screenPart (frameTidal (diagonal (frwFrame A)) (christoffel (frwMetric A) (frwFirstJet A B))
        (christoffelJet (frwMetric A) (frwFirstJet A B) (frwSecondJet A B C)) (Pi.single 0 1))
      = (-(C / A)) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have hdg : FirstJetSymm (frwFirstJet A B) := firstJetSymm_of_transpose fun e => diagonal_transpose _
  have hgs : (frwMetric A)ᵀ = frwMetric A := diagonal_transpose _
  have hR := riemannLower_symmetries (frwMetric_det hA) hgs hdg (frwSecondJet_symm A B C)
  refine ⟨frameTidal_transpose (frwMetric_det hA) (frw_adapted hA) (by norm_num) hR, ?_⟩
  rw [frameTidal_eq (frwMetric_det hA) (frw_adapted hA) (by norm_num) hR]
  ext i j
  have ht := frw_tide hA B C i j
  simp only [tide] at ht
  simp only [screenPart, submatrix_apply, diagonal_transpose, diagonal_mul, mul_diagonal, tidal_single, ht,
    frwFrame, Fin.succ_ne_zero, if_false, Matrix.smul_apply, one_apply, smul_eq_mul]
  split_ifs
  · field_simp
  · simp

/-- [definition] **The round sphere's second jet** at `θ`: `∂_θ∂_θ diag(1, sin²θ) = diag(0, 2(cos²θ − sin²θ))`. -/
def sphereSecondJet (θ : ℝ) : SecondJet 2 :=
  fun e f => if e = 0 ∧ f = 0 then diagonal ![0, 2 * (Real.cos θ ^ 2 - Real.sin θ ^ 2)] else 0

/-- [proved-standard; formal-checked] The owner's first jet has the rate `sphereSecondJet` in `θ`, entry by entry. -/
theorem hasDerivAt_sphereMetricJet (θ : ℝ) (a b : Fin 2) :
    HasDerivAt (fun t => sphereMetricJet t 0 a b) (sphereSecondJet θ 0 0 a b) θ := by
  have h : HasDerivAt (fun t => 2 * Real.sin t * Real.cos t) (2 * (Real.cos θ ^ 2 - Real.sin θ ^ 2)) θ :=
    (((Real.hasDerivAt_sin θ).const_mul 2).mul (Real.hasDerivAt_cos θ)).congr_deriv (by ring)
  fin_cases a <;> fin_cases b <;> simp [sphereMetricJet, sphereSecondJet, diagonal, h] <;>
    exact hasDerivAt_const _ _

/-- [proved-standard; formal-checked] The sphere's first jet is symmetric. -/
theorem sphereMetricJet_symm (θ : ℝ) : FirstJetSymm (sphereMetricJet θ) := by
  intro e a b
  fin_cases e <;> fin_cases a <;> fin_cases b <;> simp [sphereMetricJet, diagonal]

/-- [proved-standard; formal-checked] The sphere's second jet has `JetSymm`. -/
theorem sphereSecondJet_symm (θ : ℝ) : JetSymm (sphereSecondJet θ) where
  deriv_comm e f a b := by fin_cases e <;> fin_cases f <;> simp [sphereSecondJet]
  metric_symm e f a b := by
    fin_cases e <;> fin_cases f <;> fin_cases a <;> fin_cases b <;> simp [sphereSecondJet, diagonal]

/-- [proved-standard; formal-checked] The round metric is invertible where `sinθ ≠ 0`. -/
theorem sphereMetric_det {θ : ℝ} (hs : Real.sin θ ≠ 0) : IsUnit (diagonal ![1, Real.sin θ ^ 2]).det := by
  rw [det_diagonal, Fin.prod_univ_two]
  simp [hs]

/-- [proved-standard; formal-checked] Its inverse is `diag(1, 1/sin²θ)`. -/
theorem sphereMetric_inv {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    (diagonal ![1, Real.sin θ ^ 2])⁻¹ = diagonal ![1, (Real.sin θ ^ 2)⁻¹] := by
  refine Matrix.inv_eq_right_inv ?_
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [hs]

/-- [proved-standard; formal-checked] **The metric's jet gives the owner's connection jet** `sphereJet`. -/
theorem sphere_christoffelJet {p : Fin 2 → ℝ} (hs : Real.sin (p 0) ≠ 0) :
    christoffelJet (diagonal ![1, Real.sin (p 0) ^ 2]) (sphereMetricJet (p 0)) (sphereSecondJet (p 0))
      = sphereJet p := by
  funext e a b c
  rw [christoffelJet, inverseJet, sphereMetric_inv hs]
  fin_cases e <;> fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [sphereMetricJet, sphereSecondJet, sphereJet, sphereF', diagonal, mul_apply] <;>
    field_simp <;> linear_combination (-1 : ℝ) * Real.sin_sq_add_cos_sq (p 0)

/-- [proved-standard; formal-checked] **The sphere's quadratic part** `R(g, dg, 0)_φθφθ = cos²θ`. -/
theorem sphere_quadratic {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    riemannLower (diagonal ![1, Real.sin θ ^ 2]) (sphereMetricJet θ) 0 1 0 1 0 = Real.cos θ ^ 2 := by
  rw [riemannLower_zero_eq (sphereMetric_det hs) (sphereMetricJet_symm θ), sphere_christoffel hs]
  simp [christoffelLower, sphereF, sphereMetricJet, Fin.sum_univ_two, diagonal]
  field_simp

/-- [proved-standard; formal-checked] **The sphere's curvature** `R_φθφθ = sin²θ`, unit curvature. -/
theorem sphere_riemannLower {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    riemannLower (diagonal ![1, Real.sin θ ^ 2]) (sphereMetricJet θ) (sphereSecondJet θ) 1 0 1 0
      = Real.sin θ ^ 2 := by
  rw [riemannLower_eq_add (sphereMetric_det hs) _ (sphereSecondJet_symm θ), Pi.add_apply, Pi.add_apply,
    Pi.add_apply, Pi.add_apply, sphere_quadratic hs]
  simp [linearCurvature, sphereSecondJet, diagonal]

/-- [proved-standard; formal-checked] **The meridian's frame** `diag(1, 1/sinθ)` is adapted with `σ = 1`. -/
theorem sphere_adapted {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    AdaptedFrame (diagonal ![1, Real.sin θ ^ 2]) (Pi.single 0 1) 1 (diagonal ![1, (Real.sin θ)⁻¹]) where
  first a := by fin_cases a <;> simp [diagonal]
  orthonormal := by
    rw [diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i
    · simp [adaptedSign]
    · simp [adaptedSign]
      field_simp

/-- [proved-standard; formal-checked] The sphere's tidal matrix at `e_θ` is `diag(0, 1)`. -/
theorem sphere_tidal (p : Fin 2 → ℝ) (hs : Real.sin (p 0) ≠ 0) :
    tidal (riemannOf (sphereΓ p) (sphereJet p)) (Pi.single 0 1) = diagonal ![0, 1] := by
  ext a c
  rw [tidal_single]
  fin_cases a <;> fin_cases c <;>
    simp [riemannOf, sphereΓ, sphereJet, sphereF, sphereF', Fin.sum_univ_two, diagonal]
  field_simp
  linear_combination (-1 : ℝ) * Real.sin_sq_add_cos_sq (p 0)

/-- [proved-standard; formal-checked] Its frame tide in `diag(1, 1/sinθ)` is `diag(0, 1)`. -/
theorem sphere_frameTidal (p : Fin 2 → ℝ) (hs : Real.sin (p 0) ≠ 0) :
    frameTidal (diagonal ![1, (Real.sin (p 0))⁻¹]) (sphereΓ p) (sphereJet p) (Pi.single 0 1)
      = diagonal ![0, 1] := by
  have hinv : (diagonal ![1, (Real.sin (p 0))⁻¹])⁻¹ = diagonal ![1, Real.sin (p 0)] := by
    refine Matrix.inv_eq_right_inv ?_
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hs]
  rw [frameTidal, sphere_tidal p hs, hinv, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [hs]

/-- [proved-standard; formal-checked] **The sphere's screen**: symmetries, the owner's connection, tide `1`. -/
theorem sphere_screen {p : Fin 2 → ℝ} (hs : Real.sin (p 0) ≠ 0) :
    CurvatureSymmetries (riemannLower (diagonal ![1, Real.sin (p 0) ^ 2]) (sphereMetricJet (p 0))
        (sphereSecondJet (p 0))) ∧
      frameTidal (diagonal ![1, (Real.sin (p 0))⁻¹]) (christoffel (diagonal ![1, Real.sin (p 0) ^ 2])
          (sphereMetricJet (p 0))) (christoffelJet (diagonal ![1, Real.sin (p 0) ^ 2]) (sphereMetricJet (p 0))
          (sphereSecondJet (p 0))) (Pi.single 0 1)
        = frameTidal (diagonal ![1, (Real.sin (p 0))⁻¹]) (sphereΓ p) (sphereJet p) (Pi.single 0 1) ∧
      frameTidal (diagonal ![1, (Real.sin (p 0))⁻¹]) (sphereΓ p) (sphereJet p) (Pi.single 0 1)
        = diagonal ![0, 1] ∧
      screenPart (frameTidal (diagonal ![1, (Real.sin (p 0))⁻¹]) (sphereΓ p) (sphereJet p) (Pi.single 0 1))
        = 1 := by
  refine ⟨riemannLower_symmetries (sphereMetric_det hs) (diagonal_transpose _) (sphereMetricJet_symm _)
    (sphereSecondJet_symm _), ?_, sphere_frameTidal p hs, ?_⟩
  · rw [sphere_christoffel hs, sphere_christoffelJet hs]
    rfl
  · rw [sphere_frameTidal p hs]
    ext i j
    fin_cases i
    fin_cases j
    rfl

end Witnesses

end Holonics.Physics.Spacetime.TidalScreen

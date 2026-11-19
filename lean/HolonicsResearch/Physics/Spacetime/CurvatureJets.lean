import HolonicsResearch.Physics.Spacetime.PetrovTypes
import Holonics.Physics.Spacetime.StressEnergy

/-!
# Curvature from a metric's 2-jet: the connection's commutator, a vacuum's Weyl tensor, Newton's tide

[definition] Two boxes of #410. "Einstein: the continuum realization (Lorentzian metric, connection,
a fluid-plus-thermal constitution solving `G + Λg = κT`), the weak-field limit `R₀₀ = ∇²Φ`, and the
Regge construction (`Physics/Spacetime/Einstein`)": this module takes the weak-field limit and the
curvature of a metric's connection at a point, as finite algebra on the metric's 2-jet. "Curvature's
strain and rotation", part done in #1024 and #1031 (`Physics/Spacetime/Raychaudhuri`,
`Physics/Spacetime/PetrovTypes`), with "the deviation equation and the tide from a Lorentzian
metric's connection" left: this module takes the tide `R_ij = R_(i0j0)` from a metric's connection
at a point. Sources: `Physics/Spacetime/Einstein`'s `[open]` paragraph ("A nontrivial continuum
realization (a Lorentzian metric, its connection and curvature, and a fluid-plus-thermal
constitution solving `G + Λg = κT`) is owed"); `Physics/Spacetime/StressEnergy`'s trace reversal
("In the weak static field `R₀₀ = ∇²Φ`, so this is Poisson's `∇²Φ = 4πGρ`; that limit is not
formalized here"; atlas `gr.trace-reversal-newtonian`); `Raychaudhuri`'s "What is not claimed" ("No
`C` with the curvature symmetries is built from a metric, no nonzero instance of `WeylSymmetries` is
exhibited, and that the vacuum's tidal matrix is `E` (Riemann is Weyl where the Ricci tensor
vanishes) is read, not derived"; atlas `coupling.weyl-electric-magnetic`) and its §4
(`minkowskiSign`, `WeylSymmetries`, `electric`, `magnetic`, `raychaudhuriRate`,
`raychaudhuriRate_electric`), with `raychaudhuriRate_le`, `rotation_eq_turn`, `symPart_eq_boost`
and `hasDerivAt_ringInverse_comp`; `PetrovTypes`' "What is not claimed" ("no witness is exhibited
as `weylQ C` of a built `C`") and its `weylQ`, `classify`, `classify_eq_of_hasType`,
`hasType_N_iff`, `classify_schwarzschild`, `classify_weylQ_of_magnetic_eq_zero` (atlas
`coupling.petrov-types`); the Swing record
(`research/records/2026-09-28_THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_A_GRIP_TURNS_A_PUSH_BOOSTS_AND_A_FREE_BODY_FALLS.md`
§5.6: "Free fall is the geodesic, and gravity the connection"; "Tidal curvature is a strain
field"); and atlas `motion.turn-boost-split`, `gr.curvature-commutator`,
`cell.connection-route-return`.

A metric's **2-jet** at a point, in coordinates `Fin n`, is its value `g` (invertible), its first
jet `dg e a b = ∂_e g_ab` (`FirstJet`) and its second jet `ddg e f a b = ∂_e∂_f g_ab` (`SecondJet`),
symmetric in `e f` and in `a b` (`JetSymm`). The jet's inverse rate is `∂_e g⁻¹ = −g⁻¹(∂_e g)g⁻¹`
(`inverseJet`); the **Christoffel symbols** are `Γ^a_bc = ½ g^(ad)(∂_b g_dc + ∂_c g_db − ∂_d g_bc)`
(`christoffel`), with first jet `∂_eΓ^a_bc` (`christoffelJet`), and the connection's matrix in the
direction `c` is `A_c = (Γ^a_cb)_(ab)` (`connection`). The **Riemann tensor** is
`R^a_bcd = ∂_cΓ^a_db − ∂_dΓ^a_cb + Γ^a_ce Γ^e_db − Γ^a_de Γ^e_cb` (`riemann`), lowered
`R_abcd = g_ae R^e_bcd` (`riemannLower`), with Ricci contraction `R_bd = R^a_bad = g^(ae) R_ebad`
(`ricci`). The sign convention is Misner–Thorne–Wheeler's: with it the deviation of free fall reads
`J″ = −RJ` with the **tide** `R_ij = R_(i0j0)` (`tide`, the observer `u = e₀`), and a static weak
field's tide is `+∂_i∂_jΦ`, Newton's tidal tensor. The second jet's **linear form** is
`K(ddg)_abcd = ½(∂_b∂_c g_ad + ∂_a∂_d g_bc − ∂_a∂_c g_bd − ∂_b∂_d g_ac)` (`linearCurvature`). At
`n = 4` the frame `η = diag(−1, 1, 1, 1)` is `minkowski`.

[proved-standard; formal-checked] What is proved. Everything is over ℝ.

1. **The jet calculus** (`hasDerivAt_inv_metric`, `hasDerivAt_christoffel`). Along a coordinate
   line, a metric path `G` whose rate is `∂_e g` has the inverse rate `inverseJet` (the owner's
   `hasDerivAt_ringInverse_comp`, in Mathlib's `linftyOp` norm), and the Christoffel symbols of `G`
   and of a first-jet path whose entries have the rates `∂_e∂ g` have the rate `christoffelJet`:
   the definitions are the derivatives they name.
2. **Curvature is the connection's commutator** (`riemann_eq_commutator`, `connectionJet`):
   `R_cd = ∂_cA_d − ∂_dA_c + [A_c, A_d]` as matrices `(R^a_bcd)_(ab)`, the form
   `F = dA + A∧A` of atlas `gr.curvature-commutator`.
3. **Linear in the second jet, quadratic in the first** (`contract_inv`, `jetCombo`,
   `riemann_eq_add`, `jetCombo_eq`, `riemannLower_eq_add`, `inverseJet_smul`, `christoffel_smul`,
   `christoffelJet_smul`, `riemann_smul`, `riemannLower_smul`, `linearCurvature_smul`,
   `jetSymm_smul`, `riemannLower_scale`, `christoffel_zero`, `riemannLower_zero`,
   `riemannLower_of_firstJet_zero`). For any invertible `g` and a second jet with `JetSymm`,
   `R(g, dg, ddg) = K(ddg) + R(g, dg, 0)` and `R(g, t·dg, 0) = t²·R(g, dg, 0)`, so
   `R(g, t·dg, t·ddg) = t·K(ddg) + t²·R(g, dg, 0)` (the symmetry of `g` is not used). Where the
   first jet vanishes (coordinates normal at the point to first order), `Γ = 0` and `R = K(ddg)`.
   Read on a perturbation `g = η + h` scaled by `t`, `K(∂∂h)` is the **linearized Riemann tensor**,
   the term of first order in `t`, and the rest carries `t²`.
4. **The curvature symmetries and the vacuum's Weyl tensor** (`CurvatureSymmetries`,
   `linearCurvature_symmetries`, `minkowski_mul_self`, `minkowski_inv`, `minkowski_det`,
   `ricci_minkowski`, `weylSymmetries_of_ricci`, `linearCurvature_weyl`, `riemannLower_minkowski`,
   `vacuum_weyl`, `tide_eq_electric`, `vacuum_tide`, `vacuum_raychaudhuriRate`,
   `tide_transpose`). For any `n`, `K(ddg)` is antisymmetric in each pair (no symmetry of the jet
   used) and has the pair exchange and the cyclic identity (both symmetries used). At `n = 4`,
   `g = η`, `dg = 0`, where the Ricci contraction `Σ_a η^(aa) R_abad` vanishes, the curvature built
   through the connection is a Weyl tensor (`WeylSymmetries`); its tide is the owner's electric
   part `E`, so the vacuum's tidal matrix is `E` by construction and leaves Raychaudhuri's rate as
   at `R = 0`. The tide of a tensor with the curvature symmetries is symmetric, as the owner's
   `rotation_law` asks of a tidal matrix.
5. **The weak field** (`spaceLift`, `weakJet`, `weakJet_symm`, `weakField_tide`,
   `weakField_electric`, `weakField_magnetic`, `weakField_ricci`, `weakField_vacuum_iff`,
   `weakField_curvature_split`, `weakField_weylQ`, `weakField_weyl`, `weakField_classify`,
   `weakField_poisson`, `weakField_raychaudhuriRate`, `weakField_focusing`). The static perturbation
   `h_00 = −2Φ`, `h_ij = −2Φδ_ij` (in coordinates `h_ab = −2Φδ_ab`) has the second jet
   `∂_e∂_f h_ab = −2Φ_ef δ_ab`, with `Φ_ef` the Hessian of `Φ` lifted by a zero time row and column
   (time derivatives zero). Its linearized curvature has the tide `R_(i0j0) = Φ_ij` and no magnetic
   part, and its Ricci tensor is `R_ab = ∇²Φ·δ_ab` (`R_00 = ∇²Φ`, `R_0j = 0`, `R_jk = ∇²Φ·δ_jk`),
   which vanishes iff `∇²Φ = Σ_i Φ_ii = 0`; then, `Φ` symmetric, it is a Weyl tensor of Petrov type
   I, D or O. Joined to `StressEnergy`: this Ricci tensor solves the trace-reversed field equation
   `Ric − ½(tr_η Ric)η = 8πG·T` with dust of density `ρ` iff `∇²Φ = 4πGρ`, Poisson's equation
   (forward through the owner's `dust_newtonian_source`). Raychaudhuri's rate at this tide is the
   rate at `R = 0` minus `∇²Φ`, so with Poisson, `G ≥ 0`, `ρ ≥ 0` and no rotation,
   `θ′ ≤ −θ²/3`: the source's density focuses.
6. **Witnesses from built metrics** (`waveH`, `waveGrad`, `waveProfile`, `waveMetric`,
   `waveFirstJet`, `waveHess`, `waveJet`, `waveMetric_zero`, `waveFirstJet_zero`,
   `hasDerivAt_waveH`, `hasDerivAt_waveGrad`, `hasDerivAt_waveFirstJet`, `hasDerivAt_waveMetric`,
   `wave_christoffel_rate`, `waveJet_symm`, `wave_ricci`, `wave_weyl`, `wave_curvature`,
   `wave_curvature_built`, `wave_ne_zero`, `waveTide`, `waveDrag`, `wave_electric`,
   `wave_magnetic`, `wave_classify`; `pointMassHessian`, `pointMassHessian_eq`,
   `pointMass_laplacian`, `pointMass_weyl`, `pointMass_tide`, `pointMass_classify`). The plane wave
   `ds² = −dt² + dx² + dy² + dz² + H(dt − dz)²`, `H = x² − y²`: its metric, first jet and second jet
   are read from `H` by Mathlib's derivatives along every coordinate line (the mixed rates
   included), and at the origin `g = η`, the first jet vanishes and the second is
   `∂_e∂_f H·(h/H)` with `∂_x∂_x H = 2`, `∂_y∂_y H = −2`. Its curvature there is nonzero, Ricci-flat
   and a Weyl tensor (the first nonzero instance of `WeylSymmetries` in the tree), with
   `E = diag(−1, 1, 0)` and `H = [[0, 1, 0], [1, 0, 0], [0, 0, 0]]`, of type N. The point mass's
   weak field `Φ = −M/r` at `(r, 0, 0)`, its Hessian given as the numbers `(M/r³)·diag(−2, 1, 1)`:
   `∇²Φ = 0` there, the linearized curvature is a Weyl tensor with `E = μ·diag(−2, 1, 1)`,
   `μ = M/r³` (`PetrovTypes`' Schwarzschild tide, its sign now fixed by the convention), of type D
   for `M ≠ 0`.

[proved-derived; formal-checked]

7. **The tide is a boost** (`tide_is_boost`). A tide with the curvature symmetries is `Geometry/Motion`'s
   boost at the comoving metric `1`, and its turn vanishes.

What is not claimed. The full Riemann tensor of a 2-jet whose first jet does not vanish is defined
and split (`K` plus a part quadratic in the first jet), but its Ricci tensor and its tide are not
read here (`Physics/Spacetime/FriedmannFluid` reads the Ricci tensor and the tide of the flat
Friedmann–Lemaître–Robertson–Walker jet, whose first jet does not vanish, and
`Physics/Spacetime/CurvedFriedmann` its full Riemann tensor; the symmetries, for a symmetric invertible
metric with symmetric jets, stand in `Physics/Spacetime/TidalScreen`), and the size of
the quadratic part as a perturbation shrinks (the continuity of `g⁻¹` at `η`) is not stated:
"linearized" means the term of first order in the scale `t`, and the weak field's and the point
mass's statements are about `K(∂∂h)`, not the full curvature of `η + h`, whose first jet `∂Φ` does
not vanish at `(r, 0, 0)`. The jets live at one
point: no metric field on a manifold, no change of coordinates (the tensor character of `R`) and no
construction of normal coordinates (the vanishing first jet is a hypothesis, or read off the plane
wave at its origin); that a second jet is symmetric (Schwarz's theorem for a `C²` metric) is the
hypothesis `JetSymm`. The point mass's Hessian is given as numbers at `(r, 0, 0)` (the classical
`∂_i∂_j(−M/r) = M(δ_ij − 3x_ix_j/r²)/r³`), not derived from `Φ` by Mathlib's derivatives. The
tide is read here at a point; the deviation equation `J″ = −RJ` along a general geodesic of a
torsion-free connection, in a parallel frame, with this module's `riemann` as its curvature, stands in
`GeodesicDeviation` (on the comoving congruence of the flat Friedmann–Lemaître–Robertson–Walker
metric it is also `FriedmannFluid.comoving_deviation`). The
Bianchi identity `∇R = 0` (it needs the 3-jet) and the Regge construction are not stated; the weak
field here meets only dust's trace-reversed equation, at first order, and a fluid-plus-thermal
constitution solving `G + Λg = κT` stands in `FriedmannFluid`. No
metric of type I, II or III is built. Another sign convention flips the sign of `R` or of the Ricci
tensor.

Read on the Swing. Free fall is the geodesic and gravity the connection (the Swing record §5.6): the
matrix `A_c` carries a vector a step along the direction `c`, and the curvature is the holonomy
rate of that transport, the commutator of two transports around a coordinate cell,
`R_cd = ∂_cA_d − ∂_dA_c + [A_c, A_d]` (`riemann_eq_commutator`; atlas
`cell.connection-route-return`: two routes return their curvature), which the 2-jet fixes. Where
the first jet vanishes the transports vanish and only their rates remain, and the curvature is the
second jet's linear form `K` (`riemannLower_of_firstJet_zero`). The tide is that curvature read by
the observer `e₀`, the stiffness in the deviation `J″ = −RJ`, and against the comoving metric it is
a self-adjoint boost of the deviation with no turn (`tide_is_boost`; atlas `motion.turn-boost-split`):
a tide strains a pair of neighbouring falls and does not turn it, so the owner's rotation law
`ω′ = −(Sω + ωS)` holds at it and a rotation-free instant has no rotation rate
(`rotation_rate_zero`). In the weak field the tide is Newton's `∂_i∂_jΦ`, and its trace, the
source's density through Poisson, is what focuses.

The computational object is the helical pair interaction read on a metric at a point: two
neighbouring geodesics are a pair, and the tide `R_(i0j0)` that the 2-jet builds is the stiffness
of the pair's deviation, its constitution at that point. Of the winding guide's six general objects
this touches the pair (the deviation between neighbouring strands, stiffened by the tide), the cell
holonomy (the curvature as the commutator of the connection's two transports around a coordinate
cell) and faces and placement (`E`, `H`, the Ricci contraction and the Petrov type as the observer's
faces of `R`); the helix, the tube (the congruence of `Raychaudhuri`, along which the deviation
equation is not derived here) and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.Spacetime.CurvatureJets

open Matrix
open Holonics.Physics.Spacetime.Raychaudhuri

variable {n : ℕ}

/-! ## 1. The 2-jet and its connection -/

section Jet

/-- [definition] A **first jet** at a point: `dg e a b = ∂_e g_ab`. -/
abbrev FirstJet (n : ℕ) := Fin n → Matrix (Fin n) (Fin n) ℝ

/-- [definition] A **second jet** at a point: `ddg e f a b = ∂_e∂_f g_ab`. -/
abbrev SecondJet (n : ℕ) := Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ

/-- [definition] A tensor with four indices, all down. -/
abbrev Tensor4 (n : ℕ) := Fin n → Fin n → Fin n → Fin n → ℝ

/-- [definition] **The second jet's symmetries**: in the two derivatives and in the metric pair. -/
structure JetSymm (ddg : SecondJet n) : Prop where
  deriv_comm : ∀ e f a b, ddg e f a b = ddg f e a b
  metric_symm : ∀ e f a b, ddg e f a b = ddg e f b a

/-- [definition] **The inverse's rate** on the jet: `∂_e g⁻¹ = −g⁻¹(∂_e g)g⁻¹`. -/
def inverseJet (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) : FirstJet n :=
  fun e => -(g⁻¹ * dg e * g⁻¹)

/-- [definition] **The Christoffel symbols** `Γ^a_bc = ½ g^(ad)(∂_b g_dc + ∂_c g_db − ∂_d g_bc)`. -/
def christoffel (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (a b c : Fin n) : ℝ :=
  2⁻¹ * ∑ d, g⁻¹ a d * (dg b d c + dg c d b - dg d b c)

/-- [definition] **Their first jet** `∂_eΓ^a_bc`, through `inverseJet` and the second jet. -/
def christoffelJet (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (ddg : SecondJet n)
    (e a b c : Fin n) : ℝ :=
  2⁻¹ * ∑ d, inverseJet g dg e a d * (dg b d c + dg c d b - dg d b c)
    + 2⁻¹ * ∑ d, g⁻¹ a d * (ddg e b d c + ddg e c d b - ddg e d b c)

/-- [definition] **The Riemann tensor**
`R^a_bcd = ∂_cΓ^a_db − ∂_dΓ^a_cb + Γ^a_ce Γ^e_db − Γ^a_de Γ^e_cb`. -/
def riemann (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (ddg : SecondJet n) : Tensor4 n :=
  fun a b c d => christoffelJet g dg ddg c a d b - christoffelJet g dg ddg d a c b
    + ∑ e, (christoffel g dg a c e * christoffel g dg e d b
      - christoffel g dg a d e * christoffel g dg e c b)

/-- [definition] **The lowered Riemann tensor** `R_abcd = g_ae R^e_bcd`. -/
def riemannLower (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (ddg : SecondJet n) :
    Tensor4 n :=
  fun a b c d => ∑ e, g a e * riemann g dg ddg e b c d

/-- [definition] **The second jet's linear form**
`K_abcd = ½(∂_b∂_c g_ad + ∂_a∂_d g_bc − ∂_a∂_c g_bd − ∂_b∂_d g_ac)`. -/
def linearCurvature (ddg : SecondJet n) : Tensor4 n :=
  fun a b c d => 2⁻¹ * (ddg b c a d + ddg a d b c - ddg a c b d - ddg b d a c)

/-- [definition] **The Ricci contraction** `R_bd = R^a_bad = g^(ae) R_ebad`. -/
def ricci (g : Matrix (Fin n) (Fin n) ℝ) (R : Tensor4 n) (b d : Fin n) : ℝ :=
  ∑ a, ∑ e, g⁻¹ a e * R e b a d

/-- [definition] **The connection's matrix** in the direction `c`: `A_c = (Γ^a_cb)_(ab)`. -/
def connection (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (c : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => christoffel g dg a c b

/-- [definition] **Its rate** along `e`: `∂_e A_c = (∂_eΓ^a_cb)_(ab)`. -/
def connectionJet (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (ddg : SecondJet n) (e c : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => christoffelJet g dg ddg e a c b

end Jet

section Rates

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- [proved-standard; formal-checked] **The inverse metric's rate** is `inverseJet`: `(G⁻¹)′ = −G⁻¹G′G⁻¹`. -/
theorem hasDerivAt_inv_metric {G : ℝ → Matrix (Fin n) (Fin n) ℝ} {dg : FirstJet n} {e : Fin n}
    {s : ℝ} (hG : HasDerivAt G (dg e) s) (hu : IsUnit (G s).det) :
    HasDerivAt (fun t => (G t)⁻¹) (inverseJet (G s) dg e) s := by
  have h := hasDerivAt_ringInverse_comp hG ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
  simp only [← Matrix.nonsing_inv_eq_ringInverse] at h
  exact h

/-- [proved-standard; formal-checked] **The Christoffel symbols' rate** along a coordinate line is
`christoffelJet`. -/
theorem hasDerivAt_christoffel {G : ℝ → Matrix (Fin n) (Fin n) ℝ} {dG : ℝ → FirstJet n}
    {ddg : SecondJet n} {e : Fin n} {s : ℝ} (hG : HasDerivAt G (dG s e) s) (hu : IsUnit (G s).det)
    (hdG : ∀ b a c, HasDerivAt (fun t => dG t b a c) (ddg e b a c) s) (a b c : Fin n) :
    HasDerivAt (fun t => christoffel (G t) (dG t) a b c)
      (christoffelJet (G s) (dG s) ddg e a b c) s := by
  have hinv : ∀ d, HasDerivAt (fun t => (G t)⁻¹ a d) (inverseJet (G s) (dG s) e a d) s := fun d =>
    hasDerivAt_linearMap (Matrix.entryLinearMap ℝ ℝ a d) (hasDerivAt_inv_metric hG hu)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun d _ =>
    (hinv d).mul (((hdG b d c).add (hdG c d b)).sub (hdG d b c))
  refine (hsum.const_mul (2⁻¹ : ℝ)).congr_deriv ?_
  simp only [christoffelJet, ← mul_add, ← Finset.sum_add_distrib, Pi.add_apply, Pi.sub_apply]

end Rates

/-! ## 2. Curvature is the connection's commutator -/

/-- [proved-standard; formal-checked] **The holonomy rate**: `R_cd = ∂_cA_d − ∂_dA_c + [A_c, A_d]`. -/
theorem riemann_eq_commutator (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (ddg : SecondJet n)
    (c d : Fin n) :
    Matrix.of (fun a b => riemann g dg ddg a b c d)
      = connectionJet g dg ddg c d - connectionJet g dg ddg d c
        + (connection g dg c * connection g dg d - connection g dg d * connection g dg c) := by
  ext a b
  simp only [riemann, connection, connectionJet, Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.mul_apply, Finset.sum_sub_distrib]

/-! ## 3. Linear in the second jet, quadratic in the first -/

section Split

/-- [proved-standard; formal-checked] `Σ_e g_ae Σ_f g^(ef) X_f = X_a` for an invertible `g`. -/
theorem contract_inv {g : Matrix (Fin n) (Fin n) ℝ} (hg : IsUnit g.det) (X : Fin n → ℝ) (a : Fin n) :
    ∑ e, g a e * ∑ f, g⁻¹ e f * X f = X a := by
  have h := congrFun (Matrix.mulVec_mulVec X g g⁻¹) a
  rw [Matrix.mul_nonsing_inv g hg, Matrix.one_mulVec] at h
  rw [← h]
  simp [Matrix.mulVec, dotProduct]

/-- [definition] The second jet's terms in `∂_cΓ_fdb − ∂_dΓ_fcb`, all indices down. -/
def jetCombo (ddg : SecondJet n) (f b c d : Fin n) : ℝ :=
  (ddg c d f b + ddg c b f d - ddg c f d b) - (ddg d c f b + ddg d b f c - ddg d f c b)

/-- [proved-standard; formal-checked] **The second jet enters linearly**:
`R^e_bcd(ddg) = R^e_bcd(0) + ½ g^(ef) jetCombo_fbcd`. -/
theorem riemann_eq_add (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (ddg : SecondJet n)
    (e b c d : Fin n) : riemann g dg ddg e b c d
      = riemann g dg 0 e b c d + 2⁻¹ * ∑ f, g⁻¹ e f * jetCombo ddg f b c d := by
  simp only [riemann, christoffelJet, jetCombo, Pi.zero_apply, Matrix.zero_apply, sub_self, add_zero,
    mul_zero, Finset.sum_const_zero, mul_sub, Finset.sum_sub_distrib]
  ring

/-- [proved-standard; formal-checked] With the jet's symmetries, `½ jetCombo = K`. -/
theorem jetCombo_eq {ddg : SecondJet n} (h : JetSymm ddg) (a b c d : Fin n) :
    2⁻¹ * jetCombo ddg a b c d = linearCurvature ddg a b c d := by
  simp only [jetCombo, linearCurvature]
  linarith [h.deriv_comm c d a b, h.deriv_comm c b a d, h.deriv_comm c a d b, h.metric_symm a c d b,
    h.deriv_comm d b a c, h.deriv_comm d a c b, h.metric_symm a d c b]

/-- [proved-standard; formal-checked] **The split**: `R(g, dg, ddg) = K(ddg) + R(g, dg, 0)` for an
invertible `g`. -/
theorem riemannLower_eq_add {g : Matrix (Fin n) (Fin n) ℝ} (hg : IsUnit g.det) (dg : FirstJet n)
    {ddg : SecondJet n} (h : JetSymm ddg) :
    riemannLower g dg ddg = linearCurvature ddg + riemannLower g dg 0 := by
  funext a b c d
  have h1 : riemannLower g dg ddg a b c d = riemannLower g dg 0 a b c d
      + 2⁻¹ * ∑ e, g a e * ∑ f, g⁻¹ e f * jetCombo ddg f b c d := by
    simp only [riemannLower, riemann_eq_add g dg ddg, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
    ring
  rw [h1, contract_inv hg, jetCombo_eq h]
  simp only [Pi.add_apply]
  ring

/-- [proved-standard; formal-checked] The inverse's rate is linear in the first jet. -/
theorem inverseJet_smul (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (t : ℝ) :
    inverseJet g (t • dg) = t • inverseJet g dg := by
  funext e
  simp [inverseJet]

/-- [proved-standard; formal-checked] The Christoffel symbols are linear in the first jet. -/
theorem christoffel_smul (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (t : ℝ) (a b c : Fin n) :
    christoffel g (t • dg) a b c = t * christoffel g dg a b c := by
  simp only [christoffel, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by ring

/-- [proved-standard; formal-checked] At a zero second jet, `∂Γ` is quadratic in the first jet. -/
theorem christoffelJet_smul (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (t : ℝ)
    (e a b c : Fin n) :
    christoffelJet g (t • dg) 0 e a b c = t ^ 2 * christoffelJet g dg 0 e a b c := by
  simp only [christoffelJet, inverseJet_smul, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
    Pi.zero_apply, Matrix.zero_apply, sub_self, add_zero, mul_zero, Finset.sum_const_zero,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by ring

/-- [proved-standard; formal-checked] At a zero second jet, `R^a_bcd` is quadratic in the first jet. -/
theorem riemann_smul (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (t : ℝ) (a b c d : Fin n) :
    riemann g (t • dg) 0 a b c d = t ^ 2 * riemann g dg 0 a b c d := by
  simp only [riemann, christoffelJet_smul, christoffel_smul, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun e _ => by ring

/-- [proved-standard; formal-checked] **The first jet enters quadratically**:
`R(g, t·dg, 0) = t²·R(g, dg, 0)`. -/
theorem riemannLower_smul (g : Matrix (Fin n) (Fin n) ℝ) (dg : FirstJet n) (t : ℝ) :
    riemannLower g (t • dg) 0 = t ^ 2 • riemannLower g dg 0 := by
  funext a b c d
  simp only [riemannLower, riemann_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => by ring

/-- [proved-standard; formal-checked] `K` is linear in the second jet. -/
theorem linearCurvature_smul (ddg : SecondJet n) (t : ℝ) :
    linearCurvature (t • ddg) = t • linearCurvature ddg := by
  funext a b c d
  simp only [linearCurvature, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- [proved-standard; formal-checked] A scaled symmetric second jet is symmetric. -/
theorem jetSymm_smul {ddg : SecondJet n} (h : JetSymm ddg) (t : ℝ) : JetSymm (t • ddg) where
  deriv_comm e f a b := by simp only [Pi.smul_apply, Matrix.smul_apply, h.deriv_comm e f a b]
  metric_symm e f a b := by simp only [Pi.smul_apply, Matrix.smul_apply, h.metric_symm e f a b]

/-- [proved-standard; formal-checked] **The linearized Riemann tensor**:
`R(g, t·dg, t·ddg) = t·K(ddg) + t²·R(g, dg, 0)`. -/
theorem riemannLower_scale {g : Matrix (Fin n) (Fin n) ℝ} (hg : IsUnit g.det) (dg : FirstJet n)
    {ddg : SecondJet n} (h : JetSymm ddg) (t : ℝ) :
    riemannLower g (t • dg) (t • ddg) = t • linearCurvature ddg + t ^ 2 • riemannLower g dg 0 := by
  rw [riemannLower_eq_add hg _ (jetSymm_smul h t), linearCurvature_smul, riemannLower_smul]

/-- [proved-standard; formal-checked] **A vanishing first jet has no connection**: `Γ = 0`. -/
theorem christoffel_zero (g : Matrix (Fin n) (Fin n) ℝ) : christoffel g 0 = 0 := by
  funext a b c
  simp [christoffel]

/-- [proved-standard; formal-checked] A vanishing first and second jet carry no curvature. -/
theorem riemannLower_zero (g : Matrix (Fin n) (Fin n) ℝ) : riemannLower g 0 0 = 0 := by
  funext a b c d
  simp [riemannLower, riemann, christoffelJet, christoffel, inverseJet]

/-- [proved-standard; formal-checked] **Where the first jet vanishes**, the curvature built through
the connection is `K(ddg)`. -/
theorem riemannLower_of_firstJet_zero {g : Matrix (Fin n) (Fin n) ℝ} (hg : IsUnit g.det)
    {ddg : SecondJet n} (h : JetSymm ddg) : riemannLower g 0 ddg = linearCurvature ddg := by
  rw [riemannLower_eq_add hg 0 h, riemannLower_zero, add_zero]

end Split

/-! ## 4. The curvature symmetries and the vacuum's Weyl tensor -/

section Vacuum

/-- [definition] **The algebraic curvature symmetries**, indices all down. -/
structure CurvatureSymmetries (R : Tensor4 n) : Prop where
  anti_left : ∀ a b c d, R b a c d = -R a b c d
  anti_right : ∀ a b c d, R a b d c = -R a b c d
  pair : ∀ a b c d, R c d a b = R a b c d
  cyclic : ∀ a b c d, R a b c d + R a c d b + R a d b c = 0

/-- [proved-standard; formal-checked] **`K` has the curvature symmetries** for a symmetric second jet. -/
theorem linearCurvature_symmetries {ddg : SecondJet n} (h : JetSymm ddg) :
    CurvatureSymmetries (linearCurvature ddg) where
  anti_left a b c d := by simp only [linearCurvature]; ring
  anti_right a b c d := by simp only [linearCurvature]; ring
  pair a b c d := by
    simp only [linearCurvature]
    linarith [h.deriv_comm d a c b, h.metric_symm a d c b, h.deriv_comm c b d a, h.metric_symm b c d a,
      h.deriv_comm c a d b, h.metric_symm a c d b, h.deriv_comm d b c a, h.metric_symm b d c a]
  cyclic a b c d := by
    simp only [linearCurvature]
    linarith [h.deriv_comm c b a d, h.metric_symm a d c b, h.metric_symm a c d b, h.deriv_comm d b a c,
      h.deriv_comm d c a b, h.metric_symm a b d c]

/-- [definition] **The orthonormal frame** `η = diag(−1, 1, 1, 1)`. -/
def minkowski : Matrix (Fin 4) (Fin 4) ℝ := diagonal minkowskiSign

/-- [proved-standard; formal-checked] `η² = 1`. -/
theorem minkowski_mul_self : minkowski * minkowski = 1 := by
  rw [minkowski, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  fin_cases a <;> simp [minkowskiSign]

/-- [proved-standard; formal-checked] `η⁻¹ = η`. -/
theorem minkowski_inv : minkowski⁻¹ = minkowski :=
  Matrix.inv_eq_left_inv minkowski_mul_self

/-- [proved-standard; formal-checked] `η` is invertible. -/
theorem minkowski_det : IsUnit minkowski.det := by
  have h := congrArg Matrix.det minkowski_mul_self
  rw [det_mul, det_one] at h
  exact IsUnit.of_mul_eq_one _ h

/-- [proved-standard; formal-checked] At `η` the Ricci contraction is `Σ_a η^(aa) R_abad`, the owner's
`η`-trace. -/
theorem ricci_minkowski (R : Tensor4 4) (b d : Fin 4) :
    ricci minkowski R b d = ∑ a, minkowskiSign a * R a b a d := by
  rw [ricci, minkowski_inv]
  simp [minkowski, diagonal_apply]

/-- [proved-standard; formal-checked] **Riemann is Weyl where the Ricci tensor vanishes.** -/
theorem weylSymmetries_of_ricci {R : Tensor4 4} (h : CurvatureSymmetries R)
    (hv : ∀ b d, ricci minkowski R b d = 0) : WeylSymmetries R :=
  ⟨h.anti_left, h.anti_right, h.pair, h.cyclic, fun b d => (ricci_minkowski R b d) ▸ hv b d⟩

/-- [proved-standard; formal-checked] A Ricci-flat `K` at `η` is a Weyl tensor. -/
theorem linearCurvature_weyl {ddg : SecondJet 4} (h : JetSymm ddg)
    (hv : ∀ b d, ricci minkowski (linearCurvature ddg) b d = 0) : WeylSymmetries (linearCurvature ddg) :=
  weylSymmetries_of_ricci (linearCurvature_symmetries h) hv

/-- [definition] **The tide** `R_ij = R_(i0j0)` read by the observer `u = e₀`. -/
def tide (R : Tensor4 4) (i j : Fin 3) : ℝ := R i.succ 0 j.succ 0

/-- [proved-standard; formal-checked] **The tide is the electric part** `E_ij = R_(0i0j)`. -/
theorem tide_eq_electric {R : Tensor4 4} (h : CurvatureSymmetries R) : tide R = electric R := by
  funext i j
  simp only [tide, electric]
  rw [h.anti_left, h.anti_right, neg_neg]

/-- [proved-standard; formal-checked] At `g = η` with no first jet, the curvature is `K(ddg)`. -/
theorem riemannLower_minkowski {ddg : SecondJet 4} (h : JetSymm ddg) :
    riemannLower minkowski 0 ddg = linearCurvature ddg :=
  riemannLower_of_firstJet_zero minkowski_det h

/-- [proved-standard; formal-checked] **A vacuum 2-jet's curvature is a Weyl tensor**, built through
the connection. -/
theorem vacuum_weyl {ddg : SecondJet 4} (h : JetSymm ddg)
    (hv : ∀ b d, ricci minkowski (riemannLower minkowski 0 ddg) b d = 0) :
    WeylSymmetries (riemannLower minkowski 0 ddg) := by
  rw [riemannLower_minkowski h] at hv ⊢
  exact linearCurvature_weyl h hv

/-- [proved-standard; formal-checked] **The tide built from the connection is `E`.** -/
theorem vacuum_tide {ddg : SecondJet 4} (h : JetSymm ddg) :
    tide (riemannLower minkowski 0 ddg) = electric (riemannLower minkowski 0 ddg) := by
  rw [riemannLower_minkowski h]
  exact tide_eq_electric (linearCurvature_symmetries h)

/-- [proved-standard; formal-checked] **The vacuum's built tide leaves Raychaudhuri's rate as at
`R = 0`.** -/
theorem vacuum_raychaudhuriRate {ddg : SecondJet 4} (h : JetSymm ddg)
    (hv : ∀ b d, ricci minkowski (riemannLower minkowski 0 ddg) b d = 0)
    (B : Matrix (Fin 3) (Fin 3) ℝ) :
    raychaudhuriRate B (Matrix.of (tide (riemannLower minkowski 0 ddg))) = raychaudhuriRate B 0 := by
  rw [vacuum_tide h]
  exact raychaudhuriRate_electric (vacuum_weyl h hv) B

/-- [proved-standard; formal-checked] **The tide is symmetric** (pair exchange). -/
theorem tide_transpose {R : Tensor4 4} (h : CurvatureSymmetries R) :
    (Matrix.of (tide R))ᵀ = Matrix.of (tide R) := by
  ext i j
  simp only [transpose_apply, Matrix.of_apply, tide]
  rw [← h.pair, h.anti_left, h.anti_right, neg_neg]

/-- [proved-derived; formal-checked] **The tide is a boost**: Motion's turn of it vanishes and its boost
is itself. -/
theorem tide_is_boost {R : Tensor4 4} (h : CurvatureSymmetries R) :
    Holonics.Geometry.Motion.turn 1 (Matrix.of (tide R)) = 0 ∧
      Holonics.Geometry.Motion.boost 1 (Matrix.of (tide R)) = Matrix.of (tide R) := by
  rw [← rotation_eq_turn, ← symPart_eq_boost, rotation_of_symm (tide_transpose h)]
  refine ⟨rfl, ?_⟩
  rw [symPart, tide_transpose h, ← two_smul ℝ, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

end Vacuum

/-! ## 5. The weak field -/

section WeakField

open Holonics.Physics.Spacetime.PetrovTypes

/-- [definition] A spatial Hessian lifted to four coordinates by a zero time row and column. -/
def spaceLift (Φ : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0; 0, Φ 0 0, Φ 0 1, Φ 0 2; 0, Φ 1 0, Φ 1 1, Φ 1 2; 0, Φ 2 0, Φ 2 1, Φ 2 2]

/-- [definition] **The static weak field's second jet**: `h_ab = −2Φδ_ab`, so
`∂_e∂_f h_ab = −2Φ_ef δ_ab`. -/
def weakJet (Φ : Matrix (Fin 3) (Fin 3) ℝ) : SecondJet 4 :=
  fun e f => (-2 * spaceLift Φ e f) • (1 : Matrix (Fin 4) (Fin 4) ℝ)

/-- [proved-standard; formal-checked] A symmetric Hessian gives a symmetric second jet. -/
theorem weakJet_symm {Φ : Matrix (Fin 3) (Fin 3) ℝ} (hΦ : Φᵀ = Φ) : JetSymm (weakJet Φ) where
  deriv_comm e f a b := by
    have hs : ∀ i j, Φ j i = Φ i j := fun i j => by rw [← transpose_apply Φ i j, hΦ]
    have h : spaceLift Φ e f = spaceLift Φ f e := by
      fin_cases e <;> fin_cases f <;> simp [spaceLift, hs]
    simp only [weakJet, h]
  metric_symm e f a b := by
    by_cases hab : a = b
    · rw [hab]
    · simp [weakJet, one_apply, hab, Ne.symm hab]

/-- [proved-standard; formal-checked] **Newton's tide**: the linearized `R_(i0j0)` is `Φ_ij`. -/
theorem weakField_tide (Φ : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.of (tide (linearCurvature (weakJet Φ))) = Φ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tide, linearCurvature, weakJet, spaceLift, one_apply]

/-- [proved-standard; formal-checked] The weak field's electric part is `Φ_ij`. -/
theorem weakField_electric (Φ : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix.of (electric (linearCurvature (weakJet Φ))) = Φ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [electric, linearCurvature, weakJet, spaceLift, one_apply]

/-- [proved-standard; formal-checked] **A static weak field drags no frame**: `H = 0`. -/
theorem weakField_magnetic (Φ : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    magnetic (linearCurvature (weakJet Φ)) i j = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [magnetic, leviCivita, Fin.sum_univ_three, linearCurvature, weakJet, spaceLift, one_apply]

/-- [proved-standard; formal-checked] **The weak field's Ricci tensor** is `R_ab = ∇²Φ·δ_ab`, so
`R₀₀ = ∇²Φ`. -/
theorem weakField_ricci (Φ : Matrix (Fin 3) (Fin 3) ℝ) (b d : Fin 4) :
    ricci minkowski (linearCurvature (weakJet Φ)) b d = Φ.trace * (1 : Matrix (Fin 4) (Fin 4) ℝ) b d := by
  rw [ricci_minkowski, trace_fin_three]
  fin_cases b <;> fin_cases d <;>
    simp [Fin.sum_univ_four, minkowskiSign, linearCurvature, weakJet, spaceLift, one_apply] <;> ring

/-- [proved-standard; formal-checked] **The weak field is a vacuum iff `∇²Φ = 0`.** -/
theorem weakField_vacuum_iff (Φ : Matrix (Fin 3) (Fin 3) ℝ) :
    (∀ b d, ricci minkowski (linearCurvature (weakJet Φ)) b d = 0) ↔ Φ.trace = 0 := by
  constructor
  · intro h
    simpa [weakField_ricci] using h 0 0
  · intro h b d
    rw [weakField_ricci, h, zero_mul]

/-- [proved-standard; formal-checked] The full curvature at the weak field's 2-jet is `K(∂∂h)` plus the
part quadratic in the first jet. -/
theorem weakField_curvature_split {Φ : Matrix (Fin 3) (Fin 3) ℝ} (hΦ : Φᵀ = Φ)
    {g : Matrix (Fin 4) (Fin 4) ℝ} (hg : IsUnit g.det) (dh : FirstJet 4) :
    riemannLower g dh (weakJet Φ) = linearCurvature (weakJet Φ) + riemannLower g dh 0 :=
  riemannLower_eq_add hg dh (weakJet_symm hΦ)

/-- [proved-standard; formal-checked] The weak field's `Q = E + iH` is `Φ + i·0`. -/
theorem weakField_weylQ (Φ : Matrix (Fin 3) (Fin 3) ℝ) :
    weylQ (linearCurvature (weakJet Φ)) = complexQ Φ 0 := by
  have hH : Matrix.of (magnetic (linearCurvature (weakJet Φ))) = 0 := by
    ext i j
    exact weakField_magnetic Φ i j
  rw [weylQ, weakField_electric, hH]

/-- [proved-standard; formal-checked] **A harmonic weak field's curvature is a Weyl tensor.** -/
theorem weakField_weyl {Φ : Matrix (Fin 3) (Fin 3) ℝ} (hΦ : Φᵀ = Φ) (hv : Φ.trace = 0) :
    WeylSymmetries (linearCurvature (weakJet Φ)) :=
  linearCurvature_weyl (weakJet_symm hΦ) ((weakField_vacuum_iff Φ).mpr hv)

/-- [proved-standard; formal-checked] A harmonic weak field is of Petrov type I, D or O. -/
theorem weakField_classify {Φ : Matrix (Fin 3) (Fin 3) ℝ} (hΦ : Φᵀ = Φ) (hv : Φ.trace = 0) :
    classify (weylQ (linearCurvature (weakJet Φ))) = .I ∨
      classify (weylQ (linearCurvature (weakJet Φ))) = .D ∨
      classify (weylQ (linearCurvature (weakJet Φ))) = .O :=
  classify_weylQ_of_magnetic_eq_zero (weakField_weyl hΦ hv) (weakField_magnetic Φ)

/-- [proved-standard; formal-checked] **Poisson's equation**: the weak field solves the trace-reversed
field equation with dust iff `∇²Φ = 4πGρ`. -/
theorem weakField_poisson (Φ : Matrix (Fin 3) (Fin 3) ℝ) (G ρ : ℝ) :
    StressEnergy.traceReversed (ricci minkowski (linearCurvature (weakJet Φ)))
        = (8 * Real.pi * G) • Holonics.Physics.ReceiverStressEnergy.perfectFluidTensor ρ 0
      ↔ Φ.trace = 4 * Real.pi * G * ρ := by
  constructor
  · intro h
    have h00 := StressEnergy.dust_newtonian_source h
    rwa [weakField_ricci, one_apply_eq, mul_one] at h00
  · intro h
    funext μ ν
    simp only [StressEnergy.traceReversed, StressEnergy.minkowskiTrace, weakField_ricci, h]
    fin_cases μ <;> fin_cases ν <;>
      simp [Fin.sum_univ_four, Holonics.Physics.ReceiverStressEnergy.minkowskiSign,
        Holonics.Physics.ReceiverStressEnergy.minkowskiMetricComponent,
        Holonics.Physics.ReceiverStressEnergy.perfectFluidTensor,
        Holonics.Physics.ReceiverStressEnergy.restObserver, one_apply]
    ring

/-- [proved-standard; formal-checked] **Raychaudhuri's rate at Newton's tide** is the rate at `R = 0`
minus `∇²Φ`. -/
theorem weakField_raychaudhuriRate (Φ B : Matrix (Fin 3) (Fin 3) ℝ) :
    raychaudhuriRate B (Matrix.of (tide (linearCurvature (weakJet Φ)))) = raychaudhuriRate B 0 - Φ.trace := by
  rw [weakField_tide]
  simp [raychaudhuriRate]

/-- [proved-standard; formal-checked] **The source's density focuses**: with Poisson, `G, ρ ≥ 0` and no
rotation, `θ′ ≤ −θ²/3`. -/
theorem weakField_focusing {Φ B : Matrix (Fin 3) (Fin 3) ℝ} {G ρ : ℝ} (hω : rotation B = 0)
    (hG : 0 ≤ G) (hρ : 0 ≤ ρ) (hP : Φ.trace = 4 * Real.pi * G * ρ) :
    raychaudhuriRate B (Matrix.of (tide (linearCurvature (weakJet Φ)))) ≤ -(expansion B ^ 2 / 3) := by
  have h := raychaudhuriRate_le (R := Matrix.of (tide (linearCurvature (weakJet Φ)))) hω
    (by rw [weakField_tide, hP]; positivity)
  simpa using h

end WeakField

/-! ## 6. Witnesses from built metrics -/

section Witnesses

open Holonics.Physics.Spacetime.PetrovTypes

/-- [definition] The plane wave's profile `H = x² − y²` at the point `(t, x, y, z)`. -/
def waveH (p : Fin 4 → ℝ) : ℝ := p 1 ^ 2 - p 2 ^ 2

/-- [definition] Its gradient `∂_e H = (0, 2x, −2y, 0)`. -/
def waveGrad (p : Fin 4 → ℝ) : Fin 4 → ℝ := ![0, 2 * p 1, -2 * p 2, 0]

/-- [definition] Its Hessian `∂_e∂_f H = diag(0, 2, −2, 0)`. -/
def waveHess : Matrix (Fin 4) (Fin 4) ℝ := diagonal ![0, 2, -2, 0]

/-- [definition] The polarization `(dt − dz)²`: `h_tt = h_zz = H`, `h_tz = h_zt = −H`. -/
def waveProfile : Matrix (Fin 4) (Fin 4) ℝ := !![1, 0, 0, -1; 0, 0, 0, 0; 0, 0, 0, 0; -1, 0, 0, 1]

/-- [definition] **The plane wave** `ds² = −dt² + dx² + dy² + dz² + H(dt − dz)²`. -/
def waveMetric (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ := minkowski + waveH p • waveProfile

/-- [definition] Its first jet `∂_e g = ∂_e H·(dt − dz)²`. -/
def waveFirstJet (p : Fin 4 → ℝ) : FirstJet 4 := fun e => waveGrad p e • waveProfile

/-- [definition] Its second jet `∂_e∂_f g = ∂_e∂_f H·(dt − dz)²`. -/
def waveJet : SecondJet 4 := fun e f => waveHess e f • waveProfile

/-- [proved-standard; formal-checked] At the origin the plane wave is `η`. -/
theorem waveMetric_zero : waveMetric 0 = minkowski := by simp [waveMetric, waveH]

/-- [proved-standard; formal-checked] At the origin its first jet vanishes. -/
theorem waveFirstJet_zero : waveFirstJet 0 = 0 := by
  funext e
  fin_cases e <;> simp [waveFirstJet, waveGrad]

/-- [proved-standard; formal-checked] `H`'s rate along the coordinate `e` is `waveGrad`. -/
theorem hasDerivAt_waveH (p : Fin 4 → ℝ) (e : Fin 4) :
    HasDerivAt (fun t : ℝ => waveH (p + t • Pi.single e 1)) (waveGrad p e) 0 := by
  have hf : ∀ t : ℝ, waveH (p + t • Pi.single e 1)
      = waveH p + t * waveGrad p e + t ^ 2 * (waveHess e e / 2) := fun t => by
    fin_cases e <;> simp [waveH, waveGrad, waveHess] <;> ring
  have h : HasDerivAt (fun t : ℝ => waveH p + t * waveGrad p e + t ^ 2 * (waveHess e e / 2))
      (waveGrad p e) 0 := by
    simpa using (((hasDerivAt_id' (0 : ℝ)).mul_const (waveGrad p e)).const_add (waveH p)).fun_add
      ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (waveHess e e / 2))
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall hf)

/-- [proved-standard; formal-checked] The gradient's rate along `e` is `waveHess`. -/
theorem hasDerivAt_waveGrad (p : Fin 4 → ℝ) (e f : Fin 4) :
    HasDerivAt (fun t : ℝ => waveGrad (p + t • Pi.single e 1) f) (waveHess e f) 0 := by
  have hf : ∀ t : ℝ, waveGrad (p + t • Pi.single e 1) f = waveGrad p f + t * waveHess e f := fun t => by
    fin_cases e <;> fin_cases f <;> simp [waveGrad, waveHess] <;> ring
  have h : HasDerivAt (fun t : ℝ => waveGrad p f + t * waveHess e f) (waveHess e f) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const (waveHess e f)).const_add (waveGrad p f)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall hf)

/-- [proved-standard; formal-checked] **The second jet is the first jet's rate**, at every point. -/
theorem hasDerivAt_waveFirstJet (p : Fin 4 → ℝ) (e f a b : Fin 4) :
    HasDerivAt (fun t : ℝ => waveFirstJet (p + t • Pi.single e 1) f a b) (waveJet e f a b) 0 := by
  simp only [waveFirstJet, waveJet, Matrix.smul_apply, smul_eq_mul]
  exact (hasDerivAt_waveGrad p e f).mul_const _

section WaveRates

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- [proved-standard; formal-checked] **The first jet is the metric's rate**, at every point. -/
theorem hasDerivAt_waveMetric (p : Fin 4 → ℝ) (e : Fin 4) :
    HasDerivAt (fun t : ℝ => waveMetric (p + t • Pi.single e 1)) (waveFirstJet p e) 0 :=
  ((hasDerivAt_waveH p e).smul_const waveProfile).const_add minkowski

/-- [proved-standard; formal-checked] **The built metric's Christoffel symbols** have the rate
`christoffelJet η 0 waveJet` at the origin. -/
theorem wave_christoffel_rate (e a b c : Fin 4) :
    HasDerivAt
      (fun t : ℝ => christoffel (waveMetric (t • Pi.single e 1)) (waveFirstJet (t • Pi.single e 1)) a b c)
      (christoffelJet minkowski 0 waveJet e a b c) 0 := by
  have hG := hasDerivAt_waveMetric 0 e
  have hd := fun b a c => hasDerivAt_waveFirstJet 0 e b a c
  simp only [zero_add] at hG hd
  have h := hasDerivAt_christoffel (G := fun t : ℝ => waveMetric (t • Pi.single e 1))
    (dG := fun t : ℝ => waveFirstJet (t • Pi.single e 1)) (s := 0) (by simpa using hG)
    (by simpa [waveMetric_zero] using minkowski_det) hd a b c
  simpa [waveMetric_zero, waveFirstJet_zero] using h

end WaveRates

/-- [proved-standard; formal-checked] The plane wave's second jet is symmetric. -/
theorem waveJet_symm : JetSymm waveJet where
  deriv_comm e f a b := by
    by_cases hef : e = f
    · rw [hef]
    · simp [waveJet, waveHess, hef, Ne.symm hef]
  metric_symm e f a b := by
    fin_cases a <;> fin_cases b <;> simp [waveJet, waveProfile]

/-- [proved-standard; formal-checked] At the origin the curvature built through the connection is
`K(waveJet)`. -/
theorem wave_curvature : riemannLower minkowski 0 waveJet = linearCurvature waveJet :=
  riemannLower_minkowski waveJet_symm

/-- [proved-standard; formal-checked] **The built metric's curvature at the origin** is `K(waveJet)`. -/
theorem wave_curvature_built :
    riemannLower (waveMetric 0) (waveFirstJet 0) waveJet = linearCurvature waveJet := by
  rw [waveMetric_zero, waveFirstJet_zero]
  exact wave_curvature

/-- [proved-standard; formal-checked] **The plane wave is Ricci-flat** (`∂_x²H + ∂_y²H = 0`). -/
theorem wave_ricci (b d : Fin 4) : ricci minkowski (linearCurvature waveJet) b d = 0 := by
  rw [ricci_minkowski]
  fin_cases b <;> fin_cases d <;>
    simp [Fin.sum_univ_four, minkowskiSign, linearCurvature, waveJet, waveHess, waveProfile]

/-- [proved-standard; formal-checked] **The plane wave's curvature is a Weyl tensor.** -/
theorem wave_weyl : WeylSymmetries (linearCurvature waveJet) :=
  linearCurvature_weyl waveJet_symm wave_ricci

/-- [proved-standard; formal-checked] **It is not zero**: `R_0101 = −1`. -/
theorem wave_ne_zero : linearCurvature waveJet 0 1 0 1 = -1 := by
  simp [linearCurvature, waveJet, waveHess, waveProfile]

/-- [definition] The plane wave's tide `E = diag(−1, 1, 0)`. -/
def waveTide : Matrix (Fin 3) (Fin 3) ℝ := !![-1, 0, 0; 0, 1, 0; 0, 0, 0]

/-- [definition] The plane wave's frame dragging `H = [[0, 1, 0], [1, 0, 0], [0, 0, 0]]`. -/
def waveDrag : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 1, 0, 0; 0, 0, 0]

/-- [proved-standard; formal-checked] The plane wave's electric part is `diag(−1, 1, 0)`. -/
theorem wave_electric : Matrix.of (electric (linearCurvature waveJet)) = waveTide := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [electric, linearCurvature, waveJet, waveHess, waveProfile, waveTide]

/-- [proved-standard; formal-checked] The plane wave's magnetic part is `waveDrag`. -/
theorem wave_magnetic : Matrix.of (magnetic (linearCurvature waveJet)) = waveDrag := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [magnetic, leviCivita, Fin.sum_univ_three, linearCurvature, waveJet, waveHess, waveProfile,
      waveDrag] <;> norm_num

/-- [proved-standard; formal-checked] **The plane wave is of type N.** -/
theorem wave_classify : classify (weylQ (linearCurvature waveJet)) = .N := by
  apply classify_eq_of_hasType (weylQ_trace wave_weyl)
  rw [weylQ, wave_electric, wave_magnetic, hasType_N_iff]
  refine ⟨Or.inl fun h => ?_, ?_, ?_⟩
  · have := congrFun (congrFun h 1) 1
    simp [waveTide] at this
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [waveTide, waveDrag]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [waveTide, waveDrag]

/-- [definition] **The point mass's Hessian** at `(r, 0, 0)`, given as the numbers
`∂_i∂_j(−M/r) = (M/r³)·diag(−2, 1, 1)`. -/
def pointMassHessian (M r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := (M / r ^ 3) • diagonal ![-2, 1, 1]

/-- [proved-standard; formal-checked] It is `PetrovTypes`' Schwarzschild tide at `μ = M/r³`. -/
theorem pointMassHessian_eq (M r : ℝ) : pointMassHessian M r = schwarzschildTide (M / r ^ 3) := rfl

/-- [proved-standard; formal-checked] **`∇²Φ = 0` there.** -/
theorem pointMass_laplacian (M r : ℝ) : (pointMassHessian M r).trace = 0 :=
  (schwarzschildTide_admissible _).2

/-- [proved-standard; formal-checked] **The point mass's linearized curvature is a Weyl tensor.** -/
theorem pointMass_weyl (M r : ℝ) : WeylSymmetries (linearCurvature (weakJet (pointMassHessian M r))) :=
  weakField_weyl (schwarzschildTide_admissible _).1 (schwarzschildTide_admissible _).2

/-- [proved-standard; formal-checked] **Its tide is `μ·diag(−2, 1, 1)`**, `μ = M/r³`. -/
theorem pointMass_tide (M r : ℝ) :
    Matrix.of (tide (linearCurvature (weakJet (pointMassHessian M r)))) = schwarzschildTide (M / r ^ 3) :=
  weakField_tide _

/-- [proved-standard; formal-checked] **The point mass is of type D** for `M ≠ 0`. -/
theorem pointMass_classify {M r : ℝ} (hM : M ≠ 0) (hr : r ≠ 0) :
    classify (weylQ (linearCurvature (weakJet (pointMassHessian M r)))) = .D := by
  rw [weakField_weylQ, pointMassHessian_eq]
  exact (classify_schwarzschild (div_ne_zero hM (pow_ne_zero 3 hr))).2

end Witnesses

end Holonics.Physics.Spacetime.CurvatureJets

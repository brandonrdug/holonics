import Holonics.Physics.Fluid.Cells
import Holonics.Objects.Pairing
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Fluid.ControlVolume: per-face returns, the joined balance, viscous heat and the coholon reading

[definition] Battle test 3 of rebuild step 6, K3 (#74). A **control volume** is a cubical cell of
`Fluid/Cells` with the grid's Euclidean metric declared. Each oriented face carries a **transported
normal** (`normal`, the Hodge reading of the face's orientation: `sgn(univ,i)·eᵢ` on a face missing
direction `i`, unit area) and a centroid. A per-face return is any value on the faces
(`faceRead` reads it against an oriented boundary chain); for a fluid with density `ρ`, velocity `u`
and stress `σ` the returns are

```text
mass flux        ρ (u·N)            momentum flux   ρ u (u·N)           traction   σ N
```

and **storage plus outflow equals the source** cell by cell.

[proved-derived; formal-checked]

* **Gauss on the cell** (grid metric, volume one): the transported normals close,
  `Σ_f ∂_f N_f = 0` (`closed_surface`), and their first moment is the identity,
  `Σ_f ∂_f N_f ⊗ x_f = 1` (`first_moment`).
* **The face returns are exact for an affine field** `u(x) = u₀ + G x` read at face centroids:
  the mass outflow is `ρ tr G` (`massOutflow_eq`), the momentum outflow is
  `ρ (G u_c + (tr G) u_c)`, i.e. `div(ρ u ⊗ u)` at the centre (`momentumOutflow_eq`), a uniform
  stress has no net traction (`tractionOutflow_eq_zero`), and the traction power is `σ : G`
  (`tractionPower_eq`).
* **The join**: the outflow of the joined cells is the sum of the two cells' outflows
  (`outflow_join`) and does not depend on the return placed on the shared face
  (`outflow_join_ignores_sharedFace`, from `Cells.join_cancels`), and for an affine field the
  joined box returns the full-volume divergence integral directly, `2ρ tr G`
  (`joined_massOutflow_eq`): storage plus outflow equals the source for the whole whenever it does
  for both parts (`balance_join`).
* **Newtonian stress and viscous heat.** For `σ = −pI + 2μ Def u + λ (tr G) I` the traction power
  splits into pressure work and dissipation, `σ : G = −p tr G + Φ` (`stress_power_split`), with
  `Φ = 2μ |Def u|² + λ (tr G)²` (`dissipation_eq`). Reversing the motion flips the pressure work
  and keeps `Φ` (`dissipation_even`, `stress_power_reversal`): `Φ` is the irreversible part, the
  **viscous heat handed to the thermal instance** (`viscousHeat`, a signed exact quantity), and
  `Φ ≥ 0` when `μ ≥ 0` and `nλ + 2μ ≥ 0` (`dissipation_nonneg`). On a cell the heat port receives
  exactly the traction power less the pressure work (`cell_heat_port`).
* **The coholon reading** (ELEMENTARY_OBJECTS, "The targets"): on a Holarchy cell complex the
  velocity is a coholon on edges, its vorticity is `du♭ = ∂₂ᵀu` (`vorticity`); the circulation
  around a bounding cycle is the vorticity flux (Stokes, owned by
  `Objects/Pairing.coordinate_stokes`); pressure is the exact part and is silent in vorticity and in
  every cycle's circulation (`pressure_vorticity_zero`, `pressure_circulation_zero`); for a
  vorticity-free velocity the circulation is a holonomy pairing of classes, unchanged by pressure
  and by moving the cycle across cells (owned by `Objects/Pairing.classPairing_representatives`).
  This is gauge and homology invariance at one instant, not Kelvin's theorem (conservation of
  circulation along a material loop in time), which is open. The Lamb term is the cross-current: the
  advection `G u` splits into the exact Bernoulli part `Gᵀu` and `(G − Gᵀ)u`
  (`advection_split`), which is `ω × u` in three dimensions (`lamb_eq_cross`) and does no work
  (`lamb_no_work`); the Bernoulli part is the exact difference of kinetic energy
  (`kinetic_difference`).

[counterexample; formal-checked]

* **`μ ≥ 0` is load-bearing**: a shear at `μ = −1` dissipates `−1` (`negative_shear_viscosity`).
* **`nλ + 2μ ≥ 0` is load-bearing**: a dilation at `μ = 1`, `λ = −1` in three dimensions
  dissipates `−3` (`negative_bulk_viscosity`).
* **Pressure work is not heat**: a compression with `p = 1` does work `+3` and its reversal `−3`
  (`pressureWork_not_heat`).
* **A closed velocity is not exact**: on the square with one hollow triangle
  (`Objects/Pairing.squareBd₁`), a vorticity-free velocity circulates `1` around the hole, so it is
  not a pressure gradient (`dormant_vortex`, composing `square_class_pairing_is_one`).

[open] The balances are read at one instant with uniform density and an affine velocity in the
cell, and `Balances` relates a storage rate supplied by the caller: no storage rate `ρ̇V` is
computed here independently of the outflow. Owed (#62): the exact time advance of the cell
(storage `ρ̇V` and the kinetic-energy change from a tick of the momentum balance, so that the
mechanical debit of the viscous heat is computed rather than supplied), the pressure solve
(incompressibility `tr G = 0` enforced by a projection whose multiplier is `p`), Kelvin's
conservation of circulation along a material loop, the discretization defect of a non-affine
field, and a native source-conforming fluid solver. The continuum cell balance with its analytic
trace is `HolonicsResearch/Fluid/NavierStokesLambCurrentCell` (not imported: research closure).
-/

noncomputable section

namespace Holonics.Physics.Fluid.ControlVolume

open Matrix Finsupp
open Holonics.Physics.Fluid.Cells

variable {n : ℕ}

/-! ## 1. Transported normals and the cell's Gauss identities -/

/-- [definition] **The transported normal** of a cell: the Hodge reading of its orientation in the
grid metric, `Σ_{i ∉ S} sgn(univ,i) eᵢ`. On a face missing direction `i` it is `sgn(univ,i) eᵢ`
with unit area. -/
def normal (f : Cell n) : Point n := ∑ i ∈ f.2ᶜ, (sgn Finset.univ i : ℚ) • unit i

/-- [definition] The centroid of a cell. -/
def centroid (f : Cell n) : Point n := f.1 + (1 / 2 : ℚ) • ind f.2

/-- [definition] **A per-face return read against an oriented chain**: `Σ_f x_f φ(f)`. -/
def faceRead {M : Type*} [AddCommGroup M] [Module ℚ M] (φ : Cell n → M) : Chain n →ₗ[ℤ] M :=
  Finsupp.linearCombination ℤ φ

theorem faceRead_cell {M : Type*} [AddCommGroup M] [Module ℚ M] (φ : Cell n → M) (c : Cell n) :
    faceRead φ (cell c) = φ c := by
  simp [faceRead, cell]

/-- The oriented boundary of a top cell, read face pair by face pair. -/
theorem faceRead_faces {M : Type*} [AddCommGroup M] [Module ℚ M] (φ : Cell n → M) (v : Point n) :
    faceRead φ (faces (v, Finset.univ)) =
      ∑ i, sgn Finset.univ i • (φ (v + unit i, Finset.univ.erase i) - φ (v, Finset.univ.erase i)) := by
  unfold faces
  simp only [map_sum, map_zsmul, map_sub, faceRead_cell]

theorem normal_face (w : Point n) (i : Fin n) :
    normal (w, Finset.univ.erase i) = (sgn Finset.univ i : ℚ) • unit i := by
  simp [normal, Finset.compl_erase]

theorem centroid_step (v : Point n) (i : Fin n) :
    centroid (v + unit i, Finset.univ.erase i) = centroid (v, Finset.univ) + (1 / 2 : ℚ) • unit i := by
  unfold centroid
  rw [← ind_erase_add_unit (Finset.mem_univ i)]
  simp only
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem centroid_base (v : Point n) (i : Fin n) :
    centroid (v, Finset.univ.erase i) = centroid (v, Finset.univ) - (1 / 2 : ℚ) • unit i := by
  unfold centroid
  rw [← ind_erase_add_unit (Finset.mem_univ i)]
  simp only
  funext j
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem sgn_mul_self (S : Finset (Fin n)) (i : Fin n) : sgn S i * sgn S i = 1 := by
  unfold sgn; rw [← pow_add, ← two_mul, pow_mul]; norm_num

theorem sgn_cast_mul_self (S : Finset (Fin n)) (i : Fin n) :
    (sgn S i : ℚ) * (sgn S i : ℚ) = 1 := by
  exact_mod_cast sgn_mul_self S i

/-- A signed pair difference: `sgn • (sgn • a) = a`. -/
theorem sgn_smul_sgn_smul {M : Type*} [AddCommGroup M] [Module ℚ M] (S : Finset (Fin n))
    (i : Fin n) (a : M) : sgn S i • ((sgn S i : ℚ) • a) = a := by
  rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, sgn_cast_mul_self, one_smul]

/-- [proved-derived; formal-checked] **The transported normals close**: `Σ_f ∂_f N_f = 0`. -/
theorem closed_surface (v : Point n) : faceRead normal (faces (v, Finset.univ)) = 0 := by
  rw [faceRead_faces]
  simp [normal_face]

/-- [proved-derived; formal-checked] **Their first moment is the volume times the identity**:
`Σ_f ∂_f N_f ⊗ x_f = 1` on the unit cell. -/
theorem first_moment (v : Point n) :
    faceRead (fun f => vecMulVec (normal f) (centroid f)) (faces (v, Finset.univ)) = 1 := by
  rw [faceRead_faces]
  have hterm : ∀ i : Fin n,
      sgn Finset.univ i • (vecMulVec (normal (v + unit i, Finset.univ.erase i))
          (centroid (v + unit i, Finset.univ.erase i)) -
        vecMulVec (normal (v, Finset.univ.erase i)) (centroid (v, Finset.univ.erase i))) =
      vecMulVec (unit i) (unit i) := by
    intro i
    rw [normal_face, normal_face, centroid_step, centroid_base, ← Int.cast_smul_eq_zsmul ℚ]
    have h := sgn_cast_mul_self Finset.univ i
    ext a b
    simp only [Matrix.smul_apply, Matrix.sub_apply, vecMulVec_apply, Pi.smul_apply, Pi.add_apply,
      Pi.sub_apply, smul_eq_mul]
    linear_combination (unit i a * unit i b) * h
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  ext a b
  simp only [Matrix.sum_apply, vecMulVec_apply, unit, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab; simp [Pi.single_apply]
  · rw [if_neg hab]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hai : a = i
    · subst hai; simp [Ne.symm hab]
    · simp [Pi.single_apply, hai]

/-! ## 2. Per-face returns of an affine field -/

/-- [definition] An affine velocity field `u(x) = u₀ + G x` (`G a b = ∂_b u_a`). -/
def affine (u₀ : Point n) (G : Matrix (Fin n) (Fin n) ℚ) (x : Point n) : Point n := u₀ + G *ᵥ x

/-- [definition] **The per-face returns** on a face with transported normal `N`: mass flux
`ρ (u·N)`, momentum flux `ρ u (u·N)` and traction `σ N`. -/
structure FaceReturn (n : ℕ) where
  mass : ℚ
  momentum : Point n
  traction : Point n

/-- [definition] The face return of density `ρ`, velocity `u` and stress `σ` at a face. -/
def faceReturn (ρ : ℚ) (u : Point n) (σ : Matrix (Fin n) (Fin n) ℚ) (N : Point n) : FaceReturn n :=
  ⟨ρ * (u ⬝ᵥ N), (ρ * (u ⬝ᵥ N)) • u, σ *ᵥ N⟩

/-- [definition] The affine field's mass flux on each face, read at its centroid. -/
def massFlux (ρ : ℚ) (u₀ : Point n) (G : Matrix (Fin n) (Fin n) ℚ) (f : Cell n) : ℚ :=
  (faceReturn ρ (affine u₀ G (centroid f)) 0 (normal f)).mass

/-- [definition] The affine field's momentum flux on each face, read at its centroid. -/
def momentumFlux (ρ : ℚ) (u₀ : Point n) (G : Matrix (Fin n) (Fin n) ℚ) (f : Cell n) : Point n :=
  (faceReturn ρ (affine u₀ G (centroid f)) 0 (normal f)).momentum

/-- [definition] A uniform stress's traction on each face. -/
def tractionFlux (σ : Matrix (Fin n) (Fin n) ℚ) (f : Cell n) : Point n :=
  (faceReturn 0 0 σ (normal f)).traction

/-- [definition] The traction power on each face: `(σN)·u` at its centroid. -/
def tractionPowerFlux (σ : Matrix (Fin n) (Fin n) ℚ) (u₀ : Point n) (G : Matrix (Fin n) (Fin n) ℚ)
    (f : Cell n) : ℚ :=
  (σ *ᵥ normal f) ⬝ᵥ affine u₀ G (centroid f)

theorem affine_step (u₀ : Point n) (G : Matrix (Fin n) (Fin n) ℚ) (x : Point n) (i : Fin n) (s : ℚ) :
    affine u₀ G (x + s • unit i) = affine u₀ G x + s • (G *ᵥ unit i) := by
  simp [affine, mulVec_add, mulVec_smul, add_assoc]

theorem affine_step_sub (u₀ : Point n) (G : Matrix (Fin n) (Fin n) ℚ) (x : Point n) (i : Fin n)
    (s : ℚ) : affine u₀ G (x - s • unit i) = affine u₀ G x - s • (G *ᵥ unit i) := by
  simp [affine, mulVec_sub, mulVec_smul, add_sub_assoc]

theorem dotProduct_unit (w : Point n) (i : Fin n) : w ⬝ᵥ unit i = w i := by
  simp [unit, dotProduct_single]

theorem mulVec_unit_apply (G : Matrix (Fin n) (Fin n) ℚ) (i a : Fin n) :
    (G *ᵥ unit i) a = G a i := by
  simp [unit, mulVec_single]

/-- [proved-derived; formal-checked] **The mass outflow of an affine field is `ρ tr G`** on the
unit cell: the face-centroid return is exact. -/
theorem massOutflow_eq (ρ : ℚ) (u₀ : Point n) (G : Matrix (Fin n) (Fin n) ℚ) (v : Point n) :
    faceRead (massFlux ρ u₀ G) (faces (v, Finset.univ)) = ρ * trace G := by
  rw [faceRead_faces]
  have hterm : ∀ i : Fin n,
      sgn Finset.univ i • (massFlux ρ u₀ G (v + unit i, Finset.univ.erase i) -
        massFlux ρ u₀ G (v, Finset.univ.erase i)) = ρ * G i i := by
    intro i
    simp only [massFlux, faceReturn]
    rw [normal_face, normal_face, centroid_step, centroid_base, affine_step, affine_step_sub,
      ← Int.cast_smul_eq_zsmul ℚ]
    have h := sgn_cast_mul_self Finset.univ i
    simp only [dotProduct_smul, add_dotProduct, sub_dotProduct, smul_dotProduct, dotProduct_unit,
      mulVec_unit_apply, smul_eq_mul]
    linear_combination (ρ * G i i) * h
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum]
  rfl

/-- [proved-derived; formal-checked] **The momentum outflow of an affine field is
`div(ρ u ⊗ u)` at the centre**: `ρ (G u_c + (tr G) u_c)`. -/
theorem momentumOutflow_eq (ρ : ℚ) (u₀ : Point n) (G : Matrix (Fin n) (Fin n) ℚ) (v : Point n) :
    faceRead (momentumFlux ρ u₀ G) (faces (v, Finset.univ)) =
      ρ • (G *ᵥ affine u₀ G (centroid (v, Finset.univ)) +
        trace G • affine u₀ G (centroid (v, Finset.univ))) := by
  set uc := affine u₀ G (centroid (v, Finset.univ))
  rw [faceRead_faces]
  have hterm : ∀ i : Fin n,
      sgn Finset.univ i • (momentumFlux ρ u₀ G (v + unit i, Finset.univ.erase i) -
        momentumFlux ρ u₀ G (v, Finset.univ.erase i)) =
        ρ • (uc i • (G *ᵥ unit i) + G i i • uc) := by
    intro i
    simp only [momentumFlux, faceReturn]
    rw [normal_face, normal_face, centroid_step, centroid_base, affine_step, affine_step_sub]
    rw [← Int.cast_smul_eq_zsmul ℚ]
    have h := sgn_cast_mul_self Finset.univ i
    funext a
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, dotProduct_smul,
      add_dotProduct, sub_dotProduct, smul_dotProduct, dotProduct_unit, mulVec_unit_apply]
    linear_combination (ρ * (uc i * G a i + G i i * uc a)) * h
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.smul_sum]
  congr 1
  funext a
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec_unit_apply,
    Finset.sum_add_distrib, trace, diag, Finset.sum_mul]
  rw [add_left_inj]
  simp only [mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- [proved-derived; formal-checked] **A uniform stress returns no net traction** (the normals
close). -/
theorem tractionOutflow_eq_zero (σ : Matrix (Fin n) (Fin n) ℚ) (v : Point n) :
    faceRead (tractionFlux σ) (faces (v, Finset.univ)) = 0 := by
  rw [faceRead_faces]
  simp [tractionFlux, faceReturn, normal_face]

/-- [definition] The Frobenius pairing `A : B = Σ A_ab B_ab`. -/
def frob (A B : Matrix (Fin n) (Fin n) ℚ) : ℚ := ∑ a, ∑ b, A a b * B a b

/-- [proved-derived; formal-checked] **The traction power of a uniform stress on an affine field is
`σ : G`** on the unit cell. -/
theorem tractionPower_eq (σ : Matrix (Fin n) (Fin n) ℚ) (u₀ : Point n) (G : Matrix (Fin n) (Fin n) ℚ)
    (v : Point n) :
    faceRead (tractionPowerFlux σ u₀ G) (faces (v, Finset.univ)) = frob σ G := by
  rw [faceRead_faces]
  have hterm : ∀ i : Fin n,
      sgn Finset.univ i • (tractionPowerFlux σ u₀ G (v + unit i, Finset.univ.erase i) -
        tractionPowerFlux σ u₀ G (v, Finset.univ.erase i)) = ∑ a, σ a i * G a i := by
    intro i
    simp only [tractionPowerFlux]
    rw [normal_face, normal_face, centroid_step, centroid_base, affine_step, affine_step_sub,
      ← Int.cast_smul_eq_zsmul ℚ]
    have h := sgn_cast_mul_self Finset.univ i
    have hdot : (σ *ᵥ unit i) ⬝ᵥ (G *ᵥ unit i) = ∑ a, σ a i * G a i := by
      simp [dotProduct, mulVec_unit_apply]
    simp only [mulVec_smul, dotProduct_add, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hdot]
    linear_combination (∑ a, σ a i * G a i) * h
  rw [Finset.sum_congr rfl fun i _ => hterm i, frob, Finset.sum_comm]

/-! ## 3. The join: storage plus outflow equals source for the whole -/

/-- [proved-derived; formal-checked] **The joined outflow is the sum of the parts' outflows**, for
every per-face return. -/
theorem outflow_join {M : Type*} [AddCommGroup M] [Module ℚ M] (φ : Cell n → M) (i : Fin n) :
    faceRead φ (boundary (cell cube + cell (neighbour i))) =
      faceRead φ (faces cube) + faceRead φ (faces (neighbour i)) := by
  rw [map_add, boundary_cell, boundary_cell, map_add]

/-- [proved-derived; formal-checked] **The shared face's return cancels exactly**: two per-face
returns that agree off the shared face give the same joined outflow, whatever each places on the
shared face (`Cells.join_cancels`). -/
theorem outflow_join_ignores_sharedFace {M : Type*} [AddCommGroup M] [Module ℚ M]
    (φ ψ : Cell n → M) (i : Fin n) (hagree : ∀ f, f ≠ sharedFace i → φ f = ψ f) :
    faceRead φ (boundary (cell cube + cell (neighbour i))) =
      faceRead ψ (boundary (cell cube + cell (neighbour i))) := by
  set x := boundary (cell cube + cell (neighbour i))
  have hx : x (sharedFace i) = 0 := join_cancels i
  simp only [faceRead, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun f hf => ?_
  have hne : f ≠ sharedFace i := by
    rintro rfl
    exact (Finsupp.mem_support_iff.mp hf) hx
  rw [hagree f hne]

/-- [proved-derived; formal-checked] **The joined box returns the full-volume divergence integral**:
for an affine field the mass outflow through the boundary of the cube joined to its neighbour is
`2ρ tr G`, `ρ div u` integrated over the joined volume `2`, read face by face with the shared face
cancelled. -/
theorem joined_massOutflow_eq (ρ : ℚ) (u₀ : Point n) (G : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) :
    faceRead (massFlux ρ u₀ G) (boundary (cell cube + cell (neighbour i))) = 2 * (ρ * trace G) := by
  rw [outflow_join]
  change faceRead (massFlux ρ u₀ G) (faces (0, Finset.univ)) +
    faceRead (massFlux ρ u₀ G) (faces (unit i, Finset.univ)) = _
  rw [massOutflow_eq, massOutflow_eq]
  ring

/-- [definition] **A cell balance**: storage rate plus outflow equals source. -/
def Balances {M : Type*} [AddCommGroup M] [Module ℚ M] (storage outflow source : M) : Prop :=
  storage + outflow = source

/-- [proved-derived; formal-checked] **Storage plus outflow equals the source for the whole** when
it does for the cube and its neighbour: the parts' storages and sources add, and the whole's
outflow is the sum of theirs with the shared face cancelled. -/
theorem balance_join {M : Type*} [AddCommGroup M] [Module ℚ M] (φ : Cell n → M) (i : Fin n)
    {sL sR qL qR : M} (hL : Balances sL (faceRead φ (faces cube)) qL)
    (hR : Balances sR (faceRead φ (faces (neighbour i))) qR) :
    Balances (sL + sR) (faceRead φ (boundary (cell cube + cell (neighbour i)))) (qL + qR) := by
  unfold Balances at *
  rw [outflow_join, ← hL, ← hR]
  abel

/-! ## 4. Newtonian stress, dissipation and the heat port -/

/-- [definition] The rate of deformation `Def u = (G + Gᵀ)/2`. -/
def strain (G : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ := (1 / 2 : ℚ) • (G + Gᵀ)

/-- [definition] The viscous stress `τ = 2μ Def u + λ (tr G) I`. -/
def viscousStress (μ lam : ℚ) (G : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  (2 * μ) • strain G + (lam * trace G) • (1 : Matrix (Fin n) (Fin n) ℚ)

/-- [definition] **The Newtonian stress** `σ = −pI + 2μ Def u + λ (tr G) I`. -/
def stress (p μ lam : ℚ) (G : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  (-p) • (1 : Matrix (Fin n) (Fin n) ℚ) + viscousStress μ lam G

/-- [definition] **The dissipation** `Φ = τ : G`. -/
def dissipation (μ lam : ℚ) (G : Matrix (Fin n) (Fin n) ℚ) : ℚ := frob (viscousStress μ lam G) G

/-- [definition] **The viscous heat handed to the thermal port** of a cell of volume `V`: the
signed exact quantity `V Φ`. -/
def viscousHeat (μ lam V : ℚ) (G : Matrix (Fin n) (Fin n) ℚ) : ℚ := V * dissipation μ lam G

theorem frob_one (G : Matrix (Fin n) (Fin n) ℚ) : frob 1 G = trace G := by
  simp only [frob, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, trace, diag]

theorem frob_add_left (A B G : Matrix (Fin n) (Fin n) ℚ) : frob (A + B) G = frob A G + frob B G := by
  simp only [frob, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem frob_smul_left (s : ℚ) (A G : Matrix (Fin n) (Fin n) ℚ) : frob (s • A) G = s * frob A G := by
  simp only [frob, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem frob_strain (G : Matrix (Fin n) (Fin n) ℚ) : frob (strain G) G = frob (strain G) (strain G) := by
  simp only [frob, strain, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
  have h : ∀ a b : Fin n, 1 / 2 * (G a b + G b a) * G a b =
      1 / 2 * (G a b + G b a) * (1 / 2 * (G a b + G b a)) +
        (1 / 4 * (G a b * G a b - G b a * G b a)) := fun a b => by ring
  simp only [h, Finset.sum_add_distrib]
  have hanti : ∑ a : Fin n, ∑ b : Fin n, 1 / 4 * (G a b * G a b - G b a * G b a) = 0 := by
    simp only [← Finset.mul_sum, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun a b => G b a * G b a)]
    ring
  rw [hanti, add_zero]

theorem trace_strain (G : Matrix (Fin n) (Fin n) ℚ) : trace (strain G) = trace G := by
  simp only [strain, trace_smul, trace_add, trace_transpose, smul_eq_mul]
  ring

/-- [proved-derived; formal-checked] **The dissipation** is `Φ = 2μ |Def u|² + λ (tr G)²`. -/
theorem dissipation_eq (μ lam : ℚ) (G : Matrix (Fin n) (Fin n) ℚ) :
    dissipation μ lam G = 2 * μ * frob (strain G) (strain G) + lam * trace G ^ 2 := by
  rw [dissipation, viscousStress, frob_add_left, frob_smul_left, frob_smul_left, frob_one,
    frob_strain]
  ring

/-- [proved-derived; formal-checked] **The traction power splits** into pressure work and
dissipation: `σ : G = −p tr G + Φ`. -/
theorem stress_power_split (p μ lam : ℚ) (G : Matrix (Fin n) (Fin n) ℚ) :
    frob (stress p μ lam G) G = -p * trace G + dissipation μ lam G := by
  rw [stress, frob_add_left, frob_smul_left, frob_one, dissipation]

/-- [proved-derived; formal-checked] **On a cell, the heat port receives the traction power less the
pressure work**: for a uniform Newtonian stress on an affine field, the face-by-face traction power
of the unit cell is `−p tr G + Φ`, and `Φ` is the viscous heat. -/
theorem cell_heat_port (p μ lam : ℚ) (u₀ : Point n) (G : Matrix (Fin n) (Fin n) ℚ) (v : Point n) :
    faceRead (tractionPowerFlux (stress p μ lam G) u₀ G) (faces (v, Finset.univ)) - (-p * trace G) =
      viscousHeat μ lam 1 G := by
  rw [tractionPower_eq, stress_power_split, viscousHeat]
  ring

/-- [proved-derived; formal-checked] **Dissipation is even under reversing the motion.** -/
theorem dissipation_even (μ lam : ℚ) (G : Matrix (Fin n) (Fin n) ℚ) :
    dissipation μ lam (-G) = dissipation μ lam G := by
  rw [dissipation_eq, dissipation_eq]
  simp only [strain, frob, trace_neg, transpose_neg, Matrix.smul_apply, Matrix.add_apply,
    Matrix.neg_apply, smul_eq_mul]
  ring_nf

/-- [proved-derived; formal-checked] **Reversing the motion flips the pressure work and keeps the
heat**: the traction power of `−G` is `p tr G + Φ(G)`, against `−p tr G + Φ(G)` for `G`. -/
theorem stress_power_reversal (p μ lam : ℚ) (G : Matrix (Fin n) (Fin n) ℚ) :
    frob (stress p μ lam (-G)) (-G) = -(-p * trace G) + dissipation μ lam G := by
  rw [stress_power_split, dissipation_even, trace_neg]
  ring

theorem frob_self_ge_diag (S : Matrix (Fin n) (Fin n) ℚ) : ∑ a, S a a ^ 2 ≤ frob S S := by
  unfold frob
  refine Finset.sum_le_sum fun a _ => ?_
  rw [sq]
  exact Finset.single_le_sum (f := fun b => S a b * S a b) (fun b _ => mul_self_nonneg _)
    (Finset.mem_univ a)

/-- [proved-derived; formal-checked] **`Φ ≥ 0` when `μ ≥ 0` and `nλ + 2μ ≥ 0`**: `|Def u|² ≥ (tr G)²/n`
(Cauchy–Schwarz on the diagonal), so `n Φ ≥ (2μ + nλ)(tr G)²`. -/
theorem dissipation_nonneg {μ lam : ℚ} (hμ : 0 ≤ μ) (hbulk : 0 ≤ n * lam + 2 * μ)
    (G : Matrix (Fin n) (Fin n) ℚ) : 0 ≤ dissipation μ lam G := by
  rw [dissipation_eq]
  have hcs : trace G ^ 2 ≤ n * frob (strain G) (strain G) := by
    have h1 : trace G ^ 2 ≤ (n : ℚ) * ∑ a, strain G a a ^ 2 := by
      rw [← trace_strain]
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
        (f := fun a => strain G a a)
      simpa [trace, diag] using this
    exact h1.trans (mul_le_mul_of_nonneg_left (frob_self_ge_diag _) (Nat.cast_nonneg n))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [frob, trace]
  · have hnq : (0 : ℚ) < n := Nat.cast_pos.mpr hn
    have key : 0 ≤ (n : ℚ) * (2 * μ * frob (strain G) (strain G) + lam * trace G ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hcs (by linarith : (0 : ℚ) ≤ 2 * μ),
        mul_nonneg hbulk (sq_nonneg (trace G))]
    exact (mul_nonneg_iff_of_pos_left hnq).mp key

/-- [definition] The shear `x₁ ↦ x₀` direction in three dimensions. -/
def shear3 : Matrix (Fin 3) (Fin 3) ℚ := !![0, 1, 0; 0, 0, 0; 0, 0, 0]

/-- [counterexample; formal-checked] **`μ ≥ 0` is load-bearing**: at `μ = −1`, `λ = 1`
(`3λ + 2μ = 1 ≥ 0`) a shear dissipates `−1`. -/
theorem negative_shear_viscosity : dissipation (-1) 1 shear3 = -1 := by
  rw [dissipation_eq]
  simp [shear3, frob, strain, trace, Fin.sum_univ_three]
  norm_num

/-- [counterexample; formal-checked] **`nλ + 2μ ≥ 0` is load-bearing**: at `μ = 1`, `λ = −1` in
three dimensions (`3λ + 2μ = −1`), a pure dilation dissipates `−3`. -/
theorem negative_bulk_viscosity : dissipation 1 (-1) (1 : Matrix (Fin 3) (Fin 3) ℚ) = -3 := by
  rw [dissipation_eq]
  simp [frob, strain, trace, Fin.sum_univ_three, Matrix.one_apply]
  norm_num

/-- [counterexample; formal-checked] **Pressure work is not heat**: at `p = 1` a unit compression
`G = −I` in three dimensions receives work `+3`, and its reversal `−3`. -/
theorem pressureWork_not_heat :
    -(1 : ℚ) * trace (-(1 : Matrix (Fin 3) (Fin 3) ℚ)) = 3 ∧
      -(1 : ℚ) * trace (1 : Matrix (Fin 3) (Fin 3) ℚ) = -3 := by
  simp [trace]

/-! ## 5. Velocity as a coholon: vorticity, pressure and the Lamb cross-current

The Stokes and holonomy readings of `circulation` are their owners' theorems, applied to
`circulation K u γ = u ⬝ᵥ γ` and `vorticity K u = K.d₂ᵀ *ᵥ u` without a wrapper here: the circulation
around the boundary `K.d₂ *ᵥ σ` of a face chain is the vorticity flux `vorticity K u ⬝ᵥ σ`
(`Objects/Pairing.coordinate_stokes`), and for a vorticity-free velocity and a cycle, adding a
pressure part and moving the cycle across faces leave the circulation unchanged
(`Objects/Pairing.classPairing_representatives K.d₁ K.d₂ K.dd`). -/

section Coholon

variable {𝕜 : Type*} [Field 𝕜] (K : HolarchyCore.CellComplex 𝕜)

/-- [definition] **The vorticity** of a velocity coholon on edges: `du♭ = ∂₂ᵀ u` on faces. -/
def vorticity (u : K.C₁ → 𝕜) : K.C₂ → 𝕜 := K.d₂ᵀ *ᵥ u

/-- [definition] **The circulation** of a velocity coholon around a 1-chain: `⟨u, γ⟩`. -/
def circulation (u : K.C₁ → 𝕜) (γ : K.C₁ → 𝕜) : 𝕜 := u ⬝ᵥ γ

/-- [definition] **The pressure part**: the exact coholon `d p = ∂₁ᵀ p` of a vertex potential. -/
def pressurePart (p : K.C₀ → 𝕜) : K.C₁ → 𝕜 := K.d₁ᵀ *ᵥ p

/-- [proved-derived; formal-checked] **Pressure is silent in vorticity** (`∂₁∂₂ = 0`). -/
theorem pressure_vorticity_zero (p : K.C₀ → 𝕜) : vorticity K (pressurePart K p) = 0 := by
  rw [vorticity, pressurePart, mulVec_mulVec, ← transpose_mul, K.dd, transpose_zero, zero_mulVec]

/-- [proved-derived; formal-checked] **Pressure has no circulation around a cycle**. -/
theorem pressure_circulation_zero (p : K.C₀ → 𝕜) {γ : K.C₁ → 𝕜} (hγ : K.d₁ *ᵥ γ = 0) :
    circulation K (pressurePart K p) γ = 0 := by
  rw [circulation, pressurePart, Holonics.Objects.Pairing.coordinate_stokes, hγ, dotProduct_zero]

end Coholon

/-- [counterexample; formal-checked] **A dormant vortex**: on the square with one filled and one
hollow triangle (`Objects/Pairing.squareBd₁`, `squareBd₂`), the velocity reading edge `e₃` has zero
vorticity and circulates `1` around the hole, so it is no pressure gradient and the hollow cycle
bounds nothing (`Objects/Pairing.square_class_pairing_is_one`). -/
theorem dormant_vortex :
    Holonics.Objects.Pairing.squareBd₂ᵀ *ᵥ Holonics.Objects.Pairing.squareCocycle = 0 ∧
      Holonics.Objects.Pairing.squareCocycle ⬝ᵥ Holonics.Objects.Pairing.squareCycle = 1 ∧
      (¬ ∃ p, Holonics.Objects.Pairing.squareBd₁ᵀ *ᵥ p = Holonics.Objects.Pairing.squareCocycle) := by
  obtain ⟨hpair, hnot, -, -⟩ := Holonics.Objects.Pairing.square_class_pairing_is_one
  refine ⟨Holonics.Objects.Pairing.squareCocycle_mem, ?_, hnot⟩
  rw [Holonics.Objects.Pairing.classPairing_mk] at hpair
  exact hpair

/-- [proved-derived; formal-checked] **Advection splits into the exact Bernoulli part and the Lamb
cross-current**: `G u = Gᵀ u + (G − Gᵀ) u`. -/
theorem advection_split (G : Matrix (Fin n) (Fin n) ℚ) (u : Point n) :
    G *ᵥ u = Gᵀ *ᵥ u + (G - Gᵀ) *ᵥ u := by
  rw [sub_mulVec]; abel

/-- [proved-derived; formal-checked] **The Lamb cross-current does no work**: `u · (G − Gᵀ) u = 0`. -/
theorem lamb_no_work (G : Matrix (Fin n) (Fin n) ℚ) (u : Point n) :
    u ⬝ᵥ ((G - Gᵀ) *ᵥ u) = 0 := by
  have hc : (u ᵥ* G) ⬝ᵥ u = u ⬝ᵥ (u ᵥ* G) := dotProduct_comm _ _
  rw [sub_mulVec, dotProduct_sub, mulVec_transpose, dotProduct_mulVec, hc, sub_self]

/-- [definition] The vorticity of a three-dimensional velocity gradient, `ω = curl u`. -/
def curl (G : Matrix (Fin 3) (Fin 3) ℚ) : Fin 3 → ℚ :=
  ![G 2 1 - G 1 2, G 0 2 - G 2 0, G 1 0 - G 0 1]

/-- [proved-derived; formal-checked] **In three dimensions the Lamb term is `ω × u`**. -/
theorem lamb_eq_cross (G : Matrix (Fin 3) (Fin 3) ℚ) (u : Fin 3 → ℚ) :
    (G - Gᵀ) *ᵥ u = crossProduct (curl G) u := by
  funext a
  fin_cases a <;>
    simp [cross_apply, curl, mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- [proved-derived; formal-checked] **The Bernoulli part is the exact kinetic-energy difference**:
for `u(x) = u₀ + G x`, `½|u(x+h)|² − ½|u(x)|² = (Gᵀ u(x))·h + ½|G h|²`. -/
theorem kinetic_difference (u₀ : Point n) (G : Matrix (Fin n) (Fin n) ℚ) (x h : Point n) :
    (1 / 2 : ℚ) * (affine u₀ G (x + h) ⬝ᵥ affine u₀ G (x + h)) -
        (1 / 2 : ℚ) * (affine u₀ G x ⬝ᵥ affine u₀ G x) =
      (Gᵀ *ᵥ affine u₀ G x) ⬝ᵥ h + (1 / 2 : ℚ) * ((G *ᵥ h) ⬝ᵥ (G *ᵥ h)) := by
  have hstep : affine u₀ G (x + h) = affine u₀ G x + G *ᵥ h := by
    simp [affine, mulVec_add, add_assoc]
  rw [hstep, mulVec_transpose, ← dotProduct_mulVec]
  simp only [add_dotProduct, dotProduct_add, dotProduct_comm (G *ᵥ h) (affine u₀ G x)]
  ring

section Audit

#print axioms closed_surface
#print axioms first_moment
#print axioms massOutflow_eq
#print axioms momentumOutflow_eq
#print axioms tractionPower_eq
#print axioms outflow_join_ignores_sharedFace
#print axioms joined_massOutflow_eq
#print axioms balance_join
#print axioms cell_heat_port
#print axioms dissipation_nonneg
#print axioms pressure_circulation_zero
#print axioms dormant_vortex
#print axioms lamb_eq_cross
#print axioms kinetic_difference

end Audit

end Holonics.Physics.Fluid.ControlVolume

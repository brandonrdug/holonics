import Holonics.Objects.Parametron
import Holonics.Aeon.Production.FirstLaw
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Resonating and emanating: the split of a drive against a constitution's modes

[definition] Rebuild step 3 (#145) and ELEMENTARY_OBJECTS "Emanation and resonance". A
constitution `(K, C)` (stiffness and capacity, `Objects/Parametron`, `Physics/CoupledIncidence`)
has at each eigenvalue `λ` its **mode space** `E_λ = ker(K − λC)`, whose nonzero members are the
generalized modes `K v = λ C v`. A drive profile `d` at a stated frequency `ω` (`λ = ω²`) splits as

```text
d = r + e,     r ∈ E_λ (resonating: rides the existing modes, RIDE),
               e ⟂_C E_λ (emanating: off-resonance or founding, FOUND)
```

[proved-derived; formal-checked] What is proved.

1. **The split is `C`-orthogonal and unique** (`split_exists_unique`, `split_orthogonal`) for a
   symmetric capacity form that is anisotropic (`c v v = 0 ⇒ v = 0`), in finite dimension.
2. **The effort of a drive is the effort of its emanating part** (`effort_split`), and it vanishes
   exactly when the emanating part does (`emanating_effort_eq_zero_iff`).
3. **The reactive quadratic form sees only the emanating part**:
   `λ c(d,d) − k(d,d) = λ c(e,e) − k(e,e)` whenever `r ∈ E_λ` (`reactive_split`), with no
   orthogonality needed.

The parametron join (`Node → ℝ`, the owners' `diagonalStorage`, `diagonalResponse`,
`IsGeneralizedMode`, `modeEnergy`):

4. The owners' constitution is a pair of symmetric storage forms (`storageForm`), and the mode
   space is exactly `IsGeneralizedMode` with zero (`isGeneralizedMode_iff`).
5. **The energy balance of a held motion.** To hold `x(t) = cos(ωt) d` the constitution's equation
   `C ẍ + K x = f` requires the port effort `f(t) = cos(ωt)(K − ω²C) d` (`holdingEffort_newton`),
   and the stored energy changes at exactly the power of that effort:
   `dE/dt = ⟨f(t), ẋ(t)⟩` (`hasDerivAt_modeEnergy`). This is what *work* means here: the time
   integral of the port power, which by the balance is the change of stored energy.
6. **RIDE is free.** Driving within the eigenspace keeps a generalized mode at the same frequency,
   its energy is conserved (`Parametron.modeEnergy_conserved`) and the holding effort is zero at
   every time (`resonant_drive_rides`).
7. **FOUND needs effort.** A nonzero emanating part needs a nonzero holding effort
   (`emanating_drive_needs_effort`), and the work it exchanges over `[0, t]` is
   `sin²(ωt)·(ω² S_C(e) − S_K(e))`, independent of the resonating part (`work_ledger`). A nonzero
   generalized mode's energy `ω² S_C(v)` is positive at every time (`founded_mode_energy_pos`).
8. **The energy balance of any motion, and founding from rest.** For every twice-differentiable
   motion `x` (continuous `ẍ`), the stored energy `E = S_C(ẋ) + S_K(x)` changes at exactly the port
   power `⟨C ẍ + K x, ẋ⟩` (`hasDerivAt_motionEnergy`), so `E(t) − E(0) = ∫₀ᵗ ⟨C ẍ + K x, ẋ⟩`
   (`motion_work_ledger`). From rest (`x 0 = 0`, `ẋ 0 = 0`), a motion that arrives at a phase of a
   nonzero generalized mode has received exactly the mode's energy `ω² S_C(v) > 0` as port work
   (`founding_from_rest_costs_work`).

The learning chart (`Aeon/Production/FirstLaw`):

9. **Gibbs' equality case** `D(p‖q) = 0 ⇔ p = q` (`klDivergence_eq_zero_iff`), so the first law's
   deposition onto the arrived source is zero exactly when the receiver already resonates with the
   source, and otherwise strictly negative by the KL excess (`deposition_onto_source_zero_iff`);
   `T · deposition` is its work on the levels (`FirstLaw.thermal_first_law`).

[counterexample; formal-checked] **Effort is not work** (`clamp_witness`). On the chain of
`Objects/Parametron.modeWitness` (modes at `ω² = 1, 3`), holding `(2, 0)` at `ω² = 2` needs the
nonzero effort `(0, −2)·cos(ωt)` on a node that never moves: the power is zero at every time and
the energy stays `4`. The emanating part always costs effort; whether it costs net work is the
quadratic form of item 7, which is `−2` on `(2, 0) = (1, 1) + (1, −1)` at `ω² = 1`
(`work_witness`). There is no fixed price per unit of emanation.
-/

noncomputable section

namespace Holonics.Compression.Core.Resonance

open scoped BigOperators

/-! ## 1. The split -/

section Split

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- [definition] The **mode space** of the constitution `(k, c)` at eigenvalue `eigen`: the
kernel of `k − eigen · c` as a map to coholons. -/
def modeSpace (k c : LinearMap.BilinForm 𝕜 V) (eigen : 𝕜) : Submodule 𝕜 V :=
  LinearMap.ker (k - eigen • c)

theorem mem_modeSpace (k c : LinearMap.BilinForm 𝕜 V) (eigen : 𝕜) (v : V) :
    v ∈ modeSpace k c eigen ↔ ∀ w, k v w = eigen * c v w := by
  simp only [modeSpace, LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, sub_eq_zero]

/-- [definition] The **emanation space**: the `c`-orthogonal complement of the mode space. -/
def emanationSpace (k c : LinearMap.BilinForm 𝕜 V) (eigen : 𝕜) : Submodule 𝕜 V :=
  c.orthogonal (modeSpace k c eigen)

/-- [proved-derived; formal-checked] The two parts of a split are `c`-orthogonal, in both orders
when `c` is symmetric. -/
theorem split_orthogonal (k c : LinearMap.BilinForm 𝕜 V) (eigen : 𝕜)
    (hsymm : ∀ x y, c x y = c y x) {r e : V} (hr : r ∈ modeSpace k c eigen)
    (he : e ∈ emanationSpace k c eigen) : c r e = 0 ∧ c e r = 0 := by
  have h := LinearMap.BilinForm.mem_orthogonal_iff.mp he r hr
  exact ⟨h, by rw [hsymm]; exact h⟩

theorem modeSpace_disjoint_emanationSpace (k c : LinearMap.BilinForm 𝕜 V) (eigen : 𝕜)
    (hanis : ∀ v, c v v = 0 → v = 0) :
    Disjoint (modeSpace k c eigen) (emanationSpace k c eigen) := by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  exact hanis x (LinearMap.BilinForm.mem_orthogonal_iff.mp hx' x hx)

/-- [proved-derived; formal-checked] **The resonating/emanating split exists and is unique.** For a
symmetric anisotropic capacity form in finite dimension, every drive is uniquely a mode-space part
plus a `c`-orthogonal part. -/
theorem split_exists_unique [FiniteDimensional 𝕜 V] (k c : LinearMap.BilinForm 𝕜 V) (eigen : 𝕜)
    (hsymm : ∀ x y, c x y = c y x) (hanis : ∀ v, c v v = 0 → v = 0) (d : V) :
    ∃ r ∈ modeSpace k c eigen, ∃ e ∈ emanationSpace k c eigen, d = r + e ∧
      ∀ r' ∈ modeSpace k c eigen, ∀ e' ∈ emanationSpace k c eigen, d = r' + e' →
        r' = r ∧ e' = e := by
  have hrefl : c.IsRefl := fun x y h => by rw [hsymm]; exact h
  have hcompl : IsCompl (modeSpace k c eigen) (emanationSpace k c eigen) :=
    (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hrefl).mpr
      (modeSpace_disjoint_emanationSpace k c eigen hanis)
  obtain ⟨u, v, huv, huniq⟩ := Submodule.existsUnique_add_of_isCompl hcompl d
  refine ⟨u, u.2, v, v.2, huv.symm, ?_⟩
  intro r' hr' e' he' hd
  have := huniq ⟨r', hr'⟩ ⟨e', he'⟩ hd.symm
  exact ⟨congrArg Subtype.val this.1, congrArg Subtype.val this.2⟩

/-- [proved-derived; formal-checked] **The effort of a drive is the effort of its emanating part**:
the resonating part is annihilated by `k − eigen · c`. -/
theorem effort_split (k c : LinearMap.BilinForm 𝕜 V) (eigen : 𝕜) {r : V}
    (hr : r ∈ modeSpace k c eigen) (e : V) :
    (k - eigen • c) (r + e) = (k - eigen • c) e := by
  rw [map_add, LinearMap.mem_ker.mp hr, zero_add]

/-- [proved-derived; formal-checked] **An emanating part needs zero effort only when it is zero.** -/
theorem emanating_effort_eq_zero_iff (k c : LinearMap.BilinForm 𝕜 V) (eigen : 𝕜)
    (hanis : ∀ v, c v v = 0 → v = 0) {e : V} (he : e ∈ emanationSpace k c eigen) :
    (k - eigen • c) e = 0 ↔ e = 0 := by
  constructor
  · intro h
    exact (Submodule.disjoint_def.mp (modeSpace_disjoint_emanationSpace k c eigen hanis)) e
      (LinearMap.mem_ker.mpr h) he
  · rintro rfl
    exact map_zero _

/-- [proved-derived; formal-checked] **The reactive quadratic form sees only the emanating part.**
With symmetric `k`, `c` and `r` in the mode space, `eigen·c(d,d) − k(d,d)` for `d = r + e` equals
`eigen·c(e,e) − k(e,e)`. -/
theorem reactive_split (k c : LinearMap.BilinForm 𝕜 V) (eigen : 𝕜)
    (hk : ∀ x y, k x y = k y x) (hc : ∀ x y, c x y = c y x) {r : V}
    (hr : r ∈ modeSpace k c eigen) (e : V) :
    eigen * c (r + e) (r + e) - k (r + e) (r + e) = eigen * c e e - k e e := by
  have hmode := (mem_modeSpace k c eigen r).mp hr
  have h1 := hmode r
  have h2 := hmode e
  have h3 : k e r = eigen * c r e := by rw [hk]; exact h2
  have h4 : c e r = c r e := hc e r
  simp only [map_add, LinearMap.add_apply]
  rw [h1, h2, h3, h4]
  ring

end Split

/-! ## 2. The parametron constitution as a pair of storage forms -/

section Parametron

open Holonics.Physics.HolonicComplexParametron
open Holonics.Objects.Parametron

variable {Node Branch : Type*} [Fintype Node] [Fintype Branch]

omit [Fintype Branch] in
theorem branchDrop_add (incidence : Branch → Node → ℝ) (u v : Node → ℝ) (b : Branch) :
    branchDrop incidence (u + v) b = branchDrop incidence u b + branchDrop incidence v b := by
  simp only [branchDrop, Pi.add_apply, mul_add, Finset.sum_add_distrib]

omit [Fintype Branch] in
theorem branchDrop_smul (incidence : Branch → Node → ℝ) (a : ℝ) (u : Node → ℝ) (b : Branch) :
    branchDrop incidence (a • u) b = a * branchDrop incidence u b := by
  simp only [branchDrop, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- [definition] The **storage form** `⟨u, v⟩_W = Σ_b W_b (Bu)_b (Bv)_b` of branch weights `W`:
the bilinear form whose diagonal is twice `diagonalStorage` and whose pairing with a state is
`diagonalResponse`. -/
def storageForm (weight : Branch → ℝ) (incidence : Branch → Node → ℝ) :
    LinearMap.BilinForm ℝ (Node → ℝ) :=
  LinearMap.mk₂ ℝ
    (fun u v => ∑ b, weight b * branchDrop incidence u b * branchDrop incidence v b)
    (by
      intro u u' v
      simp only [branchDrop_add, mul_add, add_mul, Finset.sum_add_distrib])
    (by
      intro a u v
      simp only [branchDrop_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)
    (by
      intro u v v'
      simp only [branchDrop_add, mul_add, Finset.sum_add_distrib])
    (by
      intro a u v
      simp only [branchDrop_smul, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)

theorem storageForm_apply (weight : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (u v : Node → ℝ) :
    storageForm weight incidence u v =
      ∑ b, weight b * branchDrop incidence u b * branchDrop incidence v b := rfl

theorem storageForm_symm (weight : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (u v : Node → ℝ) : storageForm weight incidence u v = storageForm weight incidence v u := by
  simp only [storageForm_apply]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- [proved-derived; formal-checked] The diagonal of the storage form is twice the owners'
`diagonalStorage`. -/
theorem storageForm_self (weight : Branch → ℝ) (incidence : Branch → Node → ℝ) (v : Node → ℝ) :
    storageForm weight incidence v v = 2 * diagonalStorage weight incidence v := by
  simp only [storageForm_apply, diagonalStorage, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- [proved-derived; formal-checked] Pairing a state with the owners' `diagonalResponse` of
another is the storage form. -/
theorem storageForm_eq_pairing (weight : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (u v : Node → ℝ) :
    storageForm weight incidence u v = ∑ node, u node * diagonalResponse weight incidence v node := by
  simp only [storageForm_apply, diagonalResponse, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [show branchDrop incidence u b = ∑ node, incidence b node * u node from rfl,
    Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem diagonalResponse_add (weight : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (u v : Node → ℝ) (node : Node) :
    diagonalResponse weight incidence (u + v) node =
      diagonalResponse weight incidence u node + diagonalResponse weight incidence v node := by
  simp only [diagonalResponse, branchDrop_add, mul_add, Finset.sum_add_distrib]

theorem diagonalResponse_smul (weight : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (a : ℝ) (v : Node → ℝ) (node : Node) :
    diagonalResponse weight incidence (fun n => a * v n) node =
      a * diagonalResponse weight incidence v node := by
  have : (fun n => a * v n) = a • v := rfl
  simp only [this, diagonalResponse, branchDrop_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- [proved-derived; formal-checked] **The mode space of the owners' constitution** is the set of
states with `K v = eigen · C v` at every node. -/
theorem mem_modeSpace_iff_response (stiffness capacity : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (eigen : ℝ) (v : Node → ℝ) :
    v ∈ modeSpace (storageForm stiffness incidence) (storageForm capacity incidence) eigen ↔
      ∀ node, diagonalResponse stiffness incidence v node =
        eigen * diagonalResponse capacity incidence v node := by
  classical
  rw [mem_modeSpace]
  constructor
  · intro h node
    have := h (Pi.single node 1)
    rw [storageForm_symm stiffness, storageForm_eq_pairing, storageForm_symm capacity,
      storageForm_eq_pairing] at this
    simpa [Pi.single_apply] using this
  · intro h w
    rw [storageForm_symm stiffness, storageForm_eq_pairing, storageForm_symm capacity,
      storageForm_eq_pairing, Finset.mul_sum]
    exact Finset.sum_congr rfl fun node _ => by rw [h node]; ring

/-- [proved-derived; formal-checked] `IsGeneralizedMode` is exactly a nonzero member of the mode
space. -/
theorem isGeneralizedMode_iff (stiffness capacity : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (eigen : ℝ) (v : Node → ℝ) :
    IsGeneralizedMode stiffness capacity incidence eigen v ↔
      v ≠ 0 ∧ v ∈ modeSpace (storageForm stiffness incidence) (storageForm capacity incidence)
        eigen := by
  rw [mem_modeSpace_iff_response]
  rfl

/-! ### The held motion `x(t) = cos(ωt) d` -/

/-- [definition] The **holding effort**: the port effort `f = C ẍ + K x` needed to hold
`x(t) = cos(ωt) d` against the constitution, `cos(ωt)(K − ω²C) d`. -/
def holdingEffort (stiffness capacity : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (ω : ℝ) (d : Node → ℝ) (t : ℝ) (node : Node) : ℝ :=
  Real.cos (ω * t) * (diagonalResponse stiffness incidence d node -
    ω ^ 2 * diagonalResponse capacity incidence d node)

/-- [proved-derived; formal-checked] **The holding effort is Newton's residual** `C ẍ + K x` of the
motion `x(t) = cos(ωt) d`, with `ẍ(t) = −ω² cos(ωt) d`. -/
theorem holdingEffort_newton (stiffness capacity : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (ω : ℝ) (d : Node → ℝ) (t : ℝ) (node : Node) :
    holdingEffort stiffness capacity incidence ω d t node =
      diagonalResponse capacity incidence (fun n => -(ω ^ 2 * Real.cos (ω * t)) * d n) node +
        diagonalResponse stiffness incidence (fun n => Real.cos (ω * t) * d n) node := by
  rw [diagonalResponse_smul, diagonalResponse_smul, holdingEffort]
  ring

/-- [proved-derived; formal-checked] The stored energy of the held motion in closed form. -/
theorem modeEnergy_closed (stiffness capacity : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (ω : ℝ) (d : Node → ℝ) (t : ℝ) :
    modeEnergy stiffness capacity incidence ω d t =
      (ω * Real.sin (ω * t)) ^ 2 * diagonalStorage capacity incidence d +
        Real.cos (ω * t) ^ 2 * diagonalStorage stiffness incidence d := by
  simp only [modeEnergy, diagonalStorage_smul]
  ring

/-- [proved-derived; formal-checked] **The energy balance of the held motion**: the stored energy
changes at exactly the power of the holding effort, `dE/dt = ⟨f(t), ẋ(t)⟩`, with
`ẋ(t) = −ω sin(ωt) d`. -/
theorem hasDerivAt_modeEnergy (stiffness capacity : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (ω : ℝ) (d : Node → ℝ) (t : ℝ) :
    HasDerivAt (fun τ => modeEnergy stiffness capacity incidence ω d τ)
      (∑ node, holdingEffort stiffness capacity incidence ω d t node *
        (-(ω * Real.sin (ω * t)) * d node)) t := by
  set SC := diagonalStorage capacity incidence d
  set SK := diagonalStorage stiffness incidence d
  have hlin : HasDerivAt (fun τ => ω * τ) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  have hs : HasDerivAt (fun τ => Real.sin (ω * τ)) (Real.cos (ω * t) * ω) t :=
    (Real.hasDerivAt_sin (ω * t)).comp t hlin
  have hc : HasDerivAt (fun τ => Real.cos (ω * τ)) (-Real.sin (ω * t) * ω) t :=
    (Real.hasDerivAt_cos (ω * t)).comp t hlin
  have hE := (((hs.const_mul ω).pow 2).mul_const SC).add ((hc.pow 2).mul_const SK)
  have hfun : (fun τ => modeEnergy stiffness capacity incidence ω d τ) =
      (fun τ => (ω * Real.sin (ω * τ)) ^ 2 * SC + Real.cos (ω * τ) ^ 2 * SK) := by
    funext τ
    exact modeEnergy_closed stiffness capacity incidence ω d τ
  rw [hfun]
  refine hE.congr_deriv ?_
  have hK := sum_mul_diagonalResponse stiffness incidence d
  have hC := sum_mul_diagonalResponse capacity incidence d
  have hpower : ∑ node, holdingEffort stiffness capacity incidence ω d t node *
        (-(ω * Real.sin (ω * t)) * d node) =
      -(ω * Real.sin (ω * t) * Real.cos (ω * t)) *
        (∑ node, d node * diagonalResponse stiffness incidence d node -
          ω ^ 2 * ∑ node, d node * diagonalResponse capacity incidence d node) := by
    simp only [holdingEffort, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hpower, hK, hC]
  push_cast
  ring

/-- [proved-derived; formal-checked] **The work ledger.** For `d = r + e` with `r` in the mode space
at `ω²`, the energy exchanged with the port over `[0, t]` is `sin²(ωt)·(ω² S_C(e) − S_K(e))`: the
resonating part contributes nothing. -/
theorem work_ledger (stiffness capacity : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (ω : ℝ) {r : Node → ℝ}
    (hr : r ∈ modeSpace (storageForm stiffness incidence) (storageForm capacity incidence) (ω ^ 2))
    (e : Node → ℝ) (t : ℝ) :
    modeEnergy stiffness capacity incidence ω (r + e) t -
        modeEnergy stiffness capacity incidence ω (r + e) 0 =
      Real.sin (ω * t) ^ 2 *
        (ω ^ 2 * diagonalStorage capacity incidence e - diagonalStorage stiffness incidence e) := by
  have hreact := reactive_split (storageForm stiffness incidence) (storageForm capacity incidence)
    (ω ^ 2) (storageForm_symm stiffness incidence) (storageForm_symm capacity incidence) hr e
  rw [storageForm_self, storageForm_self, storageForm_self, storageForm_self] at hreact
  have htrig := Real.sin_sq_add_cos_sq (ω * t)
  rw [modeEnergy_closed, modeEnergy_closed]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero]
  have hd : ω ^ 2 * diagonalStorage capacity incidence (r + e) -
      diagonalStorage stiffness incidence (r + e) =
      ω ^ 2 * diagonalStorage capacity incidence e - diagonalStorage stiffness incidence e := by
    linarith
  linear_combination Real.sin (ω * t) ^ 2 * hd +
    diagonalStorage stiffness incidence (r + e) * htrig

/-- [proved-derived; formal-checked] **RIDE is free.** Driving an existing motion `v` in the mode
space at `ω²` by a resonant increment `δ` in the same mode space keeps a generalized mode at the
same frequency: its energy is conserved (`Parametron.modeEnergy_conserved`) and it needs zero
holding effort at every time. -/
theorem resonant_drive_rides (stiffness capacity : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (ω : ℝ) {v δ : Node → ℝ}
    (hv : v ∈ modeSpace (storageForm stiffness incidence) (storageForm capacity incidence) (ω ^ 2))
    (hδ : δ ∈ modeSpace (storageForm stiffness incidence) (storageForm capacity incidence) (ω ^ 2))
    (hne : v + δ ≠ 0) :
    IsGeneralizedMode stiffness capacity incidence (ω ^ 2) (v + δ) ∧
      (∀ t, modeEnergy stiffness capacity incidence ω (v + δ) t =
        ω ^ 2 * diagonalStorage capacity incidence (v + δ)) ∧
      ∀ t node, holdingEffort stiffness capacity incidence ω (v + δ) t node = 0 := by
  have hsum := Submodule.add_mem _ hv hδ
  have hmode : IsGeneralizedMode stiffness capacity incidence (ω ^ 2) (v + δ) :=
    (isGeneralizedMode_iff stiffness capacity incidence _ _).mpr ⟨hne, hsum⟩
  refine ⟨hmode, fun t => modeEnergy_conserved hmode t, fun t node => ?_⟩
  have := (mem_modeSpace_iff_response stiffness capacity incidence _ _).mp hsum node
  simp [holdingEffort, this]

/-- [proved-derived; formal-checked] **FOUND needs effort.** With positive capacitive storage, a
nonzero part `c`-orthogonal to the mode space at `ω²` needs a nonzero holding effort at `t = 0`,
and adding any resonating part does not change that effort. -/
theorem emanating_drive_needs_effort (stiffness capacity : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (ω : ℝ)
    (hpos : ∀ v, v ≠ 0 → 0 < diagonalStorage capacity incidence v)
    {r e : Node → ℝ}
    (hr : r ∈ modeSpace (storageForm stiffness incidence) (storageForm capacity incidence) (ω ^ 2))
    (he : e ∈ emanationSpace (storageForm stiffness incidence) (storageForm capacity incidence)
      (ω ^ 2)) (hne : e ≠ 0) :
    (∀ t node, holdingEffort stiffness capacity incidence ω (r + e) t node =
        holdingEffort stiffness capacity incidence ω e t node) ∧
      ∃ node, holdingEffort stiffness capacity incidence ω (r + e) 0 node ≠ 0 := by
  have hresp := (mem_modeSpace_iff_response stiffness capacity incidence _ _).mp hr
  have hsame : ∀ t node, holdingEffort stiffness capacity incidence ω (r + e) t node =
      holdingEffort stiffness capacity incidence ω e t node := by
    intro t node
    simp only [holdingEffort, diagonalResponse_add, hresp node]
    ring
  refine ⟨hsame, ?_⟩
  by_contra hall
  push Not at hall
  have hmem : e ∈ modeSpace (storageForm stiffness incidence) (storageForm capacity incidence)
      (ω ^ 2) := by
    rw [mem_modeSpace_iff_response]
    intro node
    have := hall node
    rw [hsame] at this
    simp only [holdingEffort, mul_zero, Real.cos_zero, one_mul] at this
    linarith
  have hanis : ∀ v, storageForm capacity incidence v v = 0 → v = 0 := by
    intro v hv
    by_contra hv0
    have := hpos v hv0
    rw [storageForm_self] at hv
    linarith
  exact hne (Submodule.disjoint_def.mp
    (modeSpace_disjoint_emanationSpace _ _ _ hanis) e hmem he)

/-- [proved-derived; formal-checked] **A mode's energy is positive.** The energy of a nonzero
generalized mode at `ω ≠ 0` with positive capacitive storage is `ω² S_C(v) > 0` at every time. -/
theorem founded_mode_energy_pos (stiffness capacity : Branch → ℝ)
    (incidence : Branch → Node → ℝ) {ω : ℝ} (hω : ω ≠ 0)
    (hpos : ∀ v, v ≠ 0 → 0 < diagonalStorage capacity incidence v) {v : Node → ℝ}
    (hmode : IsGeneralizedMode stiffness capacity incidence (ω ^ 2) v) (t : ℝ) :
    0 < modeEnergy stiffness capacity incidence ω v t := by
  rw [modeEnergy_conserved hmode t]
  exact mul_pos (by positivity) (hpos v hmode.1)

/-! ### The energy balance of any motion -/

/-- [definition] The stored energy of a motion `x` with velocity `x'` at time `t`:
`S_C(x'(t)) + S_K(x(t))`. -/
def motionEnergy (stiffness capacity : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (x x' : ℝ → Node → ℝ) (t : ℝ) : ℝ :=
  diagonalStorage capacity incidence (x' t) + diagonalStorage stiffness incidence (x t)

/-- [definition] The port power of a motion: `⟨C x'' + K x, x'⟩`, the effort the constitution's
equation requires, paired with the velocity. -/
def portPower (stiffness capacity : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (x x' x'' : ℝ → Node → ℝ) (t : ℝ) : ℝ :=
  ∑ node, (diagonalResponse capacity incidence (x'' t) node +
    diagonalResponse stiffness incidence (x t) node) * x' t node

omit [Fintype Branch] in
theorem hasDerivAt_branchDrop (incidence : Branch → Node → ℝ) {u u' : ℝ → Node → ℝ} {t : ℝ}
    (h : ∀ node, HasDerivAt (fun s => u s node) (u' t node) t) (b : Branch) :
    HasDerivAt (fun s => branchDrop incidence (u s) b) (branchDrop incidence (u' t) b) t := by
  unfold branchDrop
  exact HasDerivAt.fun_sum fun node _ => (h node).const_mul (incidence b node)

/-- [proved-derived; formal-checked] The storage of a moving state changes at the pairing of its
response with the state's rate. -/
theorem hasDerivAt_diagonalStorage (weight : Branch → ℝ) (incidence : Branch → Node → ℝ)
    {u u' : ℝ → Node → ℝ} {t : ℝ} (h : ∀ node, HasDerivAt (fun s => u s node) (u' t node) t) :
    HasDerivAt (fun s => diagonalStorage weight incidence (u s))
      (∑ node, diagonalResponse weight incidence (u t) node * u' t node) t := by
  have hsum : HasDerivAt (fun s => (1 / 2 : ℝ) *
      ∑ b, weight b * branchDrop incidence (u s) b ^ 2)
      ((1 / 2 : ℝ) * ∑ b, weight b * (2 * branchDrop incidence (u t) b ^ 1 *
        branchDrop incidence (u' t) b)) t := by
    apply HasDerivAt.const_mul
    apply HasDerivAt.fun_sum
    intro b _
    have := (hasDerivAt_branchDrop incidence h b).pow 2
    simpa using this.const_mul (weight b)
  refine hsum.congr_deriv ?_
  have hpair := storageForm_eq_pairing weight incidence (u' t) (u t)
  rw [storageForm_apply] at hpair
  calc (1 / 2 : ℝ) * ∑ b, weight b * (2 * branchDrop incidence (u t) b ^ 1 *
        branchDrop incidence (u' t) b)
      = ∑ b, weight b * branchDrop incidence (u' t) b * branchDrop incidence (u t) b := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ node, diagonalResponse weight incidence (u t) node * u' t node := by
        rw [hpair]
        exact Finset.sum_congr rfl fun _ _ => by ring

/-- [proved-derived; formal-checked] **The energy balance of any motion**: the stored energy
changes at exactly the port power, `dE/dt = ⟨C x'' + K x, x'⟩`. -/
theorem hasDerivAt_motionEnergy (stiffness capacity : Branch → ℝ)
    (incidence : Branch → Node → ℝ) {x x' x'' : ℝ → Node → ℝ}
    (hx : ∀ s node, HasDerivAt (fun r => x r node) (x' s node) s)
    (hx' : ∀ s node, HasDerivAt (fun r => x' r node) (x'' s node) s) (t : ℝ) :
    HasDerivAt (motionEnergy stiffness capacity incidence x x')
      (portPower stiffness capacity incidence x x' x'' t) t := by
  have h := (hasDerivAt_diagonalStorage capacity incidence (hx' t)).add
    (hasDerivAt_diagonalStorage stiffness incidence (hx t))
  refine h.congr_deriv ?_
  have e1 : ∑ node, diagonalResponse capacity incidence (x' t) node * x'' t node =
      ∑ node, diagonalResponse capacity incidence (x'' t) node * x' t node := by
    have hc := (storageForm_eq_pairing capacity incidence (x'' t) (x' t)).symm.trans
      ((storageForm_symm capacity incidence (x'' t) (x' t)).trans
        (storageForm_eq_pairing capacity incidence (x' t) (x'' t)))
    simpa [mul_comm] using hc
  rw [portPower, e1, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- [proved-derived; formal-checked] **The work ledger of any motion**: over `[0, t]` the port work
`∫₀ᵗ ⟨C x'' + K x, x'⟩` is exactly the change of stored energy. -/
theorem motion_work_ledger (stiffness capacity : Branch → ℝ) (incidence : Branch → Node → ℝ)
    {x x' x'' : ℝ → Node → ℝ}
    (hx : ∀ s node, HasDerivAt (fun r => x r node) (x' s node) s)
    (hx' : ∀ s node, HasDerivAt (fun r => x' r node) (x'' s node) s)
    (hx'' : ∀ node, Continuous fun s => x'' s node) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, portPower stiffness capacity incidence x x' x'' s =
      motionEnergy stiffness capacity incidence x x' t -
        motionEnergy stiffness capacity incidence x x' 0 := by
  have hxc : ∀ node, Continuous fun s => x s node := fun node =>
    continuous_iff_continuousAt.mpr fun s => (hx s node).continuousAt
  have hx'c : ∀ node, Continuous fun s => x' s node := fun node =>
    continuous_iff_continuousAt.mpr fun s => (hx' s node).continuousAt
  have hcont : Continuous (portPower stiffness capacity incidence x x' x'') := by
    unfold portPower diagonalResponse branchDrop
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_motionEnergy stiffness capacity incidence hx hx' s)
    (hcont.intervalIntegrable 0 t)

/-- [proved-derived; formal-checked] **Founding from rest costs the mode's energy as work.** A
twice-differentiable motion starting at rest (`x 0 = 0`, `x' 0 = 0`) that arrives at time `t` at
the phase `τ` of a nonzero generalized mode `v` (`x t = cos(ωτ) v`, `x' t = −ω sin(ωτ) v`) has
received through the ports exactly the mode's energy `ω² S_C(v)`, which is positive. -/
theorem founding_from_rest_costs_work (stiffness capacity : Branch → ℝ)
    (incidence : Branch → Node → ℝ) {ω : ℝ} (hω : ω ≠ 0)
    (hpos : ∀ v, v ≠ 0 → 0 < diagonalStorage capacity incidence v) {v : Node → ℝ}
    (hmode : IsGeneralizedMode stiffness capacity incidence (ω ^ 2) v)
    {x x' x'' : ℝ → Node → ℝ}
    (hx : ∀ s node, HasDerivAt (fun r => x r node) (x' s node) s)
    (hx' : ∀ s node, HasDerivAt (fun r => x' r node) (x'' s node) s)
    (hx'' : ∀ node, Continuous fun s => x'' s node)
    (rest : x 0 = 0) (rest' : x' 0 = 0) {t τ : ℝ}
    (arrive : x t = fun node => Real.cos (ω * τ) * v node)
    (arrive' : x' t = fun node => -(ω * Real.sin (ω * τ)) * v node) :
    ∫ s in (0 : ℝ)..t, portPower stiffness capacity incidence x x' x'' s =
        ω ^ 2 * diagonalStorage capacity incidence v ∧
      0 < ∫ s in (0 : ℝ)..t, portPower stiffness capacity incidence x x' x'' s := by
  have hzero : ∀ weight : Branch → ℝ, diagonalStorage weight incidence (0 : Node → ℝ) = 0 := by
    intro weight
    simp [diagonalStorage, branchDrop]
  have hwork : ∫ s in (0 : ℝ)..t, portPower stiffness capacity incidence x x' x'' s =
      modeEnergy stiffness capacity incidence ω v τ := by
    rw [motion_work_ledger stiffness capacity incidence hx hx' hx'' t, motionEnergy, motionEnergy,
      rest, rest', hzero, hzero, arrive, arrive', modeEnergy]
    ring
  rw [hwork]
  exact ⟨modeEnergy_conserved hmode τ,
    founded_mode_energy_pos stiffness capacity incidence hω hpos hmode τ⟩

/-! ### Witnesses on the owners' chain -/

/-- [counterexample; formal-checked] **Effort is not work: the clamp.** On
`Parametron.chainIncidence` with `K = [[2,−1],[−1,2]]`, `C = I`, the mode space at `ω² = 2` is
zero, so `(2, 0)` is wholly emanating. Holding it needs the effort `−2 cos(ωt)` at node `1`, yet the
port power is zero at every time and the stored energy stays `4`: node `1` never moves. -/
theorem clamp_witness :
    modeSpace (storageForm chainStiffness chainIncidence) (storageForm chainCapacity chainIncidence)
        (Real.sqrt 2 ^ 2) = ⊥ ∧
      holdingEffort chainStiffness chainCapacity chainIncidence (Real.sqrt 2) ![2, 0] 0 1 = -2 ∧
      (∀ t, ∑ node, holdingEffort chainStiffness chainCapacity chainIncidence (Real.sqrt 2)
          ![2, 0] t node * (-(Real.sqrt 2 * Real.sin (Real.sqrt 2 * t)) * (![2, 0] : Fin 2 → ℝ) node)
          = 0) ∧
      ∀ t, modeEnergy chainStiffness chainCapacity chainIncidence (Real.sqrt 2) ![2, 0] t = 4 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro v hv
    rw [mem_modeSpace_iff_response, h2] at hv
    have h0 := hv 0
    have h1 := hv 1
    simp [diagonalResponse, branchDrop, chainIncidence, chainStiffness, chainCapacity,
      Fin.sum_univ_three, Fin.sum_univ_two] at h0 h1
    rw [Submodule.mem_bot]
    funext i
    fin_cases i <;> simp <;> linarith
  · simp [holdingEffort, h2, diagonalResponse, branchDrop, chainIncidence, chainStiffness,
      chainCapacity, Fin.sum_univ_three, Fin.sum_univ_two]
  · intro t
    simp [holdingEffort, h2, diagonalResponse, branchDrop, chainIncidence, chainStiffness,
      chainCapacity, Fin.sum_univ_three, Fin.sum_univ_two]
    norm_num
  · intro t
    rw [modeEnergy_closed]
    have htrig := Real.sin_sq_add_cos_sq (Real.sqrt 2 * t)
    simp [diagonalStorage, branchDrop, chainIncidence, chainStiffness, chainCapacity,
      Fin.sum_univ_three, Fin.sum_univ_two, mul_pow, h2]
    linear_combination 4 * htrig

/-- [proved-derived; formal-checked] **Emanation that does exchange work.** At `ω = 1` the drive
`(2, 0)` splits as the resonating `(1, 1)` (the mode of `Parametron.modeWitness`) plus the
emanating `(1, −1)`, which is `C`-orthogonal to the whole mode space; the energy exchanged over
`[0, t]` is `−2 sin² t`, which is `−2` at `t = π/2`. -/
theorem work_witness :
    (![1, 1] : Fin 2 → ℝ) ∈ modeSpace (storageForm chainStiffness chainIncidence)
        (storageForm chainCapacity chainIncidence) (1 ^ 2) ∧
      (![1, -1] : Fin 2 → ℝ) ∈ emanationSpace (storageForm chainStiffness chainIncidence)
        (storageForm chainCapacity chainIncidence) (1 ^ 2) ∧
      (![2, 0] : Fin 2 → ℝ) = ![1, 1] + ![1, -1] ∧
      ∀ t, modeEnergy chainStiffness chainCapacity chainIncidence 1 ![2, 0] t -
          modeEnergy chainStiffness chainCapacity chainIncidence 1 ![2, 0] 0 =
        -2 * Real.sin t ^ 2 := by
  have hr : (![1, 1] : Fin 2 → ℝ) ∈ modeSpace (storageForm chainStiffness chainIncidence)
      (storageForm chainCapacity chainIncidence) (1 ^ 2) := by
    rw [one_pow]
    exact ((isGeneralizedMode_iff _ _ _ _ _).mp modeWitness.2.1).2
  have hsplit : (![2, 0] : Fin 2 → ℝ) = ![1, 1] + ![1, -1] := by
    funext i; fin_cases i <;> norm_num
  refine ⟨hr, ?_, hsplit, ?_⟩
  · rw [emanationSpace, LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [mem_modeSpace_iff_response] at hn
    have h0 := hn 0
    have h1 := hn 1
    simp [diagonalResponse, branchDrop, chainIncidence, chainStiffness, chainCapacity,
      Fin.sum_univ_three, Fin.sum_univ_two] at h0 h1
    simp [storageForm_apply, branchDrop, chainIncidence, chainCapacity, Fin.sum_univ_three,
      Fin.sum_univ_two]
    linarith
  · intro t
    rw [hsplit]
    have := work_ledger chainStiffness chainCapacity chainIncidence 1 hr ![1, -1] t
    rw [this]
    simp [diagonalStorage, branchDrop, chainIncidence, chainStiffness, chainCapacity,
      Fin.sum_univ_three, Fin.sum_univ_two]
    norm_num
    ring

end Parametron

/-! ## 3. The learning chart: deposition onto the arrived source -/

section Learning

open Holonics.Computation.HolonicInformationTheory
open Holonics.Aeon.Production.FirstLaw

variable {Index : Type*} [Fintype Index]

/-- [proved-derived; formal-checked] **Gibbs' equality case.** On the declared positive support,
`D(p‖q) = 0` exactly when the two sections are equal. This completes
`InformationReceiver.klDivergence_nonnegative`. -/
theorem klDivergence_eq_zero_iff (p q : PositiveProbabilitySection Index) :
    p.klDivergence q = 0 ↔ p.mass = q.mass := by
  constructor
  · intro h
    have bound : ∀ i, p.mass i - q.mass i ≤
        p.mass i * (Real.log (p.mass i) - Real.log (q.mass i)) := by
      intro i
      have hlog := Real.log_le_sub_one_of_pos (div_pos (q.positive i) (p.positive i))
      have hmul := mul_le_mul_of_nonneg_left hlog (p.nonnegative i)
      have cancel : p.mass i * (q.mass i / p.mass i - 1) = q.mass i - p.mass i := by
        field_simp [p.ne_zero i]
      rw [cancel, Real.log_div (q.ne_zero i) (p.ne_zero i)] at hmul
      nlinarith
    have hsum : ∑ i, (p.mass i * (Real.log (p.mass i) - Real.log (q.mass i)) -
        (p.mass i - q.mass i)) = 0 := by
      rw [Finset.sum_sub_distrib, ← PositiveProbabilitySection.klDivergence_eq_logDifference, h,
        Finset.sum_sub_distrib, p.normalized, q.normalized]
      ring
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sub_nonneg.mpr (bound i))).mp hsum
    funext i
    by_contra hne
    have hx : q.mass i / p.mass i ≠ 1 := by
      intro h1
      apply hne
      rw [div_eq_one_iff_eq (p.ne_zero i)] at h1
      exact h1.symm
    have hlog := Real.log_lt_sub_one_of_pos (div_pos (q.positive i) (p.positive i)) hx
    rw [Real.log_div (q.ne_zero i) (p.ne_zero i)] at hlog
    have hstrict := mul_lt_mul_of_pos_left hlog (p.positive i)
    have cancel : p.mass i * (q.mass i / p.mass i - 1) = q.mass i - p.mass i := by
      field_simp [p.ne_zero i]
    rw [cancel] at hstrict
    have := hzero i (Finset.mem_univ i)
    nlinarith
  · intro h
    unfold PositiveProbabilitySection.klDivergence
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [h, div_self (q.ne_zero i), Real.log_one, mul_zero]

/-- [proved-derived; formal-checked] **RIDE and FOUND in the learning chart.** The first law's
deposition onto the arrived source (`FirstLaw.deposition_onto_source`) is zero exactly when the
receiver already resonates with the source (`q = p'`); otherwise it is strictly negative, by exactly
the KL excess. With canonical receivers, `T · deposition` is the work on the levels
(`FirstLaw.thermal_first_law`). -/
theorem deposition_onto_source_zero_iff (p' q : PositiveProbabilitySection Index) :
    (deposition p' q p' = 0 ↔ q.mass = p'.mass) ∧
      (deposition p' q p' < 0 ↔ q.mass ≠ p'.mass) := by
  obtain ⟨hdep, _⟩ := deposition_onto_source p' q
  have hkl := PositiveProbabilitySection.klDivergence_nonnegative p' q
  have hiff := klDivergence_eq_zero_iff p' q
  rw [hdep]
  constructor
  · rw [neg_eq_zero, hiff]
    exact eq_comm
  · constructor
    · intro hneg heq
      have : PositiveProbabilitySection.klDivergence p' q = 0 := hiff.mpr heq.symm
      linarith
    · intro hne
      have : PositiveProbabilitySection.klDivergence p' q ≠ 0 := fun h0 => hne (hiff.mp h0).symm
      exact neg_neg_of_pos (lt_of_le_of_ne hkl (Ne.symm this))

end Learning

section Audit

#print axioms split_exists_unique
#print axioms effort_split
#print axioms emanating_effort_eq_zero_iff
#print axioms reactive_split
#print axioms isGeneralizedMode_iff
#print axioms holdingEffort_newton
#print axioms hasDerivAt_modeEnergy
#print axioms work_ledger
#print axioms resonant_drive_rides
#print axioms emanating_drive_needs_effort
#print axioms founded_mode_energy_pos
#print axioms hasDerivAt_motionEnergy
#print axioms motion_work_ledger
#print axioms founding_from_rest_costs_work
#print axioms clamp_witness
#print axioms work_witness
#print axioms klDivergence_eq_zero_iff
#print axioms deposition_onto_source_zero_iff

end Audit

end Holonics.Compression.Core.Resonance

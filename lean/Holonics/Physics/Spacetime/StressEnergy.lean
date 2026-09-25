import Holonics.Physics.ObserverBoundaryCurrent
import Holonics.Physics.Fluid.ControlVolume
import Holonics.Physics.Spacetime.Boost

/-!
# The source map: a constituted fluid and thermal cell read as stress–energy, and its observer

[definition] Rebuild step 6, K4 (#75); restructure plan §3.6 at `13f8c734`. A cell of the K3 fluid
instance carries its Newtonian stress `σ = −pI + 2μ Def u + λ (tr G) I`
(`Physics/Fluid/ControlVolume.stress`); its thermal cell carries an internal energy, and its
contact a heat flux `q` (`Physics/Thermal/Exchange`). The **source map** reads that constituted
state, in its rest chart (`c = 1`, signature `(−,+,+,+)`), as the Eckart stress–energy
`T` of the existing finite owner `Physics/ReceiverStressEnergy.Tensor`:

```text
T⁰⁰ = ε = ρ₀ + e        T⁰ⁱ = Tⁱ⁰ = qⁱ        Tⁱʲ = −σᵢⱼ = p δᵢⱼ − τᵢⱼ
```

The momentum flux is the negative of the Cauchy stress, so pressure enters `T` positively and the
viscous stress negatively. No coefficient is chosen here: every entry is the K3 owner's.

[proved-derived; formal-checked]

* **Symmetry and the perfect-fluid face.** `T` is symmetric (`sourceMap_symmetric`), its rest
  observer reads `ε` (`sourceMap_restReading`, through `restObserver_contraction_eq_density`), and
  without viscosity or heat flux it is exactly the owner's `perfectFluidTensor ε p`
  (`sourceMap_perfect`). Its spatial trace is `3p − (2μ + 3λ) tr G`, the bulk-viscous pressure
  (`sourceMap_spatialTrace`).
* **A boosted observer mixes energy, heat and stress.** The owner's boosted observer
  `(5/3, 4/3, 0, 0)` reads `25ε/9 − 40q₁/9 + 16T¹¹/9` (`sourceMap_boostedEnergy`): the heat flux
  along the boost enters the energy it reads.
* **A boosted observer reads the transported tensor.** For any matrix `Λ`, the observer pair
  `(Λu, Λv)` reads `T` as `(u, v)` reads `(ηΛᵀη) T (ηΛη)` (`observerBilinear_transport`); for a
  Lorentz transformation (`Λᵀ η Λ = η`) `ηΛᵀη = Λ⁻¹` (`lorentz_inverse`), so the boosted observer
  `Λe₀` reads the rest energy density of `Λ⁻¹ T Λ⁻ᵀ`, `T(Λe₀, Λe₀) = (Λ⁻¹TΛ⁻ᵀ)⁰⁰`
  (`boosted_reads_transported`). The owner's boosted observer is the Doppler boost `k = 3` of the
  rest observer (`boostT`, `boostT_lorentz`, `boostedObserver_eq`), and the source it reads is the
  transported source's rest energy (`sourceMap_boosted_transport`).
* **Trace reversal gives the Newtonian coupling `8π = 2·4π`.** In four dimensions with `Λ = 0`,
  `Ric − ½(tr_η Ric)η = κT` is `Ric = κ(T − ½(tr_η T)η)` (`trace_reversal`, with
  `minkowskiTrace_metric`: `tr_η η = 4`). The trace-reversed time component is
  `(T⁰⁰ + Σᵢ Tⁱⁱ)/2` (`traceReversed_zero_zero`): `(ε + 3p − (2μ + 3λ) tr G)/2` on the source map
  (`sourceMap_traceReversed`), `(ε + 3p)/2` on the perfect fluid and `ε/2` on dust. So at
  `κ = 8πG` a dust source has `R₀₀ = 4πGρ` (`dust_newtonian_source`), and the source map has
  `R₀₀ = 4πG(ε + 3p − (2μ + 3λ) tr G)` (`sourceMap_newtonian_source`). [proved-standard] In the weak
  static field `R₀₀ = ∇²Φ`, so this is Poisson's `∇²Φ = 4πGρ`; that limit is not formalized here.
* **The observer's deformation term is the K3 heat port.** The spatial block contracted with the
  velocity gradient is `p tr G − Φ` (`sourceMap_spatialPower`, from `stress_power_split`). For the
  comoving receiver `u_ν = (−1, 0, 0, 0)` with `∂ᵢu_ⱼ = Gⱼᵢ`, the divergence of its current
  `j_U = −T·u` is `f⁰ − p tr G + Φ` (`comoving_observerDivergence`, over
  `ObserverBoundaryCurrent.observerCurrentDivergence`): the relativistic first law, with the
  pressure work and the viscous heat `Φ = dissipation μ λ G` of the fluid's thermal port. A rigid
  (Killing) comoving receiver reads the force alone (`rigid_comoving_reads_force`, through
  `observerCurrentDivergence_killing`).

[counterexample; formal-checked] **Conservation belongs to a receiver.** A force-free source
(`∇·T = 0`) is read with nonzero current divergence by a deforming receiver: an expanding one reads
the pressure work `−3` (`expanding_receiver_reads_pressure_work`), a sheared viscous one the heat
`+1` (`sheared_receiver_reads_viscous_heat`).

Scope: one cell at one instant of its rest chart; the comoving gradient keeps the spatial block
and sets the time derivatives to zero. The covariant derivative on a curved chart is the supplied
port of `Spacetime/Einstein`.
-/

noncomputable section

namespace Holonics.Physics.Spacetime.StressEnergy

open Matrix
open Holonics.Physics.ReceiverStressEnergy
open Holonics.Physics.ObserverBoundaryCurrent
open Holonics.Physics.Fluid.ControlVolume

/-- [definition] **A constituted cell in its rest chart**: rest-mass energy density, the thermal
cell's internal energy density, and the fluid's pressure, Newtonian material and velocity gradient
(`G_ab = ∂_b u_a`), with the contact's heat flux. -/
structure ConstitutedState where
  restEnergy : ℚ
  internalEnergy : ℚ
  pressure : ℚ
  shear : ℚ
  bulk : ℚ
  gradient : Matrix (Fin 3) (Fin 3) ℚ
  heatFlux : Fin 3 → ℚ

namespace ConstitutedState

variable (s : ConstitutedState)

/-- [definition] The rest-frame energy density `ε = ρ₀ + e`. -/
def energyDensity : ℚ := s.restEnergy + s.internalEnergy

/-- [definition] The K3 Newtonian stress of the cell (`ControlVolume.stress`). -/
def cauchy : Matrix (Fin 3) (Fin 3) ℚ := stress s.pressure s.shear s.bulk s.gradient

/-- [proved-derived; formal-checked] The Newtonian stress is symmetric. -/
theorem cauchy_symm (i j : Fin 3) : s.cauchy i j = s.cauchy j i := by
  simp only [cauchy, stress, viscousStress, strain, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.transpose_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]; ring

end ConstitutedState

/-- [definition] **The source map** `T(s)`: energy density, heat flux and the negative Cauchy
stress, in the owner's sixteen-component chart. -/
def sourceMap (s : ConstitutedState) : Tensor := fun μ ν =>
  Fin.cases (motive := fun _ => ℝ)
    (Fin.cases (motive := fun _ => ℝ) (s.energyDensity : ℝ) (fun j => (s.heatFlux j : ℝ)) ν)
    (fun i => Fin.cases (motive := fun _ => ℝ) (s.heatFlux i : ℝ)
      (fun j => -(s.cauchy i j : ℝ)) ν) μ

section Entries

variable (s : ConstitutedState)

@[simp] theorem sourceMap_zero_zero : sourceMap s 0 0 = s.energyDensity := rfl

@[simp] theorem sourceMap_zero_succ (j : Fin 3) : sourceMap s 0 j.succ = s.heatFlux j := rfl

@[simp] theorem sourceMap_succ_zero (i : Fin 3) : sourceMap s i.succ 0 = s.heatFlux i := rfl

@[simp] theorem sourceMap_succ_succ (i j : Fin 3) :
    sourceMap s i.succ j.succ = -(s.cauchy i j : ℝ) := rfl

@[simp] theorem sourceMap_zero_one : sourceMap s 0 1 = s.heatFlux 0 := rfl

@[simp] theorem sourceMap_one_zero : sourceMap s 1 0 = s.heatFlux 0 := rfl

end Entries

/-- [proved-derived; formal-checked] **The source is symmetric**, as the owner's observer-current
laws require. -/
theorem sourceMap_symmetric (s : ConstitutedState) :
    ∀ μ ν, sourceMap s μ ν = sourceMap s ν μ := by
  intro μ ν
  refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
    simp [s.cauchy_symm]

/-- [proved-derived; formal-checked] The rest observer reads the energy density
(`restObserver_contraction_eq_density`). -/
theorem sourceMap_restReading (s : ConstitutedState) :
    minkowskiContraction restObserver (sourceMap s) = s.energyDensity := by
  rw [restObserver_contraction_eq_density]
  rfl

/-- [proved-derived; formal-checked] **The perfect-fluid face.** Without viscosity or heat flux
the source map is exactly the owner's `perfectFluidTensor ε p`. -/
theorem sourceMap_perfect (s : ConstitutedState) (hμ : s.shear = 0) (hbulk : s.bulk = 0)
    (hq : s.heatFlux = 0) :
    sourceMap s = perfectFluidTensor (s.energyDensity : ℝ) (s.pressure : ℝ) := by
  have hrest : ∀ j : Fin 3, restObserver j.succ = 0 := by
    intro j; fin_cases j <;> rfl
  funext μ ν
  refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν
  · simp [perfectFluidTensor, restObserver, minkowskiMetricComponent, minkowskiSign]
  · simp [perfectFluidTensor, hrest, minkowskiMetricComponent, hq, (Fin.succ_ne_zero j).symm]
  · simp [perfectFluidTensor, hrest, minkowskiMetricComponent, hq, Fin.succ_ne_zero]
  · simp only [sourceMap_succ_succ, ConstitutedState.cauchy, stress, viscousStress, hμ, hbulk,
      perfectFluidTensor, minkowskiMetricComponent, minkowskiSign, hrest]
    by_cases h : i = j
    · subst h; simp [Fin.succ_ne_zero]
    · have h' : i.succ ≠ j.succ := fun e => h (Fin.succ_injective _ e)
      simp [h, h']

/-- [proved-derived; formal-checked] **The spatial trace is the bulk-viscous pressure**
`3p − (2μ + 3λ) tr G`. -/
theorem sourceMap_spatialTrace (s : ConstitutedState) :
    ∑ i : Fin 3, sourceMap s i.succ i.succ =
      3 * (s.pressure : ℝ) - (2 * s.shear + 3 * s.bulk) * ((trace s.gradient : ℚ) : ℝ) := by
  have htr : ∑ i : Fin 3, s.cauchy i i =
      3 * -s.pressure + (2 * s.shear + 3 * s.bulk) * trace s.gradient := by
    have h := congrArg (fun M => trace M) (rfl : s.cauchy = s.cauchy)
    simp only [ConstitutedState.cauchy, stress, viscousStress] at h
    have ht : trace s.cauchy = 3 * -s.pressure + (2 * s.shear + 3 * s.bulk) * trace s.gradient := by
      simp only [ConstitutedState.cauchy, stress, viscousStress, trace_add, trace_smul,
        trace_one, trace_strain, smul_eq_mul, Fintype.card_fin]
      push_cast
      ring
    simpa [trace, diag] using ht
  simp only [sourceMap_succ_succ]
  rw [show (∑ i : Fin 3, -(s.cauchy i i : ℝ)) = -((∑ i : Fin 3, s.cauchy i i : ℚ) : ℝ) by
    push_cast; simp [Finset.sum_neg_distrib]]
  rw [htr]
  push_cast
  ring

/-- [proved-derived; formal-checked] **A boosted observer mixes energy, heat and stress.** The
owner's observer `(5/3, 4/3, 0, 0)` reads `25ε/9 − 40q₁/9 + 16T¹¹/9`. -/
theorem sourceMap_boostedEnergy (s : ConstitutedState) :
    observerBilinear boostedObserver boostedObserver (sourceMap s) =
      25 * (s.energyDensity : ℝ) / 9 - 40 * (s.heatFlux 0 : ℝ) / 9 +
        16 * sourceMap s 1 1 / 9 := by
  simp only [observerBilinear, Fin.sum_univ_succ, Fin.sum_univ_zero, boostedObserver,
    minkowskiSign]
  simp
  ring

/-- [proved-derived; formal-checked] **The stress block against the velocity gradient** is the
pressure work less the dissipation: `Σ Tⁱʲ Gᵢⱼ = p tr G − Φ` (`stress_power_split`). -/
theorem sourceMap_spatialPower (s : ConstitutedState) :
    ∑ i : Fin 3, ∑ j : Fin 3, sourceMap s i.succ j.succ * (s.gradient i j : ℝ) =
      (s.pressure : ℝ) * ((trace s.gradient : ℚ) : ℝ) -
        ((dissipation s.shear s.bulk s.gradient : ℚ) : ℝ) := by
  have h := stress_power_split s.pressure s.shear s.bulk s.gradient
  have hR : ((frob (stress s.pressure s.shear s.bulk s.gradient) s.gradient : ℚ) : ℝ) =
      ((-s.pressure * trace s.gradient + dissipation s.shear s.bulk s.gradient : ℚ) : ℝ) := by
    rw [h]
  simp only [frob] at hR
  push_cast at hR
  simp only [sourceMap_succ_succ, ConstitutedState.cauchy, neg_mul, Finset.sum_neg_distrib]
  linarith

/-! ## A boosted observer reads the transported tensor -/

/-- [definition] The Minkowski metric `η = diag(−1, 1, 1, 1)` as a matrix. -/
def eta : Matrix Index Index ℝ := Matrix.diagonal minkowskiSign

theorem eta_mul_eta : eta * eta = 1 := by
  rw [eta, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  unfold minkowskiSign
  split_ifs <;> norm_num

theorem eta_transpose : etaᵀ = eta := Matrix.diagonal_transpose _

/-- [proved-derived; formal-checked] The observer pairing is `(ηu) · T(ηv)`. -/
theorem observerBilinear_eq (u v : Index → ℝ) (T : Tensor) :
    observerBilinear u v T = (eta *ᵥ u) ⬝ᵥ (Matrix.of T *ᵥ (eta *ᵥ v)) := by
  have hη : ∀ w : Index → ℝ, eta *ᵥ w = fun i => minkowskiSign i * w i := fun w => by
    funext i; exact Matrix.mulVec_diagonal _ _ _
  rw [hη, hη]
  simp only [observerBilinear, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- [definition] **The transported tensor** `(ηΛᵀη) T (ηΛη)`: for a Lorentz transformation it is
`Λ⁻¹ T Λ⁻ᵀ` (`lorentz_inverse`). -/
def transport (L : Matrix Index Index ℝ) (T : Tensor) : Tensor :=
  (eta * Lᵀ * eta) * Matrix.of T * (eta * L * eta)

/-- [proved-derived; formal-checked] For a Lorentz transformation, `ηΛᵀη` is its inverse. -/
theorem lorentz_inverse {L : Matrix Index Index ℝ} (hL : Lᵀ * eta * L = eta) :
    (eta * Lᵀ * eta) * L = 1 := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Lᵀ, hL, eta_mul_eta]

/-- [proved-derived; formal-checked] **The observer pair `(Λu, Λv)` reads `T` as `(u, v)` reads the
transported tensor.** -/
theorem observerBilinear_transport (L : Matrix Index Index ℝ) (u v : Index → ℝ) (T : Tensor) :
    observerBilinear (L *ᵥ u) (L *ᵥ v) T = observerBilinear u v (transport L T) := by
  rw [observerBilinear_eq, observerBilinear_eq]
  have hT : Matrix.of (transport L T) = (eta * Lᵀ * eta) * Matrix.of T * (eta * L * eta) := rfl
  have hv : (eta * L * eta) *ᵥ (eta *ᵥ v) = eta *ᵥ (L *ᵥ v) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, eta_mul_eta, Matrix.mul_one]
  have hu : (eta * Lᵀ * eta)ᵀ *ᵥ (eta *ᵥ u) = eta *ᵥ (L *ᵥ u) := by
    simp only [Matrix.transpose_mul, eta_transpose, Matrix.transpose_transpose,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, eta_mul_eta, Matrix.mul_one]
  have key : ∀ (a b : Index → ℝ) (M : Matrix Index Index ℝ), a ⬝ᵥ (M *ᵥ b) = (Mᵀ *ᵥ a) ⬝ᵥ b :=
    fun a b M => by rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  rw [hT, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, key (eta *ᵥ u) _ (eta * Lᵀ * eta),
    hu]

/-- [proved-derived; formal-checked] **A boosted observer reads the transported tensor's rest
energy**: `T(Λe₀, Λe₀) = (ηΛᵀη T ηΛη)⁰⁰`, which is `(Λ⁻¹ T Λ⁻ᵀ)⁰⁰` for a Lorentz `Λ`. -/
theorem boosted_reads_transported (L : Matrix Index Index ℝ) (T : Tensor) :
    observerBilinear (L *ᵥ restObserver) (L *ᵥ restObserver) T =
      restEnergyDensity (transport L T) := by
  rw [observerBilinear_transport]
  exact restObserver_contraction_eq_density _

/-- [definition] **The Doppler boost along `x`** of ratio `k` on `(t, x, y, z)`, with
`γ = (k + k⁻¹)/2`, `γβ = (k − k⁻¹)/2` (`Boost.gammaOf`, `Boost.gammaBetaOf`). -/
def boostT (k : ℝ) : Matrix Index Index ℝ :=
  !![Boost.gammaOf k, Boost.gammaBetaOf k, 0, 0; Boost.gammaBetaOf k, Boost.gammaOf k, 0, 0;
    0, 0, 1, 0; 0, 0, 0, 1]

/-- [proved-derived; formal-checked] The Doppler boost is a Lorentz transformation. -/
theorem boostT_lorentz {k : ℝ} (hk : k ≠ 0) : (boostT k)ᵀ * eta * boostT k = eta := by
  have hh : Boost.gammaOf k ^ 2 - Boost.gammaBetaOf k ^ 2 = 1 :=
    Holonics.Physics.CompositeMassEnergy.multiplicativeScale_lorentz_identity hk
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostT, eta, Matrix.mul_apply, Fin.sum_univ_four, minkowskiSign, Matrix.diagonal] <;>
    first | linear_combination hh | linear_combination (-1 : ℝ) * hh | linear_combination (0 : ℝ) * hh

/-- [proved-derived; formal-checked] The owner's boosted observer `(5/3, 4/3, 0, 0)` is the rest
observer carried by the Doppler boost `k = 3`. -/
theorem boostedObserver_eq : boostedObserver = boostT 3 *ᵥ restObserver := by
  ext i
  fin_cases i <;>
    simp [boostedObserver, boostT, restObserver, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Boost.gammaOf, Boost.gammaBetaOf] <;> norm_num

/-- [proved-derived; formal-checked] **The source a boosted observer reads is the transported
source's rest energy**: `(Λ⁻¹ T Λ⁻ᵀ)⁰⁰ = 25ε/9 − 40q₁/9 + 16T¹¹/9` at `k = 3`. -/
theorem sourceMap_boosted_transport (s : ConstitutedState) :
    restEnergyDensity (transport (boostT 3) (sourceMap s)) =
      25 * (s.energyDensity : ℝ) / 9 - 40 * (s.heatFlux 0 : ℝ) / 9 + 16 * sourceMap s 1 1 / 9 := by
  rw [← boosted_reads_transported, ← boostedObserver_eq, sourceMap_boostedEnergy]

/-! ## Trace reversal and the Newtonian coupling -/

/-- [definition] The Minkowski trace `tr_η A = Σ_μ η_μμ A^{μμ}`. -/
def minkowskiTrace (A : Tensor) : ℝ := ∑ μ, minkowskiSign μ * A μ μ

/-- [definition] **The trace reversal** `Ā = A − ½ (tr_η A) η`. -/
def traceReversed (A : Tensor) : Tensor := fun μ ν =>
  A μ ν - minkowskiTrace A / 2 * minkowskiMetricComponent μ ν

/-- [proved-derived; formal-checked] `tr_η η = 4`. -/
theorem minkowskiTrace_metric : minkowskiTrace minkowskiMetricComponent = 4 := by
  simp [minkowskiTrace, minkowskiMetricComponent, minkowskiSign, Fin.sum_univ_four]
  norm_num

/-- [proved-derived; formal-checked] `tr_η Ā = −tr_η A` in four dimensions. -/
theorem minkowskiTrace_traceReversed (A : Tensor) :
    minkowskiTrace (traceReversed A) = -minkowskiTrace A := by
  simp [minkowskiTrace, traceReversed, Fin.sum_univ_four, minkowskiMetricComponent, minkowskiSign]
  ring

/-- [proved-derived; formal-checked] **Trace reversal of the field equation.** With `Λ = 0` in four
dimensions, `Ric − ½(tr_η Ric)η = κT` is `Ric = κ(T − ½(tr_η T)η)`. -/
theorem trace_reversal {Ric T : Tensor} {κ : ℝ} (h : traceReversed Ric = κ • T) :
    Ric = κ • traceReversed T := by
  have htr : minkowskiTrace Ric = -(κ * minkowskiTrace T) := by
    have h1 := congrArg minkowskiTrace h
    rw [minkowskiTrace_traceReversed] at h1
    have h2 : minkowskiTrace (κ • T) = κ * minkowskiTrace T := by
      simp [minkowskiTrace, Fin.sum_univ_four]; ring
    rw [h2] at h1
    linarith
  funext μ ν
  have hμν := congrFun (congrFun h μ) ν
  simp only [traceReversed, Pi.smul_apply, smul_eq_mul] at hμν ⊢
  rw [htr] at hμν
  linarith

/-- [proved-derived; formal-checked] The trace-reversed time component is `(T⁰⁰ + Σᵢ Tⁱⁱ)/2`. -/
theorem traceReversed_zero_zero (T : Tensor) :
    traceReversed T 0 0 = (T 0 0 + spatialPressureTrace T) / 2 := by
  simp [traceReversed, minkowskiTrace, minkowskiMetricComponent, minkowskiSign,
    spatialPressureTrace, Fin.sum_univ_four]
  ring

/-- [proved-derived; formal-checked] **On the source map**: `(ε + 3p − (2μ + 3λ) tr G)/2`. -/
theorem sourceMap_traceReversed (s : ConstitutedState) :
    traceReversed (sourceMap s) 0 0 =
      ((s.energyDensity : ℝ) + (3 * (s.pressure : ℝ) -
        (2 * s.shear + 3 * s.bulk) * ((trace s.gradient : ℚ) : ℝ))) / 2 := by
  have hsp : spatialPressureTrace (sourceMap s) = ∑ i : Fin 3, sourceMap s i.succ i.succ := by
    simp only [spatialPressureTrace, Fin.sum_univ_three]; rfl
  rw [traceReversed_zero_zero, hsp, sourceMap_spatialTrace, sourceMap_zero_zero]

/-- [proved-derived; formal-checked] **On the perfect fluid** `(ε + 3p)/2`, on dust `ε/2`. -/
theorem perfectFluid_traceReversed (ε p : ℝ) :
    traceReversed (perfectFluidTensor ε p) 0 0 = (ε + 3 * p) / 2 ∧
      traceReversed (perfectFluidTensor ε 0) 0 0 = ε / 2 := by
  rw [traceReversed_zero_zero, traceReversed_zero_zero,
    perfectFluidTensor_spatialPressureTrace, perfectFluidTensor_spatialPressureTrace]
  have h := perfectFluidTensor_restEnergy ε p
  have h0 := perfectFluidTensor_restEnergy ε 0
  simp only [restEnergyDensity] at h h0
  rw [h, h0]
  constructor <;> ring

/-- [proved-derived; formal-checked] **The Newtonian coupling `8π = 2·4π`**: with `κ = 8πG` and a
dust source of density `ρ`, the trace-reversed field equation gives `R₀₀ = 4πGρ`. -/
theorem dust_newtonian_source {Ric : Tensor} {G ρ : ℝ}
    (h : traceReversed Ric = (8 * Real.pi * G) • perfectFluidTensor ρ 0) :
    Ric 0 0 = 4 * Real.pi * G * ρ := by
  rw [trace_reversal h, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    (perfectFluid_traceReversed ρ 0).2]
  ring

/-- [proved-derived; formal-checked] **The source map's Newtonian source**: at `κ = 8πG`,
`R₀₀ = 4πG(ε + 3p − (2μ + 3λ) tr G)`. -/
theorem sourceMap_newtonian_source {Ric : Tensor} {G : ℝ} (s : ConstitutedState)
    (h : traceReversed Ric = (8 * Real.pi * G) • sourceMap s) :
    Ric 0 0 = 4 * Real.pi * G * ((s.energyDensity : ℝ) + (3 * (s.pressure : ℝ) -
      (2 * s.shear + 3 * s.bulk) * ((trace s.gradient : ℚ) : ℝ))) := by
  rw [trace_reversal h, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, sourceMap_traceReversed]
  ring

/-! ## The comoving receiver and its deformation term -/

/-- [definition] The rest receiver as a covector, `u_ν = (−1, 0, 0, 0)`. -/
def restCovector : Index → ℝ := ![-1, 0, 0, 0]

/-- [definition] **The comoving receiver's gradient** `∂_μ u_ν`: the fluid's `∂ᵢuⱼ = Gⱼᵢ` on the
spatial block, zero elsewhere. -/
def comovingGradient (G : Matrix (Fin 3) (Fin 3) ℚ) : Tensor := fun μ ν =>
  Fin.cases (motive := fun _ => ℝ) 0
    (fun i => Fin.cases (motive := fun _ => ℝ) 0 (fun j => (G j i : ℝ)) ν) μ

/-- [proved-derived; formal-checked] The source contracted with the comoving gradient is
`p tr G − Φ`. -/
theorem sourceMap_contraction_comoving (s : ConstitutedState) :
    tensorContraction (sourceMap s) (comovingGradient s.gradient) =
      (s.pressure : ℝ) * ((trace s.gradient : ℚ) : ℝ) -
        ((dissipation s.shear s.bulk s.gradient : ℚ) : ℝ) := by
  calc tensorContraction (sourceMap s) (comovingGradient s.gradient)
      = ∑ i : Fin 3, ∑ j : Fin 3, sourceMap s j.succ i.succ * (s.gradient j i : ℝ) := by
        unfold tensorContraction
        rw [Fin.sum_univ_succ]
        simp only [comovingGradient, Fin.cases_zero, mul_zero, Finset.sum_const_zero, zero_add]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Fin.sum_univ_succ]
        simp only [Fin.cases_zero, Fin.cases_succ, mul_zero, zero_add]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sourceMap_symmetric s i.succ j.succ]
    _ = ∑ j : Fin 3, ∑ i : Fin 3, sourceMap s j.succ i.succ * (s.gradient j i : ℝ) :=
        Finset.sum_comm
    _ = _ := sourceMap_spatialPower s

/-- [proved-derived; formal-checked] **The comoving receiver's current** `j_U = −T·u` has
divergence `f⁰ − p tr G + Φ`: the force it reads, the pressure work and the viscous heat of the
fluid's thermal port (`ObserverBoundaryCurrent.observerCurrentDivergence`). -/
theorem comoving_observerDivergence (s : ConstitutedState) (force : Index → ℝ) :
    observerCurrentDivergence restCovector force (sourceMap s) (comovingGradient s.gradient) =
      force 0 - (s.pressure : ℝ) * ((trace s.gradient : ℚ) : ℝ) +
        ((dissipation s.shear s.bulk s.gradient : ℚ) : ℝ) := by
  rw [observerCurrentDivergence_eq, sourceMap_contraction_comoving]
  simp [Fin.sum_univ_succ, restCovector]
  ring

/-- [proved-derived; formal-checked] **A rigid comoving receiver reads the force alone**: when the
gradient is antisymmetric (rigid rotation), the comoving gradient is Killing
(`observerCurrentDivergence_killing`). -/
theorem rigid_comoving_reads_force (s : ConstitutedState) (force : Index → ℝ)
    (hrigid : ∀ i j, s.gradient i j + s.gradient j i = 0) :
    observerCurrentDivergence restCovector force (sourceMap s) (comovingGradient s.gradient) =
      force 0 := by
  rw [observerCurrentDivergence_killing _ _ _ _ (sourceMap_symmetric s)]
  · simp [Fin.sum_univ_succ, restCovector]
  · intro μ ν
    refine Fin.cases ?_ (fun i => ?_) μ <;> refine Fin.cases ?_ (fun j => ?_) ν <;>
      simp [comovingGradient]
    exact_mod_cast hrigid j i

/-! ## Conservation belongs to a receiver -/

/-- [definition] A pressurized, inviscid, heat-free cell expanding uniformly (`G = I`). -/
def expandingCell : ConstitutedState where
  restEnergy := 1
  internalEnergy := 0
  pressure := 1
  shear := 0
  bulk := 0
  gradient := 1
  heatFlux := 0

/-- [counterexample; formal-checked] **A force-free source read by an expanding receiver**: the
current divergence is the pressure work `−3`, not zero. -/
theorem expanding_receiver_reads_pressure_work :
    observerCurrentDivergence restCovector 0 (sourceMap expandingCell)
      (comovingGradient expandingCell.gradient) = -3 := by
  rw [comoving_observerDivergence]
  simp [expandingCell, dissipation_eq, trace, frob, strain, Fin.sum_univ_three]

/-- [definition] A viscous cell in simple shear (`ControlVolume.shear3`), at zero pressure. -/
def shearedCell : ConstitutedState where
  restEnergy := 1
  internalEnergy := 0
  pressure := 0
  shear := 1
  bulk := 0
  gradient := shear3
  heatFlux := 0

/-- [counterexample; formal-checked] **A force-free source read by a sheared viscous receiver**:
the current divergence is the viscous heat `Φ = 1`. -/
theorem sheared_receiver_reads_viscous_heat :
    observerCurrentDivergence restCovector 0 (sourceMap shearedCell)
      (comovingGradient shearedCell.gradient) = 1 := by
  rw [comoving_observerDivergence]
  have hΦ : dissipation 1 0 shear3 = 1 := by
    rw [dissipation_eq]
    simp [shear3, frob, strain, trace, Fin.sum_univ_three]
    norm_num
  simp [shearedCell, hΦ]

section Audit

#print axioms sourceMap_symmetric
#print axioms sourceMap_restReading
#print axioms sourceMap_perfect
#print axioms sourceMap_spatialTrace
#print axioms sourceMap_boostedEnergy
#print axioms sourceMap_spatialPower
#print axioms observerBilinear_transport
#print axioms lorentz_inverse
#print axioms boosted_reads_transported
#print axioms boostT_lorentz
#print axioms boostedObserver_eq
#print axioms sourceMap_boosted_transport
#print axioms minkowskiTrace_metric
#print axioms trace_reversal
#print axioms traceReversed_zero_zero
#print axioms sourceMap_traceReversed
#print axioms perfectFluid_traceReversed
#print axioms dust_newtonian_source
#print axioms sourceMap_newtonian_source
#print axioms comoving_observerDivergence
#print axioms rigid_comoving_reads_force
#print axioms expanding_receiver_reads_pressure_work
#print axioms sheared_receiver_reads_viscous_heat

end Audit

end Holonics.Physics.Spacetime.StressEnergy

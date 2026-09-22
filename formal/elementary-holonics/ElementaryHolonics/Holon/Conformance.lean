import ElementaryHolonics.Holon.Law
import ElementaryHolonics.Holon.Complex
import ElementaryHolonics.Holon.Generator
import ElementaryHolonics.Transport.HolonicInteraction
import ElementaryHolonics.Objects.Pairing

/-!
# Holon.Conformance: the existing owners are port Holons

[proved-derived; formal-checked]

* **Medium.** `HolonicInteraction`'s `q̇ = (Ω − M) G q + B u` is the port Holon `mediumHolon`
  (skew interconnection `mediumJ`, storage `G`, resistance `M`); every motion is admitted
  (`medium_admits`), and twice the balance's storage rate is the owner's rate-form reading
  `quad (Aᵀ G + G A) q` (`medium_rate_agrees`, through `storage_rate_reading`).
* **Holon of Holons.** Two media joined at a shared port (`two_media_witness`).
* **Diffusion** is the medium with `Ω = 0`, dissipative for passive `M` (`diffusion_dissipates`).
* **Linear SSM.** The collocated output `Bᵀ G x` is the external port flow and the balance reads
  `−⟨Gx, MGx⟩ + ⟨u, y⟩` (`ssm_port_output`); a general `y = C'(Gx)` is a passive coholon reading.
* **Parametron.** The pumped LC loop is the lossless medium with time-varying storage; its energy
  changes by the pump work `½ ċ q²` only (`lc_pump_work`, through `PortHolon.energy_balance`).
* **Maxwell** is the medium with the Stokes–Dirac skew structure `[[0, d₁ᵀ], [−d₁, 0]]` on a
  cochain complex; Gauss's law is preserved when `d₁ d₀ = 0` (`maxwell_gauss`, witness
  `triangle_face_complex`) and the balance is Joule loss plus source power (`maxwell_balance`).
* **Euler/Navier–Stokes** in the three-mode Lie–Poisson truncation `ẋ = (hat(x) − M) G x`: the
  Casimir `|x|²` is preserved by the bracket (`hat_casimir`) and the energy changes by exactly
  `−⟨Gx, M Gx⟩` (`navierStokes_balance`), zero for Euler.
* **Pair contact** is a resistive element `f = Jv`, `e = −Df` with power `−quad(faceForm 1 J D) v ≤ 0`
  (`pairContact_resistive`).
* **Event chart.** For `BoundaryHolon.comp`, the potential on the joined occurrence is the sum of
  the two port drops and the shared port contributes nothing (`comp_is_port_identification`,
  composing `Objects/Pairing.face_is_potential_drop` and the join).
-/

noncomputable section

namespace Soma.Holonics.HolonCore

open Matrix

/-! ## 1. The linear medium `q̇ = (Ω − M) G q + B u` is a port Holon -/

section Medium

variable {𝕜 : Type*} [Field 𝕜] {σ μ : Type*} [Fintype σ] [Fintype μ] [DecidableEq σ]
  [DecidableEq μ]

/-- [definition] The skew block `Ω` on the storage ports. -/
def omegaBlock (Ω : Matrix σ σ 𝕜) : Matrix (Ports σ σ μ (Fin 0)) (Ports σ σ μ (Fin 0)) 𝕜 :=
  Matrix.of fun i j => match i, j with
    | .inl i, .inl j => -Ω i j
    | _, _ => 0

/-- [definition] The one-sided couplings: storage ← resistive (`−1`) and storage ← input (`−B`). -/
def couplingBlock (B : Matrix σ μ 𝕜) : Matrix (Ports σ σ μ (Fin 0)) (Ports σ σ μ (Fin 0)) 𝕜 :=
  Matrix.of fun i j => match i, j with
    | .inl i, .inr (.inl j) => -(1 : Matrix σ σ 𝕜) i j
    | .inl i, .inr (.inr (.inl k)) => -B i k
    | _, _ => 0

/-- [definition] The skew interconnection of the medium:
`f_S = −Ω e_S − e_R − B e_P`, `f_R = e_S`, `f_P = Bᵀ e_S`. -/
def mediumJ (Ω : Matrix σ σ 𝕜) (B : Matrix σ μ 𝕜) :
    Matrix (Ports σ σ μ (Fin 0)) (Ports σ σ μ (Fin 0)) 𝕜 :=
  omegaBlock Ω + (couplingBlock B - (couplingBlock B)ᵀ)

omit [Fintype σ] [Fintype μ] [DecidableEq μ] in
theorem mediumJ_skew {Ω : Matrix σ σ 𝕜} (hΩ : Ωᵀ = -Ω) (B : Matrix σ μ 𝕜) :
    (mediumJ Ω B)ᵀ = -mediumJ Ω B := by
  have hΩ' : ∀ i j, Ω j i = -Ω i j := fun i j => by
    have := congrFun (congrFun hΩ i) j; simpa using this
  have hO : (omegaBlock (μ := μ) Ω)ᵀ = -omegaBlock Ω := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [omegaBlock, Matrix.transpose_apply, Matrix.of_apply, Matrix.neg_apply, neg_zero]
    rw [hΩ', neg_neg]
  unfold mediumJ
  rw [Matrix.transpose_add, hO, Matrix.transpose_sub, Matrix.transpose_transpose]
  abel

omit [DecidableEq μ] in
/-- [proved-derived; formal-checked] The medium interconnection in block form. -/
theorem mediumJ_mulVec (Ω : Matrix σ σ 𝕜) (B : Matrix σ μ 𝕜) (eS eR : σ → 𝕜) (eP : μ → 𝕜)
    (eA : Fin 0 → 𝕜) :
    mediumJ Ω B *ᵥ Sum.elim eS (Sum.elim eR (Sum.elim eP eA)) =
      Sum.elim (-(Ω *ᵥ eS) - eR - B *ᵥ eP) (Sum.elim eS (Sum.elim (Bᵀ *ᵥ eS) eA)) := by
  ext i
  rcases i with i | i | i | i
  · simp [mediumJ, omegaBlock, couplingBlock, mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply]
    ring
  · simp [mediumJ, omegaBlock, couplingBlock, mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.one_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply]
  · simp [mediumJ, omegaBlock, couplingBlock, mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply]
  · exact i.elim0

/-- [definition] **The medium as a port Holon**: storage `G`, skew structure `Ω`, contact
dissipation `M` on the resistive ports, inputs `B`. -/
def mediumHolon {Ω : Matrix σ σ 𝕜} (hΩ : Ωᵀ = -Ω) (M G : Matrix σ σ 𝕜) (hG : Gᵀ = G)
    (B : Matrix σ μ 𝕜) : PortHolon 𝕜 σ σ μ (Fin 0) where
  D := skewGraph (mediumJ Ω B)
  dirac := skewGraph_isDirac (mediumJ_skew hΩ B)
  Q := G
  Q_symm := hG
  R := M

/-- [proved-derived; formal-checked] **Every motion of the medium is an admitted motion of its port
Holon**: with `ẋ = (Ω − M) G q + B u`, the bond `(−ẋ, G q; G q, −M G q; Bᵀ G q, u)` lies in the
skew graph. -/
theorem medium_admits {Ω : Matrix σ σ 𝕜} (hΩ : Ωᵀ = -Ω) (M G : Matrix σ σ 𝕜) (hG : Gᵀ = G)
    (B : Matrix σ μ 𝕜) (q : σ → 𝕜) (u : μ → 𝕜) :
    (mediumHolon hΩ M G hG B).Admits G q ((Ω - M) *ᵥ (G *ᵥ q) + B *ᵥ u) (G *ᵥ q)
      (Bᵀ *ᵥ (G *ᵥ q)) u 0 0 := by
  show _ = mediumJ Ω B *ᵥ _
  simp only [assemble, mediumHolon]
  rw [mediumJ_mulVec]
  congr 1
  rw [sub_mulVec]
  abel

end Medium

/-- [proved-derived; formal-checked] **The medium's storage rate agrees with
`HolonicInteraction.port_storage_rate`.** With no input, the port Holon balance gives
`⟨G q, A q⟩ = −⟨G q, M G q⟩`, and twice it is the owner's rate-form reading
`quad (Aᵀ G + G A) q = −2 quad M (G q)` (`storage_rate_reading`). -/
theorem medium_rate_agrees {n : ℕ} (Ω M G : Matrix (Fin n) (Fin n) ℚ) (hΩ : Ωᵀ = -Ω) (hM : Mᵀ = M)
    (hG : Gᵀ = G) (q : Fin n → ℚ) :
    2 * ((G *ᵥ q) ⬝ᵥ (Transport.HolonicInteraction.portGenerator Ω M G *ᵥ q)) =
      Transport.HolonicInteraction.quad
        (Transport.HolonicInteraction.rateFormQ (Transport.HolonicInteraction.portGenerator Ω M G) G)
        q := by
  have hbal := (mediumHolon (μ := Fin 0) hΩ M G hG 0).power_balance
    (medium_admits hΩ M G hG 0 q 0)
  have hz : (0 : Fin 0 → ℚ) ⬝ᵥ (0 : Fin 0 → ℚ) = 0 := dotProduct_zero _
  have hz' : (0 : Fin 0 → ℚ) ⬝ᵥ ((0 : Matrix (Fin n) (Fin 0) ℚ)ᵀ *ᵥ (G *ᵥ q)) = 0 := by
    simp
  rw [hz, add_zero, hz', add_zero, mulVec_zero, add_zero] at hbal
  rw [Transport.HolonicInteraction.storage_rate_reading Ω M G hG hΩ hM,
    Transport.HolonicInteraction.portGenerator, ← mulVec_mulVec, hbal]
  unfold Transport.HolonicInteraction.quad
  simp only [mediumHolon]
  ring

/-- [proved-derived; formal-checked] **Witness: a Holon of Holons.** Two one-coordinate media,
joined at one shared input port, form a port Holon (`PortHolon.interconnect`) with a Dirac
structure and block storage, and its energy at `(1, 1)` with storages `2` and `3` is `1 + 3/2`,
the sum of the parts. -/
theorem two_media_witness :
    let A := mediumHolon (μ := Fin 0 ⊕ Fin 1) (Ω := (0 : Matrix (Fin 1) (Fin 1) ℚ)) (by simp)
      1 !![2] (by ext i j; fin_cases i; fin_cases j; rfl) 0
    let B := mediumHolon (μ := Fin 1 ⊕ Fin 0) (Ω := (0 : Matrix (Fin 1) (Fin 1) ℚ)) (by simp)
      1 !![3] (by ext i j; fin_cases i; fin_cases j; rfl) 0
    IsDirac (bondForm ℚ _) (A.interconnect B).D ∧
      storageEnergy (A.interconnect B).Q (Sum.elim ![1] ![1]) = 1 + 3 / 2 := by
  intro A B
  refine ⟨(A.interconnect B).dirac, ?_⟩
  show storageEnergy (Matrix.fromBlocks A.Q 0 0 B.Q) _ = _
  rw [storageEnergy_blocks]
  simp [A, B, mediumHolon, storageEnergy, dotProduct, mulVec]
  norm_num

/-! ## 2. Diffusion is the purely resistive medium -/

/-- [proved-derived; formal-checked] **Diffusion** (`Ω = 0`, `ẋ = −M G q`) dissipates: the storage
rate is `−⟨Gq, M Gq⟩ ≤ 0` for a passive `M`. Witness: `G = M = 1`, `q = 1` gives rate `−1`. -/
theorem diffusion_dissipates {n : ℕ} (M G : Matrix (Fin n) (Fin n) ℚ)
    (hMpsd : ∀ v, 0 ≤ v ⬝ᵥ (M *ᵥ v)) (q : Fin n → ℚ) :
    (G *ᵥ q) ⬝ᵥ ((0 - M) *ᵥ (G *ᵥ q)) = -((G *ᵥ q) ⬝ᵥ (M *ᵥ (G *ᵥ q))) ∧
      (G *ᵥ q) ⬝ᵥ ((0 - M) *ᵥ (G *ᵥ q)) ≤ 0 := by
  have h : (G *ᵥ q) ⬝ᵥ ((0 - M) *ᵥ (G *ᵥ q)) = -((G *ᵥ q) ⬝ᵥ (M *ᵥ (G *ᵥ q))) := by
    rw [zero_sub, neg_mulVec, dotProduct_neg]
  exact ⟨h, by rw [h]; linarith [hMpsd (G *ᵥ q)]⟩

theorem diffusion_witness :
    ((1 : Matrix (Fin 1) (Fin 1) ℚ) *ᵥ ![1]) ⬝ᵥ ((0 - 1) *ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℚ) *ᵥ ![1]))
      = -1 := by
  norm_num [dotProduct, mulVec]

/-! ## 3. The linear SSM: output as a port reading -/

/-- [proved-derived; formal-checked] **A linear SSM is a port Holon with a port output.** For
`ẋ = (Ω − M) G x + B u`, the collocated output `y = Bᵀ G x` is the external port flow, the supplied
power is `⟨u, y⟩`, and the storage rate is `−⟨Gx, M Gx⟩ + ⟨u, y⟩`. A general output `y = C' (G x)`
is a passive coholon's linear reading of the storage effort, drawing zero power. -/
theorem ssm_port_output {σ μ : Type*} [Fintype σ] [Fintype μ] [DecidableEq σ] [DecidableEq μ]
    {Ω : Matrix σ σ ℚ} (hΩ : Ωᵀ = -Ω) (M G : Matrix σ σ ℚ) (hG : Gᵀ = G) (B : Matrix σ μ ℚ)
    (x : σ → ℚ) (u : μ → ℚ) :
    (G *ᵥ x) ⬝ᵥ ((Ω - M) *ᵥ (G *ᵥ x) + B *ᵥ u) =
      -((G *ᵥ x) ⬝ᵥ (M *ᵥ (G *ᵥ x))) + u ⬝ᵥ (Bᵀ *ᵥ (G *ᵥ x)) := by
  have hbal := (mediumHolon hΩ M G hG B).power_balance (medium_admits hΩ M G hG B x u)
  have hz : (0 : Fin 0 → ℚ) ⬝ᵥ (0 : Fin 0 → ℚ) = 0 := dotProduct_zero _
  rw [hz, add_zero] at hbal
  exact hbal

/-! ## 4. The parametron LC loop with a pump -/

/-- [definition] The LC storage with time-varying inverse capacitance `c(t)` and fixed `1/L = l`. -/
def lcStorage (c : ℝ → ℝ) (l : ℝ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c t, 0; 0, l]

/-- [definition] The LC exchange `q̇ = l φ`, `φ̇ = −c q` as a skew structure on the efforts. -/
def lcExchange : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

theorem lcExchange_skew : lcExchangeᵀ = -lcExchange := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [lcExchange]

/-- [proved-derived; formal-checked] **The pumped LC loop is a lossless port Holon whose energy
change is the pump work.** It is the medium with `Ω` the LC exchange, no contact dissipation and
no inputs; along its motion `ẋ = Ω Q(t) x` with storage `Q(t) = diag(c(t), l)`, the balance
`PortHolon.energy_balance` returns only the deposition term: `dE/dt = ½ ċ q²`. -/
theorem lc_pump_work {c : ℝ → ℝ} {cd l : ℝ} {x : ℝ → Fin 2 → ℝ} {t : ℝ}
    (hc : HasDerivAt c cd t)
    (hx : ∀ i, HasDerivAt (fun s => x s i) ((lcExchange *ᵥ (lcStorage c l t *ᵥ x t)) i) t) :
    HasDerivAt (fun s => storageEnergy (lcStorage c l s) (x s))
      ((1 / 2) * (cd * x t 0 ^ 2)) t := by
  have hQ : ∀ i j, HasDerivAt (fun s => lcStorage c l s i j)
      ((!![cd, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) i j) t := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [lcStorage] <;>
      first | exact hc | exact hasDerivAt_const _ _
  have hsymm : (lcStorage c l t)ᵀ = lcStorage c l t := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [lcStorage]
  have hv : lcExchange *ᵥ (lcStorage c l t *ᵥ x t) =
      (lcExchange - 0) *ᵥ (lcStorage c l t *ᵥ x t) + (0 : Matrix (Fin 2) (Fin 0) ℝ) *ᵥ 0 := by
    simp
  rw [hv] at hx
  have h := (mediumHolon lcExchange_skew 0 (lcStorage c l t) hsymm 0).energy_balance hx hQ hsymm
    (medium_admits lcExchange_skew 0 (lcStorage c l t) hsymm 0 (x t) 0)
  refine h.congr_deriv ?_
  simp [mediumHolon, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- [proved-derived; formal-checked] Witness: a constant capacitance conserves the LC energy; a
pump `ċ = 1` at `q = 1` supplies power `1/2`. -/
theorem lc_pump_witness {x : ℝ → Fin 2 → ℝ} {t : ℝ} (hx0 : x t 0 = 1) :
    (1 / 2 : ℝ) * (0 * x t 0 ^ 2) = 0 ∧ (1 / 2 : ℝ) * (1 * x t 0 ^ 2) = 1 / 2 := by
  rw [hx0]; norm_num

/-! ## 4b. Maxwell: the Stokes–Dirac medium on a cochain complex -/

section Maxwell

variable {𝕜 : Type*} [Field 𝕜] {ν ε κ : Type*} [Fintype ν] [Fintype ε] [Fintype κ]

/-- [definition] The Maxwell skew structure on `(D on edges, B on faces)`:
`Ḋ = d₁ᵀ H`, `Ḃ = −d₁ E` with `(E, H)` the storage efforts. -/
def maxwellSkew (d₁ : Matrix κ ε 𝕜) : Matrix (ε ⊕ κ) (ε ⊕ κ) 𝕜 :=
  Matrix.fromBlocks 0 d₁ᵀ (-d₁) 0

omit [Fintype ε] [Fintype κ] in
theorem maxwellSkew_skew (d₁ : Matrix κ ε 𝕜) : (maxwellSkew d₁)ᵀ = -maxwellSkew d₁ := by
  rw [maxwellSkew, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]; simp

omit [Fintype ν] in
/-- [proved-derived; formal-checked] **Gauss's law is preserved.** With `d₁ d₀ = 0`, the lossless
Maxwell rate of the edge field has zero discrete divergence: `d₀ᵀ Ḋ = (d₁d₀)ᵀ H = 0`. -/
theorem maxwell_gauss (d₀ : Matrix ε ν 𝕜) (d₁ : Matrix κ ε 𝕜) (hdd : d₁ * d₀ = 0)
    (E : ε → 𝕜) (H : κ → 𝕜) :
    d₀ᵀ *ᵥ ((maxwellSkew d₁ *ᵥ Sum.elim E H) ∘ Sum.inl) = 0 := by
  rw [maxwellSkew, Matrix.fromBlocks_mulVec]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, zero_add, add_zero]
  rw [mulVec_mulVec, ← Matrix.transpose_mul, hdd, Matrix.transpose_zero, zero_mulVec]

/-- [proved-derived; formal-checked] Witness: the triangle with its one face, `d₁ = (1, 1, 1)`,
satisfies `d₁ d₀ = 0`, so Gauss's law is preserved on it. -/
theorem triangle_face_complex : (!![1, 1, 1] : Matrix (Fin 1) (Fin 3) ℚ) * triangle = 0 := by
  ext i j; fin_cases i; fin_cases j <;> simp [triangle, Matrix.mul_apply, Fin.sum_univ_three]

end Maxwell

/-- [proved-derived; formal-checked] **Maxwell is a port Holon.** With storage `G = diag(ε⁻¹, μ⁻¹)`,
Ohmic conduction `M` on the edges and sources `B`, every motion
`ẋ = (Ω_Maxwell − M) G x + B u` is admitted by the medium Holon with `Ω = maxwellSkew d₁`, and the
balance reads `⟨Gx, ẋ⟩ = −⟨Gx, M Gx⟩ + ⟨u, Bᵀ G x⟩` (Joule loss plus source power). -/
theorem maxwell_balance {ε κ μ : Type*} [Fintype ε] [Fintype κ] [Fintype μ] [DecidableEq ε]
    [DecidableEq κ] [DecidableEq μ] (d₁ : Matrix κ ε ℚ) (M G : Matrix (ε ⊕ κ) (ε ⊕ κ) ℚ)
    (hG : Gᵀ = G) (B : Matrix (ε ⊕ κ) μ ℚ) (x : ε ⊕ κ → ℚ) (u : μ → ℚ) :
    (G *ᵥ x) ⬝ᵥ ((maxwellSkew d₁ - M) *ᵥ (G *ᵥ x) + B *ᵥ u) =
      -((G *ᵥ x) ⬝ᵥ (M *ᵥ (G *ᵥ x))) + u ⬝ᵥ (Bᵀ *ᵥ (G *ᵥ x)) :=
  ssm_port_output (maxwellSkew_skew d₁) M G hG B x u

/-! ## 4c. Euler and Navier–Stokes: Lie–Poisson plus viscous resistance -/

/-- [definition] The Lie–Poisson structure of `so(3)` (the three-mode Galerkin triad):
`hat(x) w = x × w`. -/
def hat (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -x 2, x 1; x 2, 0, -x 0; -x 1, x 0, 0]

theorem hat_skew (x : Fin 3 → ℝ) : (hat x)ᵀ = -hat x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hat]

/-- [proved-derived; formal-checked] **The Casimir.** `⟨x, hat(x) w⟩ = 0`: the Lie–Poisson flow
preserves `|x|²` whatever the storage. -/
theorem hat_casimir (x w : Fin 3 → ℝ) : x ⬝ᵥ (hat x *ᵥ w) = 0 := by
  simp [hat, mulVec, dotProduct, Fin.sum_univ_three]; ring

/-- [proved-derived; formal-checked] **Euler/Navier–Stokes as a port Holon.** For the modulated
Dirac structure `Ω = hat(x)` (Lie–Poisson), storage `G` and viscous resistance `M`, along
`ẋ = (hat(x) − M) G x` the energy `½⟨x, Gx⟩` changes by exactly `−⟨Gx, M Gx⟩`: zero for Euler
(`M = 0`), the viscous dissipation for Navier–Stokes. -/
theorem navierStokes_balance (M G : Matrix (Fin 3) (Fin 3) ℝ) (hG : Gᵀ = G) {x : ℝ → Fin 3 → ℝ}
    {t : ℝ} (hx : ∀ i, HasDerivAt (fun s => x s i) (((hat (x t) - M) *ᵥ (G *ᵥ x t)) i) t) :
    HasDerivAt (fun s => storageEnergy G (x s)) (-((G *ᵥ x t) ⬝ᵥ (M *ᵥ (G *ᵥ x t)))) t := by
  have hv : (hat (x t) - M) *ᵥ (G *ᵥ x t) =
      (hat (x t) - M) *ᵥ (G *ᵥ x t) + (0 : Matrix (Fin 3) (Fin 0) ℝ) *ᵥ 0 := by simp
  rw [hv] at hx
  have h := (mediumHolon (hat_skew (x t)) M G hG 0).energy_balance_const hx
    (medium_admits (hat_skew (x t)) M G hG 0 (x t) 0)
  refine h.congr_deriv ?_
  simp [mediumHolon]

/-! ## 5. The pair contact is a resistive element -/

/-- [proved-derived; formal-checked] **The pair contact as a resistive element.** With slip flow
`f = J v` and traction effort `e = −D f`, the element's power is `−⟨J v, D J v⟩`, which is minus
the contact form `HolonicInteraction.quad_faceForm` at unit weight; it is dissipative when `D` is
positive semidefinite. -/
theorem pairContact_resistive {r n : ℕ} (J : Matrix (Fin r) (Fin n) ℚ) (D : Matrix (Fin r) (Fin r) ℚ)
    (hD : ∀ s, 0 ≤ s ⬝ᵥ (D *ᵥ s)) (v : Fin n → ℚ) :
    power ((J *ᵥ v, -(D *ᵥ (J *ᵥ v))) : Bond ℚ (Fin r)) =
      -Transport.HolonicInteraction.quad (Transport.HolonicInteraction.faceForm 1 J D) v ∧
      power ((J *ᵥ v, -(D *ᵥ (J *ᵥ v))) : Bond ℚ (Fin r)) ≤ 0 := by
  have h : power ((J *ᵥ v, -(D *ᵥ (J *ᵥ v))) : Bond ℚ (Fin r)) =
      -Transport.HolonicInteraction.quad (Transport.HolonicInteraction.faceForm 1 J D) v := by
    rw [Transport.HolonicInteraction.quad_faceForm, power, neg_dotProduct, dotProduct_comm]
    ring
  exact ⟨h, by rw [h, Transport.HolonicInteraction.quad_faceForm]; linarith [hD (J *ᵥ v)]⟩

/-! ## 6. The event chart: an occurrence is a port event -/

section EventChart

variable {R C₀ Cur : Type*} [CommRing R] [AddCommGroup C₀] [Module R C₀] [AddCommGroup Cur]

/-- [proved-derived; formal-checked] **An occurrence is a port event; composition is port
identification.** For `BoundaryHolon.comp`, the potential read on the joined occurrence's returned
current is the sum of the two port drops, and the shared port contributes nothing: the join
`left.target = right.source` identifies the two ports, whose efforts are then equal. -/
theorem comp_is_port_identification (H₁ H₂ : BoundaryHolon C₀ Cur)
    (same : H₂.boundary = H₁.boundary) (φ : Objects.Pairing.Coholon R C₀)
    (o : (BoundaryHolon.comp H₂ H₁ same).Occurrence) :
    φ ((BoundaryHolon.comp H₂ H₁ same).boundary ((BoundaryHolon.comp H₂ H₁ same).receive o)) =
      (φ (H₁.target o.left) - φ (H₁.source o.left)) +
        (φ (H₂.target o.right) - φ (H₂.source o.right)) ∧
      φ (H₁.target o.left) - φ (H₂.source o.right) = 0 := by
  refine ⟨?_, by rw [show H₁.target o.left = H₂.source o.right from o.joins, sub_self]⟩
  rw [Objects.Pairing.face_is_potential_drop]
  have hj : H₁.target o.left = H₂.source o.right := o.joins
  change φ (H₂.target o.right) - φ (H₁.source o.left) = _
  rw [hj]; ring

end EventChart

end Soma.Holonics.HolonCore

import Holonics.HNN.Floquet
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# HNN.DrivenRingSupply: the driven ring's supply-rate certificate, its span and the field's return

[definition] The pumped ring of `HNN/Floquet` with its port loaded. One executed tick of the ring
driven through its port is `x′ = M x + B e`: `M` the undriven tick (the port terminated, the
operator `HNN/Floquet` certifies by `Mᵀ G M ⪯ ρ² G`), `B` the loaded port and `e` the drive the
field sends into the ring. A **supply-rate certificate** of the tick in the form `G` is
`E_G(M x + B e) ≤ σ² E_G(x) + s(x, e)` for every state and drive (`SupplyCertifies`): the energy
the ring carries to the next tick is at most its own growth `σ²` plus the supply `s` that crossed
the port. The supply is read on the state and the drive, so the record's `supply(e, s′)` is one of
these whenever its second argument is read from the pair (a port output `C x + D e`, or the next
state `M x + B e`). A span of such ticks
(`DrivenTick`, `drivenSpan`) is the driven ring's loop within a span.

Sources. The box of #410: "The carried pumped loop's supply-rate certificate, which the founded
ring's driven span needs (`Field::{found, founding_cost}`)". `Holonics/Holon/Deposition`'s open
paragraph ("the driven ring's supply-rate certificate `E_G(x′) ≤ σ²E_G(x) + supply(e, s′)` that would
discharge that factorization through the field's return into the ring is owed"); the record of
September 29, "The certified step reads the Floquet reach: a deposit through a pumped ring is
certified below and past its bifurcation" (`research/records/2026-09-29_THE_CERTIFIED_STEP_READS_`
`THE_FLOQUET_REACH_A_DEPOSIT_THROUGH_A_PUMPED_RING_IS_CERTIFIED_BELOW_AND_PAST_ITS_BIFURCATION.md`),
§6 item 1 (the driven ring's loop, owed beside `HNN/Floquet` and `Holon/Deposition` §10). The owner
is `Holonics/HNN/Floquet` (`energy`, `FloquetCertifies`, `FormNonneg`, `certificate_reading`,
`floquet_energy_step`, `floquet_span_reach`). Atlas rows: `parametron.floquet-certificate`,
`parametron.floquet-consumer` and `hnn.pumped-span-factor`, each of which names this loop owed;
`ph.lc-pump-work` (a pumped loop's only energy change is the pump's supply) and
`physics.port-hamiltonian` (a port's supply is its effort–flow pairing).

What is proved.

1. **The supply-rate certificate from the undriven one (Young).** [proved-standard; formal-checked]
   For any form with `E_G ≥ 0` (no symmetry asked) the energy along a line is
   `E_G(u + t v) = E_G(u) + t c + t² E_G(v)`, `c = ⟨u, G v⟩ + ⟨v, G u⟩` (`energy_add_smul`,
   `energy_add`, `energy_smul`); the form's positivity on that line gives its Cauchy–Schwarz
   `c² ≤ 4 E_G(u) E_G(v)` (`form_cauchy_schwarz`; for symmetric `G`,
   `⟨u, G v⟩² ≤ E_G(u) E_G(v)`, `form_cauchy_schwarz_symm`) and Young's split `c ≤ ε E_G(u) + E_G(v)/ε`
   (`form_young`). [proved-derived; formal-checked] So the certificate `Mᵀ G M ⪯ ρ² G` gives, for every
   `ε > 0`, `E_G(M x + B e) ≤ (1 + ε) ρ² E_G(x) + (1 + 1/ε) E_G(B e)` (`young_supply`): the undriven
   ring is supply-certified at `σ² = (1 + ε)ρ²` with the quadratic supply `(1 + 1/ε) BᵀGB`
   (`young_certifies`, `energy_smul_pullback`, `young_block_nonneg`).
2. **The dissipation form (KYP).** [proved-standard; formal-checked] With a quadratic supply
   `s(e) = e ⬝ S e`, the block form
   `[[σ²G − MᵀGM, −MᵀGB], [−BᵀGM, S − BᵀGB]]` read on `(x, e)` is
   `σ² E_G(x) + s(e) − E_G(M x + B e)` (`dissipationBlock_reading`, through `pullback_pairing`), so the
   supply-rate inequality for all `(x, e)` holds iff the block form is positive semidefinite on
   `n ⊕ m` (`supply_certifies_iff_block`). The undriven certificate is its `e = 0` face
   (`supply_certifies_undriven`, `block_undriven_face`), and its `(x, x)` corner is the certificate's
   own form (`dissipationBlock_corner`).
3. **The driven span.** [proved-standard; formal-checked] A real sequence with
   `a_(k+1) ≤ r_k a_k + c_k`, `r_k ≥ 0`, obeys the discrete Grönwall bound
   `a_N ≤ (∏_(k<N) r_k) a_0 + Σ_(t<N) (∏_(t<k<N) r_k) c_t` (`discrete_gronwall`). [proved-derived;
   formal-checked] So a span of ticks each supply-certified in one `G` satisfies
   `E_G(x_N) ≤ (∏_t σ_t²) E_G(x₀) + Σ_t (∏_(k>t) σ_k²) s_t(x_t, e_t)` (`driven_span_bound`), read in a
   reference form `γ_lo Q ⪯ G ⪯ γ_hi Q` as `γ_lo E_Q(x_N) ≤ γ_hi (∏_t σ_t²) E_Q(x₀) + Σ_t …`
   (`driven_span_metric_change`). With the drive switched off and supplies not positive there, the span
   is the product of its undriven ticks (`spanTransport`, `drivenSpan_undriven`), certified at
   `∏_t σ_t²` (`undriven_partial_period`), and two such partial periods around `k` whole periods
   read the owner's undriven reach
   `E_Q(Post Mᵏ Pre x) ≤ (γ_hi/γ_lo) σ_post ρ^(2k) σ_pre E_Q(x)` (`undriven_span_reach`, through
   `floquet_span_reach`).
4. **Below, at and past the bifurcation.** [proved-standard; formal-checked] At one growth `σ² ≥ 0`
   (every tick's `σ_t² ≤ σ²`, `E_G ≥ 0`) with supplies along the span at most `s̄`:
   `E_G(x_N) ≤ σ^(2N) E_G(x₀) + s̄ Σ_(j<N) σ^(2j)` (`gronwall_const`, `driven_span_const`); below,
   `σ² < 1`, `E_G(x_N) ≤ σ^(2N) E_G(x₀) + s̄ (1 − σ^(2N))/(1 − σ²)` (`driven_span_below`), and with
   `s̄ ≥ 0` the energy stays under `E_G(x₀) + s̄/(1 − σ²)` for every span (`driven_span_below_uniform`):
   a bounded drive keeps a bounded energy; at `σ² = 1`, `E_G(x_N) ≤ E_G(x₀) + N s̄`
   (`driven_span_at`); past it, `σ² > 1` and `s̄ ≥ 0`, `E_G(x_N) ≤ σ^(2N) (E_G(x₀) + s̄/(σ² − 1))`
   (`driven_span_past`).
5. **The field's return into the ring (small gain).** [proved-standard; formal-checked] If the drive
   is the field's return `e = K x` (the loaded port closed by the field) and its supply obeys
   `s(x, K x) ≤ μ E_G(x)`, the closed loop `M + B K` is certified at `σ² + μ`:
   `FloquetCertifies G (M + B K) (σ² + μ)` (`return_certifies`); for a quadratic supply the hypothesis is
   `KᵀSK ⪯ μ G` (`return_quadratic`). [proved-derived; formal-checked] The span through the return then
   reads the owner's reach at `σ² + μ` (`return_span_reach`): the factorization of
   `Holon/Deposition` §10 is discharged through the field's return, its whole periods certified as
   the closed loop's.
6. **A witness.** [proved-derived; formal-checked] The quarter turn damped by `½`,
   `M = ½ [[0, −1], [1, 0]]` (`ringTurn`, `ringTurn_eq`), in `G = 1` with `B = 1`: `MᵀM = ¼ I`
   (`ringTurn_gram`), so it is certified at `σ² = ¼` (`witness_certificate`); at `ε = 1` the Young
   supply reads `E(M x + e) ≤ ½ E(x) + 2 E(e)` (`witness_young`); drives with `E(e_t) ≤ 1` keep
   `E(x_N) ≤ 2^(−N) E(x₀) + 4 (1 − 2^(−N))` (`witness_span`) and so under `E(x₀) + 4`
   (`witness_span_uniform`); the return `K = ¼ I` supplies `⅛ E(x)`, so the closed loop
   `[[¼, −½], [½, ¼]]` is certified at `½ + ⅛ = ⅝ < 1` (`witness_return`) and is passive over every
   number of periods (`witness_return_passive`). Its own Gram reads `5/16 I`
   (`closedLoop_eq`, `witness_closed_loop_own`): the small-gain reading stands above the closed loop's
   own certificate by the Young split's price.

What is not claimed. The reach along a ring's own gain ray (a certificate over the tube of
monodromies `M_T(η)`, the record's §6 item 2); a modulated pump's passage-dependent schedule (item
4); the executed chart's lattice word against the law's ticks (item 5); the word-level composition of
each span's gain (item 3); continuous-time dissipation (the KYP lemma for `ẋ = A x + B e`); the
frequency-domain side of the KYP lemma, or the existence of a quadratic storage for a given supply
(both take controllability hypotheses and are not the algebraic identity proved here). The consumer
the box names, `Field::{found, founding_cost}`, and the span reach the record's runs read
(`hnn::ring::FloquetBound::reach`, `hnn::constitution`) are Rust in the October library
(`crates/holonics/src/hnn/field.rs@d5ed4adc1`, `crates/holonics/src/hnn/ring.rs@d5ed4adc1`), which
retired with C8 of #603; they are named, not restated, and no statement here is read from them.

The computational object is the helical pair interaction read on the pumped ring with its port
loaded: the ring is a parametron whose pump's period composes its monodromy, the cell holonomy of
the pump's cycle; the loaded port is the pair contact through which the field drives the ring, and
the supply is the power that contact passes; the field's return closes the contact back on the ring,
and the small-gain step reads what that loop adds to the ring's growth. Of the winding guide's six
general objects this touches the helix (the ring's ticks over its pump period, the span their
carry), the pair (the loaded port and its return), the cell holonomy (the monodromy certified per
period) and the tube (the span as a longitudinal clocked run of ticks and its reach); faces and
placement and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.DrivenRingSupply

open Matrix Finset
open Holonics.HNN.Floquet
open scoped BigOperators

/-! ## 1. The supply-rate certificate and the Young supply -/

section Young

variable {n m : Type*} [Fintype n] [Fintype m]

/-- [definition] **The supply-rate certificate** of a driven tick `x′ = M x + B e` in the form `G`:
`E_G(M x + B e) ≤ σ² E_G(x) + s(x, e)` for every state and drive. -/
def SupplyCertifies (G M : Matrix n n ℝ) (B : Matrix n m ℝ) (σ2 : ℝ)
    (s : (n → ℝ) → (m → ℝ) → ℝ) : Prop :=
  ∀ x e, energy G (M *ᵥ x + B *ᵥ e) ≤ σ2 * energy G x + s x e

/-- [definition] **The form's cross term** `⟨u, G v⟩ + ⟨v, G u⟩`, twice its symmetric part's
pairing. -/
def crossTerm (G : Matrix n n ℝ) (u v : n → ℝ) : ℝ := u ⬝ᵥ (G *ᵥ v) + v ⬝ᵥ (G *ᵥ u)

/-- [proved-standard; formal-checked] **The energy along a line**:
`E_G(u + t v) = E_G(u) + t c + t² E_G(v)`. -/
theorem energy_add_smul (G : Matrix n n ℝ) (u v : n → ℝ) (t : ℝ) :
    energy G (u + t • v) = energy G u + t * crossTerm G u v + t ^ 2 * energy G v := by
  unfold energy crossTerm
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/-- [proved-standard; formal-checked] **The energy of a sum**: `E_G(u + v) = E_G(u) + c + E_G(v)`. -/
theorem energy_add (G : Matrix n n ℝ) (u v : n → ℝ) :
    energy G (u + v) = energy G u + crossTerm G u v + energy G v := by
  simpa using energy_add_smul G u v 1

/-- [proved-standard; formal-checked] **The energy is quadratic**: `E_G(c x) = c² E_G(x)`. -/
theorem energy_smul (G : Matrix n n ℝ) (c : ℝ) (x : n → ℝ) :
    energy G (c • x) = c ^ 2 * energy G x := by
  unfold energy
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

/-- [proved-standard; formal-checked] **The form's Cauchy–Schwarz**: for `E_G ≥ 0`,
`(⟨u, G v⟩ + ⟨v, G u⟩)² ≤ 4 E_G(u) E_G(v)`. -/
theorem form_cauchy_schwarz {G : Matrix n n ℝ} (hG : FormNonneg G) (u v : n → ℝ) :
    crossTerm G u v ^ 2 ≤ 4 * energy G u * energy G v := by
  have h : ∀ t : ℝ, 0 ≤ energy G v * (t * t) + crossTerm G u v * t + energy G u := by
    intro t
    have ht := hG (u + t • v)
    rw [energy_add_smul] at ht
    have e : energy G v * (t * t) + crossTerm G u v * t + energy G u =
        energy G u + t * crossTerm G u v + t ^ 2 * energy G v := by ring
    rw [e]
    exact ht
  have hd := discrim_le_zero h
  unfold discrim at hd
  linarith

/-- [proved-standard; formal-checked] **Cauchy–Schwarz for a symmetric form**:
`⟨u, G v⟩² ≤ E_G(u) E_G(v)`. -/
theorem form_cauchy_schwarz_symm {G : Matrix n n ℝ} (hS : G.IsSymm) (hG : FormNonneg G)
    (u v : n → ℝ) : (u ⬝ᵥ (G *ᵥ v)) ^ 2 ≤ energy G u * energy G v := by
  have hsym : v ⬝ᵥ (G *ᵥ u) = u ⬝ᵥ (G *ᵥ v) := by
    rw [dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hS.eq]
  have h := form_cauchy_schwarz hG u v
  unfold crossTerm at h
  rw [hsym] at h
  nlinarith

/-- [proved-standard; formal-checked] **Young's split of the cross term**: for `E_G ≥ 0` and
`ε > 0`, `c ≤ ε E_G(u) + ε⁻¹ E_G(v)`. -/
theorem form_young {G : Matrix n n ℝ} (hG : FormNonneg G) {ε : ℝ} (hε : 0 < ε) (u v : n → ℝ) :
    crossTerm G u v ≤ ε * energy G u + ε⁻¹ * energy G v := by
  have h := hG (u + (-ε⁻¹) • v)
  rw [energy_add_smul] at h
  have hinv : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
  have key : ε * (energy G u + -ε⁻¹ * crossTerm G u v + (-ε⁻¹) ^ 2 * energy G v) =
      ε * energy G u - (ε * ε⁻¹) * crossTerm G u v + (ε * ε⁻¹) * ε⁻¹ * energy G v := by ring
  rw [hinv] at key
  have h2 := mul_nonneg hε.le h
  rw [key] at h2
  linarith

/-- [proved-derived; formal-checked] **The undriven certificate supplies the driven tick**:
`Mᵀ G M ⪯ ρ² G` gives `E_G(M x + B e) ≤ (1 + ε) ρ² E_G(x) + (1 + 1/ε) E_G(B e)` for `ε > 0`. -/
theorem young_supply {G M : Matrix n n ℝ} {ρ2 ε : ℝ} (hG : FormNonneg G)
    (hcert : FloquetCertifies G M ρ2) (hε : 0 < ε) (B : Matrix n m ℝ) (x : n → ℝ) (e : m → ℝ) :
    energy G (M *ᵥ x + B *ᵥ e) ≤ (1 + ε) * ρ2 * energy G x + (1 + 1 / ε) * energy G (B *ᵥ e) := by
  rw [energy_add, one_div]
  have hy := form_young hG hε (M *ᵥ x) (B *ᵥ e)
  have hstep := floquet_energy_step hcert x
  have h1 : 0 ≤ 1 + ε := by linarith
  have h2 := mul_le_mul_of_nonneg_left hstep h1
  linarith

/-- [proved-derived; formal-checked] **The Young supply as a certificate**: the undriven ring is
supply-certified at `σ² = (1 + ε) ρ²` with the supply `(1 + 1/ε) E_G(B e)`. -/
theorem young_certifies {G M : Matrix n n ℝ} {ρ2 ε : ℝ} (hG : FormNonneg G)
    (hcert : FloquetCertifies G M ρ2) (hε : 0 < ε) (B : Matrix n m ℝ) :
    SupplyCertifies G M B ((1 + ε) * ρ2) (fun _ e => (1 + 1 / ε) * energy G (B *ᵥ e)) :=
  fun x e => young_supply hG hcert hε B x e

end Young

/-! ## 2. The dissipation form (KYP) -/

section Block

variable {n m : Type*} [Fintype n] [Fintype m]

/-- [proved-standard; formal-checked] **A pulled-back pairing**:
`x ⬝ (Pᵀ G R) y = (P x) ⬝ G (R y)`. -/
theorem pullback_pairing {k l : Type*} [Fintype k] [Fintype l] (G : Matrix n n ℝ)
    (P : Matrix n k ℝ) (R : Matrix n l ℝ) (x : k → ℝ) (y : l → ℝ) :
    x ⬝ᵥ ((Pᵀ * G * R) *ᵥ y) = (P *ᵥ x) ⬝ᵥ (G *ᵥ (R *ᵥ y)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, Matrix.vecMul_transpose]

/-- [proved-standard; formal-checked] **A quadratic supply through the port's pullback**:
`E_(c BᵀGB)(e) = c E_G(B e)`. -/
theorem energy_smul_pullback (G : Matrix n n ℝ) (B : Matrix n m ℝ) (c : ℝ) (e : m → ℝ) :
    energy (c • (Bᵀ * G * B)) e = c * energy G (B *ᵥ e) := by
  unfold energy
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, pullback_pairing]

/-- [definition] **The dissipation form** of a driven tick with the quadratic supply `e ⬝ S e`:
`[[σ²G − MᵀGM, −MᵀGB], [−BᵀGM, S − BᵀGB]]` on `n ⊕ m`. -/
def dissipationBlock (G M : Matrix n n ℝ) (B : Matrix n m ℝ) (σ2 : ℝ) (S : Matrix m m ℝ) :
    Matrix (n ⊕ m) (n ⊕ m) ℝ :=
  Matrix.fromBlocks (σ2 • G - Mᵀ * G * M) (-(Mᵀ * G * B)) (-(Bᵀ * G * M)) (S - Bᵀ * G * B)

omit [Fintype m] in
/-- [proved-standard; formal-checked] **The dissipation form's corner is the undriven
certificate's form** `σ²G − MᵀGM`. -/
theorem dissipationBlock_corner (G M : Matrix n n ℝ) (B : Matrix n m ℝ) (σ2 : ℝ)
    (S : Matrix m m ℝ) : (dissipationBlock G M B σ2 S).toBlocks₁₁ = σ2 • G - Mᵀ * G * M :=
  Matrix.toBlocks_fromBlocks₁₁ _ _ _ _

/-- [proved-standard; formal-checked] **The dissipation form read on a state and a drive**:
`(x, e) ⬝ D (x, e) = σ² E_G(x) + e ⬝ S e − E_G(M x + B e)`. -/
theorem dissipationBlock_reading (G M : Matrix n n ℝ) (B : Matrix n m ℝ) (σ2 : ℝ)
    (S : Matrix m m ℝ) (x : n → ℝ) (e : m → ℝ) :
    (Sum.elim x e) ⬝ᵥ (dissipationBlock G M B σ2 S *ᵥ Sum.elim x e) =
      σ2 * energy G x + energy S e - energy G (M *ᵥ x + B *ᵥ e) := by
  rw [dissipationBlock, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    sumElim_dotProduct_sumElim, energy_add]
  simp only [Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.smul_mulVec, dotProduct_add,
    dotProduct_sub, dotProduct_neg, dotProduct_smul, smul_eq_mul, pullback_pairing]
  unfold energy crossTerm
  ring

/-- [proved-standard; formal-checked] **The supply-rate inequality is the dissipation form's
positivity**: `E_G(M x + B e) ≤ σ² E_G(x) + e ⬝ S e` for all `(x, e)` iff the block form is positive
semidefinite on `n ⊕ m`. -/
theorem supply_certifies_iff_block (G M : Matrix n n ℝ) (B : Matrix n m ℝ) (σ2 : ℝ)
    (S : Matrix m m ℝ) :
    SupplyCertifies G M B σ2 (fun _ e => energy S e) ↔
      ∀ z : n ⊕ m → ℝ, 0 ≤ z ⬝ᵥ (dissipationBlock G M B σ2 S *ᵥ z) := by
  constructor
  · intro h z
    have hz := Sum.elim_comp_inl_inr z
    rw [← hz, dissipationBlock_reading]
    have := h (z ∘ Sum.inl) (z ∘ Sum.inr)
    linarith
  · intro h x e
    have hb := h (Sum.elim x e)
    rw [dissipationBlock_reading] at hb
    linarith

/-- [proved-standard; formal-checked] **The undriven certificate is the supply certificate's
`e = 0` face**: a supply that is not positive at zero drive leaves `Mᵀ G M ⪯ σ² G`. -/
theorem supply_certifies_undriven {G M : Matrix n n ℝ} {B : Matrix n m ℝ} {σ2 : ℝ}
    {s : (n → ℝ) → (m → ℝ) → ℝ} (h : SupplyCertifies G M B σ2 s) (h0 : ∀ x, s x 0 ≤ 0) :
    FloquetCertifies G M σ2 := by
  intro x
  rw [certificate_reading]
  have hx := h x 0
  rw [Matrix.mulVec_zero, add_zero] at hx
  linarith [h0 x]

/-- [proved-standard; formal-checked] **The dissipation form's `e = 0` face**: a positive
semidefinite block form certifies the undriven tick at `σ²`. -/
theorem block_undriven_face {G M : Matrix n n ℝ} {B : Matrix n m ℝ} {σ2 : ℝ} {S : Matrix m m ℝ}
    (h : ∀ z : n ⊕ m → ℝ, 0 ≤ z ⬝ᵥ (dissipationBlock G M B σ2 S *ᵥ z)) :
    FloquetCertifies G M σ2 :=
  supply_certifies_undriven ((supply_certifies_iff_block G M B σ2 S).mpr h) fun _ => by
    simp [energy]

/-- [proved-derived; formal-checked] **The Young supply makes the dissipation form positive**:
`Mᵀ G M ⪯ ρ² G` and `ε > 0` give a positive semidefinite block form at `σ² = (1 + ε) ρ²` and
`S = (1 + 1/ε) BᵀGB`. -/
theorem young_block_nonneg {G M : Matrix n n ℝ} {ρ2 ε : ℝ} (hG : FormNonneg G)
    (hcert : FloquetCertifies G M ρ2) (hε : 0 < ε) (B : Matrix n m ℝ) (z : n ⊕ m → ℝ) :
    0 ≤ z ⬝ᵥ (dissipationBlock G M B ((1 + ε) * ρ2) ((1 + 1 / ε) • (Bᵀ * G * B)) *ᵥ z) := by
  refine (supply_certifies_iff_block G M B _ _).mp ?_ z
  intro x e
  beta_reduce
  rw [energy_smul_pullback]
  exact young_supply hG hcert hε B x e

end Block

/-! ## 3. The driven span -/

section Span

variable {n m : Type*} [Fintype n] [Fintype m]

/-- [proved-standard; formal-checked] **The discrete Grönwall bound**: `a_(k+1) ≤ r_k a_k + c_k`
with `r_k ≥ 0` gives `a_N ≤ (∏_(k<N) r_k) a_0 + Σ_(t<N) (∏_(t<k<N) r_k) c_t`. -/
theorem discrete_gronwall (a r c : ℕ → ℝ) :
    ∀ N : ℕ, (∀ k < N, 0 ≤ r k) → (∀ k < N, a (k + 1) ≤ r k * a k + c k) →
      a N ≤ (∏ k ∈ range N, r k) * a 0 + ∑ t ∈ range N, (∏ k ∈ Ico (t + 1) N, r k) * c t := by
  intro N
  induction N with
  | zero => intro _ _; simp
  | succ N ih =>
    intro hr hstep
    have ihN := ih (fun k hk => hr k (Nat.lt_succ_of_lt hk))
      (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
    have hsum : ∑ t ∈ range (N + 1), (∏ k ∈ Ico (t + 1) (N + 1), r k) * c t =
        r N * ∑ t ∈ range N, (∏ k ∈ Ico (t + 1) N, r k) * c t + c N := by
      rw [Finset.sum_range_succ, Finset.Ico_self, Finset.prod_empty, one_mul, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Finset.prod_Ico_succ_top (Nat.succ_le_of_lt (Finset.mem_range.mp ht))]
      ring
    rw [hsum, Finset.prod_range_succ]
    have h1 := hstep N (Nat.lt_succ_self N)
    have h2 := mul_le_mul_of_nonneg_left ihN (hr N (Nat.lt_succ_self N))
    linarith

/-- [definition] **A driven tick**: the undriven tick `M`, the loaded port `B`, the tick's growth
`σ²` in the form and the supply `s(x, e)` through the port. -/
structure DrivenTick (n m : Type*) where
  /-- The undriven tick (the port terminated). -/
  M : Matrix n n ℝ
  /-- The loaded port: how the drive enters the ring. -/
  B : Matrix n m ℝ
  /-- The tick's growth in the form. -/
  σ2 : ℝ
  /-- The supply through the port, read on the state and the drive. -/
  supply : (n → ℝ) → (m → ℝ) → ℝ

/-- [definition] A driven tick is **certified in `G`** when its supply-rate certificate holds. -/
def DrivenTick.Certifies (τ : DrivenTick n m) (G : Matrix n n ℝ) : Prop :=
  SupplyCertifies G τ.M τ.B τ.σ2 τ.supply

/-- [definition] **The driven span** from `x₀` driven by `e₀, e₁, …`:
`x_(t+1) = M_t x_t + B_t e_t`. -/
def drivenSpan (ticks : ℕ → DrivenTick n m) (e : ℕ → m → ℝ) (x₀ : n → ℝ) : ℕ → n → ℝ
  | 0 => x₀
  | t + 1 => (ticks t).M *ᵥ drivenSpan ticks e x₀ t + (ticks t).B *ᵥ e t

/-- [proved-derived; formal-checked] **The driven span's Grönwall bound**: ticks each certified in
one `G` with `σ_t² ≥ 0` give
`E_G(x_N) ≤ (∏_t σ_t²) E_G(x₀) + Σ_t (∏_(k>t) σ_k²) s_t(x_t, e_t)`. -/
theorem driven_span_bound (G : Matrix n n ℝ) (ticks : ℕ → DrivenTick n m) (e : ℕ → m → ℝ)
    (x₀ : n → ℝ) (N : ℕ) (h : ∀ t < N, 0 ≤ (ticks t).σ2 ∧ (ticks t).Certifies G) :
    energy G (drivenSpan ticks e x₀ N) ≤ (∏ t ∈ range N, (ticks t).σ2) * energy G x₀ +
      ∑ t ∈ range N, (∏ k ∈ Ico (t + 1) N, (ticks k).σ2) *
        (ticks t).supply (drivenSpan ticks e x₀ t) (e t) :=
  discrete_gronwall (fun t => energy G (drivenSpan ticks e x₀ t)) (fun t => (ticks t).σ2)
    (fun t => (ticks t).supply (drivenSpan ticks e x₀ t) (e t)) N (fun k hk => (h k hk).1)
    (fun k hk => (h k hk).2 _ _)

/-- [proved-derived; formal-checked] **The driven span in a reference form**: with
`γ_lo Q ⪯ G ⪯ γ_hi Q`, `γ_lo E_Q(x_N) ≤ γ_hi (∏_t σ_t²) E_Q(x₀) + Σ_t (∏_(k>t) σ_k²) s_t`. -/
theorem driven_span_metric_change {G Q : Matrix n n ℝ} {γlo γhi : ℝ}
    (hbelow : ∀ x, γlo * energy Q x ≤ energy G x) (habove : ∀ x, energy G x ≤ γhi * energy Q x)
    (ticks : ℕ → DrivenTick n m) (e : ℕ → m → ℝ) (x₀ : n → ℝ) (N : ℕ)
    (h : ∀ t < N, 0 ≤ (ticks t).σ2 ∧ (ticks t).Certifies G) :
    γlo * energy Q (drivenSpan ticks e x₀ N) ≤
      γhi * (∏ t ∈ range N, (ticks t).σ2) * energy Q x₀ +
        ∑ t ∈ range N, (∏ k ∈ Ico (t + 1) N, (ticks k).σ2) *
          (ticks t).supply (drivenSpan ticks e x₀ t) (e t) := by
  have hb := driven_span_bound G ticks e x₀ N h
  have hP : 0 ≤ ∏ t ∈ range N, (ticks t).σ2 :=
    Finset.prod_nonneg fun t ht => (h t (Finset.mem_range.mp ht)).1
  have h1 := hbelow (drivenSpan ticks e x₀ N)
  have h3 := mul_le_mul_of_nonneg_left (habove x₀) hP
  linarith

/-- [definition] **The undriven span's transport** `M_(N−1) ⋯ M_0` (the head acts last). -/
def spanTransport [DecidableEq n] (ticks : ℕ → DrivenTick n m) : ℕ → Matrix n n ℝ
  | 0 => 1
  | t + 1 => (ticks t).M * spanTransport ticks t

/-- [proved-standard; formal-checked] **With the drive off the span is its ticks' product**:
`x_N = M_(N−1) ⋯ M_0 x₀`. -/
theorem drivenSpan_undriven [DecidableEq n] (ticks : ℕ → DrivenTick n m) (x₀ : n → ℝ) (N : ℕ) :
    drivenSpan ticks (fun _ => 0) x₀ N = spanTransport ticks N *ᵥ x₀ := by
  induction N with
  | zero => exact (Matrix.one_mulVec x₀).symm
  | succ N ih =>
    simp only [drivenSpan, spanTransport, ih, Matrix.mulVec_zero, add_zero, Matrix.mulVec_mulVec]

/-- [proved-derived; formal-checked] **The undriven partial period from the driven span**: ticks
certified in `G` whose supply is not positive at zero drive have
`E_G(M_(N−1) ⋯ M_0 x) ≤ (∏_t σ_t²) E_G(x)`. -/
theorem undriven_partial_period [DecidableEq n] (G : Matrix n n ℝ) (ticks : ℕ → DrivenTick n m)
    (N : ℕ) (h : ∀ t < N, 0 ≤ (ticks t).σ2 ∧ (ticks t).Certifies G)
    (h0 : ∀ t < N, ∀ x, (ticks t).supply x 0 ≤ 0) (x : n → ℝ) :
    energy G (spanTransport ticks N *ᵥ x) ≤ (∏ t ∈ range N, (ticks t).σ2) * energy G x := by
  rw [← drivenSpan_undriven ticks x N]
  refine (driven_span_bound G ticks (fun _ => 0) x N h).trans (add_le_of_nonpos_right ?_)
  refine Finset.sum_nonpos fun t ht => mul_nonpos_of_nonneg_of_nonpos ?_ ?_
  · exact Finset.prod_nonneg fun k hk => (h k (Finset.mem_Ico.mp hk).2).1
  · exact h0 t (Finset.mem_range.mp ht) _

/-- [proved-derived; formal-checked] **The driven span with the drive off reads the owner's
undriven reach**: two undriven partial periods around `k` whole periods certified at `ρ²` give
`E_Q(Post Mᵏ Pre x) ≤ (γ_hi/γ_lo) σ_post ρ^(2k) σ_pre E_Q(x)` (`floquet_span_reach`). -/
theorem undriven_span_reach [DecidableEq n] {G Q M : Matrix n n ℝ} {ρ2 γlo γhi : ℝ}
    (pre post : ℕ → DrivenTick n m) (Npre Npost : ℕ) (hρ : 0 ≤ ρ2) (hlo : 0 < γlo)
    (hbelow : ∀ x, γlo * energy Q x ≤ energy G x) (habove : ∀ x, energy G x ≤ γhi * energy Q x)
    (hcert : FloquetCertifies G M ρ2)
    (hpre : ∀ t < Npre, 0 ≤ (pre t).σ2 ∧ (pre t).Certifies G)
    (hpre0 : ∀ t < Npre, ∀ x, (pre t).supply x 0 ≤ 0)
    (hpost : ∀ t < Npost, 0 ≤ (post t).σ2 ∧ (post t).Certifies G)
    (hpost0 : ∀ t < Npost, ∀ x, (post t).supply x 0 ≤ 0) (k : ℕ) (x : n → ℝ) :
    energy Q ((spanTransport post Npost * M ^ k * spanTransport pre Npre) *ᵥ x) ≤
      γhi / γlo * ((∏ t ∈ range Npost, (post t).σ2) * ρ2 ^ k * ∏ t ∈ range Npre, (pre t).σ2) *
        energy Q x :=
  floquet_span_reach hρ
    (Finset.prod_nonneg fun t ht => (hpre t (Finset.mem_range.mp ht)).1)
    (Finset.prod_nonneg fun t ht => (hpost t (Finset.mem_range.mp ht)).1) hlo hbelow habove hcert
    (undriven_partial_period G pre Npre hpre hpre0) (undriven_partial_period G post Npost hpost hpost0)
    k x

end Span

/-! ## 4. Below, at and past the bifurcation -/

section Regimes

variable {n m : Type*} [Fintype n] [Fintype m]

/-- [proved-standard; formal-checked] **Grönwall at one rate**: `a_(k+1) ≤ r a_k + c` with `r ≥ 0`
gives `a_N ≤ r^N a_0 + c Σ_(j<N) r^j`. -/
theorem gronwall_const (a : ℕ → ℝ) {r c : ℝ} (hr : 0 ≤ r) :
    ∀ N : ℕ, (∀ k < N, a (k + 1) ≤ r * a k + c) →
      a N ≤ r ^ N * a 0 + c * ∑ j ∈ range N, r ^ j := by
  intro N
  induction N with
  | zero => intro _; simp
  | succ N ih =>
    intro h
    have ihN := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
    have h1 := h N (Nat.lt_succ_self N)
    have h2 := mul_le_mul_of_nonneg_left ihN hr
    rw [geom_sum_succ, pow_succ]
    linarith

/-- [proved-derived; formal-checked] **The driven span at one growth**: ticks certified in `G ⪰ 0`
with `σ_t² ≤ σ²`, `σ² ≥ 0`, and supplies along the span at most `s̄` give
`E_G(x_N) ≤ σ^(2N) E_G(x₀) + s̄ Σ_(j<N) σ^(2j)`. -/
theorem driven_span_const {G : Matrix n n ℝ} (hG : FormNonneg G) (ticks : ℕ → DrivenTick n m)
    (e : ℕ → m → ℝ) (x₀ : n → ℝ) {σ2 sbar : ℝ} (hσ : 0 ≤ σ2) (N : ℕ)
    (h : ∀ t < N, (ticks t).Certifies G ∧ (ticks t).σ2 ≤ σ2 ∧
      (ticks t).supply (drivenSpan ticks e x₀ t) (e t) ≤ sbar) :
    energy G (drivenSpan ticks e x₀ N) ≤ σ2 ^ N * energy G x₀ + sbar * ∑ j ∈ range N, σ2 ^ j := by
  refine gronwall_const (fun t => energy G (drivenSpan ticks e x₀ t)) hσ N fun k hk => ?_
  obtain ⟨hc, hle, hs⟩ := h k hk
  have h1 := hc (drivenSpan ticks e x₀ k) (e k)
  have h2 := mul_le_mul_of_nonneg_right hle (hG (drivenSpan ticks e x₀ k))
  show energy G ((ticks k).M *ᵥ drivenSpan ticks e x₀ k + (ticks k).B *ᵥ e k) ≤
    σ2 * energy G (drivenSpan ticks e x₀ k) + sbar
  linarith

/-- [proved-derived; formal-checked] **Below the bifurcation** (`0 ≤ σ² < 1`):
`E_G(x_N) ≤ σ^(2N) E_G(x₀) + s̄ (1 − σ^(2N))/(1 − σ²)`. -/
theorem driven_span_below {G : Matrix n n ℝ} (hG : FormNonneg G) (ticks : ℕ → DrivenTick n m)
    (e : ℕ → m → ℝ) (x₀ : n → ℝ) {σ2 sbar : ℝ} (hσ0 : 0 ≤ σ2) (hσ1 : σ2 < 1) (N : ℕ)
    (h : ∀ t < N, (ticks t).Certifies G ∧ (ticks t).σ2 ≤ σ2 ∧
      (ticks t).supply (drivenSpan ticks e x₀ t) (e t) ≤ sbar) :
    energy G (drivenSpan ticks e x₀ N) ≤
      σ2 ^ N * energy G x₀ + sbar * (1 - σ2 ^ N) / (1 - σ2) := by
  have hb := driven_span_const hG ticks e x₀ hσ0 N h
  have hne : σ2 ≠ 1 := ne_of_lt hσ1
  have hgeom : ∑ j ∈ range N, σ2 ^ j = (1 - σ2 ^ N) / (1 - σ2) := by
    rw [geom_sum_eq hne, div_eq_div_iff (sub_ne_zero.mpr hne) (sub_ne_zero.mpr hne.symm)]
    ring
  rw [hgeom, ← mul_div_assoc] at hb
  exact hb

/-- [proved-derived; formal-checked] **A bounded drive keeps a bounded energy below the
bifurcation**: with `s̄ ≥ 0`, `E_G(x_N) ≤ E_G(x₀) + s̄/(1 − σ²)` for every span. -/
theorem driven_span_below_uniform {G : Matrix n n ℝ} (hG : FormNonneg G)
    (ticks : ℕ → DrivenTick n m) (e : ℕ → m → ℝ) (x₀ : n → ℝ) {σ2 sbar : ℝ} (hσ0 : 0 ≤ σ2)
    (hσ1 : σ2 < 1) (hs : 0 ≤ sbar) (N : ℕ)
    (h : ∀ t < N, (ticks t).Certifies G ∧ (ticks t).σ2 ≤ σ2 ∧
      (ticks t).supply (drivenSpan ticks e x₀ t) (e t) ≤ sbar) :
    energy G (drivenSpan ticks e x₀ N) ≤ energy G x₀ + sbar / (1 - σ2) := by
  have hb := driven_span_below hG ticks e x₀ hσ0 hσ1 N h
  have hpos : 0 < 1 - σ2 := by linarith
  have hp0 : 0 ≤ σ2 ^ N := pow_nonneg hσ0 N
  have hp1 : σ2 ^ N ≤ 1 := pow_le_one₀ hσ0 hσ1.le
  have hE := hG x₀
  have h1 : σ2 ^ N * energy G x₀ ≤ energy G x₀ := by nlinarith
  have h2 : sbar * (1 - σ2 ^ N) / (1 - σ2) ≤ sbar / (1 - σ2) := by
    rw [div_le_div_iff_of_pos_right hpos]
    nlinarith
  linarith

/-- [proved-derived; formal-checked] **At the bifurcation** (`σ_t² ≤ 1`):
`E_G(x_N) ≤ E_G(x₀) + N s̄`. -/
theorem driven_span_at {G : Matrix n n ℝ} (hG : FormNonneg G) (ticks : ℕ → DrivenTick n m)
    (e : ℕ → m → ℝ) (x₀ : n → ℝ) {sbar : ℝ} (N : ℕ)
    (h : ∀ t < N, (ticks t).Certifies G ∧ (ticks t).σ2 ≤ 1 ∧
      (ticks t).supply (drivenSpan ticks e x₀ t) (e t) ≤ sbar) :
    energy G (drivenSpan ticks e x₀ N) ≤ energy G x₀ + N * sbar := by
  have hb := driven_span_const hG ticks e x₀ zero_le_one N h
  simp only [one_pow, one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hb
  linarith

/-- [proved-derived; formal-checked] **Past the bifurcation** (`σ² > 1`, `s̄ ≥ 0`):
`E_G(x_N) ≤ σ^(2N) (E_G(x₀) + s̄/(σ² − 1))`. -/
theorem driven_span_past {G : Matrix n n ℝ} (hG : FormNonneg G) (ticks : ℕ → DrivenTick n m)
    (e : ℕ → m → ℝ) (x₀ : n → ℝ) {σ2 sbar : ℝ} (hσ : 1 < σ2) (hs : 0 ≤ sbar) (N : ℕ)
    (h : ∀ t < N, (ticks t).Certifies G ∧ (ticks t).σ2 ≤ σ2 ∧
      (ticks t).supply (drivenSpan ticks e x₀ t) (e t) ≤ sbar) :
    energy G (drivenSpan ticks e x₀ N) ≤ σ2 ^ N * (energy G x₀ + sbar / (σ2 - 1)) := by
  have hb := driven_span_const hG ticks e x₀ (by linarith) N h
  have hpos : 0 < σ2 - 1 := by linarith
  rw [geom_sum_eq (ne_of_gt hσ)] at hb
  have key : sbar * ((σ2 ^ N - 1) / (σ2 - 1)) ≤ σ2 ^ N * (sbar / (σ2 - 1)) := by
    rw [mul_div_assoc', mul_div_assoc', div_le_div_iff_of_pos_right hpos]
    linarith
  rw [mul_add]
  linarith

end Regimes

/-! ## 5. The field's return into the ring (small gain) -/

section Return

variable {n m : Type*} [Fintype n] [Fintype m]

/-- [proved-standard; formal-checked] **The return closes the loop at `σ² + μ`**: a supply-certified
tick whose supply through the return `e = K x` obeys `s(x, K x) ≤ μ E_G(x)` has its closed loop
`M + B K` certified at `σ² + μ`. -/
theorem return_certifies {G M : Matrix n n ℝ} {B : Matrix n m ℝ} {K : Matrix m n ℝ} {σ2 μ : ℝ}
    {s : (n → ℝ) → (m → ℝ) → ℝ} (hcert : SupplyCertifies G M B σ2 s)
    (hret : ∀ x, s x (K *ᵥ x) ≤ μ * energy G x) : FloquetCertifies G (M + B * K) (σ2 + μ) := by
  intro x
  rw [certificate_reading, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
  have h1 := hcert x (K *ᵥ x)
  have h2 := hret x
  linarith

/-- [proved-standard; formal-checked] **The return through a quadratic supply**: with the supply
`e ⬝ S e`, the return's condition is `KᵀSK ⪯ μ G`, and the closed loop is certified at `σ² + μ`. -/
theorem return_quadratic {G M : Matrix n n ℝ} {B : Matrix n m ℝ} {K : Matrix m n ℝ}
    {S : Matrix m m ℝ} {σ2 μ : ℝ} (hcert : SupplyCertifies G M B σ2 (fun _ e => energy S e))
    (hK : ∀ x, 0 ≤ x ⬝ᵥ ((μ • G - Kᵀ * S * K) *ᵥ x)) :
    FloquetCertifies G (M + B * K) (σ2 + μ) := by
  refine return_certifies hcert fun x => ?_
  have hx := hK x
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    pullback_pairing] at hx
  show (K *ᵥ x) ⬝ᵥ (S *ᵥ (K *ᵥ x)) ≤ μ * energy G x
  unfold energy
  linarith

/-- [proved-derived; formal-checked] **The span through the field's return reads the owner's
reach at `σ² + μ`**: the factorization `Post (M + B K)ᵏ Pre` is certified
`E_Q(…x) ≤ (γ_hi/γ_lo) σ_post (σ² + μ)^k σ_pre E_Q(x)`. -/
theorem return_span_reach [DecidableEq n] {G Q M Pre Post : Matrix n n ℝ} {B : Matrix n m ℝ}
    {K : Matrix m n ℝ} {σ2 μ σpre σpost γlo γhi : ℝ} {s : (n → ℝ) → (m → ℝ) → ℝ}
    (hcert : SupplyCertifies G M B σ2 s) (hret : ∀ x, s x (K *ᵥ x) ≤ μ * energy G x)
    (hρ : 0 ≤ σ2 + μ) (hpre0 : 0 ≤ σpre) (hpost0 : 0 ≤ σpost) (hlo : 0 < γlo)
    (hbelow : ∀ x, γlo * energy Q x ≤ energy G x) (habove : ∀ x, energy G x ≤ γhi * energy Q x)
    (hpre : ∀ x, energy G (Pre *ᵥ x) ≤ σpre * energy G x)
    (hpost : ∀ x, energy G (Post *ᵥ x) ≤ σpost * energy G x) (k : ℕ) (x : n → ℝ) :
    energy Q ((Post * (M + B * K) ^ k * Pre) *ᵥ x) ≤
      γhi / γlo * (σpost * (σ2 + μ) ^ k * σpre) * energy Q x :=
  floquet_span_reach hρ hpre0 hpost0 hlo hbelow habove (return_certifies hcert hret) hpre hpost k x

end Return

/-! ## 6. A witness: the quarter turn damped by one half -/

section Witness

/-- [definition] **The quarter turn damped by `½`**, `M = ½ [[0, −1], [1, 0]]`. -/
def ringTurn : Matrix (Fin 2) (Fin 2) ℝ := !![0, -(1 / 2); 1 / 2, 0]

/-- [proved-derived; formal-checked] The witness is `½` times the quarter turn. -/
theorem ringTurn_eq : ringTurn = (1 / 2 : ℝ) • !![(0 : ℝ), -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ringTurn]

/-- [proved-derived; formal-checked] **The witness's Gram**: `Mᵀ 1 M = ¼ I`. -/
theorem ringTurn_gram : ringTurnᵀ * 1 * ringTurn = (1 / 4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ringTurn, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- [proved-standard; formal-checked] The unit form is positive semidefinite. -/
theorem one_formNonneg {n : Type*} [Fintype n] [DecidableEq n] :
    FormNonneg (1 : Matrix n n ℝ) := by
  intro x
  unfold energy
  rw [Matrix.one_mulVec]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- [proved-derived; formal-checked] **The witness is certified at `σ² = ¼`**. -/
theorem witness_certificate : FloquetCertifies 1 ringTurn (1 / 4) := by
  intro x
  rw [ringTurn_gram, sub_self, Matrix.zero_mulVec, dotProduct_zero]

/-- [proved-derived; formal-checked] **The witness's Young supply at `ε = 1`**:
`E(M x + e) ≤ ½ E(x) + 2 E(e)`. -/
theorem witness_young :
    SupplyCertifies 1 ringTurn (1 : Matrix (Fin 2) (Fin 2) ℝ) (1 / 2) (fun _ e => 2 * energy 1 e) := by
  intro x e
  have h := young_supply one_formNonneg witness_certificate one_pos
    (1 : Matrix (Fin 2) (Fin 2) ℝ) x e
  rw [Matrix.one_mulVec] at h
  rw [Matrix.one_mulVec]
  norm_num at h ⊢
  linarith

/-- [definition] **The witness's driven tick**: `(M, B, σ², s) = (ringTurn, 1, ½, 2 E(e))`. -/
def witnessTick : DrivenTick (Fin 2) (Fin 2) :=
  ⟨ringTurn, 1, 1 / 2, fun _ e => 2 * energy 1 e⟩

/-- [proved-derived; formal-checked] **The witness's span bound**: drives with `E(e_t) ≤ 1` keep
`E(x_N) ≤ 2^(−N) E(x₀) + 4 (1 − 2^(−N))`. -/
theorem witness_span (e : ℕ → Fin 2 → ℝ) (x₀ : Fin 2 → ℝ) (N : ℕ)
    (he : ∀ t < N, energy 1 (e t) ≤ 1) :
    energy 1 (drivenSpan (fun _ => witnessTick) e x₀ N) ≤
      (1 / 2) ^ N * energy 1 x₀ + 4 * (1 - (1 / 2) ^ N) := by
  have hb := driven_span_below one_formNonneg (fun _ => witnessTick) e x₀ (σ2 := 1 / 2)
    (sbar := 2) (by norm_num) (by norm_num) N fun t ht =>
      ⟨witness_young, le_refl _, by
        show 2 * energy 1 (e t) ≤ 2
        linarith [he t ht]⟩
  have e2 : (2 : ℝ) * (1 - (1 / 2) ^ N) / (1 - 1 / 2) = 4 * (1 - (1 / 2) ^ N) := by ring
  linarith

/-- [proved-derived; formal-checked] **The witness's energy stays bounded**: drives with
`E(e_t) ≤ 1` keep `E(x_N) ≤ E(x₀) + 4` for every span. -/
theorem witness_span_uniform (e : ℕ → Fin 2 → ℝ) (x₀ : Fin 2 → ℝ) (N : ℕ)
    (he : ∀ t < N, energy 1 (e t) ≤ 1) :
    energy 1 (drivenSpan (fun _ => witnessTick) e x₀ N) ≤ energy 1 x₀ + 4 := by
  have hb := driven_span_below_uniform one_formNonneg (fun _ => witnessTick) e x₀ (σ2 := 1 / 2)
    (sbar := 2) (by norm_num) (by norm_num) (by norm_num) N fun t ht =>
      ⟨witness_young, le_refl _, by
        show 2 * energy 1 (e t) ≤ 2
        linarith [he t ht]⟩
  have e2 : (2 : ℝ) / (1 - 1 / 2) = 4 := by norm_num
  linarith

/-- [proved-derived; formal-checked] **The witness's return stays certified below one**: the
return `K = ¼ I` supplies `⅛ E(x)`, so `M + 1 · K` is certified at `½ + ⅛ = ⅝`. -/
theorem witness_return :
    FloquetCertifies 1 (ringTurn + 1 * ((1 / 4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) (5 / 8) := by
  have h := return_certifies witness_young (K := (1 / 4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (μ := 1 / 8) fun x => by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, energy_smul]
      norm_num
      linarith
  have e : (1 / 2 : ℝ) + 1 / 8 = 5 / 8 := by norm_num
  rw [e] at h
  exact h

/-- [proved-derived; formal-checked] **The witness's closed loop is passive** over every number of
periods: `E((M + K)ᵏ x) ≤ E(x)`. -/
theorem witness_return_passive (k : ℕ) (x : Fin 2 → ℝ) :
    energy 1 ((ringTurn + 1 * ((1 / 4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) ^ k *ᵥ x) ≤
      energy 1 x :=
  floquet_passive (by norm_num) (by norm_num) one_formNonneg witness_return k x

/-- [proved-derived; formal-checked] **The witness's closed loop** is `[[¼, −½], [½, ¼]]`. -/
theorem closedLoop_eq :
    ringTurn + 1 * ((1 / 4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = !![1 / 4, -(1 / 2); 1 / 2, 1 / 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ringTurn]

/-- [proved-derived; formal-checked] **The closed loop's own certificate is `5/16`**, under the
small-gain reading `⅝`. -/
theorem witness_closed_loop_own :
    FloquetCertifies 1 (ringTurn + 1 * ((1 / 4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) (5 / 16) := by
  have hg : (!![1 / 4, -(1 / 2); 1 / 2, 1 / 4] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1 *
      !![1 / 4, -(1 / 2); 1 / 2, 1 / 4] = (5 / 16 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  intro x
  rw [closedLoop_eq, hg, sub_self, Matrix.zero_mulVec, dotProduct_zero]

end Witness

end Holonics.HNN.DrivenRingSupply

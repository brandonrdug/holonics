import Holonics.Physics.InformationDifference
import Holonics.Objects.Deposition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The first law of learning

[definition] Aeon record A7, Lean obligation 6. Along an aeon a source law `p` (what arrives)
and a receiver law `q` (what the constitution predicts) both move. Their cross-entropy
`C(p, q) = −Σ pᵢ log qᵢ` is the existing face `InformationReceiver.crossEntropy`. Over one epoch
from `(p, q)` to `(p', q')` its change has two parts:

```text
exchange     −Σ (p'ᵢ − pᵢ) log qᵢ          the source's flux through the unchanged receiver
deposition   −Σ p'ᵢ (log q'ᵢ − log qᵢ)      the change of the constitution's contribution
```

and in the continuous chart, along a clock `λ`,
`dC/dλ = −Σ dpᵢ log qᵢ − Σ pᵢ dqᵢ/qᵢ`.

[proved-derived; formal-checked] What is proved, for finite strictly positive sections. The epoch
and aeon forms (1–2) are exact telescoping identities, as the record grades A7; the substantive
laws are the KL form of deposition, the path dependence, the continuous and thermal charts and the
reached-edge work law.

1. **The first law, exact per epoch:** `C(p',q') − C(p,q) = exchange + deposition`
   (`first_law_epoch`). Exchange is the change at the unchanged receiver
   (`exchange_eq_crossEntropy_change`); deposition is the change at the arrived source and equals
   the change of the KL excess, `D(p'‖q') − D(p'‖q)` (`deposition_eq_kl_change`, over
   `InformationDifference.crossEntropy_excess_eq_kl`).
2. **Along an aeon:** the epoch terms telescope, so the sum of all exchanges and depositions
   depends only on the two bounding occurrences (`first_law_aeon`), and **over a cycle exchange is
   minus deposition** (`cycle_exchange_eq_neg_deposition`).
3. **Each term alone depends on the path** (`exchange_is_path_dependent`): two aeons with the
   same bounding laws, one moving the source first and one depositing first, exchange `0` and
   `−(log 2)/4`.
4. **A deposition onto the arrived source lowers cross-entropy by exactly its KL excess**
   (`deposition_onto_source`).
5. **The continuous chart:** the derivative of `C` along differentiable curves is the exchange rate
   plus the deposition rate (`hasDerivAt_crossEntropy`), and integrating that rate over a clock
   interval returns the boundary difference (`first_law_integral`).
6. **Heat and work.** Against canonical receivers `T log qᵢ = −Eᵢ − T log Z`
   (`InformationDifference.thermal_crossEntropy_identity`), `T · exchange` is the heat
   `Σ (p'ᵢ − pᵢ) Eᵢ` and `T · deposition` is the work `Σ p'ᵢ (E'ᵢ − Eᵢ)` plus the shift of the
   log partition (`thermal_first_law`): the first law of learning is the first law of
   thermodynamics in that chart.
7. **Deposition acts only where the covector arrived.** The canonical receiver of an
   `Objects/Deposition` constitution at thermal scale `T` reads the edge levels
   (`canonicalReceiver`, `q_Θ(e) ∝ exp(−level(Θ_e)/T)`, `canonicalReceiver_log`). For a law that
   deposits nothing at zero flux and zero drop, the first law's deposition between the receivers
   of `Θ` and of its deposit `Θ'` is exactly the work on the reached edges plus the shift of the
   log partition: `T · deposition(p', q_Θ, q_Θ') = Σ_(e reached) p'_e (level Θ'_e − level Θ_e) +
   T (log Z_Θ' − log Z_Θ)` (`work_on_reached_edges`, composing `thermal_first_law` and
   `Deposition.unreached_edge_unchanged`).

8. **The ledger read on enclosed code lengths** (the HNN's receiver reads its code lengths only as
   exact enclosures, its faces lying in `ℚ(θ)`). Along any walk whose steps each move the source or
   the constitution, exchange plus deposition telescopes to the change of code length
   (`ledger_telescopes`), and with cross-entropies whose steps move one law at a time the two sums
   are `first_law_aeon`'s (`ledger_is_first_law`). Read on enclosures `lo k ≤ C k ≤ hi k`, each
   step's Minkowski difference sums to an enclosure of its exact sum (`enclosed_contains`), and the
   two kinds together are the enclosed change widened by the interior occurrences' widths, exactly
   (`enclosed_telescopes`). Rust `holonics::aeon::EnclosedLedger`.

[agent-inferred] The names exchange/deposition read the record's heat/work structure of learning;
the identities hold as stated whatever reading is chosen.

No `axiom`, no `sorry`.
-/

noncomputable section

namespace Holonics.Aeon.Production.FirstLaw

open scoped BigOperators
open Finset
open Holonics.Computation.HolonicInformationTheory
open Holonics.Computation.HolonicInformationTheory.PositiveProbabilitySection

variable {Index : Type*} [Fintype Index]

/-! ## 1. One epoch -/

/-- [definition] **Exchange**: the source moves through the unchanged receiver,
`−Σ (p'ᵢ − pᵢ) log qᵢ`. -/
def exchange (p p' q : PositiveProbabilitySection Index) : ℝ :=
  -∑ i, (p'.mass i - p.mass i) * Real.log (q.mass i)

/-- [definition] **Deposition**: the constitution's contribution changes at the arrived source,
`−Σ p'ᵢ (log q'ᵢ − log qᵢ)`. -/
def deposition (p' q q' : PositiveProbabilitySection Index) : ℝ :=
  -∑ i, p'.mass i * (Real.log (q'.mass i) - Real.log (q.mass i))

/-- [proved-derived; formal-checked] Exchange is the change of cross-entropy at the unchanged
receiver. -/
theorem exchange_eq_crossEntropy_change (p p' q : PositiveProbabilitySection Index) :
    exchange p p' q = crossEntropy p' q - crossEntropy p q := by
  unfold exchange crossEntropy
  simp only [sub_mul, sum_sub_distrib]
  ring

/-- [proved-derived; formal-checked] Deposition is the change of cross-entropy at the arrived
source. -/
theorem deposition_eq_crossEntropy_change (p' q q' : PositiveProbabilitySection Index) :
    deposition p' q q' = crossEntropy p' q' - crossEntropy p' q := by
  unfold deposition crossEntropy
  simp only [mul_sub, sum_sub_distrib]
  ring

/-- [proved-derived; formal-checked] **Deposition is the change of the KL excess** at the arrived
source: `D(p'‖q') − D(p'‖q)`. -/
theorem deposition_eq_kl_change (p' q q' : PositiveProbabilitySection Index) :
    deposition p' q q' = klDivergence p' q' - klDivergence p' q := by
  rw [deposition_eq_crossEntropy_change,
    ← Holonics.Physics.InformationDifference.crossEntropy_excess_eq_kl,
    ← Holonics.Physics.InformationDifference.crossEntropy_excess_eq_kl]
  ring

/-- [proved-derived; formal-checked] **The first law of learning, one epoch:**
`C(p',q') − C(p,q) = exchange + deposition`. -/
theorem first_law_epoch (p p' q q' : PositiveProbabilitySection Index) :
    crossEntropy p' q' - crossEntropy p q = exchange p p' q + deposition p' q q' := by
  rw [exchange_eq_crossEntropy_change, deposition_eq_crossEntropy_change]
  ring

/-- [proved-derived; formal-checked] **A deposition onto the arrived source** lowers
cross-entropy by exactly the KL excess: `deposition p' q p' = −D(p'‖q) ≤ 0`. -/
theorem deposition_onto_source (p' q : PositiveProbabilitySection Index) :
    deposition p' q p' = -klDivergence p' q ∧ deposition p' q p' ≤ 0 := by
  have h : deposition p' q p' = -klDivergence p' q := by
    rw [deposition_eq_kl_change, ← Holonics.Physics.InformationDifference.crossEntropy_excess_eq_kl
      p' p', Holonics.Physics.InformationDifference.crossEntropy_self_eq_entropy, sub_self,
      zero_sub]
  exact ⟨h, by rw [h]; exact neg_nonpos.mpr (klDivergence_nonnegative p' q)⟩

/-! ## 2. Along an aeon -/

/-- [proved-derived; formal-checked] **The first law along an aeon of `N` epochs:** the exchanges
and depositions sum to the boundary difference of cross-entropy. -/
theorem first_law_aeon (p q : ℕ → PositiveProbabilitySection Index) (N : ℕ) :
    crossEntropy (p N) (q N) - crossEntropy (p 0) (q 0) =
      ∑ k ∈ range N, exchange (p k) (p (k + 1)) (q k) +
        ∑ k ∈ range N, deposition (p (k + 1)) (q k) (q (k + 1)) := by
  rw [← sum_add_distrib, ← sum_range_sub (fun k => crossEntropy (p k) (q k))]
  exact sum_congr rfl fun k _ => first_law_epoch _ _ _ _

/-- [proved-derived; formal-checked] **Over a cycle exchange is minus deposition.** -/
theorem cycle_exchange_eq_neg_deposition (p q : ℕ → PositiveProbabilitySection Index) (N : ℕ)
    (hp : p N = p 0) (hq : q N = q 0) :
    ∑ k ∈ range N, exchange (p k) (p (k + 1)) (q k) =
      -∑ k ∈ range N, deposition (p (k + 1)) (q k) (q (k + 1)) := by
  have h := first_law_aeon p q N
  rw [hp, hq, sub_self] at h
  linarith

/-! ## 3. Each term depends on the path -/

namespace PathWitness

/-- [definition] A two-point law with mass `a` on `true`. -/
def twoPoint (a : ℝ) (h0 : 0 < a) (h1 : a < 1) : PositiveProbabilitySection Bool where
  mass := fun b => if b then a else 1 - a
  positive := fun b => by cases b <;> simp [h0, h1]
  normalized := by simp

def half : PositiveProbabilitySection Bool := twoPoint (1 / 2) (by norm_num) (by norm_num)
def quarter : PositiveProbabilitySection Bool := twoPoint (1 / 4) (by norm_num) (by norm_num)
def third : PositiveProbabilitySection Bool := twoPoint (1 / 3) (by norm_num) (by norm_num)

/-- [counterexample; formal-checked] **Exchange depends on the path.** From `(½, ½)` to
`(¼, ⅓)`: moving the source first and then depositing exchanges `0`; depositing first and then
moving the source exchanges `−(log 2)/4`. Both aeons have the same total change of
cross-entropy, so deposition differs by the opposite amount. -/
theorem exchange_is_path_dependent :
    exchange half quarter half + exchange quarter quarter third = 0 ∧
      exchange half half half + exchange half quarter third = -(Real.log 2 / 4) ∧
      (exchange half quarter half + deposition quarter half third) =
        (deposition half half third + exchange half quarter third) := by
  have hq : ∀ p q : PositiveProbabilitySection Bool, exchange p p q = 0 := fun p q => by
    simp [exchange]
  have h12 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have h23 : Real.log (2 / 3) = Real.log 2 - Real.log 3 := Real.log_div (by norm_num) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [hq, add_zero]
    simp [exchange, half, quarter, twoPoint]
    norm_num [Real.log_inv]
    rw [h12]
    ring
  · rw [hq, zero_add]
    simp [exchange, half, quarter, third, twoPoint]
    norm_num
    rw [h23]
    ring
  · rw [← first_law_epoch, deposition_eq_crossEntropy_change, exchange_eq_crossEntropy_change]
    ring

end PathWitness

/-! ## 4. The continuous chart -/

section Continuous

variable {Index : Type*} [Fintype Index]

/-- [proved-derived; formal-checked] **The first law in the continuous chart.** Along
differentiable curves `p`, `q` with `q > 0`,
`d/dλ (−Σ pᵢ log qᵢ) = −Σ dpᵢ log qᵢ − Σ pᵢ dqᵢ/qᵢ`: the exchange rate plus the deposition rate. -/
theorem hasDerivAt_crossEntropy {p q : ℝ → Index → ℝ} {dp dq : Index → ℝ} {t : ℝ}
    (hp : ∀ i, HasDerivAt (fun s => p s i) (dp i) t)
    (hq : ∀ i, HasDerivAt (fun s => q s i) (dq i) t) (hpos : ∀ i, 0 < q t i) :
    HasDerivAt (fun s => -∑ i, p s i * Real.log (q s i))
      (-∑ i, dp i * Real.log (q t i) + -∑ i, p t i * (dq i / q t i)) t := by
  have hsum : HasDerivAt (fun s => ∑ i, p s i * Real.log (q s i))
      (∑ i, (dp i * Real.log (q t i) + p t i * (dq i / q t i))) t := by
    apply HasDerivAt.fun_sum
    intro i _
    exact (hp i).mul ((hq i).log (hpos i).ne')
  rw [sum_add_distrib] at hsum
  rw [show ∀ a b : ℝ, -a + -b = -(a + b) from fun a b => by ring]
  exact hsum.fun_neg

/-- [proved-derived; formal-checked] **Integrated over a clock interval**, the exchange and
deposition rates return the boundary difference of cross-entropy. -/
theorem first_law_integral {p q dp dq : ℝ → Index → ℝ} {a b : ℝ}
    (hp : ∀ t ∈ Set.uIcc a b, ∀ i, HasDerivAt (fun s => p s i) (dp t i) t)
    (hq : ∀ t ∈ Set.uIcc a b, ∀ i, HasDerivAt (fun s => q s i) (dq t i) t)
    (hpos : ∀ t ∈ Set.uIcc a b, ∀ i, 0 < q t i)
    (hint : IntervalIntegrable (fun t => -∑ i, dp t i * Real.log (q t i) +
      -∑ i, p t i * (dq t i / q t i)) MeasureTheory.volume a b) :
    ∫ t in a..b, (-∑ i, dp t i * Real.log (q t i) + -∑ i, p t i * (dq t i / q t i)) =
      (-∑ i, p b i * Real.log (q b i)) - (-∑ i, p a i * Real.log (q a i)) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_crossEntropy (hp t ht) (hq t ht) (hpos t ht)) hint

end Continuous

/-! ## 5. Heat and work -/

open Holonics.Physics.InformationDifference in
/-- [proved-derived; formal-checked] **The first law of learning is the first law of
thermodynamics in the canonical chart.** For canonical receivers at thermal scale `T`,
`T · exchange = Σ (p'ᵢ − pᵢ) Eᵢ` (heat: the populations move over fixed levels) and
`T · deposition = Σ p'ᵢ (E'ᵢ − Eᵢ) + T (log Z' − log Z)` (work on the levels plus the
log-partition shift). -/
theorem thermal_first_law (T : ℝ) (E E' : Index → ℝ) (logZ logZ' : ℝ)
    (p p' q q' : PositiveProbabilitySection Index)
    (hq : ∀ i, T * Real.log (q.mass i) = -E i - T * logZ)
    (hq' : ∀ i, T * Real.log (q'.mass i) = -E' i - T * logZ') :
    T * exchange p p' q = energyExpectation E p' - energyExpectation E p ∧
      T * deposition p' q q' =
        (energyExpectation E' p' - energyExpectation E p') + T * (logZ' - logZ) := by
  have h1 := thermal_crossEntropy_identity T E logZ p q hq
  have h2 := thermal_crossEntropy_identity T E logZ p' q hq
  have h3 := thermal_crossEntropy_identity T E' logZ' p' q' hq'
  refine ⟨?_, ?_⟩
  · rw [exchange_eq_crossEntropy_change, mul_sub, h1, h2]; ring
  · rw [deposition_eq_crossEntropy_change, mul_sub, h2, h3]; ring

/-! ## 6. Deposition acts only where the covector arrived -/

section Reached

open Holonics.Objects.Deposition
open Holonics.Physics.InformationDifference

variable {k : ℕ} [NeZero k]

/-- [definition] The partition function of a constitution's edge levels at thermal scale `T`:
`Z_Θ = Σ_e exp(−level(Θ_e)/T)`. -/
def partitionOf (level : ℚ → ℝ) (T : ℝ) (Θ : Constitution k) : ℝ :=
  ∑ e, Real.exp (-level (Θ.1 e) / T)

theorem partitionOf_pos (level : ℚ → ℝ) (T : ℝ) (Θ : Constitution k) :
    0 < partitionOf level T Θ :=
  sum_pos (fun _ _ => Real.exp_pos _) univ_nonempty

/-- [definition] **The canonical receiver of a constitution** at thermal scale `T`: the law
`q_Θ(e) = exp(−level(Θ_e)/T) / Z_Θ` over the edges, read from the constitution's edge levels. -/
def canonicalReceiver (level : ℚ → ℝ) (T : ℝ) (Θ : Constitution k) :
    PositiveProbabilitySection (Fin k) where
  mass e := Real.exp (-level (Θ.1 e) / T) / partitionOf level T Θ
  positive e := div_pos (Real.exp_pos _) (partitionOf_pos level T Θ)
  normalized := by
    rw [← sum_div]
    exact div_self (partitionOf_pos level T Θ).ne'

/-- [proved-derived; formal-checked] The canonical receiver is canonical:
`T log q_Θ(e) = −level(Θ_e) − T log Z_Θ`. -/
theorem canonicalReceiver_log (level : ℚ → ℝ) {T : ℝ} (hT : T ≠ 0) (Θ : Constitution k) (e : Fin k) :
    T * Real.log ((canonicalReceiver level T Θ).mass e) =
      -level (Θ.1 e) - T * Real.log (partitionOf level T Θ) := by
  simp only [canonicalReceiver]
  rw [Real.log_div (Real.exp_pos _).ne' (partitionOf_pos level T Θ).ne', Real.log_exp]
  field_simp

/-- [proved-derived; formal-checked] **The work of a deposition acts only on the reached edges.**
For the canonical receivers of a constitution `Θ` and of its deposit `Θ'` at thermal scale `T`,
and a deposition law that deposits nothing at zero flux and zero drop,
`T · deposition(p', q_Θ, q_Θ') = Σ_(e reached) p'_e (level Θ'_e − level Θ_e) + T (log Z_Θ' − log Z_Θ)`:
the first law's deposition is work on the levels of exactly the edges the flux reached, plus the
shift of the log partition (`thermal_first_law`, `Deposition.unreached_edge_unchanged`). -/
theorem work_on_reached_edges {m : ℕ} (L : DepositionLaw k) (hzero : ∀ e, L.Γ e 0 0 = 0)
    (d : Matrix (Fin k) (Fin m) ℚ) (Θ : Constitution k) (φ : Fin m → ℚ) (level : ℚ → ℝ)
    {T : ℝ} (hT : T ≠ 0) (p' : PositiveProbabilitySection (Fin k)) :
    T * deposition p' (canonicalReceiver level T Θ) (canonicalReceiver level T (deposit L d Θ φ)) =
      ∑ e ∈ univ.filter (fun e => flux d Θ φ e ≠ 0),
          p'.mass e * (level ((deposit L d Θ φ).1 e) - level (Θ.1 e)) +
        T * (Real.log (partitionOf level T (deposit L d Θ φ)) -
          Real.log (partitionOf level T Θ)) := by
  have h := (thermal_first_law T (fun e => level (Θ.1 e)) (fun e => level ((deposit L d Θ φ).1 e))
    (Real.log (partitionOf level T Θ)) (Real.log (partitionOf level T (deposit L d Θ φ)))
    p' p' (canonicalReceiver level T Θ) (canonicalReceiver level T (deposit L d Θ φ))
    (canonicalReceiver_log level hT Θ) (canonicalReceiver_log level hT _)).2
  rw [h]
  congr 1
  unfold energyExpectation
  rw [← sum_sub_distrib, sum_filter]
  refine sum_congr rfl fun e _ => ?_
  split_ifs with he
  · ring
  · push Not at he
    simp only [unreached_edge_unchanged L hzero d Θ φ he, sub_self]

end Reached

/-! ## 7. The ledger read on enclosed code lengths -/

section Ledger

/-- [definition] **The ledger's exchange**: along occurrences `0, …, N` with code lengths `C k`, the
steps that move the source (`dep k = false`: new targets through the unchanged constitution),
summed. -/
def ledgerExchange (C : ℕ → ℝ) (dep : ℕ → Bool) (N : ℕ) : ℝ :=
  ∑ k ∈ range N, if dep k = true then 0 else C (k + 1) - C k

/-- [definition] **The ledger's deposition**: the steps that move the constitution (`dep k = true`:
the arrived targets at the successor), summed. -/
def ledgerDeposition (C : ℕ → ℝ) (dep : ℕ → Bool) (N : ℕ) : ℝ :=
  ∑ k ∈ range N, if dep k = true then C (k + 1) - C k else 0

/-- [proved-derived; formal-checked] **The ledger telescopes**: whatever the steps' kinds, exchange
plus deposition is the change of code length between the bounding occurrences. -/
theorem ledger_telescopes (C : ℕ → ℝ) (dep : ℕ → Bool) (N : ℕ) :
    ledgerExchange C dep N + ledgerDeposition C dep N = C N - C 0 := by
  unfold ledgerExchange ledgerDeposition
  rw [← sum_add_distrib, ← sum_range_sub C]
  refine sum_congr rfl fun k _ => ?_
  cases dep k <;> simp

/-- [proved-derived; formal-checked] **The ledger is the first law.** When each step moves only the
source (an exchange: the receiver unchanged) or only the receiver (a deposition: the source
unchanged), and the code length is the cross-entropy, the ledger's two sums are the exchange and
deposition sums of `first_law_aeon`. -/
theorem ledger_is_first_law (p q : ℕ → PositiveProbabilitySection Index) (dep : ℕ → Bool)
    (N : ℕ) (hex : ∀ k, dep k = false → q (k + 1) = q k)
    (hdep : ∀ k, dep k = true → p (k + 1) = p k) :
    ledgerExchange (fun k => crossEntropy (p k) (q k)) dep N =
        ∑ k ∈ range N, exchange (p k) (p (k + 1)) (q k) ∧
      ledgerDeposition (fun k => crossEntropy (p k) (q k)) dep N =
        ∑ k ∈ range N, deposition (p (k + 1)) (q k) (q (k + 1)) := by
  constructor
  · unfold ledgerExchange
    refine sum_congr rfl fun k _ => ?_
    cases h : dep k
    · simp only [Bool.false_eq_true, if_false]
      rw [exchange_eq_crossEntropy_change, hex k h]
    · simp only [if_true]
      rw [hdep k h, exchange_eq_crossEntropy_change, sub_self]
  · unfold ledgerDeposition
    refine sum_congr rfl fun k _ => ?_
    cases h : dep k
    · simp only [Bool.false_eq_true, if_false]
      rw [hex k h, deposition_eq_crossEntropy_change, sub_self]
    · simp only [if_true]
      rw [deposition_eq_crossEntropy_change, hdep k h]

/-- [definition] **The enclosed ledger's lower ends**: code lengths read as enclosures
`lo k ≤ C k ≤ hi k`, each step of kind `b` the lower end `lo (k+1) − hi k` of its Minkowski
difference, summed. -/
def enclosedLower (lo hi : ℕ → ℝ) (dep : ℕ → Bool) (b : Bool) (N : ℕ) : ℝ :=
  ∑ k ∈ range N, if dep k = b then lo (k + 1) - hi k else 0

/-- [definition] **The enclosed ledger's upper ends**: `hi (k+1) − lo k` per step of kind `b`. -/
def enclosedUpper (lo hi : ℕ → ℝ) (dep : ℕ → Bool) (b : Bool) (N : ℕ) : ℝ :=
  ∑ k ∈ range N, if dep k = b then hi (k + 1) - lo k else 0

/-- [proved-derived; formal-checked] **Each enclosed sum contains its exact sum.** -/
theorem enclosed_contains (C lo hi : ℕ → ℝ) (dep : ℕ → Bool) (N : ℕ)
    (hlo : ∀ k, lo k ≤ C k) (hhi : ∀ k, C k ≤ hi k) :
    (enclosedLower lo hi dep false N ≤ ledgerExchange C dep N ∧
        ledgerExchange C dep N ≤ enclosedUpper lo hi dep false N) ∧
      (enclosedLower lo hi dep true N ≤ ledgerDeposition C dep N ∧
        ledgerDeposition C dep N ≤ enclosedUpper lo hi dep true N) := by
  unfold enclosedLower enclosedUpper ledgerExchange ledgerDeposition
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
  · apply sum_le_sum
    intro k _
    have := hlo k
    have := hhi k
    have := hlo (k + 1)
    have := hhi (k + 1)
    cases dep k <;> simp only [Bool.false_eq_true, Bool.true_eq_false, if_true, if_false] <;>
      linarith

/-- The Minkowski sums of a chain of steps telescope, widened by the interior occurrences. -/
theorem telescope_widened (lo hi : ℕ → ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ range N, (lo (k + 1) - hi k) = (lo N - hi 0) - ∑ k ∈ Ico 1 N, (hi k - lo k) ∧
      ∑ k ∈ range N, (hi (k + 1) - lo k) = (hi N - lo 0) + ∑ k ∈ Ico 1 N, (hi k - lo k) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [sum_range_succ, sum_range_succ, h1, h2, sum_Ico_succ_top hn]
    constructor <;> ring

/-- [proved-derived; formal-checked] **The enclosed ledger telescopes, widened by its interior.**
For `N ≥ 1` steps, the two kinds' lower sums total the enclosed change's lower end `lo N − hi 0`
less the widths `W = Σ_(0<k<N) (hi k − lo k)` of the interior occurrences, and the upper sums its
upper end `hi N − lo 0` plus `W`, exactly. -/
theorem enclosed_telescopes (lo hi : ℕ → ℝ) (dep : ℕ → Bool) {N : ℕ} (hN : 1 ≤ N) :
    enclosedLower lo hi dep false N + enclosedLower lo hi dep true N =
        (lo N - hi 0) - ∑ k ∈ Ico 1 N, (hi k - lo k) ∧
      enclosedUpper lo hi dep false N + enclosedUpper lo hi dep true N =
        (hi N - lo 0) + ∑ k ∈ Ico 1 N, (hi k - lo k) := by
  have split : ∀ f : ℕ → ℝ, (∑ k ∈ range N, if dep k = false then f k else 0) +
      (∑ k ∈ range N, if dep k = true then f k else 0) = ∑ k ∈ range N, f k := by
    intro f
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    cases dep k <;> simp
  unfold enclosedLower enclosedUpper
  rw [split (fun k => lo (k + 1) - hi k), split (fun k => hi (k + 1) - lo k)]
  exact telescope_widened lo hi hN

end Ledger

section Audit

#print axioms first_law_epoch
#print axioms deposition_eq_kl_change
#print axioms deposition_onto_source
#print axioms first_law_aeon
#print axioms cycle_exchange_eq_neg_deposition
#print axioms PathWitness.exchange_is_path_dependent
#print axioms hasDerivAt_crossEntropy
#print axioms first_law_integral
#print axioms thermal_first_law
#print axioms work_on_reached_edges
#print axioms ledger_telescopes
#print axioms ledger_is_first_law
#print axioms enclosed_contains
#print axioms enclosed_telescopes

end Audit

end Holonics.Aeon.Production.FirstLaw

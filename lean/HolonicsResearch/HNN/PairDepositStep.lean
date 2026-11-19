import Holonics.Holon.Deposition
import Holonics.HNN.Normal
import Mathlib.Data.Int.Log
import Mathlib.Data.Rat.Floor

/-!
# HNN.PairDepositStep: the pair deposit's certified quadratic step

[definition] The box of #410: "The pair deposit's certified quadratic step (#359):
`hnn::executed::pair_deposit`, `CertifiedStep::certify(a, C, c)`." Learning is locating keys: a key
`(δ, f)` located by loop closure becomes material by one certified deposition of the source port
(`hnn::executed::{pair_deposit, deposit_reads}` and `holon::deposition::CertifiedStep`, held at
`d5ed4adc1`). Each oriented read `r` is a pair contact whose slip `Δ_r = v_r − (E − B) e_(x_r)` sets
the carried image of the antecedent's prior, `v_r = P^(t_r) B e_(y_r)`, against the learned part of
the consequence's column. The slip is the declared comparison's descent covector (target less
produced) at the column it reaches; its square `Q` is the pair contact's quadrance and `DQ = 2J*Δ`
its first variation. One sample per read (feature `e_(x_r)`, covector `Δ_r`, weight one) enters the
source port's normal law, and one dyadic step serves every read.

Sources: the box; `Holon/Deposition` §6 ("The certified step": `certified_step_descends`,
`quadratic_upper_model`) and its open paragraph ("Owed in #62 ('The certified deposition step')");
`HNN/Normal` §3 and §7 (`depositLocus`, `windowCovector`, `windowGram`, `certified_normal_step`,
`frobenius_chart`); `HNN/PairedDeposit` (`reversal_identity`: the dyad images read at `−δ` enter the
same step as oriented reads); `HNN/ChartResidual` (`certified_move_scaled`, the same cap under a
prior); the record `research/records/2026-10-05_LOCATED_KEYS_BECOME_THE_SOURCE_PORTS_PAIR_COMPONENT.md`
(§2 "The deposit"; §4: `Q = 120 = 2³·3·5 → 0` at `η = 2`, `a = 120`, `C = 60`, `c = 1/2`, largest
entry 1); the atlas rows `hnn.pair-deposit`, `holon.certified-step` (whose note "not in Lean … the
machine's step η = max{2^k : ηC ≤ a, ηc ≤ 1}" item 2 states), `hnn.certified-normal-step`,
`hnn.paired-deposit` and `contact.dq`.

What is proved: [proved-derived; formal-checked], except the quadratic's own algebra (`score_along`,
`quadratic_at_minimizer`, `quadratic_ge_minimizer`, `step_bracket`, `three_quarters`,
`line_minimizer`) and the dyadic logarithm's facts (`two_zpow_pos`, `two_zpow_le_iff`,
`curvature_bound_iff`, `covector_bound_iff`), which are [proved-standard; formal-checked].

1. **The slip and its square** (`Reads`, `Reads.slip`, `Reads.score`, `Reads.alignment`,
   `Reads.curvature`, `Reads.col_eq_mulVec_single`, `Reads.slip_along`, `Reads.score_along`,
   `Reads.dot_self_nonneg`, `Reads.score_nonneg`, `Reads.curvature_nonneg`, `Reads.curvature_pos`,
   `Reads.score_ray`). Along any step `D`, `Q(E + ηD) = Q(E) − ηa + ½η²C` for every `η`, with
   `a = 2 Σ_r ⟨Δ_r, D e_(x_r)⟩` and `C = 2 Σ_r |D e_(x_r)|² ≥ 0`. Over `ℝ` the ray's slope is
   `−a + tC` and its curvature `C` at every `t`, so `quadratic_upper_model` applies and its bound is
   attained. A step with `a > 0` has `C > 0`.
2. **The certified step** (`Admits`, `certExp`, `certStep`, `admits_iff`, `admits_certExp`,
   `not_admits_succ`, `certStep_spec`, `certExp_eq_of`, `certExp_mono`, `admits_anti`,
   `halved_admits`, `curvature_binds`). For `a > 0`, `C, c ≥ 0`, not both zero, the exponent
   `k = min(⌊log₂(a/C)⌋, ⌊log₂(1/c)⌋)` over the bounds present (`Int.log 2`) is the largest with
   `2^k C ≤ a` and `2^k c ≤ 1`: `2^j` admits both iff `j ≤ k`, so `η = 2^k` holds both and `2η`
   breaks one. A larger `a` or a smaller `C` or `c` never shrinks `k`; every smaller dyadic, the
   halved step among them, keeps both bounds; with `C > 0` and `ac ≤ C` the curvature is the bound
   that binds, `a < 2ηC`.
3. **The certified descent** (`Reads.descends`, `Reads.certified_descent`, `Reads.line_minimizer`,
   `Reads.certified_three_quarters`). At the certified `η`, `Q(E + ηD) ≤ Q(E) − ½ηa`, through
   `certified_step_descends` at one locus. For `C > 0` the line's minimizer is `η* = a/C`, with
   `Q(E + η*D) = Q(E) − a²/(2C)` least on the line; where the curvature binds (`a < 2ηC`) the
   certified step lies in `(η*/2, η*]` and `Q(E) − Q(E + ηD) = ηa − ½η²C ≥ ¾ · a²/(2C)`, three
   quarters of the minimizer's decrease.
4. **The unit step aligns** (`Reads.count`, `Reads.fiberSlip`, `Reads.slipMatrix`, `Reads.unitStep`,
   `Reads.col_unitStep`, `Reads.fiberSlip_of_card`, `Reads.pairing_fiberwise`,
   `Reads.alignment_frobenius`, `Reads.unit_step_alignment`, `Reads.trace_chart`,
   `Reads.chart_alignment`, `Reads.unitStep_eq_chart`, `Reads.count_nonneg`,
   `Reads.fiberSlip_of_denominator`, `Reads.unit_step_alignment_nonneg`,
   `Reads.unit_step_alignment_eq_zero_iff`, `Reads.unitStep_eq_zero_iff`,
   `Reads.chart_alignment_nonneg`, `Reads.window`, `Reads.window_covector`, `Reads.window_gram`,
   `Reads.normal_unit_step`). The reads regroup by class: `a = 2 Σ_k ⟨S_k, D e_k⟩` with
   `S_k = Σ_(x_r = k) Δ_r`, the Frobenius pairing `2⟨G, D⟩` with the reached covector `G = [S_k]`
   (`contact.dq` on the port). The samples reach the normal law with covector `G` and Gram `diag(n)`,
   `n_k = #{r : x_r = k}`, so at the diagonal statistic `diag(h)` with every `h_k + n_k ≠ 0`,
   `HNN/Normal.depositLocus` moves the port by `η D`, `D e_k = S_k/(h_k + n_k)`. At `h ≥ 0`,
   `a = 2 Σ_k |S_k|²/(h_k + n_k) ≥ 0`, and `a = 0` iff every `S_k = 0` iff `D = 0`: nothing descends
   and nothing moves. In general `D = G M` gives `a = 2 tr(G M Gᵀ)`, nonnegative when
   `⟨v, M v⟩ ≥ 0` for every `v` (through `HNN/Normal.frobenius_chart`; the symmetry of `M` is not
   used); the unit step is `M = diag((h + n)⁻¹)`.
5. **The consumer** (`Reads.score_eq_zero_iff`, `Reads.alignment_of_closed`, `classMap`,
   `col_mul_classMap`, `Reads.slip_eq_zero_iff`, `Reads.score_eq_zero_iff_consumer`,
   `Reads.consumer`). `Q(E) = 0` iff every slip vanishes iff `(E − B) e_(x_r) = v_r` at every read;
   for reads `(y, f y)` with `v = U B e_y` this is `(E − B) T = U B` on the menu's classes, with
   `T e_y = e_(f y)`. A closed slip aligns no step: a second deposit of the same key moves nothing.
6. **The opening closes in one step** (`Reads.slip_prior`, `Reads.col_smul`,
   `Reads.fiber_of_injective`, `Reads.opening_col`, `Reads.opening_alignment`,
   `Reads.opening_curvature`, `Reads.opening_minimizer`, `Reads.opening_closes`,
   `Reads.opening_certified`). At `E = B`, with one read per class and the statistic `h₀` at every
   read class: `D e_(x_r) = v_r/(h₀ + 1)`, `a = 2Q/(h₀ + 1)`, `C = 2Q/(h₀ + 1)²`, `η* = h₀ + 1`.
   When `h₀ + 1 = 2^j`, `c(h₀ + 1) ≤ 1` and `Q > 0`, the certified exponent is `j`, the step is
   `η*`, every slip closes and the consumer holds.
7. **The order-2 reading** (`order_two_certificate`, `order_two_reading`, `portPrior`,
   `quarterTurn`, `portMap`, `portAntecedent`, `portReads`, `portAfter`, `port_transport`,
   `port_images`, `port_injective`, `port_opening`, `port_deposit`). The record's numbers: at
   `a = 120`, `C = 60`, `c = 1/2` the exponent is `1` (`2·60 ≤ 120`, `2·½ ≤ 1`, and `4` breaks
   both); at `Q = 120`, `h = 1`, `a = 120`, `C = 60`, `η* = 2`, `Q(2) = 120 − 240 + 120 = 0`, the
   certified decrease `½ηa = 120` is the whole slip, and `120 = 2³·3·5`. A port of two rows and three
   classes carries the same law at small scale: `B = [[½, 0, 1], [0, ½, −1]]`, the ring's transport
   a quarter turn `U = [[0, −1], [1, 0]]`, the located map `f = (0 1 2)` read at `y = 0, 1`; the
   slips `(0, ½)` and `(−½, 0)` give `Q = ½`, `a = ½`, `C = ¼` and the largest entry `c = ½`, the
   exponent is `1`, and the port after the step, `[[½, 0, ½], [0, 1, −1]]` (entries in
   `{0, ±½, ±1}`, largest entry 1), closes both slips and holds `(E − B) T = U B` on the menu's
   classes.

What is not claimed. The adoption checks the run adds beside the certificate: the entry bound `2³`
(`entry_bound`), the constitution's storage growth and its budget, and the refusal when the slip
falls by less than `½ηa` (item 3 proves that it falls by at least that much). The retention fibre
the normal law reads (`retained_on_motion`) is not modeled: every column the reads reach moves. The
ring's transport `P^(t_r)` itself is abstracted as the carried image `v_r`; its holonomy is
`HolonicsResearch/Holon/RingCellHolonomy` and its reversal under the pairing `HNN/PairedDeposit`.
The covector scale `c` enters as a parameter `c ≥ 0`; the run reads the largest slip entry, which
item 7 reads on the concrete port. The normal law's step (`Reads.normal_unit_step`) assumes
`h_k + n_k ≠ 0` at every class: where a class no read reaches has `h_k = 0` the Gram is singular,
Lean's inverse reads `0` there, and `depositLocus` leaves the port as it was. No parity ties these
statements to the retired Rust owners.

The computational object is the helical pair interaction, read on the source port: a located pair
is a pair contact between a consequence's column and its antecedent's prior carried `t_r` ticks by
the ring's own transport; the slip is the contact's separation, `Q` its quadrance, `a` its first
variation read along the normal law's unit step, and the deposit is one certified move of the port
at the loci the key reaches. Of the winding guide's six general objects this touches the pair (the
contact between two crossings and its slip), faces and placement (the source port's columns, the
class map `T` and the consumer `(E − B) T = U B`) and the helix (the ring's clock, carried in the
image `v_r`); the cell holonomy, the tube and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.PairDepositStep

open Matrix

/-! ## 1. The slip and its square -/

/-- [definition] **The oriented reads of a pair deposit.** -/
structure Reads (𝕜 ρ κ ι : Type*) where
  /-- The declared prior `B` of the source port (the opening `E₀`). -/
  prior : Matrix ρ κ 𝕜
  /-- The carried image `v_r = P^(t_r) B e_(y_r)` of each read. -/
  image : ι → ρ → 𝕜
  /-- The consequence class `x_r` of each read, the column its slip moves. -/
  cls : ι → κ

namespace Reads

section Slip

variable {𝕜 : Type*} [Field 𝕜] {ρ κ ι : Type*} (R : Reads 𝕜 ρ κ ι)

/-- [definition] **The slip** of read `r` at the port `E`: `Δ_r(E) = v_r − (E − B) e_(x_r)`. -/
def slip (E : Matrix ρ κ 𝕜) (r : ι) : ρ → 𝕜 := R.image r - (E - R.prior).col (R.cls r)

/-- [proved-standard; formal-checked] The column `M e_k` is `M` applied to the one-hot `e_k`. -/
theorem col_eq_mulVec_single [Fintype κ] [DecidableEq κ] (M : Matrix ρ κ 𝕜) (k : κ) :
    M.col k = M *ᵥ Pi.single k 1 :=
  (mulVec_single_one M k).symm

/-- [proved-derived; formal-checked] Along `E + η D` each slip moves by `−η D e_(x_r)`. -/
theorem slip_along (E D : Matrix ρ κ 𝕜) (η : 𝕜) (r : ι) :
    R.slip (E + η • D) r = R.slip E r - η • D.col (R.cls r) := by
  funext i
  simp only [slip, col_apply, Pi.sub_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- [proved-derived; formal-checked] At the prior itself each slip is its carried image. -/
theorem slip_prior (r : ι) : R.slip R.prior r = R.image r := by
  funext i
  simp [slip]

/-- [proved-standard; formal-checked] The column of a scaled matrix is the scaled column. -/
theorem col_smul (η : 𝕜) (D : Matrix ρ κ 𝕜) (k : κ) : (η • D).col k = η • D.col k := by
  funext i
  simp

variable [Fintype ρ] [Fintype ι]

/-- [definition] **The slip's square** `Q(E) = Σ_r ⟨Δ_r, Δ_r⟩`. -/
def score (E : Matrix ρ κ 𝕜) : 𝕜 := ∑ r, R.slip E r ⬝ᵥ R.slip E r

/-- [definition] **The alignment** of a step `D`: `a = 2 Σ_r ⟨Δ_r, D e_(x_r)⟩`. -/
def alignment (E D : Matrix ρ κ 𝕜) : 𝕜 := 2 * ∑ r, R.slip E r ⬝ᵥ D.col (R.cls r)

/-- [definition] **The curvature** of a step `D`: `C = 2 Σ_r |D e_(x_r)|²`. -/
def curvature (D : Matrix ρ κ 𝕜) : 𝕜 := 2 * ∑ r, D.col (R.cls r) ⬝ᵥ D.col (R.cls r)

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- [proved-standard; formal-checked] **The score is a quadratic**: `Q(E + ηD) = Q(E) − ηa + ½η²C`. -/
theorem score_along (E D : Matrix ρ κ 𝕜) (η : 𝕜) :
    R.score (E + η • D) = R.score E - η * R.alignment E D + 1 / 2 * η ^ 2 * R.curvature D := by
  have hterm : ∀ r, R.slip (E + η • D) r ⬝ᵥ R.slip (E + η • D) r =
      R.slip E r ⬝ᵥ R.slip E r - 2 * η * (R.slip E r ⬝ᵥ D.col (R.cls r)) +
        η ^ 2 * (D.col (R.cls r) ⬝ᵥ D.col (R.cls r)) := by
    intro r
    rw [R.slip_along]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm (D.col (R.cls r)) (R.slip E r)]
    ring
  simp only [score, alignment, curvature, hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  ring

omit [Fintype ι] in
/-- [proved-standard; formal-checked] A vector's square is nonnegative. -/
theorem dot_self_nonneg (w : ρ → 𝕜) : 0 ≤ w ⬝ᵥ w :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)

/-- [proved-standard; formal-checked] The slip's square is nonnegative. -/
theorem score_nonneg (E : Matrix ρ κ 𝕜) : 0 ≤ R.score E :=
  Finset.sum_nonneg fun _ _ => dot_self_nonneg _

/-- [proved-standard; formal-checked] **The curvature is nonnegative**, `C ≥ 0`. -/
theorem curvature_nonneg (D : Matrix ρ κ 𝕜) : 0 ≤ R.curvature D :=
  mul_nonneg zero_le_two (Finset.sum_nonneg fun _ _ => dot_self_nonneg _)

/-- [proved-derived; formal-checked] **A step that aligns curves**: `a > 0` forces `C > 0`. -/
theorem curvature_pos (E D : Matrix ρ κ 𝕜) (ha : 0 < R.alignment E D) : 0 < R.curvature D := by
  rcases (R.curvature_nonneg D).lt_or_eq with h | h
  · exact h
  · exfalso
    have h0 : ∑ r, D.col (R.cls r) ⬝ᵥ D.col (R.cls r) = 0 := by
      unfold curvature at h
      linarith
    have hcol : ∀ r, D.col (R.cls r) = 0 := fun r =>
      dotProduct_self_eq_zero.mp
        ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => dot_self_nonneg _).mp h0 r (Finset.mem_univ r))
    have : R.alignment E D = 0 := by simp [alignment, hcol]
    linarith

/-- [proved-derived; formal-checked] **Q vanishes iff every slip does**: `Q(E) = 0 ↔ ∀ r, Δ_r(E) = 0`. -/
theorem score_eq_zero_iff (E : Matrix ρ κ 𝕜) : R.score E = 0 ↔ ∀ r, R.slip E r = 0 := by
  rw [score, Finset.sum_eq_zero_iff_of_nonneg fun _ _ => dot_self_nonneg _]
  simp only [Finset.mem_univ, true_implies, dotProduct_self_eq_zero]

/-- [proved-derived; formal-checked] **A closed slip aligns no step**: `Q(E) = 0 ⇒ a = 0`. -/
theorem alignment_of_closed (E D : Matrix ρ κ 𝕜) (h : R.score E = 0) : R.alignment E D = 0 := by
  have hs := (R.score_eq_zero_iff E).mp h
  simp [alignment, hs]

end Slip

/-! ### The quadratic upper model holds with equality -/

section Ray

variable {ρ κ ι : Type*} [Fintype ρ] [Fintype ι] (R : Reads ℝ ρ κ ι)

/-- [proved-derived; formal-checked] **The upper model is attained**: slope `−a + tC`, curvature `C`. -/
theorem score_ray (E D : Matrix ρ κ ℝ) {η : ℝ} (hη : 0 ≤ η) :
    (∀ t, HasDerivAt (fun s => R.score (E + s • D)) (-R.alignment E D + t * R.curvature D) t) ∧
      (∀ t, HasDerivAt (fun s => -R.alignment E D + s * R.curvature D) (R.curvature D) t) ∧
      R.score (E + η • D) ≤ R.score E - η * R.alignment E D + 1 / 2 * η ^ 2 * R.curvature D ∧
      R.score (E + η • D) = R.score E - η * R.alignment E D + 1 / 2 * η ^ 2 * R.curvature D := by
  have hfun : (fun s => R.score (E + s • D)) =
      fun s => R.score E - s * R.alignment E D + 1 / 2 * s ^ 2 * R.curvature D :=
    funext fun s => R.score_along E D s
  have d1 : ∀ t, HasDerivAt (fun s => R.score (E + s • D))
      (-R.alignment E D + t * R.curvature D) t := by
    intro t
    rw [hfun]
    have h := (((hasDerivAt_id' t).mul_const (R.alignment E D)).const_sub (R.score E)).add
      (((hasDerivAt_pow 2 t).const_mul (1 / 2 : ℝ)).mul_const (R.curvature D))
    refine h.congr_deriv ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  have d2 : ∀ t, HasDerivAt (fun s => -R.alignment E D + s * R.curvature D) (R.curvature D) t := by
    intro t
    simpa using ((hasDerivAt_id' t).mul_const (R.curvature D)).const_add (-R.alignment E D)
  have hle := Holonics.HolonCore.quadratic_upper_model (φ := fun s => R.score (E + s • D))
    (φ' := fun t => -R.alignment E D + t * R.curvature D) (φ'' := fun _ => R.curvature D)
    (a := R.alignment E D) (C := R.curvature D) hη (fun t _ => d1 t) (fun t _ => d2 t) (by simp) (fun _ _ => le_rfl)
  simp only [zero_smul, add_zero] at hle
  exact ⟨d1, d2, hle, R.score_along E D η⟩

end Ray

end Reads

/-! ## 2. The certified step -/

section Exponent

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [FloorSemiring 𝕜]

/-- [definition] **Both bounds at `η = 2^j`**: `2^j C ≤ a` and `2^j c ≤ 1`. -/
def Admits (a C c : 𝕜) (j : ℤ) : Prop := (2 : 𝕜) ^ j * C ≤ a ∧ (2 : 𝕜) ^ j * c ≤ 1

/-- [definition] **The certified exponent**: `min(⌊log₂(a/C)⌋, ⌊log₂(1/c)⌋)` over the bounds present. -/
def certExp (a C c : 𝕜) : ℤ :=
  if C = 0 then Int.log 2 (1 / c)
  else if c = 0 then Int.log 2 (a / C)
  else min (Int.log 2 (a / C)) (Int.log 2 (1 / c))

/-- [definition] **The certified step** `η = 2^k`, `k` the certified exponent. -/
def certStep (a C c : 𝕜) : 𝕜 := (2 : 𝕜) ^ certExp a C c

omit [FloorSemiring 𝕜] in
/-- [proved-standard; formal-checked] A dyadic step is positive. -/
theorem two_zpow_pos (j : ℤ) : (0 : 𝕜) < (2 : 𝕜) ^ j := zpow_pos two_pos j

/-- [proved-standard; formal-checked] `2^j ≤ r ↔ j ≤ ⌊log₂ r⌋` for `r > 0`. -/
theorem two_zpow_le_iff {r : 𝕜} (hr : 0 < r) (j : ℤ) : (2 : 𝕜) ^ j ≤ r ↔ j ≤ Int.log 2 r := by
  have h := Int.zpow_le_iff_le_log (R := 𝕜) (b := 2) (by norm_num) (x := j) hr
  simpa using h

/-- [proved-standard; formal-checked] The curvature bound, `2^j C ≤ a ↔ j ≤ ⌊log₂(a/C)⌋`. -/
theorem curvature_bound_iff {a C : 𝕜} (ha : 0 < a) (hC : 0 < C) (j : ℤ) :
    (2 : 𝕜) ^ j * C ≤ a ↔ j ≤ Int.log 2 (a / C) := by
  rw [← two_zpow_le_iff (div_pos ha hC), le_div_iff₀ hC]

/-- [proved-standard; formal-checked] The covector bound, `2^j c ≤ 1 ↔ j ≤ ⌊log₂(1/c)⌋`. -/
theorem covector_bound_iff {c : 𝕜} (hc : 0 < c) (j : ℤ) :
    (2 : 𝕜) ^ j * c ≤ 1 ↔ j ≤ Int.log 2 (1 / c) := by
  rw [← two_zpow_le_iff (div_pos one_pos hc), le_div_iff₀ hc]

/-- [proved-derived; formal-checked] **The exponent's spec**: `2^j` admits both bounds iff `j ≤ k`. -/
theorem admits_iff {a C c : 𝕜} (ha : 0 < a) (hC : 0 ≤ C) (hc : 0 ≤ c) (hne : C ≠ 0 ∨ c ≠ 0)
    (j : ℤ) : Admits a C c j ↔ j ≤ certExp a C c := by
  unfold Admits certExp
  by_cases hC0 : C = 0
  · have hc0 : c ≠ 0 := hne.resolve_left (not_not.mpr hC0)
    subst hC0
    rw [if_pos rfl, ← covector_bound_iff (lt_of_le_of_ne hc (Ne.symm hc0)), mul_zero]
    exact ⟨fun h => h.2, fun h => ⟨ha.le, h⟩⟩
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    rw [if_neg hC0]
    by_cases hc0 : c = 0
    · subst hc0
      rw [if_pos rfl, ← curvature_bound_iff ha hCpos, mul_zero]
      exact ⟨fun h => h.1, fun h => ⟨h, zero_le_one⟩⟩
    · rw [if_neg hc0, le_min_iff, ← curvature_bound_iff ha hCpos,
        ← covector_bound_iff (lt_of_le_of_ne hc (Ne.symm hc0))]

/-- [proved-derived; formal-checked] The certified exponent admits both bounds. -/
theorem admits_certExp {a C c : 𝕜} (ha : 0 < a) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hne : C ≠ 0 ∨ c ≠ 0) : Admits a C c (certExp a C c) :=
  (admits_iff ha hC hc hne _).mpr le_rfl

/-- [proved-derived; formal-checked] One more doubling breaks a bound. -/
theorem not_admits_succ {a C c : 𝕜} (ha : 0 < a) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hne : C ≠ 0 ∨ c ≠ 0) : ¬ Admits a C c (certExp a C c + 1) := fun h => by
  have := (admits_iff ha hC hc hne _).mp h
  omega

/-- [proved-derived; formal-checked] **The step's spec**: `η > 0`, `ηC ≤ a`, `ηc ≤ 1`, `2η` breaks one. -/
theorem certStep_spec {a C c : 𝕜} (ha : 0 < a) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hne : C ≠ 0 ∨ c ≠ 0) :
    0 < certStep a C c ∧ certStep a C c * C ≤ a ∧ certStep a C c * c ≤ 1 ∧
      ¬ (2 * certStep a C c * C ≤ a ∧ 2 * certStep a C c * c ≤ 1) := by
  obtain ⟨h1, h2⟩ := admits_certExp ha hC hc hne
  have h3 := not_admits_succ ha hC hc hne
  have hdouble : (2 : 𝕜) * certStep a C c = 2 ^ (certExp a C c + 1) := by
    rw [certStep, zpow_add_one₀ two_ne_zero, mul_comm]
  refine ⟨two_zpow_pos _, h1, h2, ?_⟩
  rw [hdouble]
  exact h3

/-- [proved-derived; formal-checked] **The largest admitted**: `j` admitted, `j + 1` not, gives `k = j`. -/
theorem certExp_eq_of {a C c : 𝕜} (ha : 0 < a) (hC : 0 ≤ C) (hc : 0 ≤ c) (hne : C ≠ 0 ∨ c ≠ 0)
    {j : ℤ} (hj : Admits a C c j) (hj1 : ¬ Admits a C c (j + 1)) : certExp a C c = j := by
  have h1 := (admits_iff ha hC hc hne j).mp hj
  have h2 : ¬ (j + 1 ≤ certExp a C c) := fun h => hj1 ((admits_iff ha hC hc hne _).mpr h)
  omega

/-- [proved-derived; formal-checked] **Monotone**: a larger `a` or a smaller `C`, `c` never shrinks `k`. -/
theorem certExp_mono {a C c a' C' c' : 𝕜} (ha : 0 < a) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hne : C ≠ 0 ∨ c ≠ 0) (ha' : 0 < a') (hC' : 0 ≤ C') (hc' : 0 ≤ c') (hne' : C' ≠ 0 ∨ c' ≠ 0)
    (haa : a ≤ a') (hCC : C' ≤ C) (hcc : c' ≤ c) : certExp a C c ≤ certExp a' C' c' := by
  obtain ⟨h1, h2⟩ := admits_certExp ha hC hc hne
  have hpos := (two_zpow_pos (𝕜 := 𝕜) (certExp a C c)).le
  refine (admits_iff ha' hC' hc' hne' _).mp ⟨?_, ?_⟩
  · calc (2 : 𝕜) ^ certExp a C c * C' ≤ 2 ^ certExp a C c * C := mul_le_mul_of_nonneg_left hCC hpos
      _ ≤ a := h1
      _ ≤ a' := haa
  · calc (2 : 𝕜) ^ certExp a C c * c' ≤ 2 ^ certExp a C c * c := mul_le_mul_of_nonneg_left hcc hpos
      _ ≤ 1 := h2

omit [FloorSemiring 𝕜] in
/-- [proved-derived; formal-checked] **A smaller dyadic keeps both bounds**: `j' ≤ j` keeps `Admits`. -/
theorem admits_anti {a C c : 𝕜} (hC : 0 ≤ C) (hc : 0 ≤ c) {j j' : ℤ} (hjj : j' ≤ j)
    (h : Admits a C c j) : Admits a C c j' := by
  have hz : (2 : 𝕜) ^ j' ≤ 2 ^ j := zpow_le_zpow_right₀ one_le_two hjj
  exact ⟨(mul_le_mul_of_nonneg_right hz hC).trans h.1, (mul_le_mul_of_nonneg_right hz hc).trans h.2⟩

/-- [proved-derived; formal-checked] **Halving keeps both bounds** (`CertifiedStep::halved`). -/
theorem halved_admits {a C c : 𝕜} (ha : 0 < a) (hC : 0 ≤ C) (hc : 0 ≤ c) (hne : C ≠ 0 ∨ c ≠ 0) :
    Admits a C c (certExp a C c - 1) :=
  admits_anti hC hc (by omega) (admits_certExp ha hC hc hne)

/-- [proved-derived; formal-checked] **The curvature binds** when `C > 0` and `ac ≤ C`: `a < 2ηC`. -/
theorem curvature_binds {a C c : 𝕜} (ha : 0 < a) (hC : 0 < C) (hc : 0 ≤ c) (hcap : a * c ≤ C) :
    a < 2 * certStep a C c * C := by
  obtain ⟨hη, -, -, hfail⟩ := certStep_spec ha hC.le hc (Or.inl hC.ne')
  by_contra hle
  push Not at hle
  have hcov : 1 < 2 * certStep a C c * c := by
    by_contra h
    push Not at h
    exact hfail ⟨hle, h⟩
  have : a < 2 * certStep a C c * C :=
    calc a = a * 1 := (mul_one a).symm
      _ < a * (2 * certStep a C c * c) := mul_lt_mul_of_pos_left hcov ha
      _ = 2 * certStep a C c * (a * c) := by ring
      _ ≤ 2 * certStep a C c * C := mul_le_mul_of_nonneg_left hcap (by positivity)
  linarith

end Exponent

/-! ## 3. The certified descent -/

section Descent

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- [proved-standard; formal-checked] The line's least value: `Q − (a/C)a + ½(a/C)²C = Q − a²/(2C)`. -/
theorem quadratic_at_minimizer {Q a C : 𝕜} (hC : 0 < C) :
    Q - a / C * a + 1 / 2 * (a / C) ^ 2 * C = Q - a ^ 2 / (2 * C) := by
  have hC0 := hC.ne'
  field_simp
  ring

/-- [proved-standard; formal-checked] Every point of the line lies above its least value. -/
theorem quadratic_ge_minimizer {Q a C : 𝕜} (hC : 0 < C) (η : 𝕜) :
    Q - a ^ 2 / (2 * C) ≤ Q - η * a + 1 / 2 * η ^ 2 * C := by
  have hC0 := hC.ne'
  have hid : Q - η * a + 1 / 2 * η ^ 2 * C - (Q - a ^ 2 / (2 * C)) =
      (η * C - a) ^ 2 / (2 * C) := by
    field_simp
    ring
  have hsq : 0 ≤ (η * C - a) ^ 2 / (2 * C) := by positivity
  linarith

/-- [proved-standard; formal-checked] **The bracket**: `ηC ≤ a < 2ηC` puts `η` in `(η*/2, η*]`. -/
theorem step_bracket {a C η : 𝕜} (hC : 0 < C) (hstep : η * C ≤ a) (hbind : a < 2 * η * C) :
    a / C / 2 < η ∧ η ≤ a / C := by
  constructor
  · rw [div_div, div_lt_iff₀ (by positivity)]
    linarith
  · rw [le_div_iff₀ hC]
    exact hstep

/-- [proved-standard; formal-checked] **Three quarters**: on `[η*/2, η*]`, `ηa − ½η²C ≥ ¾ · a²/(2C)`. -/
theorem three_quarters {a C η : 𝕜} (hC : 0 < C) (hstep : η * C ≤ a) (hbind : a ≤ 2 * η * C) :
    3 / 4 * (a ^ 2 / (2 * C)) ≤ η * a - 1 / 2 * η ^ 2 * C := by
  have hC0 := hC.ne'
  have h1 : 0 ≤ 2 * η * C - a := by linarith
  have h2 : 0 ≤ 3 * a - 2 * (η * C) := by linarith
  have key : 3 / 4 * (a ^ 2 / (2 * C)) = 3 * a ^ 2 / (8 * C) := by
    field_simp
    ring
  rw [key, div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg h1 h2]

namespace Reads

variable {ρ κ ι : Type*} [Fintype ρ] [Fintype ι] (R : Reads 𝕜 ρ κ ι)

/-- [proved-derived; formal-checked] **A step within its curvature descends**: `Q′ ≤ Q − ½ηa`. -/
theorem descends (E D : Matrix ρ κ 𝕜) {η : 𝕜} (hη : 0 ≤ η)
    (hstep : η * R.curvature D ≤ R.alignment E D) :
    R.score (E + η • D) ≤ R.score E - 1 / 2 * (η * R.alignment E D) := by
  have hmodel : R.score (E + η • D) ≤ R.score E - ∑ _ℓ ∈ (Finset.univ : Finset Unit),
      η * R.alignment E D + 1 / 2 * ∑ _ℓ ∈ (Finset.univ : Finset Unit), η ^ 2 * R.curvature D := by
    rw [R.score_along]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    ring_nf
    exact le_rfl
  have h := Holonics.HolonCore.certified_step_descends (Finset.univ : Finset Unit)
    (η := fun _ => η) (a := fun _ => R.alignment E D) (C := fun _ => R.curvature D) hmodel
    (fun _ _ => hη) (fun _ _ => hstep)
  simpa using h

/-- [proved-derived; formal-checked] **The certified descent**: at `η = 2^k`, `Q(E + ηD) ≤ Q(E) − ½ηa`. -/
theorem certified_descent [FloorSemiring 𝕜] (E D : Matrix ρ κ 𝕜) {c : 𝕜}
    (ha : 0 < R.alignment E D) (hc : 0 ≤ c) :
    R.score (E + certStep (R.alignment E D) (R.curvature D) c • D) ≤
      R.score E - 1 / 2 * (certStep (R.alignment E D) (R.curvature D) c * R.alignment E D) := by
  obtain ⟨hη, hstep, -, -⟩ :=
    certStep_spec ha (R.curvature_nonneg D) hc (Or.inl (R.curvature_pos E D ha).ne')
  exact R.descends E D hη.le hstep

/-- [proved-standard; formal-checked] **The line minimizer** `η* = a/C`: `Q − a²/(2C)`, least on the line. -/
theorem line_minimizer (E D : Matrix ρ κ 𝕜) (hC : 0 < R.curvature D) :
    R.score (E + (R.alignment E D / R.curvature D) • D) =
        R.score E - R.alignment E D ^ 2 / (2 * R.curvature D) ∧
      ∀ η : 𝕜, R.score (E + (R.alignment E D / R.curvature D) • D) ≤ R.score (E + η • D) := by
  have hmin : R.score (E + (R.alignment E D / R.curvature D) • D) =
      R.score E - R.alignment E D ^ 2 / (2 * R.curvature D) := by
    rw [R.score_along]
    exact quadratic_at_minimizer hC
  refine ⟨hmin, fun η => ?_⟩
  rw [hmin, R.score_along]
  exact quadratic_ge_minimizer hC η

/-- [proved-derived; formal-checked] **Three quarters kept** where the curvature binds, `η ∈ (η*/2, η*]`. -/
theorem certified_three_quarters [FloorSemiring 𝕜] (E D : Matrix ρ κ 𝕜) {c : 𝕜}
    (ha : 0 < R.alignment E D) (hc : 0 ≤ c)
    (hbind : R.alignment E D < 2 * certStep (R.alignment E D) (R.curvature D) c * R.curvature D) :
    R.alignment E D / R.curvature D / 2 < certStep (R.alignment E D) (R.curvature D) c ∧
      certStep (R.alignment E D) (R.curvature D) c ≤ R.alignment E D / R.curvature D ∧
      3 / 4 * (R.score E - R.score (E + (R.alignment E D / R.curvature D) • D)) ≤
        R.score E - R.score (E + certStep (R.alignment E D) (R.curvature D) c • D) := by
  have hC := R.curvature_pos E D ha
  obtain ⟨-, hstep, -, -⟩ := certStep_spec ha hC.le hc (Or.inl hC.ne')
  obtain ⟨hlo, hhi⟩ := step_bracket hC hstep hbind
  refine ⟨hlo, hhi, ?_⟩
  rw [(R.line_minimizer E D hC).1, R.score_along]
  have h := three_quarters hC hstep hbind.le
  linarith

end Reads

end Descent

/-! ## 4. The unit step aligns -/

section Unit

variable {𝕜 : Type*} [Field 𝕜] {ρ κ ι : Type*} [Fintype ρ] [Fintype ι] [DecidableEq κ]

namespace Reads

variable (R : Reads 𝕜 ρ κ ι)

/-- [definition] **The reads at a class**, `n_k = #{r : x_r = k}`. -/
def count (k : κ) : 𝕜 := ((Finset.univ.filter fun r => R.cls r = k).card : 𝕜)

/-- [definition] **The slip summed at a class**, `S_k = Σ_(r : x_r = k) Δ_r`. -/
def fiberSlip (E : Matrix ρ κ 𝕜) (k : κ) : ρ → 𝕜 :=
  ∑ r ∈ Finset.univ.filter (fun r => R.cls r = k), R.slip E r

/-- [definition] **The reached covector** `G`, whose column `k` is `S_k`. -/
def slipMatrix (E : Matrix ρ κ 𝕜) : Matrix ρ κ 𝕜 := fun i k => R.fiberSlip E k i

/-- [definition] **The unit step** at the diagonal statistic `h`: `D e_k = S_k / (h_k + n_k)`. -/
def unitStep (E : Matrix ρ κ 𝕜) (h : κ → 𝕜) : Matrix ρ κ 𝕜 :=
  fun i k => (h k + R.count k)⁻¹ * R.fiberSlip E k i

omit [Fintype ρ] in
/-- [proved-derived; formal-checked] The unit step's column `k` is `S_k / (h_k + n_k)`. -/
theorem col_unitStep (E : Matrix ρ κ 𝕜) (h : κ → 𝕜) (k : κ) :
    (R.unitStep E h).col k = (h k + R.count k)⁻¹ • R.fiberSlip E k := by
  funext i
  simp [unitStep, fiberSlip, Finset.sum_apply]

omit [Fintype ρ] in
/-- [proved-derived; formal-checked] A class no read reaches holds no slip. -/
theorem fiberSlip_of_card (E : Matrix ρ κ 𝕜) (k : κ)
    (hk : (Finset.univ.filter fun r => R.cls r = k).card = 0) : R.fiberSlip E k = 0 := by
  rw [Finset.card_eq_zero] at hk
  simp [fiberSlip, hk]

variable [Fintype κ]

/-- [proved-derived; formal-checked] **By class**: `Σ_r ⟨Δ_r, D e_(x_r)⟩ = Σ_k ⟨S_k, D e_k⟩`. -/
theorem pairing_fiberwise (E D : Matrix ρ κ 𝕜) :
    ∑ r, R.slip E r ⬝ᵥ D.col (R.cls r) = ∑ k, R.fiberSlip E k ⬝ᵥ D.col k := by
  rw [← Finset.sum_fiberwise Finset.univ R.cls]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fiberSlip, sum_dotProduct]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [(Finset.mem_filter.mp hr).2]

/-- [proved-derived; formal-checked] **The first variation** (`contact.dq`): `a = 2⟨G, D⟩_F`. -/
theorem alignment_frobenius (E D : Matrix ρ κ 𝕜) :
    R.alignment E D = 2 * ∑ i, ∑ k, R.slipMatrix E i k * D i k := by
  rw [alignment, pairing_fiberwise, Finset.sum_comm]
  rfl

/-- [proved-derived; formal-checked] **The unit step's alignment**: `a = 2 Σ_k |S_k|²/(h_k + n_k)`. -/
theorem unit_step_alignment (E : Matrix ρ κ 𝕜) (h : κ → 𝕜) :
    R.alignment E (R.unitStep E h) =
      2 * ∑ k, (R.fiberSlip E k ⬝ᵥ R.fiberSlip E k) / (h k + R.count k) := by
  rw [alignment, pairing_fiberwise]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [col_unitStep, dotProduct_smul, smul_eq_mul, div_eq_inv_mul]

omit [Fintype ι] [DecidableEq κ] in
/-- [proved-standard; formal-checked] The trace `tr(G M Gᵀ)` is the Frobenius pairing of `G M` with `G`. -/
theorem trace_chart (G : Matrix ρ κ 𝕜) (M : Matrix κ κ 𝕜) :
    trace (G * M * Gᵀ) = ∑ i, ∑ k, (G * M) i k * G i k := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diag_apply, mul_apply]
  rfl

/-- [proved-derived; formal-checked] **A chart's step**: for `D = G M`, `a = 2 tr(G M Gᵀ)`. -/
theorem chart_alignment (E : Matrix ρ κ 𝕜) (M : Matrix κ κ 𝕜) :
    R.alignment E (R.slipMatrix E * M) = 2 * trace (R.slipMatrix E * M * (R.slipMatrix E)ᵀ) := by
  rw [alignment_frobenius, trace_chart]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

omit [Fintype ρ] in
/-- [proved-derived; formal-checked] The unit step is the chart `diag((h + n)⁻¹)` read on `G`. -/
theorem unitStep_eq_chart (E : Matrix ρ κ 𝕜) (h : κ → 𝕜) :
    R.unitStep E h = R.slipMatrix E * diagonal fun k => (h k + R.count k)⁻¹ := by
  ext i k
  rw [mul_diagonal]
  simp only [unitStep, slipMatrix]
  ring

section Order

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [Fintype ρ] [Fintype κ] in
/-- [proved-standard; formal-checked] A count of reads is nonnegative. -/
theorem count_nonneg (k : κ) : 0 ≤ R.count k := Nat.cast_nonneg _

omit [Fintype ρ] [Fintype κ] in
/-- [proved-derived; formal-checked] At a nonnegative statistic, `h_k + n_k = 0` leaves no slip at `k`. -/
theorem fiberSlip_of_denominator (E : Matrix ρ κ 𝕜) {h : κ → 𝕜} (hh : ∀ k, 0 ≤ h k) {k : κ}
    (hk : h k + R.count k = 0) : R.fiberSlip E k = 0 := by
  have hc : R.count k = 0 := le_antisymm (by linarith [hh k]) (R.count_nonneg k)
  exact R.fiberSlip_of_card E k (Nat.cast_eq_zero.mp hc)

/-- [proved-derived; formal-checked] **The unit step aligns**: at `h ≥ 0`, `a ≥ 0`. -/
theorem unit_step_alignment_nonneg (E : Matrix ρ κ 𝕜) {h : κ → 𝕜} (hh : ∀ k, 0 ≤ h k) :
    0 ≤ R.alignment E (R.unitStep E h) := by
  rw [unit_step_alignment]
  exact mul_nonneg zero_le_two (Finset.sum_nonneg fun k _ =>
    div_nonneg (dot_self_nonneg _) (add_nonneg (hh k) (R.count_nonneg k)))

/-- [proved-derived; formal-checked] **Nothing descends where nothing reached**: `a = 0 ↔ ∀ k, S_k = 0`. -/
theorem unit_step_alignment_eq_zero_iff (E : Matrix ρ κ 𝕜) {h : κ → 𝕜} (hh : ∀ k, 0 ≤ h k) :
    R.alignment E (R.unitStep E h) = 0 ↔ ∀ k, R.fiberSlip E k = 0 := by
  rw [unit_step_alignment, mul_eq_zero, or_iff_right two_ne_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      div_nonneg (dot_self_nonneg _) (add_nonneg (hh k) (R.count_nonneg k))]
  constructor
  · intro h0 k
    rcases div_eq_zero_iff.mp (h0 k (Finset.mem_univ k)) with h1 | h1
    · exact dotProduct_self_eq_zero.mp h1
    · exact R.fiberSlip_of_denominator E hh h1
  · intro h0 k _
    rw [h0 k, dotProduct_zero, zero_div]

omit [Fintype ρ] [Fintype κ] in
/-- [proved-derived; formal-checked] **Nothing moves where nothing reached**: `D = 0 ↔ ∀ k, S_k = 0`. -/
theorem unitStep_eq_zero_iff (E : Matrix ρ κ 𝕜) {h : κ → 𝕜} (hh : ∀ k, 0 ≤ h k) :
    R.unitStep E h = 0 ↔ ∀ k, R.fiberSlip E k = 0 := by
  constructor
  · intro h0 k
    by_cases hk : h k + R.count k = 0
    · exact R.fiberSlip_of_denominator E hh hk
    · funext i
      have := congrFun (congrFun h0 i) k
      simp only [unitStep, Matrix.zero_apply] at this
      exact (mul_eq_zero.mp this).resolve_left (inv_ne_zero hk)
  · intro h0
    ext i k
    simp [unitStep, h0 k]

/-- [proved-derived; formal-checked] **A positive semidefinite chart aligns**: `a = 2 tr(G M Gᵀ) ≥ 0`. -/
theorem chart_alignment_nonneg (E : Matrix ρ κ 𝕜) {M : Matrix κ κ 𝕜}
    (hM : ∀ v, 0 ≤ v ⬝ᵥ (M *ᵥ v)) : 0 ≤ R.alignment E (R.slipMatrix E * M) := by
  rw [chart_alignment, trace_chart, Holonics.HNN.Normal.frobenius_chart]
  exact mul_nonneg zero_le_two (Finset.sum_nonneg fun i _ => hM _)

end Order

end Reads

end Unit

/-! ### The unit step is the source port's normal law -/

section NormalLaw

open Holonics.HNN.Normal (Window windowCovector windowGram LocusState depositLocus)

variable {𝕜 : Type*} [Field 𝕜] {ρ κ ι : Type*} [Fintype ρ] [Fintype ι] [Fintype κ] [DecidableEq κ]

namespace Reads

variable (R : Reads 𝕜 ρ κ ι)

/-- [definition] **The deposit's samples**: per read, weight one, feature `e_(x_r)`, covector `Δ_r`. -/
def window (E : Matrix ρ κ 𝕜) : Window 𝕜 κ ρ :=
  Finset.univ.toList.map fun r => ((1 : 𝕜), Pi.single (R.cls r) (1 : 𝕜), R.slip E r)

omit [Fintype ρ] [Fintype κ] in
/-- [proved-derived; formal-checked] The samples' reached covector `Σ_r Δ_r e_(x_r)ᵀ` is `G`. -/
theorem window_covector (E : Matrix ρ κ 𝕜) : windowCovector (R.window E) = R.slipMatrix E := by
  rw [windowCovector, window, List.map_map, Finset.sum_map_toList]
  ext i k
  simp only [Function.comp_apply, Matrix.sum_apply, vecMulVec_apply, one_smul, Pi.single_apply,
    mul_ite, mul_one, mul_zero, slipMatrix, fiberSlip, Finset.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hk : R.cls r = k
  · simp [hk]
  · simp [hk, Ne.symm hk]

omit [Fintype ρ] [Fintype κ] in
/-- [proved-derived; formal-checked] The samples' Gram `Σ_r e_(x_r) e_(x_r)ᵀ` is `diag(n)`. -/
theorem window_gram (E : Matrix ρ κ 𝕜) : windowGram (R.window E) = diagonal R.count := by
  rw [windowGram, window, List.map_map, Finset.sum_map_toList]
  ext j k
  simp only [Function.comp_apply, Matrix.sum_apply, vecMulVec_apply, one_smul, Pi.single_apply,
    diagonal_apply, count]
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h : R.cls r = j
    · simp [h]
    · simp [h, Ne.symm h]
  · rw [if_neg hjk]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases h : R.cls r = j
    · have hk : k ≠ R.cls r := by rw [h]; exact Ne.symm hjk
      simp [hk]
    · simp [Ne.symm h]

omit [Fintype ρ] in
/-- [proved-derived; formal-checked] **The normal law's step**: `depositLocus` moves the port by `η D`. -/
theorem normal_unit_step (E : Matrix ρ κ 𝕜) (h : κ → 𝕜) (θ : LocusState 𝕜 κ ρ) (hmap : θ.map = E)
    (hgram : θ.gram = diagonal h) (hpos : ∀ k, h k + R.count k ≠ 0) (η : 𝕜) :
    (depositLocus η θ (R.window E)).map = E + η • R.unitStep E h := by
  have hinv : (diagonal h + diagonal R.count)⁻¹ = diagonal fun k => (h k + R.count k)⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [diagonal_add, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ (hpos k)
  simp only [depositLocus, hmap, hgram, R.window_gram, R.window_covector, hinv, R.unitStep_eq_chart,
    Matrix.smul_mul]

end Reads

end NormalLaw

/-! ## 5. The consumer -/

section Consumer

variable {𝕜 : Type*} [Field 𝕜] {ρ κ ι : Type*} [Fintype κ] [DecidableEq κ]

/-- [definition] **The class map's matrix** `T e_y = e_(f y)`. -/
def classMap (f : κ → κ) : Matrix κ κ 𝕜 := fun i j => if i = f j then 1 else 0

/-- [proved-derived; formal-checked] `(M T) e_y = M e_(f y)`. -/
theorem col_mul_classMap (M : Matrix ρ κ 𝕜) (f : κ → κ) (j : κ) :
    (M * classMap f).col j = M.col (f j) := by
  funext i
  simp [classMap, Matrix.mul_apply]

namespace Reads

variable (R : Reads 𝕜 ρ κ ι)

omit [Fintype κ] [DecidableEq κ] in
/-- [proved-derived; formal-checked] A slip vanishes iff `(E − B) e_(x_r) = v_r`. -/
theorem slip_eq_zero_iff (E : Matrix ρ κ 𝕜) (r : ι) :
    R.slip E r = 0 ↔ (E - R.prior).col (R.cls r) = R.image r := by
  rw [slip, sub_eq_zero, eq_comm]

variable [Fintype ρ] [Fintype ι] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [Fintype κ] [DecidableEq κ] in
/-- [proved-derived; formal-checked] **The consumer**: `Q(E) = 0 ↔ ∀ r, (E − B) e_(x_r) = v_r`. -/
theorem score_eq_zero_iff_consumer (E : Matrix ρ κ 𝕜) :
    R.score E = 0 ↔ ∀ r, (E - R.prior).col (R.cls r) = R.image r := by
  rw [score_eq_zero_iff]
  exact forall_congr' fun r => R.slip_eq_zero_iff E r

/-- [proved-derived; formal-checked] **The consumer on the menu**: `Q(E) = 0 ↔ (E − B) T = U B` there. -/
theorem consumer (E : Matrix ρ κ 𝕜) (U : Matrix ρ ρ 𝕜) (f : κ → κ) (y : ι → κ)
    (hx : ∀ r, R.cls r = f (y r)) (hv : ∀ r, R.image r = (U * R.prior).col (y r)) :
    R.score E = 0 ↔ ∀ r, ((E - R.prior) * classMap f).col (y r) = (U * R.prior).col (y r) := by
  rw [score_eq_zero_iff_consumer]
  refine forall_congr' fun r => ?_
  rw [col_mul_classMap, ← hx, hv]

end Reads

end Consumer

/-! ## 6. The opening closes in one step -/

section Opening

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {ρ κ ι : Type*} [Fintype ρ]
  [Fintype ι] [Fintype κ] [DecidableEq κ]

namespace Reads

variable (R : Reads 𝕜 ρ κ ι)

omit [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype ρ] [Fintype κ] in
/-- [proved-derived; formal-checked] With one read per class, a read's class holds that read alone. -/
theorem fiber_of_injective (hinj : Function.Injective R.cls) (r : ι) :
    Finset.univ.filter (fun s => R.cls s = R.cls r) = {r} := by
  ext s
  simp [hinj.eq_iff]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype ρ] [Fintype κ] in
/-- [proved-derived; formal-checked] **The opening's unit step**: `D e_(x_r) = v_r / (h + 1)`. -/
theorem opening_col (hinj : Function.Injective R.cls) (h : κ → 𝕜) {h₀ : 𝕜}
    (hh : ∀ r, h (R.cls r) = h₀) (r : ι) :
    (R.unitStep R.prior h).col (R.cls r) = (h₀ + 1)⁻¹ • R.image r := by
  rw [col_unitStep, hh]
  simp [count, fiberSlip, R.fiber_of_injective hinj r, slip_prior]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype κ] in
/-- [proved-derived; formal-checked] **The opening's alignment**: `a = 2Q/(h + 1)`. -/
theorem opening_alignment (hinj : Function.Injective R.cls) (h : κ → 𝕜) {h₀ : 𝕜}
    (hh : ∀ r, h (R.cls r) = h₀) :
    R.alignment R.prior (R.unitStep R.prior h) = 2 * R.score R.prior / (h₀ + 1) := by
  simp only [alignment, score, R.opening_col hinj h hh, R.slip_prior, dotProduct_smul, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype κ] in
/-- [proved-derived; formal-checked] **The opening's curvature**: `C = 2Q/(h + 1)²`. -/
theorem opening_curvature (hinj : Function.Injective R.cls) (h : κ → 𝕜) {h₀ : 𝕜}
    (hh : ∀ r, h (R.cls r) = h₀) :
    R.curvature (R.unitStep R.prior h) = 2 * R.score R.prior / (h₀ + 1) ^ 2 := by
  simp only [curvature, score, R.opening_col hinj h hh, R.slip_prior, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, ← Finset.mul_sum]
  rw [div_eq_mul_inv, ← inv_pow]
  ring

omit [Fintype κ] in
/-- [proved-derived; formal-checked] **The opening's line minimizer** is `η* = a/C = h + 1`. -/
theorem opening_minimizer (hinj : Function.Injective R.cls) (h : κ → 𝕜) {h₀ : 𝕜}
    (hh : ∀ r, h (R.cls r) = h₀) (hh₀ : 0 ≤ h₀) (hQ : 0 < R.score R.prior) :
    R.alignment R.prior (R.unitStep R.prior h) / R.curvature (R.unitStep R.prior h) = h₀ + 1 := by
  have hpos : (0 : 𝕜) < h₀ + 1 := by linarith
  rw [R.opening_alignment hinj h hh, R.opening_curvature hinj h hh]
  field_simp

omit [Fintype κ] in
/-- [proved-derived; formal-checked] **The step `h + 1` closes every slip** from the opening. -/
theorem opening_closes (hinj : Function.Injective R.cls) (h : κ → 𝕜) {h₀ : 𝕜}
    (hh : ∀ r, h (R.cls r) = h₀) (hh₀ : 0 ≤ h₀) :
    R.score (R.prior + (h₀ + 1) • R.unitStep R.prior h) = 0 := by
  have hpos : (0 : 𝕜) < h₀ + 1 := by linarith
  rw [score_eq_zero_iff_consumer]
  intro r
  rw [add_sub_cancel_left, col_smul, R.opening_col hinj h hh, smul_smul, mul_inv_cancel₀ hpos.ne',
    one_smul]

omit [Fintype κ] in
/-- [proved-derived; formal-checked] **One certified step closes the opening** at `h + 1 = 2^j`. -/
theorem opening_certified [FloorSemiring 𝕜] (hinj : Function.Injective R.cls) (h : κ → 𝕜)
    {h₀ c : 𝕜} (hh : ∀ r, h (R.cls r) = h₀) (hh₀ : 0 ≤ h₀) {j : ℤ} (hj : h₀ + 1 = 2 ^ j)
    (hc : 0 ≤ c) (hcj : c * (h₀ + 1) ≤ 1) (hQ : 0 < R.score R.prior) :
    certExp (R.alignment R.prior (R.unitStep R.prior h)) (R.curvature (R.unitStep R.prior h)) c = j ∧
      certStep (R.alignment R.prior (R.unitStep R.prior h)) (R.curvature (R.unitStep R.prior h)) c =
        h₀ + 1 ∧
      R.score (R.prior +
        certStep (R.alignment R.prior (R.unitStep R.prior h)) (R.curvature (R.unitStep R.prior h)) c •
          R.unitStep R.prior h) = 0 ∧
      ∀ r, ((h₀ + 1) • R.unitStep R.prior h).col (R.cls r) = R.image r := by
  have hpos : (0 : 𝕜) < h₀ + 1 := by linarith
  have ha' := R.opening_alignment hinj h hh
  have hC' := R.opening_curvature hinj h hh
  have ha : 0 < R.alignment R.prior (R.unitStep R.prior h) := by
    rw [ha']
    exact div_pos (by linarith) hpos
  have hC := R.curvature_pos _ _ ha
  have hk : certExp (R.alignment R.prior (R.unitStep R.prior h)) (R.curvature (R.unitStep R.prior h)) c
      = j := by
    refine certExp_eq_of ha hC.le hc (Or.inl hC.ne') ⟨?_, ?_⟩ ?_
    · rw [← hj, hC', ha']
      refine le_of_eq ?_
      field_simp
    · rw [← hj]
      linarith
    · rintro ⟨h1, -⟩
      rw [zpow_add_one₀ two_ne_zero, ← hj, hC', ha'] at h1
      have hid : (h₀ + 1) * 2 * (2 * R.score R.prior / (h₀ + 1) ^ 2) =
          2 * (2 * R.score R.prior / (h₀ + 1)) := by
        field_simp
      have hq : 0 < 2 * R.score R.prior / (h₀ + 1) := div_pos (by linarith) hpos
      linarith
  have hη : certStep (R.alignment R.prior (R.unitStep R.prior h)) (R.curvature (R.unitStep R.prior h)) c
      = h₀ + 1 := by
    rw [certStep, hk, hj]
  have hclose := R.opening_closes hinj h hh hh₀
  refine ⟨hk, hη, by rw [hη]; exact hclose, fun r => ?_⟩
  have hcons := (R.score_eq_zero_iff_consumer _).mp hclose r
  rwa [add_sub_cancel_left] at hcons

end Reads

end Opening

/-! ## 7. The order-2 reading -/

section OrderTwo

/-- [proved-derived; formal-checked] **The record's certificate**: `a = 120`, `C = 60`, `c = ½` give `η = 2`. -/
theorem order_two_certificate :
    certExp (120 : ℚ) 60 (1 / 2) = 1 ∧ certStep (120 : ℚ) 60 (1 / 2) = 2 ∧
      (2 : ℚ) * 60 ≤ 120 ∧ (2 : ℚ) * (1 / 2) ≤ 1 ∧
      ¬ ((4 : ℚ) * 60 ≤ 120) ∧ ¬ ((4 : ℚ) * (1 / 2) ≤ 1) := by
  have hk : certExp (120 : ℚ) 60 (1 / 2) = 1 := by
    refine certExp_eq_of (by norm_num) (by norm_num) (by norm_num) (Or.inl (by norm_num)) ?_ ?_
    · constructor <;> norm_num
    · rintro ⟨h1, -⟩
      norm_num at h1
  refine ⟨hk, ?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
  rw [certStep, hk]
  norm_num

/-- [proved-derived; formal-checked] **The record's order-2 numbers** at `Q = 120`, `h = 1`. -/
theorem order_two_reading :
    (2 : ℚ) * 120 / (1 + 1) = 120 ∧ (2 : ℚ) * 120 / (1 + 1) ^ 2 = 60 ∧ (120 : ℚ) / 60 = 1 + 1 ∧
      (120 : ℚ) - 2 * 120 + 1 / 2 * 2 ^ 2 * 60 = 0 ∧ 1 / 2 * ((2 : ℚ) * 120) = 120 ∧
      (120 : ℕ) = 2 ^ 3 * 3 * 5 := by
  norm_num

/-- [definition] The concrete port's declared prior `B`, two rows and three classes. -/
def portPrior : Matrix (Fin 2) (Fin 3) ℚ := !![1 / 2, 0, 1; 0, 1 / 2, -1]

/-- [definition] The ring's transport over the distance, a quarter turn `U = [[0, −1], [1, 0]]`. -/
def quarterTurn : Matrix (Fin 2) (Fin 2) ℚ := !![0, -1; 1, 0]

/-- [definition] The located map `f = (0 1 2)` on the three classes. -/
def portMap : Fin 3 → Fin 3 := ![1, 2, 0]

/-- [definition] The antecedents read, `y = (0, 1)`. -/
def portAntecedent : Fin 2 → Fin 3 := ![0, 1]

/-- [definition] The concrete reads `(y, f y)` with images `U B e_y`. -/
def portReads : Reads ℚ (Fin 2) (Fin 3) (Fin 2) where
  prior := portPrior
  image r := (quarterTurn * portPrior).col (portAntecedent r)
  cls r := portMap (portAntecedent r)

/-- [definition] The port after the certified deposit. -/
def portAfter : Matrix (Fin 2) (Fin 3) ℚ := !![1 / 2, 0, 1 / 2; 0, 1, -1]

/-- [proved-derived; formal-checked] The transport of the prior: `U B = [[0, −½, 1], [½, 0, 1]]`. -/
theorem port_transport : quarterTurn * portPrior = !![0, -(1 / 2), 1; 1 / 2, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quarterTurn, portPrior, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-derived; formal-checked] The concrete images: `U B e_0 = (0, ½)`, `U B e_1 = (−½, 0)`. -/
theorem port_images : portReads.image 0 = ![0, 1 / 2] ∧ portReads.image 1 = ![-(1 / 2), 0] := by
  have himg : ∀ r, portReads.image r = (quarterTurn * portPrior).col (portAntecedent r) := fun _ => rfl
  rw [himg, himg, port_transport]
  refine ⟨?_, ?_⟩ <;> funext i <;> fin_cases i <;> rfl

/-- [proved-derived; formal-checked] The concrete reads take one read per class. -/
theorem port_injective : Function.Injective portReads.cls := by
  decide

/-- [proved-derived; formal-checked] The opening's slip: `Q = ½`, largest entry `½`. -/
theorem port_opening :
    portReads.score portPrior = 1 / 2 ∧
      (∀ r i, |portReads.slip portPrior r i| ≤ 1 / 2) ∧ portReads.slip portPrior 0 1 = 1 / 2 := by
  have hs : ∀ r, portReads.slip portPrior r = portReads.image r := portReads.slip_prior
  have h0 := port_images.1
  have h1 := port_images.2
  refine ⟨?_, ?_, ?_⟩
  · simp only [Reads.score, hs, Fin.sum_univ_two, h0, h1, dotProduct]
    norm_num
  · intro r i
    rw [hs]
    fin_cases r <;> fin_cases i <;> norm_num [h0, h1]
  · rw [hs, h0]
    rfl

/-- [proved-derived; formal-checked] **The concrete deposit closes at `η = 2`** with its consumer. -/
theorem port_deposit :
    portReads.alignment portPrior (portReads.unitStep portPrior fun _ => 1) = 1 / 2 ∧
      portReads.curvature (portReads.unitStep portPrior fun _ => 1) = 1 / 4 ∧
      certExp (1 / 2 : ℚ) (1 / 4) (1 / 2) = 1 ∧
      portPrior + certStep (1 / 2 : ℚ) (1 / 4) (1 / 2) • portReads.unitStep portPrior (fun _ => 1) =
        portAfter ∧
      portReads.score portAfter = 0 ∧
      ∀ r, ((portAfter - portPrior) * classMap portMap).col (portAntecedent r) =
        (quarterTurn * portPrior).col (portAntecedent r) := by
  have hQ := port_opening.1
  have hp : portReads.prior = portPrior := rfl
  have hh : ∀ r, (fun _ : Fin 3 => (1 : ℚ)) (portReads.cls r) = 1 := fun _ => rfl
  have ha := portReads.opening_alignment port_injective (fun _ => 1) hh
  have hC := portReads.opening_curvature port_injective (fun _ => 1) hh
  obtain ⟨hk, hη, hclose, -⟩ := portReads.opening_certified port_injective (fun _ => 1) hh zero_le_one
    (j := 1) (c := 1 / 2) (by norm_num) (by norm_num) (by norm_num) (by rw [hp, hQ]; norm_num)
  rw [hp] at ha hC hk hη hclose
  rw [hQ] at ha hC
  norm_num at ha hC
  rw [ha, hC] at hk hη hclose
  norm_num at hη
  have hD0 : (portReads.unitStep portPrior fun _ => 1).col 0 = 0 := by
    rw [Reads.col_unitStep, portReads.fiberSlip_of_card portPrior 0 (by decide), smul_zero]
  have hD1 : (portReads.unitStep portPrior fun _ => 1).col 1 = ![0, 1 / 4] := by
    have h := portReads.opening_col port_injective (fun _ => 1) hh 0
    rw [port_images.1, hp] at h
    rw [show (1 : Fin 3) = portReads.cls 0 from rfl, h]
    funext i
    fin_cases i <;> norm_num
  have hD2 : (portReads.unitStep portPrior fun _ => 1).col 2 = ![-(1 / 4), 0] := by
    have h := portReads.opening_col port_injective (fun _ => 1) hh 1
    rw [port_images.2, hp] at h
    rw [show (2 : Fin 3) = portReads.cls 1 from rfl, h]
    funext i
    fin_cases i <;> norm_num
  have hafter : portPrior + certStep (1 / 2 : ℚ) (1 / 4) (1 / 2) •
      portReads.unitStep portPrior (fun _ => 1) = portAfter := by
    rw [hη]
    ext i k
    have e0 := congrFun hD0 i
    have e1 := congrFun hD1 i
    have e2 := congrFun hD2 i
    simp only [col_apply] at e0 e1 e2
    fin_cases k <;> fin_cases i <;> simp_all [portPrior, portAfter] <;> norm_num
  have hscore : portReads.score portAfter = 0 := by
    rw [← hafter]
    exact hclose
  refine ⟨ha, hC, hk, hafter, hscore, ?_⟩
  exact (portReads.consumer portAfter quarterTurn portMap portAntecedent (fun _ => rfl)
    (fun _ => rfl)).mp hscore

end OrderTwo

end Holonics.HNN.PairDepositStep

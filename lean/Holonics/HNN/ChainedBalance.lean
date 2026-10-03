import Holonics.HNN.Ring

/-!
# HNN.ChainedBalance: the reception carry across words, its opening split and the singular hold

[definition] Rebuild step 4 (#73), the reception carry (record B,
`research/records/2026-10-03_THE_RECEPTION_CARRIES_THE_INTERIOR_CHANGE_THE_SOURCE_PORT_IMPOSES_THE_MOMENT_AND_REST_IS_COMPLETE_ABSORPTION.md`,
§2.3 and §2.3a). Between the end of word `k` and the opening of word `k + 1` the carried change `x`
meets the deposit `Θ → Θ'` (held at each contact's momentum, `x′`) and the ingest `λ → λ'` (its
arriving waves crossed at the reference change, `x″`); the source port then imposes the moment `s`
on the source rings. The Rust owners are `hnn::word::{ReceptionCarry, ChainedBalance, PowerForm}`.

[proved-derived; formal-checked] What is proved.

1. **The chained balance on one baseline** (§1). The power form is additive by ring with the source
   rings' storage `E_S` a field constant, `P_m(x) = P_m(Π_int x) + E_S(x)` (`power_split`). When the
   deposit and the ingest keep the source coordinates, the opening is
   `P_open = P_(Θ,λ)(y) + deposition + ingest + E_S(s)`, equivalently
   `P_(Θ,λ)(x) + deposition + ingest + E_S(s) − E_S(x)`, and the deposition reads the interior and
   the whole change alike (`opening_one_baseline`). The earlier draft, which wrote `P(y)` and also
   subtracted `E_S(x)`, falls short of the opening by exactly `E_S(x)` (`draft_subtracts_twice`).
   With the next word's balance `E_end = P_open − split − L + Π + residual`, `L ≥ 0` and
   `|residual| ≤ bound`, every reception is dissipative with respect to its declared supply
   (`reception_dissipative`), and over a chain the end storage telescopes: it is the first interior
   plus every reception's supply, less every loss and every later absorbed source storage, plus the
   residuals (`chain_telescopes`), so it never exceeds the first interior plus the supply plus the
   bounds (`chain_dissipative`, `chain_dissipative_certified` with the split's certified bound of §2).
2. **The rest limit** (`rest_opens_at_imposed`, `carry_enters_additively`). At `A = I` the carried
   interior is zero, the deposit and the ingest do no work on it and the opening is `E_S(s)` alone:
   today's opening. On the abstract word the carried interior enters the trajectory additively
   (`HNN/Retention.word_opens_at_zero`), and at rest the trajectory is the word's from `s` alone.
3. **The ingest only emits** (`ingest_emits`, `ingest_nonpos`). On the contacts' wave term of the
   power form the ingest is exactly minus the reflected power of the reference change,
   `−(h/4) Σ_a Γ_a² G_a |a_a|² ≤ 0` (`HNN/Ring.{reference_lift_work, reference_lift_work_nonpos}`).
   So the stronger reading `deposition + ingest ≤ L` holds whenever the deposition does no positive
   work (`reception_within_loss`); the deposition's sign at held momentum is
   `HolonicsResearch/HNN/HeldDeposition.held_deposition_nonpos` (from #284's `held_momentum_loss`).
4. **The opening's split is bounded by the opening** (§2). With the power form `½⟨z, Q z⟩`, `Q`
   symmetric and possibly indefinite (the signed stiffness), and the representative `z − r` within
   its half cell `|r_i| ≤ c_i`, the split is exactly `½⟨r, Q(z + (z − r))⟩`
   (`opening_split_eq`), zero on the lattice, and within
   `½ Σ_i c_i (2|(Q z)_i| + Σ_j |Q_ij| c_j)`, a bound read from the opening alone
   (`opening_split_le`, `splitBound`).
5. **The momentum a singular `C′` holds** (§3). For symmetric `C′` over an ordered field, a rate
   `w′` with `C′ w′ = π` exists exactly when `π` pairs to zero with every kernel direction of `C′`
   (`hold_iff_kernel_free`), and every such rate reads the same energy (`held_energy_unique`). A
   momentum with a kernel component has no hold; along the regularized mass `C′ + εI`, `C′ ⪰ 0`,
   every hold reads at least `(k·π)²/(ε |k|²)` (`singular_hold_energy`), unbounded as `ε` falls
   (`singular_hold_unbounded`). The refusal of such a momentum is therefore the law at held
   momentum: no finite-energy successor holds it. Where the hold exists, its deposition work is
   `held_momentum_loss`'s identity, which assumes no invertibility.

[definition; agent-inferred] The state is the pair `(source coordinates, interior)`; the interior
`Π_int x = (0, x.2)` zeroes every source ring (record B §2.1). That the deposit and the ingest keep
the source coordinates is #62 comment 5973454514's hypothesis, read from the owners: deposits move
contacts and resonators, the lift moves conductances, and the ring admittances are field constants.
The scalar chain states the identities the Rust `ChainedBalance::{closes, dissipative}` checks at
every reception; resonator storage, when present, is read in the end storage and the opening alike.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.ChainedBalance

open Matrix
open scoped BigOperators

/-! ## 1. The chained balance on one baseline -/

section Chained

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {S I Med : Type*}

/-- [definition] **The power form additive by ring**: the source rings' storage `E_S` (field
constants, independent of the medium) plus the interior's reading `R m` in the medium `m`. -/
def power (ES : S → K) (R : Med → I → K) (m : Med) (z : S × I) : K := ES z.1 + R m z.2

/-- [definition] **The interior** `Π_int z`: every source ring's storage at zero. -/
def interior [Zero S] (z : S × I) : S × I := (0, z.2)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] **The power splits at the source port**:
`P_m(x) = P_m(Π_int x) + E_S(x)` under every medium. -/
theorem power_split [Zero S] (ES : S → K) (hS : ES 0 = 0) (R : Med → I → K) (m : Med)
    (z : S × I) : power ES R m z = power ES R m (interior z) + ES z.1 := by
  simp [power, interior, hS, add_comm]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] **The chained balance on one baseline** (record B §2.3). The
deposit `m → m'` holds `x` at `x′` and the ingest `m' → m''` crosses `x′` to `x″`, both keeping the
source coordinates; the source port imposes `s`. With
`deposition = P_(m')(x′) − P_m(x)` and `ingest = P_(m'')(x″) − P_(m')(x′)`, the opening
`P_(m'')(s, x″_int)` is the interior's power plus both works plus the imposed storage, and,
on the whole end power, the same less the absorbed `E_S(x)`. The deposition reads the interior and
the whole change alike. -/
theorem opening_one_baseline [Zero S] (ES : S → K) (hS : ES 0 = 0) (R : Med → I → K)
    {m m' m'' : Med} {x x' x'' : S × I} (s : S) (h₁ : x'.1 = x.1) (h₂ : x''.1 = x'.1) :
    power ES R m'' (s, x''.2) =
        power ES R m (interior x) + (power ES R m' x' - power ES R m x) +
          (power ES R m'' x'' - power ES R m' x') + ES s ∧
      power ES R m'' (s, x''.2) =
        power ES R m x + (power ES R m' x' - power ES R m x) +
          (power ES R m'' x'' - power ES R m' x') + ES s - ES x.1 ∧
      power ES R m' (interior x') - power ES R m (interior x) =
        power ES R m' x' - power ES R m x := by
  simp only [power, interior, hS, h₂, h₁]
  refine ⟨by ring, by ring, by ring⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] **The draft subtracted the absorbed storage twice.** Writing
the interior's power and also subtracting `E_S(x)` falls short of the opening by exactly `E_S(x)`,
the source rings' storage at the word's end. -/
theorem draft_subtracts_twice [Zero S] (ES : S → K) (hS : ES 0 = 0) (R : Med → I → K)
    {m m' m'' : Med} {x x' x'' : S × I} (s : S) (h₁ : x'.1 = x.1) (h₂ : x''.1 = x'.1) :
    power ES R m'' (s, x''.2) -
        (power ES R m (interior x) + (power ES R m' x' - power ES R m x) +
          (power ES R m'' x'' - power ES R m' x') + ES s - ES x.1) = ES x.1 := by
  rw [(opening_one_baseline ES hS R s h₁ h₂).1]
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] **The rest limit** (`A = I`). The carried interior is zero
and the hold and the crossing of zero are zero; every medium reads the zero interior as zero. Then
the interior's power and the work on it vanish and the opening is `E_S(s)` alone: today's opening,
so today's balance is the limit of the chained one. -/
theorem rest_opens_at_imposed [Zero S] [Zero I] (ES : S → K) (hS : ES 0 = 0) (R : Med → I → K)
    (hR : ∀ m, R m 0 = 0) {m m' m'' : Med} {x x' x'' : S × I} (s : S) (h₁ : x'.1 = x.1)
    (h₂ : x''.1 = x'.1) (hx : x.2 = 0) (hx' : x'.2 = 0) (hx'' : x''.2 = 0) :
    power ES R m (interior x) = 0 ∧ power ES R m' x' - power ES R m x = 0 ∧
      power ES R m'' x'' - power ES R m' x' = 0 ∧ power ES R m'' (s, x''.2) = ES s := by
  simp only [power, interior, hS, hR, hx, hx', hx'', h₂, h₁]
  refine ⟨by simp, by ring, by ring, by simp⟩

/-- [proved-derived; formal-checked] **One reception is dissipative with respect to its declared
supply.** With the opening `P(y) + deposition + ingest + E_S(s)` and the next word's balance
`E_end = P_open − split − L + Π + residual`, `L ≥ 0`, `|residual| ≤ bound`:
`E_end ≤ P(y) + deposition + ingest + E_S(s) − split + Π + bound`. -/
theorem reception_dissipative {Py dep ing imp spl L Pt res b Eopen Eend : K}
    (hopen : Eopen = Py + dep + ing + imp) (hend : Eend = Eopen - spl - L + Pt + res)
    (hL : 0 ≤ L) (hres : |res| ≤ b) : Eend ≤ Py + dep + ing + imp - spl + Pt + b := by
  have := le_of_abs_le hres
  rw [hend, hopen]
  linarith

/-- [proved-derived; formal-checked] **The stronger reading where no work enters between the
words.** If the deposition and the ingest do no positive work, then `deposition + ingest ≤ L` and
the end storage is within the interior, the imposed storage, the ports, the split and the bound. -/
theorem reception_within_loss {Py dep ing imp spl L Pt res b Eopen Eend : K}
    (hopen : Eopen = Py + dep + ing + imp) (hend : Eend = Eopen - spl - L + Pt + res)
    (hL : 0 ≤ L) (hres : |res| ≤ b) (hdep : dep ≤ 0) (hing : ing ≤ 0) :
    dep + ing ≤ L ∧ Eend ≤ Py + imp - spl + Pt + b := by
  have := reception_dissipative hopen hend hL hres
  constructor <;> linarith

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] **The chain telescopes.** Word `k` ends at `E k`, its source
rings hold `A k` there (absorbed at the reception), and reception `k` carries the deposition, the
ingest, the imposed storage, the split, the next word's loss, its port terms and its residual. Then
`E (n+1)` is the first interior `E 0 − A 0` plus every reception's supply less its split and loss
plus its residual, less every later absorbed storage. -/
theorem chain_telescopes (E A dep ing imp spl L Pt res : ℕ → K)
    (hstep : ∀ k, E (k + 1) = E k - A k + dep k + ing k + imp k - spl k - L k + Pt k + res k)
    (n : ℕ) :
    E (n + 1) = E 0 - A 0 +
        ∑ k ∈ Finset.range (n + 1),
          (dep k + ing k + imp k - spl k - L k + Pt k + res k) -
        ∑ k ∈ Finset.range n, A (k + 1) := by
  induction n with
  | zero => simp [hstep 0]; ring
  | succ n ih =>
    rw [hstep (n + 1), ih]
    simp only [Finset.sum_range_succ]
    ring

/-- [proved-derived; formal-checked] **The chain is dissipative with respect to its declared
supply**: the end storage never exceeds the first interior plus everything the ports supplied, less
the splits, plus the residuals' bounds. Nothing enters except through a declared port. -/
theorem chain_dissipative (E A dep ing imp spl L Pt res b : ℕ → K)
    (hstep : ∀ k, E (k + 1) = E k - A k + dep k + ing k + imp k - spl k - L k + Pt k + res k)
    (hA : ∀ k, 0 ≤ A k) (hL : ∀ k, 0 ≤ L k) (hres : ∀ k, |res k| ≤ b k) (n : ℕ) :
    E (n + 1) ≤ E 0 - A 0 +
        ∑ k ∈ Finset.range (n + 1), (dep k + ing k + imp k - spl k + Pt k + b k) := by
  rw [chain_telescopes E A dep ing imp spl L Pt res hstep n]
  have h1 : ∑ k ∈ Finset.range (n + 1), (dep k + ing k + imp k - spl k - L k + Pt k + res k) ≤
      ∑ k ∈ Finset.range (n + 1), (dep k + ing k + imp k - spl k + Pt k + b k) :=
    Finset.sum_le_sum fun k _ => by linarith [hL k, le_of_abs_le (hres k)]
  have h2 : 0 ≤ ∑ k ∈ Finset.range n, A (k + 1) := Finset.sum_nonneg fun k _ => hA (k + 1)
  linarith

/-- [proved-derived; formal-checked] **The chain's certified form**: with each opening split
within its certified bound `σ k` (§2, `opening_split_le`), the end storage is within the first
interior plus the supply plus the splits' and residuals' bounds. -/
theorem chain_dissipative_certified (E A dep ing imp spl L Pt res b σ : ℕ → K)
    (hstep : ∀ k, E (k + 1) = E k - A k + dep k + ing k + imp k - spl k - L k + Pt k + res k)
    (hA : ∀ k, 0 ≤ A k) (hL : ∀ k, 0 ≤ L k) (hres : ∀ k, |res k| ≤ b k)
    (hspl : ∀ k, |spl k| ≤ σ k) (n : ℕ) :
    E (n + 1) ≤ E 0 - A 0 +
        ∑ k ∈ Finset.range (n + 1), (dep k + ing k + imp k + Pt k + σ k + b k) := by
  have h := chain_dissipative E A dep ing imp spl L Pt res b hstep hA hL hres n
  have h1 : ∑ k ∈ Finset.range (n + 1), (dep k + ing k + imp k - spl k + Pt k + b k) ≤
      ∑ k ∈ Finset.range (n + 1), (dep k + ing k + imp k + Pt k + σ k + b k) :=
    Finset.sum_le_sum fun k _ => by linarith [neg_abs_le (spl k), hspl k]
  linarith

end Chained

section Rest

open Holonics.HNN.Propagation

variable {B : Type*} [Fintype B] {K : Type*} [Field K] {M : B → Type*}
  [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]

/-- [proved-derived; formal-checked] **The carried interior enters the word additively, and at
rest the word is today's.** On the abstract word (`HNN/Retention.word_opens_at_zero`) the trajectory
from the opening `s + y` is the trajectory from the imposed `s` plus that from the carried interior
`y`; at rest (`y = 0`) it is the trajectory from `s` alone. -/
theorem carry_enters_additively (T : BlockOp K M) (s y : (b : B) → M b) (t : ℕ) :
    trajectory T (s + y) t = trajectory T s t + trajectory T y t ∧
      trajectory T (s + 0) t = trajectory T s t := by
  obtain ⟨hzero, hlin⟩ := Holonics.HNN.Retention.word_opens_at_zero T
  have h := hlin 1 s y t
  simp only [one_smul] at h
  refine ⟨h, ?_⟩
  rw [add_zero]

end Rest

section Lift

open Holonics.Computation.HolonicConstitutiveCirculation
open Holonics.HNN.Ring (reflection reference_lift_work reference_lift_work_nonpos)

variable {Ct W : Type*} [Fintype Ct] [Fintype W]

/-- [definition] **The contacts' wave term of the power form** (`PowerForm::power`): every contact
`a` carries its arriving waves `x a i` in its conductance `G a` at the lift, read as
`(h/4) Σ_a Σ_i G_a |x_(a,i)|²`. -/
def wavePower (h : ℚ) (G : Ct → ℚ) (x : Ct → W → ℚ) : ℚ := h / 4 * ∑ a, ∑ i, G a * x a i ^ 2

/-- [definition] **The waves crossed at the reference change** `G → G'` (`ReceptionCarry::crossed`):
each crosses as the junction's successor at a zero held wave, `(1 + Γ_a) x`. -/
def crossedWaves (G G' : Ct → ℚ) (x : Ct → W → ℚ) : Ct → W → ℚ :=
  fun a i => successorHeld (G a) (G' a) (x a i) 0

/-- [proved-derived; formal-checked] **The ingest only emits** (record B §2.3a). On the wave term,
the ingest `P_(Θ',λ')(x″) − P_(Θ',λ)(x′)` is exactly minus the reflected power,
`−(h/4) Σ_a Σ_i Γ_a² G_a |x_(a,i)|²` (`HNN/Ring.reference_lift_work`). The power form's other terms
(ring storage, contact states) are read at the constitution, not the lift, and cancel. -/
theorem ingest_emits (G G' : Ct → ℚ) (hG : ∀ a, 0 < G a) (hG' : ∀ a, 0 < G' a)
    (x : Ct → W → ℚ) (h ρ : ℚ) :
    (ρ + wavePower h G' (crossedWaves G G' x)) - (ρ + wavePower h G x) =
      -(h / 4 * ∑ a, ∑ i, reflection (G a) (G' a) ^ 2 * G a * x a i ^ 2) := by
  rw [← reference_lift_work G G' hG hG' x h]
  simp only [wavePower, crossedWaves, add_sub_add_left_eq_sub, ← mul_sub,
    ← Finset.sum_sub_distrib]

/-- [proved-derived; formal-checked] **The ingest does no positive work** for `h ≥ 0`, in either
direction of the conductances' move. -/
theorem ingest_nonpos (G G' : Ct → ℚ) (hG : ∀ a, 0 < G a) (hG' : ∀ a, 0 < G' a)
    (x : Ct → W → ℚ) {h : ℚ} (hh : 0 ≤ h) (ρ : ℚ) :
    (ρ + wavePower h G' (crossedWaves G G' x)) - (ρ + wavePower h G x) ≤ 0 := by
  rw [ingest_emits G G' hG hG' x h ρ, ← reference_lift_work G G' hG hG' x h]
  exact reference_lift_work_nonpos G G' hG hG' x hh

end Lift

/-! ## 2. The opening's split at the transient lattice -/

section Split

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n : Type*} [Fintype n]

/-- [proved-derived; formal-checked] **The split is a pairing with the remainder.** For a symmetric
form `Q` (block-diagonal in the power form: the rings' and waves' admittances, the contacts' `C`
and signed `K`), the opening `z` and its representative `z − r`,
`½⟨z, Q z⟩ − ½⟨z − r, Q(z − r)⟩ = ½⟨r, Q(z + (z − r))⟩`. -/
theorem opening_split_eq (Q : Matrix n n K) (hQ : Qᵀ = Q) (z r : n → K) :
    z ⬝ᵥ (Q *ᵥ z) / 2 - (z - r) ⬝ᵥ (Q *ᵥ (z - r)) / 2 = r ⬝ᵥ (Q *ᵥ (z + (z - r))) / 2 := by
  have hsym : z ⬝ᵥ (Q *ᵥ r) = r ⬝ᵥ (Q *ᵥ z) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hQ, dotProduct_comm]
  simp only [mulVec_add, mulVec_sub, dotProduct_add, dotProduct_sub, sub_dotProduct]
  linear_combination (1 / 2 : K) * hsym

/-- [definition] **The split's certified bound read from the opening**: with half cells `c`,
`½ Σ_i c_i (2|(Q z)_i| + Σ_j |Q_ij| c_j)`. -/
def splitBound (Q : Matrix n n K) (z c : n → K) : K :=
  (∑ i, c i * (2 * |(Q *ᵥ z) i| + ∑ j, |Q i j| * c j)) / 2

/-- [proved-derived; formal-checked] **The opening's split is within its certified bound.** A
transmitted wave or held rate need not lie on the word's transient lattice; the opening splits it at
the nearest point, so the remainder is within the half cell, `|r_i| ≤ c_i`. The split
`P(z) − P(z − r)` is then within `splitBound Q z c`, read from the opening alone. No sign of `Q` is
assumed: the contacts' stiffness may be indefinite. -/
theorem opening_split_le (Q : Matrix n n K) (hQ : Qᵀ = Q) (z r c : n → K)
    (hr : ∀ i, |r i| ≤ c i) :
    |z ⬝ᵥ (Q *ᵥ z) / 2 - (z - r) ⬝ᵥ (Q *ᵥ (z - r)) / 2| ≤ splitBound Q z c := by
  rw [opening_split_eq Q hQ z r, abs_div, abs_two, splitBound]
  refine div_le_div_of_nonneg_right ?_ zero_le_two
  have hc : ∀ i, 0 ≤ c i := fun i => (abs_nonneg _).trans (hr i)
  have hrow : ∀ i, |(Q *ᵥ (z + (z - r))) i| ≤ 2 * |(Q *ᵥ z) i| + ∑ j, |Q i j| * c j := by
    intro i
    have e : (Q *ᵥ (z + (z - r))) i = 2 * (Q *ᵥ z) i - (Q *ᵥ r) i := by
      simp only [mulVec_add, mulVec_sub, Pi.add_apply, Pi.sub_apply]
      ring
    have hQr : |(Q *ᵥ r) i| ≤ ∑ j, |Q i j| * c j := by
      calc |(Q *ᵥ r) i| = |∑ j, Q i j * r j| := rfl
        _ ≤ ∑ j, |Q i j * r j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, |Q i j| * c j := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hr j) (abs_nonneg _)
    rw [e]
    calc |2 * (Q *ᵥ z) i - (Q *ᵥ r) i| ≤ |2 * (Q *ᵥ z) i| + |(Q *ᵥ r) i| := abs_sub _ _
      _ = 2 * |(Q *ᵥ z) i| + |(Q *ᵥ r) i| := by rw [abs_mul, abs_two]
      _ ≤ _ := by linarith
  calc |r ⬝ᵥ (Q *ᵥ (z + (z - r)))| = |∑ i, r i * (Q *ᵥ (z + (z - r))) i| := rfl
    _ ≤ ∑ i, |r i * (Q *ᵥ (z + (z - r))) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, c i * (2 * |(Q *ᵥ z) i| + ∑ j, |Q i j| * c j) := Finset.sum_le_sum fun i _ => by
      rw [abs_mul]; exact mul_le_mul (hr i) (hrow i) (abs_nonneg _) (hc i)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] **A change on the lattice splits to itself**: every earlier
opening is unchanged. -/
theorem opening_split_on_lattice (Q : Matrix n n K) (z : n → K) :
    z ⬝ᵥ (Q *ᵥ z) / 2 - (z - 0) ⬝ᵥ (Q *ᵥ (z - 0)) / 2 = 0 := by
  simp

end Split

/-! ## 3. The momentum a singular `C′` holds -/

section Singular

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n : Type*} [Fintype n]

/-- [proved-derived; formal-checked] A vector's square pairing is nonnegative over an ordered
field. -/
theorem dot_self_nonneg (v : n → K) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] **A held momentum pairs to zero with the kernel**: if
`C′ w′ = π` with `C′` symmetric, then `⟨k, π⟩ = 0` for every `k` with `C′ k = 0`. -/
theorem hold_needs_kernel_free (C : Matrix n n K) (hC : Cᵀ = C) {π w k : n → K}
    (hw : C *ᵥ w = π) (hk : C *ᵥ k = 0) : k ⬝ᵥ π = 0 := by
  rw [← hw, dotProduct_mulVec, ← mulVec_transpose, hC, hk, zero_dotProduct]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] **Every hold reads the same energy**: two rates holding one
momentum at a symmetric `C′` pair equally with it, so the fibre `w′ + ker C′` that the solve leaves
free carries one reading `⟨w′, C′ w′⟩ = ⟨w′, π⟩`. -/
theorem held_energy_unique (C : Matrix n n K) (hC : Cᵀ = C) {π w₁ w₂ : n → K}
    (h₁ : C *ᵥ w₁ = π) (h₂ : C *ᵥ w₂ = π) : w₁ ⬝ᵥ π = w₂ ⬝ᵥ π := by
  rw [← h₂, dotProduct_mulVec, ← mulVec_transpose, hC, h₁, dotProduct_comm, h₂]

/-- [proved-derived; formal-checked] **A symmetric mass's range meets its kernel only at zero**,
over an ordered field: `v = C ρ` and `C v = 0` give `⟨v, v⟩ = ⟨ρ, C v⟩ = 0`. -/
theorem range_inf_ker (C : Matrix n n K) (hC : Cᵀ = C) :
    LinearMap.range C.mulVecLin ⊓ LinearMap.ker C.mulVecLin = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨⟨ρ, hρ⟩, hv⟩ := Submodule.mem_inf.mp hv
  replace hv : C *ᵥ v = 0 := by simpa using LinearMap.mem_ker.mp hv
  rw [mulVecLin_apply] at hρ
  have h := hold_needs_kernel_free C hC hρ hv
  exact (Submodule.mem_bot K).mpr (dotProduct_self_eq_zero.mp h)

/-- [proved-derived; formal-checked] **The held-momentum law at a singular `C′`.** A rate holding
the momentum `π` at a symmetric `C′` exists exactly when `π` pairs to zero with every kernel
direction of `C′`. Range and kernel span the space (rank–nullity and `range_inf_ker`), so
`π = C′ ρ + π_k`, and `⟨π_k, π⟩ = 0` forces `⟨π_k, π_k⟩ = 0`. -/
theorem hold_iff_kernel_free (C : Matrix n n K) (hC : Cᵀ = C) (π : n → K) :
    (∃ w, C *ᵥ w = π) ↔ ∀ k, C *ᵥ k = 0 → k ⬝ᵥ π = 0 := by
  refine ⟨fun ⟨w, hw⟩ k hk => hold_needs_kernel_free C hC hw hk, fun h => ?_⟩
  set f := C.mulVecLin
  have hdim := LinearMap.finrank_range_add_finrank_ker f
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range f) (LinearMap.ker f)
  rw [range_inf_ker C hC, finrank_bot] at hsup
  have htop : LinearMap.range f ⊔ LinearMap.ker f = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by omega)
  obtain ⟨y, ⟨ρ, hρ⟩, k, hk, hyk⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top (x := π))
  rw [LinearMap.mem_ker, mulVecLin_apply] at hk
  rw [mulVecLin_apply] at hρ
  have hky : k ⬝ᵥ y = 0 := hold_needs_kernel_free C hC hρ hk
  have hkπ := h k hk
  rw [← hyk, dotProduct_add, hky, zero_add] at hkπ
  have hk0 : k = 0 := dotProduct_self_eq_zero.mp hkπ
  exact ⟨ρ, by rw [hρ, ← hyk, hk0, add_zero]⟩

variable [DecidableEq n]

/-- [proved-derived; formal-checked] **A kernel momentum costs `1/ε` along the regularized mass.**
For symmetric `C′ ⪰ 0`, `ε > 0`, a kernel direction `k` (`C′ k = 0`) and any rate `w` holding `π`
at `C′ + εI`, `⟨k, π⟩² ≤ ε |k|² ⟨w, π⟩`: the hold's reading `⟨w, (C′ + εI) w⟩ = ⟨w, π⟩` is at
least `⟨k, π⟩²/(ε |k|²)`. The proof is Cauchy–Schwarz in the form of `C′ + εI`, where `k` reads
`ε |k|²`. -/
theorem singular_hold_energy (C : Matrix n n K) (hC : Cᵀ = C)
    (hpsd : ∀ v, 0 ≤ v ⬝ᵥ (C *ᵥ v)) {ε : K} (hε : 0 < ε) {π w k : n → K}
    (hw : (C + ε • (1 : Matrix n n K)) *ᵥ w = π) (hk : C *ᵥ k = 0) :
    (k ⬝ᵥ π) ^ 2 ≤ ε * (k ⬝ᵥ k) * (w ⬝ᵥ π) := by
  have hMk : (C + ε • (1 : Matrix n n K)) *ᵥ k = ε • k := by
    rw [add_mulVec, hk, smul_mulVec, one_mulVec, zero_add]
  have hMs : (C + ε • (1 : Matrix n n K))ᵀ = C + ε • (1 : Matrix n n K) := by
    rw [transpose_add, hC, transpose_smul, transpose_one]
  -- `ε ⟨w, k⟩ = ⟨π, k⟩`
  have hwk : ε * (w ⬝ᵥ k) = k ⬝ᵥ π := by
    have e : w ⬝ᵥ ((C + ε • (1 : Matrix n n K)) *ᵥ k) =
        ((C + ε • (1 : Matrix n n K)) *ᵥ w) ⬝ᵥ k := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hMs, dotProduct_comm]
    rw [hMk, hw, dotProduct_smul, smul_eq_mul] at e
    rw [e, dotProduct_comm]
  -- the form of `C′ + εI` is nonnegative
  have hpos : ∀ v, 0 ≤ v ⬝ᵥ ((C + ε • (1 : Matrix n n K)) *ᵥ v) := fun v => by
    rw [add_mulVec, dotProduct_add, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
    exact add_nonneg (hpsd v) (mul_nonneg hε.le (dot_self_nonneg v))
  have hv := hpos ((ε * (k ⬝ᵥ k)) • w - (k ⬝ᵥ π) • k)
  have hexp : ((ε * (k ⬝ᵥ k)) • w - (k ⬝ᵥ π) • k) ⬝ᵥ
      ((C + ε • (1 : Matrix n n K)) *ᵥ ((ε * (k ⬝ᵥ k)) • w - (k ⬝ᵥ π) • k)) =
      ε * (k ⬝ᵥ k) * (ε * (k ⬝ᵥ k) * (w ⬝ᵥ π) - (k ⬝ᵥ π) ^ 2) := by
    rw [mulVec_sub, mulVec_smul, mulVec_smul, hw, hMk]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    linear_combination (-(ε * (k ⬝ᵥ k)) * (k ⬝ᵥ π)) * hwk
  rw [hexp] at hv
  rcases (mul_nonneg hε.le (dot_self_nonneg k)).lt_or_eq with hc | hc
  · by_contra hlt
    replace hlt := not_le.mp hlt
    have : ε * (k ⬝ᵥ k) * (ε * (k ⬝ᵥ k) * (w ⬝ᵥ π) - (k ⬝ᵥ π) ^ 2) < 0 :=
      mul_neg_of_pos_of_neg hc (by linarith)
    linarith
  · have hkk : k ⬝ᵥ k = 0 := by
      rcases mul_eq_zero.mp hc.symm with h | h
      · exact absurd h hε.ne'
      · exact h
    have hk0 : k = 0 := dotProduct_self_eq_zero.mp hkk
    subst hk0
    simp

/-- [proved-derived; formal-checked] **The refusal is the law at held momentum.** A momentum with a
kernel component (`C′ k = 0`, `⟨k, π⟩ ≠ 0`) has no hold at `C′` (`hold_iff_kernel_free`), and the
holds at the regularized mass `C′ + εI` read above every bound once `ε` is small enough: no
finite-energy successor holds it. -/
theorem singular_hold_unbounded (C : Matrix n n K) (hC : Cᵀ = C)
    (hpsd : ∀ v, 0 ≤ v ⬝ᵥ (C *ᵥ v)) {π k : n → K} (hk : C *ᵥ k = 0) (hkπ : k ⬝ᵥ π ≠ 0)
    (E : K) :
    (¬ ∃ w, C *ᵥ w = π) ∧
      ∃ ε₀ : K, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
        ∀ w, (C + ε • (1 : Matrix n n K)) *ᵥ w = π → E < w ⬝ᵥ π := by
  refine ⟨fun ⟨w, hw⟩ => hkπ (hold_needs_kernel_free C hC hw hk), ?_⟩
  have hk0 : k ≠ 0 := by rintro rfl; simp at hkπ
  have hq : 0 < k ⬝ᵥ k :=
    lt_of_le_of_ne (dot_self_nonneg k) fun h => hk0 (dotProduct_self_eq_zero.mp h.symm)
  have hb : 0 < (k ⬝ᵥ π) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hkπ))
  have hD : 0 < |E| + 1 := by positivity
  refine ⟨(k ⬝ᵥ π) ^ 2 / ((k ⬝ᵥ k) * (|E| + 1)), div_pos hb (mul_pos hq hD),
    fun ε hε hle w hw => ?_⟩
  have h := singular_hold_energy C hC hpsd hε hw hk
  rw [le_div_iff₀ (mul_pos hq hD), ← mul_assoc] at hle
  have h2 : |E| + 1 ≤ w ⬝ᵥ π := le_of_mul_le_mul_left (hle.trans h) (mul_pos hε hq)
  linarith [le_abs_self E]

end Singular

section Audit

#print axioms power_split
#print axioms opening_one_baseline
#print axioms draft_subtracts_twice
#print axioms rest_opens_at_imposed
#print axioms reception_dissipative
#print axioms reception_within_loss
#print axioms chain_telescopes
#print axioms chain_dissipative
#print axioms chain_dissipative_certified
#print axioms carry_enters_additively
#print axioms ingest_emits
#print axioms ingest_nonpos
#print axioms opening_split_eq
#print axioms opening_split_le
#print axioms opening_split_on_lattice
#print axioms dot_self_nonneg
#print axioms hold_needs_kernel_free
#print axioms held_energy_unique
#print axioms range_inf_ker
#print axioms hold_iff_kernel_free
#print axioms singular_hold_energy
#print axioms singular_hold_unbounded

end Audit

end Holonics.HNN.ChainedBalance

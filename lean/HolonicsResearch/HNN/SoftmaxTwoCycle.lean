import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# A place hearing its own softmax release in step: the pair energy falls by the relative entropy, and the orbit settles on two-cycles

The ring record of November 13 (`research/records/2026-11-13_THE_FIELD_RINGS_UNDER_ITS_OWN_RELEASE_…`, §2 and §5; atlas
`tower.field-echo`, `motion.relaxed-step-three-kinds`) read a place that hears only its own release flip between two faces
every pass, the successive changes pairing at −0.99. `HNN/SynchronousTwoCycle` proves the synchronous two-cycle in the sign
chart (Goles and Olivos). #410's box owes the release the field actually makes: a softmax over classes at the temperature the
field holds, not a sign. This file proves it for that release.

The model. Places `i : P` and classes `c : C`, both finite; a state `x : P × C → ℝ`, a law when each place's face
`x(i, ·)` is a distribution over its classes (`IsLaw`). A symmetric coupling `W` between (place, class) pairs and a bias `b`
give the field `h = W x + b` (`field`); the synchronous step releases every place at once on the softmax of its field at
the temperature `T > 0`, `F(x)(i, c) = e^(h(i,c)/T) / Z_i` (`release`, `step`). `T` is the temperature the field holds, a
store's state; nothing here sets it.

[proved-standard; formal-checked] What is proved.

1. **The release is a law** (`partition_pos`, `release_pos`, `release_sum`, `release_isLaw`, `log_release`): every face of
   the release is positive and sums to one at each place, and `log F(x)(i, c) = h(i, c)/T − log Z_i`.
2. **The pair energy falls by the relative entropy** (`energy_identity`): with the pair energy of two successive states
   `E(s, t) = −⟨t, W s⟩ − ⟨b, s + t⟩ + T (Σ s log s + Σ t log t)` (`energy`), for a symmetric coupling and a law `s`,
   `E(s, t) = E(t, F t) + T · D(s ‖ F t)`, with `D(s ‖ u) = Σ s (log s − log u)` (`kl`) summed over the places. It is the
   sign chart's identity (`SynchronousTwoCycle.energy_identity`) with the sum of terms `(F(t)_i − s_i)(W t)_i` replaced by
   the relative entropy of the state two steps apart, through Gibbs's variational principle.
3. **Gibbs's inequality** (`gap_nonneg`, `gap_eq_zero`, `kl_eq_sum_gap`, `kl_nonneg`, `kl_eq_zero_iff`): `D(s ‖ u) ≥ 0`
   for a law `s` and a positive law `u`, with equality exactly when `s = u`.
4. **The energy falls in step, and stands only on a fixed point or a two-cycle** (`energy_step_le`, `energy_step_eq_iff`,
   `orbit_isLaw`, `energy_orbit_le`, `energy_orbit_eq_iff`): along the orbit `x_(k+1) = F x_k` of a law,
   `E(x_(k+1), x_(k+2)) ≤ E(x_k, x_(k+1))`, with equality exactly when `x_(k+2) = x_k`.
5. **The fall telescopes** (`energy_telescope`): `E(x_0, x_1) = E(x_K, x_(K+1)) + T Σ_(k<K) D(x_k ‖ x_(k+2))`, so the
   relative entropies between states two passes apart sum to at most the energy's whole fall: the orbit's departure
   from a two-cycle is summable wherever the energy is bounded below (`energy_lower_bound`: on laws it is at least
   `−Σ|W| − 2Σ|b| − 2T|P × C|`), and `kl_two_apart_summable` reads it.

Limits. The softmax chart, a coupling symmetric between (place, class) pairs, one temperature for every place. The orbit's
two-cycle is approached, not reached: that `x_(k+2) − x_k → 0` in norm, or convergence of the orbit itself (which needs
Łojasiewicz's inequality or isolated critical points), is not here; statement 5 gives the summable relative entropy. The
sign chart is the limit `T → 0` of this one and is proved apart (`HNN/SynchronousTwoCycle`). The engine's release is not
tied to these statements.

The computational object is the helical pair interaction: the coupling `W` is the pair contacts' symmetric exchange, a
place's field the contacts' sum at it, the release its face at the field's temperature, and the two-cycle the sheet that
flips each pass. Of the winding guide's six general objects this touches the pair (the symmetric exchange), faces and
placement (the softmax face of each place) and the tube (the passes as a clocked span); the helix, the cell holonomy and
the tower thread stay attached.

Consumers: the atlas rows `tower.field-echo` and `motion.relaxed-step-three-kinds`; #410's box on the synchronous
two-cycle, beside `HNN/SynchronousTwoCycle`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.SoftmaxTwoCycle

open Finset Real

variable {P C : Type*} [Fintype P] [Fintype C]

/-! ## 1. The field, the release and the step -/

/-- [definition] **The field** at a (place, class) pair: the contacts' sum `Σ W(a, a′) x(a′)` and the bias. -/
def field (W : P × C → P × C → ℝ) (b : P × C → ℝ) (x : P × C → ℝ) (a : P × C) : ℝ :=
  b a + ∑ a', W a a' * x a'

/-- [definition] **The partition** of a place at the temperature `T`: `Z_i = Σ_c e^(h(i,c)/T)`. -/
noncomputable def partition (T : ℝ) (h : P × C → ℝ) (i : P) : ℝ := ∑ c, Real.exp (h (i, c) / T)

/-- [definition] **The release**: each place's softmax face of its field at the temperature `T`. -/
noncomputable def release (T : ℝ) (h : P × C → ℝ) (a : P × C) : ℝ := Real.exp (h a / T) / partition T h a.1

/-- [definition] **The synchronous step**: every place releases on the field its contacts give it, all at once. -/
noncomputable def step (W : P × C → P × C → ℝ) (b : P × C → ℝ) (T : ℝ) (x : P × C → ℝ) : P × C → ℝ :=
  release T (field W b x)

/-- [definition] A **law**: each place's face is a distribution over its classes. -/
def IsLaw (x : P × C → ℝ) : Prop := (∀ a, 0 ≤ x a) ∧ ∀ i, ∑ c, x (i, c) = 1

omit [Fintype P] in
/-- [proved-standard] The partition is positive. -/
theorem partition_pos [Nonempty C] (T : ℝ) (h : P × C → ℝ) (i : P) : 0 < partition T h i :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

omit [Fintype P] in
/-- [proved-standard] Every face of the release is positive. -/
theorem release_pos [Nonempty C] (T : ℝ) (h : P × C → ℝ) (a : P × C) : 0 < release T h a :=
  div_pos (Real.exp_pos _) (partition_pos T h a.1)

omit [Fintype P] in
/-- [proved-standard] Each place's release sums to one. -/
theorem release_sum [Nonempty C] (T : ℝ) (h : P × C → ℝ) (i : P) : ∑ c, release T h (i, c) = 1 := by
  unfold release
  dsimp only
  rw [← Finset.sum_div]
  exact div_self (partition_pos T h i).ne'

omit [Fintype P] in
/-- [proved-standard] **The release is a law.** -/
theorem release_isLaw [Nonempty C] (T : ℝ) (h : P × C → ℝ) : IsLaw (release T h) :=
  ⟨fun a => (release_pos T h a).le, release_sum T h⟩

omit [Fintype P] in
/-- [proved-standard] `log F(i, c) = h(i, c)/T − log Z_i`. -/
theorem log_release [Nonempty C] (T : ℝ) (h : P × C → ℝ) (a : P × C) :
    Real.log (release T h a) = h a / T - Real.log (partition T h a.1) := by
  unfold release
  rw [Real.log_div (Real.exp_pos _).ne' (partition_pos T h a.1).ne', Real.log_exp]

/-! ## 2. The pair energy and its identity -/

/-- [definition] The pairing `⟨x, W y⟩ = Σ x(a) W(a, a′) y(a′)`. -/
def pairing (W : P × C → P × C → ℝ) (x y : P × C → ℝ) : ℝ := ∑ a, x a * ∑ a', W a a' * y a'

/-- [definition] `Σ x log x`, the negative of the faces' entropy. -/
noncomputable def ent (x : P × C → ℝ) : ℝ := ∑ a, x a * Real.log (x a)

/-- [definition] **The pair energy** of two successive states:
`E(s, t) = −⟨t, W s⟩ − ⟨b, s + t⟩ + T (Σ s log s + Σ t log t)`. -/
noncomputable def energy (W : P × C → P × C → ℝ) (b : P × C → ℝ) (T : ℝ) (s t : P × C → ℝ) : ℝ :=
  -pairing W t s - ∑ a, b a * (s a + t a) + T * (ent s + ent t)

/-- [definition] **The relative entropy** `D(s ‖ u) = Σ s (log s − log u)`, summed over the places. -/
noncomputable def kl (s u : P × C → ℝ) : ℝ := ∑ a, s a * (Real.log (s a) - Real.log (u a))

/-- [proved-standard] For a symmetric coupling, `⟨t, W s⟩ = ⟨s, W t⟩`. -/
theorem pairing_symm {W : P × C → P × C → ℝ} (hW : ∀ a a', W a a' = W a' a) (s t : P × C → ℝ) :
    pairing W t s = pairing W s t := by
  unfold pairing
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun a' _ => ?_))
  rw [hW a' a]
  ring

/-- [proved-standard] A difference of two laws sums to zero against any weight read at the place. -/
theorem sum_sub_mul_place {s u : P × C → ℝ} (hs : ∀ i, ∑ c, s (i, c) = 1) (hu : ∀ i, ∑ c, u (i, c) = 1)
    (g : P → ℝ) : ∑ a, (u a - s a) * g a.1 = 0 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  simp only
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, hu i, hs i, sub_self, zero_mul]

/-- [proved-standard] **The pair energy falls by the relative entropy:** for a symmetric coupling, a law `s` and
`T ≠ 0`, `E(s, t) = E(t, F t) + T · D(s ‖ F t)`. -/
theorem energy_identity [Nonempty C] {W : P × C → P × C → ℝ} (hW : ∀ a a', W a a' = W a' a)
    (b : P × C → ℝ) {T : ℝ} (hT : T ≠ 0) {s : P × C → ℝ} (hs : ∀ i, ∑ c, s (i, c) = 1) (t : P × C → ℝ) :
    energy W b T s t = energy W b T t (step W b T t) + T * kl s (step W b T t) := by
  have hlaw : IsLaw (step W b T t) := release_isLaw T (field W b t)
  -- the release's log is the field less the place's partition
  have hlog : ∀ a, field W b t a - T * Real.log (step W b T t a) =
      T * Real.log (partition T (field W b t) a.1) := by
    intro a
    have h := log_release T (field W b t) a
    change Real.log (step W b T t a) = _ at h
    rw [h]
    field_simp
    ring
  have hkey : ∑ a, (step W b T t a - s a) * (field W b t a - T * Real.log (step W b T t a)) = 0 := by
    simp_rw [hlog]
    exact sum_sub_mul_place hs hlaw.2 (fun i => T * Real.log (partition T (field W b t) i))
  have hfield : ∀ a, ∑ a', W a a' * t a' = field W b t a - b a := by
    intro a
    unfold field
    ring
  -- both energies as sums over the pairs
  have hE1 : energy W b T s t = ∑ a, (-(s a * ∑ a', W a a' * t a') - b a * (s a + t a) +
      T * (s a * Real.log (s a) + t a * Real.log (t a))) := by
    unfold energy ent
    rw [pairing_symm hW, pairing]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, mul_add]
  have hE2 : energy W b T t (step W b T t) = ∑ a, (-(step W b T t a * ∑ a', W a a' * t a') -
      b a * (t a + step W b T t a) +
      T * (t a * Real.log (t a) + step W b T t a * Real.log (step W b T t a))) := by
    unfold energy ent
    rw [pairing]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, mul_add]
  rw [hE1, hE2]
  unfold kl
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← hkey]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [hfield a]
  ring

/-! ## 3. Gibbs's inequality -/

/-- [definition] The pointwise gap `s(log s − log u) − s + u`, which sums to `D(s ‖ u)` on two laws. -/
noncomputable def gap (s u : ℝ) : ℝ := s * (Real.log s - Real.log u) - s + u

/-- [proved-standard] The gap is nonnegative for `s ≥ 0 < u`. -/
theorem gap_nonneg {s u : ℝ} (hs : 0 ≤ s) (hu : 0 < u) : 0 ≤ gap s u := by
  unfold gap
  rcases hs.lt_or_eq with hs | hs
  · have h := Real.log_le_sub_one_of_pos (div_pos hu hs)
    rw [Real.log_div hu.ne' hs.ne'] at h
    have h2 : s * (Real.log u - Real.log s) ≤ s * (u / s - 1) := mul_le_mul_of_nonneg_left h hs.le
    have h3 : s * (u / s - 1) = u - s := by field_simp
    nlinarith
  · rw [← hs]
    simp [hu.le]

/-- [proved-standard] The gap vanishes only where `s = u`. -/
theorem gap_eq_zero {s u : ℝ} (hs : 0 ≤ s) (hu : 0 < u) (h0 : gap s u = 0) : s = u := by
  unfold gap at h0
  rcases hs.lt_or_eq with hs | hs
  · by_contra hne
    have hne' : u / s ≠ 1 := by
      intro h1
      rw [div_eq_one_iff_eq hs.ne'] at h1
      exact hne h1.symm
    have h := Real.log_lt_sub_one_of_pos (div_pos hu hs) hne'
    rw [Real.log_div hu.ne' hs.ne'] at h
    have h2 : s * (Real.log u - Real.log s) < s * (u / s - 1) := mul_lt_mul_of_pos_left h hs
    have h3 : s * (u / s - 1) = u - s := by field_simp
    nlinarith
  · rw [← hs] at h0
    simp at h0
    linarith

/-- [proved-standard] On two laws the relative entropy is the sum of the gaps. -/
theorem kl_eq_sum_gap {s u : P × C → ℝ} (hs : ∀ i, ∑ c, s (i, c) = 1) (hu : ∀ i, ∑ c, u (i, c) = 1) :
    kl s u = ∑ a, gap (s a) (u a) := by
  have h0 := sum_sub_mul_place hs hu (fun _ => 1)
  simp only [mul_one] at h0
  unfold kl gap
  have : ∑ a, (s a * (Real.log (s a) - Real.log (u a)) - s a + u a) =
      ∑ a, s a * (Real.log (s a) - Real.log (u a)) + ∑ a, (u a - s a) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  rw [this, h0, add_zero]

/-- [proved-standard] **Gibbs's inequality:** `D(s ‖ u) ≥ 0` for a law `s` and a positive law `u`. -/
theorem kl_nonneg {s u : P × C → ℝ} (hs : IsLaw s) (hu0 : ∀ a, 0 < u a) (hu : ∀ i, ∑ c, u (i, c) = 1) :
    0 ≤ kl s u := by
  rw [kl_eq_sum_gap hs.2 hu]
  exact Finset.sum_nonneg (fun a _ => gap_nonneg (hs.1 a) (hu0 a))

/-- [proved-standard] **Gibbs's equality:** `D(s ‖ u) = 0` exactly when `s = u`. -/
theorem kl_eq_zero_iff {s u : P × C → ℝ} (hs : IsLaw s) (hu0 : ∀ a, 0 < u a) (hu : ∀ i, ∑ c, u (i, c) = 1) :
    kl s u = 0 ↔ s = u := by
  constructor
  · intro h0
    rw [kl_eq_sum_gap hs.2 hu] at h0
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => gap_nonneg (hs.1 a) (hu0 a))).mp h0
    funext a
    exact gap_eq_zero (hs.1 a) (hu0 a) (hall a (Finset.mem_univ a))
  · rintro rfl
    unfold kl
    simp

/-! ## 4. The energy falls in step -/

/-- [proved-standard] **The energy falls in step:** for a law `s` and `T > 0`, `E(t, F t) ≤ E(s, t)`. -/
theorem energy_step_le [Nonempty C] {W : P × C → P × C → ℝ} (hW : ∀ a a', W a a' = W a' a)
    (b : P × C → ℝ) {T : ℝ} (hT : 0 < T) {s : P × C → ℝ} (hs : IsLaw s) (t : P × C → ℝ) :
    energy W b T t (step W b T t) ≤ energy W b T s t := by
  rw [energy_identity hW b hT.ne' hs.2 t]
  have hlaw := release_isLaw (P := P) T (field W b t)
  have := kl_nonneg hs (release_pos T (field W b t)) hlaw.2
  have : 0 ≤ T * kl s (step W b T t) := mul_nonneg hT.le this
  linarith

/-- [proved-standard] **The energy stands only on a fixed point or a two-cycle:** `E(t, F t) = E(s, t)` exactly when
`F t = s`. -/
theorem energy_step_eq_iff [Nonempty C] {W : P × C → P × C → ℝ} (hW : ∀ a a', W a a' = W a' a)
    (b : P × C → ℝ) {T : ℝ} (hT : 0 < T) {s : P × C → ℝ} (hs : IsLaw s) (t : P × C → ℝ) :
    energy W b T t (step W b T t) = energy W b T s t ↔ step W b T t = s := by
  rw [energy_identity hW b hT.ne' hs.2 t]
  have hlaw := release_isLaw (P := P) T (field W b t)
  constructor
  · intro h
    have h0 : T * kl s (step W b T t) = 0 := by linarith
    have hk : kl s (step W b T t) = 0 := (mul_eq_zero.mp h0).resolve_left hT.ne'
    exact ((kl_eq_zero_iff hs (release_pos T (field W b t)) hlaw.2).mp hk).symm
  · intro h
    have hk : kl s (step W b T t) = 0 := (kl_eq_zero_iff hs (release_pos T (field W b t)) hlaw.2).mpr h.symm
    rw [hk, mul_zero, add_zero]

/-- [definition] The orbit of a state under the synchronous step. -/
noncomputable def orbit (W : P × C → P × C → ℝ) (b : P × C → ℝ) (T : ℝ) (x : P × C → ℝ) (k : ℕ) : P × C → ℝ :=
  (step W b T)^[k] x

/-- [proved-standard] The orbit takes one step at a time. -/
theorem orbit_succ (W : P × C → P × C → ℝ) (b : P × C → ℝ) (T : ℝ) (x : P × C → ℝ) (k : ℕ) :
    orbit W b T x (k + 1) = step W b T (orbit W b T x k) := by
  unfold orbit
  rw [Function.iterate_succ_apply']

/-- [proved-standard] The orbit of a law stays a law. -/
theorem orbit_isLaw [Nonempty C] (W : P × C → P × C → ℝ) (b : P × C → ℝ) (T : ℝ) {x : P × C → ℝ}
    (hx : IsLaw x) (k : ℕ) : IsLaw (orbit W b T x k) := by
  cases k with
  | zero => exact hx
  | succ k => rw [orbit_succ]; exact release_isLaw T _

/-- [proved-standard] **Along the orbit the pair energy falls**:
`E(x_(k+1), x_(k+2)) ≤ E(x_k, x_(k+1))`. -/
theorem energy_orbit_le [Nonempty C] {W : P × C → P × C → ℝ} (hW : ∀ a a', W a a' = W a' a)
    (b : P × C → ℝ) {T : ℝ} (hT : 0 < T) {x : P × C → ℝ} (hx : IsLaw x) (k : ℕ) :
    energy W b T (orbit W b T x (k + 1)) (orbit W b T x (k + 2)) ≤
      energy W b T (orbit W b T x k) (orbit W b T x (k + 1)) := by
  rw [show k + 2 = k + 1 + 1 from rfl, orbit_succ W b T x (k + 1)]
  exact energy_step_le hW b hT (orbit_isLaw W b T hx k) _

/-- [proved-standard] **It stands exactly on a two-cycle**: `E(x_(k+1), x_(k+2)) = E(x_k, x_(k+1))` iff
`x_(k+2) = x_k`. -/
theorem energy_orbit_eq_iff [Nonempty C] {W : P × C → P × C → ℝ} (hW : ∀ a a', W a a' = W a' a)
    (b : P × C → ℝ) {T : ℝ} (hT : 0 < T) {x : P × C → ℝ} (hx : IsLaw x) (k : ℕ) :
    energy W b T (orbit W b T x (k + 1)) (orbit W b T x (k + 2)) =
        energy W b T (orbit W b T x k) (orbit W b T x (k + 1)) ↔
      orbit W b T x (k + 2) = orbit W b T x k := by
  rw [show k + 2 = k + 1 + 1 from rfl, orbit_succ W b T x (k + 1)]
  exact energy_step_eq_iff hW b hT (orbit_isLaw W b T hx k) _

/-- [proved-standard] **The fall telescopes:** `E(x_0, x_1) = E(x_K, x_(K+1)) + T Σ_(k<K) D(x_k ‖ x_(k+2))`. -/
theorem energy_telescope [Nonempty C] {W : P × C → P × C → ℝ} (hW : ∀ a a', W a a' = W a' a)
    (b : P × C → ℝ) {T : ℝ} (hT : T ≠ 0) {x : P × C → ℝ} (hx : IsLaw x) (K : ℕ) :
    energy W b T (orbit W b T x 0) (orbit W b T x 1) =
      energy W b T (orbit W b T x K) (orbit W b T x (K + 1)) +
        T * ∑ k ∈ Finset.range K, kl (orbit W b T x k) (orbit W b T x (k + 2)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [ih, Finset.sum_range_succ, mul_add]
    have h := energy_identity hW b hT (orbit_isLaw W b T hx K).2 (orbit W b T x (K + 1))
    rw [← orbit_succ W b T x (K + 1)] at h
    rw [h]
    ring

/-! ## 5. A floor for the energy, and the summable departure from a two-cycle -/

/-- [proved-standard] `x log x ≥ x − 1` for `x ≥ 0`. -/
theorem mul_log_ge (x : ℝ) (hx : 0 ≤ x) : x - 1 ≤ x * Real.log x := by
  rcases hx.lt_or_eq with hx | hx
  · have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
    rw [Real.log_inv] at h
    have h2 : x * (-Real.log x) ≤ x * (x⁻¹ - 1) := mul_le_mul_of_nonneg_left h hx.le
    have h3 : x * (x⁻¹ - 1) = 1 - x := by field_simp
    nlinarith
  · rw [← hx]
    simp

omit [Fintype P] in
/-- [proved-standard] On a law every face lies in `[0, 1]`. -/
theorem law_le_one {x : P × C → ℝ} (hx : IsLaw x) (a : P × C) : x a ≤ 1 := by
  have h := hx.2 a.1
  rw [← h]
  exact Finset.single_le_sum (f := fun c => x (a.1, c)) (fun c _ => hx.1 (a.1, c)) (Finset.mem_univ a.2)

/-- [proved-standard] **A floor for the pair energy on laws:**
`E(s, t) ≥ −Σ|W| − 2Σ|b| − 2T|P × C|` for `T ≥ 0`. -/
theorem energy_lower_bound (W : P × C → P × C → ℝ) (b : P × C → ℝ) {T : ℝ} (hT : 0 ≤ T) {s t : P × C → ℝ}
    (hs : IsLaw s) (ht : IsLaw t) :
    -(∑ a, ∑ a', |W a a'|) - 2 * ∑ a, |b a| - 2 * T * (Fintype.card (P × C) : ℝ) ≤ energy W b T s t := by
  unfold energy pairing ent
  have hpair : ∑ a, t a * ∑ a', W a a' * s a' ≤ ∑ a, ∑ a', |W a a'| := by
    refine Finset.sum_le_sum (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun a' _ => ?_)
    have h1 := ht.1 a; have h2 := law_le_one ht a; have h3 := hs.1 a'; have h4 := law_le_one hs a'
    have hw : W a a' ≤ |W a a'| := le_abs_self _
    have hw' : -|W a a'| ≤ W a a' := neg_abs_le _
    have hts : t a * s a' ≤ 1 := by nlinarith
    have hts0 : 0 ≤ t a * s a' := mul_nonneg h1 h3
    have habs : 0 ≤ |W a a'| := abs_nonneg _
    calc t a * (W a a' * s a') = W a a' * (t a * s a') := by ring
      _ ≤ |W a a'| * (t a * s a') := mul_le_mul_of_nonneg_right hw hts0
      _ ≤ |W a a'| * 1 := mul_le_mul_of_nonneg_left hts habs
      _ = |W a a'| := mul_one _
  have hbias : ∑ a, b a * (s a + t a) ≤ 2 * ∑ a, |b a| := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun a _ => ?_)
    have h1 := hs.1 a; have h2 := law_le_one hs a; have h3 := ht.1 a; have h4 := law_le_one ht a
    have hb : b a ≤ |b a| := le_abs_self _
    have hb' : -|b a| ≤ b a := neg_abs_le _
    nlinarith [abs_nonneg (b a)]
  have hent : ∀ x : P × C → ℝ, IsLaw x → -(Fintype.card (P × C) : ℝ) ≤ ∑ a, x a * Real.log (x a) := by
    intro x hx
    have : ∑ a, (x a - 1) ≤ ∑ a, x a * Real.log (x a) :=
      Finset.sum_le_sum (fun a _ => mul_log_ge (x a) (hx.1 a))
    have h0 : 0 ≤ ∑ a, x a := Finset.sum_nonneg (fun a _ => hx.1 a)
    rw [Finset.sum_sub_distrib] at this
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
    linarith
  have h1 := hent s hs
  have h2 := hent t ht
  have hTe : T * (-(Fintype.card (P × C) : ℝ) + -(Fintype.card (P × C) : ℝ)) ≤
      T * (∑ a, s a * Real.log (s a) + ∑ a, t a * Real.log (t a)) :=
    mul_le_mul_of_nonneg_left (by linarith) hT
  nlinarith

/-- [proved-standard] **The departure from a two-cycle is summable:** for `T > 0` the relative entropies between
states two passes apart have bounded partial sums, `T Σ_(k<K) D(x_k ‖ x_(k+2)) ≤ E(x_0, x_1) + Σ|W| + 2Σ|b| + 2T|P × C|`,
so they are summable and tend to zero. -/
theorem kl_two_apart_summable [Nonempty C] {W : P × C → P × C → ℝ} (hW : ∀ a a', W a a' = W a' a)
    (b : P × C → ℝ) {T : ℝ} (hT : 0 < T) {x : P × C → ℝ} (hx : IsLaw x) :
    Summable (fun k => kl (orbit W b T x k) (orbit W b T x (k + 2))) := by
  have hnn : ∀ k, 0 ≤ kl (orbit W b T x k) (orbit W b T x (k + 2)) := by
    intro k
    have hl := orbit_isLaw W b T hx (k + 2)
    rw [show k + 2 = k + 1 + 1 from rfl, orbit_succ W b T x (k + 1)]
    exact kl_nonneg (orbit_isLaw W b T hx k) (release_pos T _) (release_isLaw T _).2
  refine summable_of_sum_range_le hnn (c := (energy W b T (orbit W b T x 0) (orbit W b T x 1) +
    (∑ a, ∑ a', |W a a'|) + 2 * ∑ a, |b a| + 2 * T * (Fintype.card (P × C) : ℝ)) / T) (fun K => ?_)
  rw [le_div_iff₀ hT]
  have htel := energy_telescope hW b hT.ne' hx K
  have hfl := energy_lower_bound W b hT.le (orbit_isLaw W b T hx K) (orbit_isLaw W b T hx (K + 1))
  nlinarith

end Holonics.HNN.SoftmaxTwoCycle

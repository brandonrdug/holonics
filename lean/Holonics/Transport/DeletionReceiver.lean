import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# The deletion receiver: its clock, its transport, its moment, its composition and its likelihood

[definition] The deletion receiver `D_p` reads a source word `x` over an arbitrary alphabet `α`
(symbols, notes and samples alike; nothing here is modality-specific). Each position independently
survives with weight `p` or is deleted with weight `1 − p`, and the receipt is the trace, the
survivors in order. This module states the receiver's exact laws over an arbitrary commutative ring
`R` of weights. The laws are polynomial identities in `p` and `w`: none needs `p ∈ (0, 1]`, and the
rational retention of the record is the instance `R = ℚ`. No floating point enters.

[definition] **Consumers.** The record
`research/records/2026-10-08_A_KEY_IS_LOCATED_WHERE_ITS_RECEIPTS_RESONATE_AND_A_SECRET_IS_DORMANT_TO_ITS_RECEIVERS.md`:
§2 (the moment law, the receiver's clock and transport, the circle through the landmark `1`), §3
(the trace likelihood counts embeddings, and the covector on a relaxed key), §6 items 1 and 2 (the
native deletion receiver and the trace-likelihood passage, whose formal part this is). Issue #62:
the moment law and the composition `T_{p₁} ∘ T_{p₂} = T_{p₁ p₂}`. The atlas rows
`receiver.deletion-trace-moment` and `receiver.deletion-trace-likelihood`
(`docs/atlas/information.tsv`).

[definition] **The object, and what is not built.** `channel p x` is the receiver's exact law: one
`(weight, trace)` entry per deletion pattern, the finite sum that states the expectation. It is the
statement of the law, never a retained record: nothing here replays, enumerates or stores patterns
at run time, and the native receiver will realize the law through its moment (`expect_genPoly`) and
its clock transport (`transport`), not through the list. This module is not a decoder and contains
no reconstruction algorithm. The native receiver, the machine's own pair passage for the
likelihood, and the learned reconstruction come later, each with its own consumer.

[proved-derived; formal-checked] The eight laws, each with its hypotheses.
1. *The two-case recursion* (§1). The head of the word survives with weight `p` and leads the trace,
   or is deleted with weight `1 − p`: `expect_cons`. Expectation is linear (`expect_add`,
   `expect_const_mul`), and the mass is one (`expect_one`), with no hypothesis on `p`. Retaining
   everything is the identity (`expect_retain_all`, `p = 1`) and deleting everything is the empty
   trace (`expect_delete_all`, `p = 0`).
2. *The clock law* (§2). The trace index counts survivors: it is the receiver's epoch count, the
   flux through its section, not the source's tick. The survivor count is binomial,
   `E[w^{|Y|}] = T_p(w)^n` (`expect_pow_length`), with `T_p(w) = 1 + p (w − 1) = (1 − p) + p w`
   (`transport`, `transport_eq`).
3. *The moment law* (§3, owed in #62). With the generating polynomial `P_y(z) = Σ_j φ(y_j) z^j` in
   Horner form (`genPoly`; its meaning is pinned by `genPoly_singleton` and `genPoly_append`, the
   weight `z^j` of position `j`), `E[P_Y(w)] = p · P_x(T_p(w))` (`expect_genPoly`).
4. *The mean-receipt difference* (§3). Two sources differ in mean receipt by
   `p · (P_x − P_{x'})(T_p(w))` (`mean_receipt_difference`).
5. *The transports compose* (§2, owed in #62). `T_{p₁}(T_{p₂}(w)) = T_{p₁ p₂}(w)`
   (`transport_comp`, as maps `transport_comp_fun`), `T_p(1) = 1`, the landmark (`transport_one`),
   `T_p(w) − (1 − p) = p w` (`transport_sub_one_sub`), and in a normed field
   `‖T_p(w) − (1 − p)‖ = ‖p‖ ‖w‖` (`norm_transport_sub`): the unit circle goes to the circle of
   centre `1 − p` and radius `‖p‖` (`norm_transport_sub_of_norm_one`), through `1`
   (`transport_landmark_on_circle`). `p = 1` is the identity and `p = 0` is the constant landmark
   (`transport_one_left`, `transport_zero`).
6. *The receivers compose as channels* (§4). For every reading `f`,
   `expect p₂ x (fun y => expect p₁ y f) = expect (p₁ p₂) x f` (`expect_expect`): the deletion
   receivers are a one-parameter flow, with identity `p = 1` and zero `p = 0`. Its moment shadow:
   a cascade read stage by stage through `T_{p₂} ∘ T_{p₁}` and read at once through `T_{p₁ p₂}`
   agree (`cascade_moment_stagewise`, `cascade_moment`, `moment_shadow`).
7. *The likelihood counts embeddings* (§5, `[DecidableEq α]`). With the embedding count
   `embeddings x y` (the number of index sets `I` with `x_I = y`, by its recursion),
   `Pr[Y = y | x] = p^{|y|} (1 − p)^{n − |y|} N(x, y)` (`expect_trace`), the subtraction being the
   natural one: a trace longer than its source has count zero (`embeddings_eq_zero_of_length_lt`)
   and probability zero (`expect_trace_of_length_lt`). The weight depends on the pattern only
   through `|y|` and `n`, so two sources of one length compare through their counts alone
   (`trace_likelihood_cross`).
8. *The relaxed covector, algebraically* (§6). For `s` with `Σ_b s_b = 1` and
   `Ñ = A + Σ_b s_b B_b`, with `r_b = s_b B_b / Ñ` and `ρ = Σ_b r_b`:
   `(Σ_b s_b (δ_ab − s_a) B_b) / Ñ = r_a − ρ s_a` (`covector_column`) and
   `Σ_a (r_a − ρ s_a) = 0` (`covector_sum_zero`). The term `s_b (δ_ab − s_a)` is the column `a` of
   the softmax Jacobian, the standard derivative `∂ s_b / ∂ λ_a`, which is not formalized here. For
   `Ñ` affine in the soft constituent `s = softmax(λ)` (`∂Ñ/∂s_b = B_b`), the left side is
   `∂ log Ñ / ∂ λ(a)`, and the identity says it is the surviving posterior mass `r_a` less the
   predicted mass `ρ s_a`. The role of `Ñ ≠ 0` is stated by `survival_eq_one_sub`: the survival
   posterior is `ρ = 1 − A / Ñ`, one less the posterior of the paths that delete the position.

[agent-inferred] The choices, with their reasons.
- `channel` and `expect` are the suggested definitions, unchanged: the receiver stays the explicit
  finite sum, and every law below is derived from the two-case recursion `expect_cons` and the base
  case `expect_nil`, so no proof unfolds a list sum again. `expect_cons` itself unfolds it once
  (`sum_map_scale`).
- `genPoly` is Horner's form, the recursion the moment law inducts on. It is pinned to the sum
  `Σ_j φ(y_j) z^j` by `genPoly_singleton` and `genPoly_append` (a concatenation shifts its second
  part by `z^{|y|}`), which determine it.
- `embeddings` is defined by four exhaustive constructor cases, so that the three equations of its
  specification (`embeddings x [] = 1`, `embeddings [] (b :: y) = 0`, the diagonal-or-skip step)
  are theorems (`embeddings_nil_right`, `embeddings_nil_cons`, `embeddings_cons_cons`).
- The covector section names its three quantities (`normalizer`, `posterior`, `survival`) so that
  the statements read as the record's. The two identities of law 8 hold for the formal inverse; the
  hypothesis `Ñ ≠ 0` enters where the log does, in `survival_eq_one_sub`.
- The arithmetic of the likelihood induction is isolated in `trace_step`, `trace_step_nil` and
  `weight_empty`, over plain variables (the lengths are natural-number variables there), so no
  proof mixes list lengths with ring identities.
- Where a closer depends on the exact form of a rewrite or of a `simp` normal form, the proof
  carries a second path (`first | … | …`), as `Transport/HelicalRepair` does: this file was written
  without a compiler. After the kernel receipt, the unused-tactic linter names the dead
  alternatives, and they are deleted.

[open] Not claimed here, with what each needs.
- **Tangency** of the image circle to the unit circle at `1`: it is the geometry of two circles
  (the intersection is the single point `1`) and needs a complex-number lemma beyond the norm
  identity proved.
- **The Borwein–Erdélyi arc bound**, the `exp(Θ(n^{1/3}))` trace counts, the multi-symbol
  statistics, Fourier flatness (the quantitative pole of the dormancy statement, owed in #62).
- **The identification of `embeddings` with the number of index sets `I` with `x_I = y`** (the count
  of `y` among the sublists of `x`): the recursion is its definition here, as the record reads it,
  and the bijection of deletion patterns with index sets is not a separate theorem.
- **The softmax Jacobian** (the derivative) and **the forward–backward passage** over the alignment
  lattice as the machine's own pair-contact passage and its adjoint.
- **The native receiver** (its clock, its transport, the moment law at its consumer), **the learned
  reconstruction**, and **the acceptance** (exact recovery on unseen sources against the number of
  traces, beside the mean-based count).

[agent-inferred] Recorded failures checked. A parallel subsystem nothing consumes: the consumers are
named above. An authored routine standing in for learning: this is the receiver's law, and no
decoder or search is written. A refusal answered with a larger limit: no limit is set or raised.
Text run as the exception: `α` is an arbitrary type. A design thought in arrays and offsets: the
laws are stated in the receiver's clock (survivor epochs), its boost toward the landmark `1`, and
the phase-carried moment; the list is only the carrier of the word.

Written without a compiler: the `formal-checked` tag on each statement stands once the validation
queue's kernel receipt exists.

[established-bounded; formal-checked] Scope: finite lists, finite sums, a commutative ring of
weights (a normed field for the circle, a field for the covector). No float, no `axiom`, no `sorry`,
no `native_decide`, no raised limit.
-/

namespace Holonics.Transport.DeletionReceiver

/-! ## 1. The receiver and its two-case recursion -/

section Receiver

variable {α R : Type*} [CommRing R]

/-- [definition] **The deletion receiver's exact law**: one `(weight, trace)` entry per deletion
pattern of the word. The head survives with weight `p` (and leads the trace) or is deleted with
weight `1 − p`. The list is the finite sum that states the law (`2^n` entries for a word of length
`n`), not a retained record. -/
def channel (p : R) : List α → List (R × List α)
  | [] => [(1, [])]
  | a :: x => (channel p x).map (fun e => (p * e.1, a :: e.2)) ++
      (channel p x).map (fun e => ((1 - p) * e.1, e.2))

/-- [proved-derived; formal-checked] The empty word has one pattern, with weight one and the empty
trace. -/
theorem channel_nil (p : R) : channel p ([] : List α) = [((1 : R), ([] : List α))] := by
  first
    | rfl
    | simp [channel]

/-- [proved-derived; formal-checked] The patterns of `a :: x`: those where the head survives
(weight `p`, the head leads the trace), then those where it is deleted (weight `1 − p`). -/
theorem channel_cons (p : R) (a : α) (x : List α) :
    channel p (a :: x) = (channel p x).map (fun e => (p * e.1, a :: e.2)) ++
      (channel p x).map (fun e => ((1 - p) * e.1, e.2)) := by
  first
    | rfl
    | simp [channel]

/-- [definition] **The receiver's exact expectation** of a reading `f` of its trace: the sum over
the deletion patterns of the weight times `f` of the trace. -/
def expect (p : R) (x : List α) (f : List α → R) : R :=
  ((channel p x).map (fun e => e.1 * f e.2)).sum

/-- [proved-derived; formal-checked] **A reweighting scales a weighted sum**: if the reading
`G (g b)` of the reweighted entry is `c` times the reading `K b` of the entry, the weighted sum of
the reweighted list is `c` times the weighted sum of the list. With `expect_nil`, the only place
a list sum is unfolded; `expect_cons` is its consumer. -/
theorem sum_map_scale {β γ : Type*} (c : R) (L : List β) (g : β → γ) (G : γ → R) (K : β → R)
    (hK : ∀ b, G (g b) = c * K b) :
    ((L.map g).map G).sum = c * (L.map K).sum := by
  induction L with
  | nil => first | (simp only [List.map_nil, List.sum_nil, mul_zero]; done) | (simp; done)
  | cons b L ih =>
    first
      | (simp only [List.map_cons, List.sum_cons, hK b, ih]; ring1)
      | (simp [hK b, ih, mul_add]; done)

/-- [proved-derived; formal-checked] **The empty word reads its own trace**: the only pattern
returns the empty trace with weight one. -/
theorem expect_nil (p : R) (f : List α → R) : expect p [] f = f [] := by
  show (List.map (fun e : R × List α => e.1 * f e.2) (channel p [])).sum = f []
  rw [channel_nil]
  first
    | (simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero]; done)
    | (simp; done)

/-- [proved-derived; formal-checked] **The two-case recursion of the receiver** (law 1): the head
of the word survives with weight `p` and leads the trace, or is deleted with weight `1 − p`. Every
other law of this module is derived from this and `expect_nil`. -/
theorem expect_cons (p : R) (a : α) (x : List α) (f : List α → R) :
    expect p (a :: x) f = p * expect p x (fun y => f (a :: y)) + (1 - p) * expect p x f := by
  have h1 := sum_map_scale p (channel p x) (fun e : R × List α => (p * e.1, a :: e.2))
    (fun e : R × List α => e.1 * f e.2) (fun e : R × List α => e.1 * f (a :: e.2))
    (fun e : R × List α => mul_assoc p e.1 (f (a :: e.2)))
  have h2 := sum_map_scale (1 - p) (channel p x)
    (fun e : R × List α => ((1 - p) * e.1, e.2))
    (fun e : R × List α => e.1 * f e.2) (fun e : R × List α => e.1 * f e.2)
    (fun e : R × List α => mul_assoc (1 - p) e.1 (f e.2))
  have h3 : expect p (a :: x) f =
      (((channel p x).map (fun e : R × List α => (p * e.1, a :: e.2))).map
        (fun e : R × List α => e.1 * f e.2)).sum +
      (((channel p x).map (fun e : R × List α => ((1 - p) * e.1, e.2))).map
        (fun e : R × List α => e.1 * f e.2)).sum := by
    show (List.map (fun e : R × List α => e.1 * f e.2) (channel p (a :: x))).sum = _
    first
      | (rw [channel_cons, List.map_append, List.sum_append]; done)
      | (simp only [channel_cons, List.map_append, List.sum_append]; done)
  have h4 : expect p x (fun y => f (a :: y)) =
      ((channel p x).map (fun e : R × List α => e.1 * f (a :: e.2))).sum := rfl
  have h5 : expect p x f = ((channel p x).map (fun e : R × List α => e.1 * f e.2)).sum := rfl
  linear_combination h3 + h1 + h2 - p * h4 - (1 - p) * h5

/-- [proved-derived; formal-checked] Readings that agree on every trace have the same expectation. -/
theorem expect_congr (p : R) (x : List α) {f g : List α → R} (h : ∀ y, f y = g y) :
    expect p x f = expect p x g :=
  congrArg (expect p x) (funext h)

/-- [proved-derived; formal-checked] **A constant reading has that constant as expectation**, for
every `p`: the weights of the deletion patterns sum to one as polynomials, `p + (1 − p) = 1`. -/
theorem expect_const (p : R) (x : List α) (c : R) : expect p x (fun _ => c) = c := by
  induction x with
  | nil => exact expect_nil p (fun _ => c)
  | cons a x ih =>
    have e1 : expect p (a :: x) (fun _ => c)
        = p * expect p x (fun _ => c) + (1 - p) * expect p x (fun _ => c) :=
      expect_cons p a x (fun _ => c)
    linear_combination e1 + ih

/-- [proved-derived; formal-checked] **The mass law** (law 1): the total weight of the deletion
patterns is one, `expect p x (fun _ => 1) = 1`, with no hypothesis on `p`. -/
theorem expect_one (p : R) (x : List α) : expect p x (fun _ => (1 : R)) = 1 :=
  expect_const p x 1

/-- [proved-derived; formal-checked] **Additivity of the expectation** (law 1). -/
theorem expect_add (p : R) (x : List α) :
    ∀ (f g : List α → R), expect p x (fun y => f y + g y) = expect p x f + expect p x g := by
  induction x with
  | nil =>
    intro f g
    simp only [expect_nil]
  | cons a x ih =>
    intro f g
    have e1 : expect p (a :: x) (fun y => f y + g y)
        = p * expect p x (fun y => f (a :: y) + g (a :: y))
          + (1 - p) * expect p x (fun y => f y + g y) :=
      expect_cons p a x _
    have e2 := expect_cons p a x f
    have e3 := expect_cons p a x g
    have e4 := ih (fun y => f (a :: y)) (fun y => g (a :: y))
    have e5 := ih f g
    linear_combination e1 - e2 - e3 + p * e4 + (1 - p) * e5

/-- [proved-derived; formal-checked] **A constant factor passes through the expectation**
(law 1). -/
theorem expect_const_mul (p : R) (x : List α) (c : R) :
    ∀ (f : List α → R), expect p x (fun y => c * f y) = c * expect p x f := by
  induction x with
  | nil =>
    intro f
    simp only [expect_nil]
  | cons a x ih =>
    intro f
    have e1 : expect p (a :: x) (fun y => c * f y)
        = p * expect p x (fun y => c * f (a :: y)) + (1 - p) * expect p x (fun y => c * f y) :=
      expect_cons p a x _
    have e2 := expect_cons p a x f
    have e3 := ih (fun y => f (a :: y))
    have e4 := ih f
    linear_combination e1 - c * e2 + p * e3 + (1 - p) * e4

/-- [proved-derived; formal-checked] **Retaining everything is the identity receiver**: at `p = 1`
the only weighted pattern is the whole word, `expect 1 x f = f x`. -/
theorem expect_retain_all (x : List α) : ∀ (f : List α → R), expect (1 : R) x f = f x := by
  induction x with
  | nil =>
    intro f
    simp only [expect_nil]
  | cons a x ih =>
    intro f
    have e1 := expect_cons (1 : R) a x f
    have e2 := ih (fun y => f (a :: y))
    linear_combination e1 + e2

/-- [proved-derived; formal-checked] **Deleting everything returns the empty trace**: at `p = 0`
the only weighted pattern deletes every position, `expect 0 x f = f []`. -/
theorem expect_delete_all (x : List α) : ∀ (f : List α → R), expect (0 : R) x f = f [] := by
  induction x with
  | nil =>
    intro f
    simp only [expect_nil]
  | cons a x ih =>
    intro f
    have e1 := expect_cons (0 : R) a x f
    have e2 := ih f
    linear_combination e1 + e2

end Receiver

/-! ## 2. The receiver's clock and its transport -/

section Clock

variable {α R : Type*} [CommRing R]

/-- [definition] **The receiver's transport**, the boost toward the landmark `1`: the homothety of
ratio `p` about the fixed point `1`, `T_p(w) = 1 + p (w − 1)`. -/
def transport (p w : R) : R := 1 + p * (w - 1)

/-- [proved-derived; formal-checked] The transport in the record's chart, `T_p(w) = q + p w` with
`q = 1 − p`. -/
theorem transport_eq (p w : R) : transport p w = (1 - p) + p * w := by
  unfold transport
  ring

/-- [proved-derived; formal-checked] **The landmark is fixed** (law 5): every deletion receiver's
transport fixes `1`, the face where all the receivers' paths converge. -/
theorem transport_one (p : R) : transport p 1 = 1 := by
  unfold transport
  ring

/-- [proved-derived; formal-checked] Retaining everything transports nothing: `T_1 = id`. -/
theorem transport_one_left (w : R) : transport 1 w = w := by
  unfold transport
  ring

/-- [proved-derived; formal-checked] Deleting everything transports every point to the landmark:
`T_0 = 1`. -/
theorem transport_zero (w : R) : transport 0 w = 1 := by
  unfold transport
  ring

/-- [proved-derived; formal-checked] **The image sits at a distance `p w` from `1 − p`** (law 5):
`T_p(w) − (1 − p) = p w`. With `‖·‖` this is the circle of centre `1 − p` and radius `‖p‖`
(`norm_transport_sub`). -/
theorem transport_sub_one_sub (p w : R) : transport p w - (1 - p) = p * w := by
  unfold transport
  ring

/-- [proved-derived; formal-checked] **The transports compose by multiplying retentions** (law 5,
owed in #62): `T_{p₁} ∘ T_{p₂} = T_{p₁ p₂}`, the one-parameter boost flow. -/
theorem transport_comp (p₁ p₂ w : R) :
    transport p₁ (transport p₂ w) = transport (p₁ * p₂) w := by
  unfold transport
  ring

/-- [proved-derived; formal-checked] The same law as an equation of maps, in the record's notation
(law 5): `T_{p₁} ∘ T_{p₂} = T_{p₁ p₂}`. -/
theorem transport_comp_fun (p₁ p₂ : R) :
    transport p₁ ∘ transport p₂ = transport (p₁ * p₂) := by
  funext w
  first
    | exact transport_comp p₁ p₂ w
    | (simp only [Function.comp_apply]; exact transport_comp p₁ p₂ w)

/-- [proved-derived; formal-checked] A word's survivor weight: `w^{|a :: y|} = w · w^{|y|}`. -/
theorem pow_length_cons (w : R) (a : α) (y : List α) :
    w ^ (a :: y).length = w * w ^ y.length := by
  first
    | exact pow_succ' w y.length
    | (rw [List.length_cons]; ring)

/-- [proved-derived; formal-checked] **The clock law** (law 2): the trace index counts survivors,
and the survivor count is binomial, `E[w^{|Y|}] = T_p(w)^n` for a word of length `n`. The receiver
runs in its own clock: the epochs through its section are the survivors, not the source's ticks. -/
theorem expect_pow_length (p w : R) (x : List α) :
    expect p x (fun y => w ^ y.length) = transport p w ^ x.length := by
  induction x with
  | nil => simp only [expect_nil, List.length_nil, pow_zero]
  | cons a x ih =>
    have e1 : expect p (a :: x) (fun y => w ^ y.length)
        = p * expect p x (fun y => w ^ (a :: y).length)
          + (1 - p) * expect p x (fun y => w ^ y.length) :=
      expect_cons p a x _
    have e2 : expect p x (fun y => w ^ (a :: y).length)
        = w * expect p x (fun y => w ^ y.length) := by
      calc expect p x (fun y => w ^ (a :: y).length)
          = expect p x (fun y => w * w ^ y.length) :=
            expect_congr p x (fun y => pow_length_cons w a y)
        _ = w * expect p x (fun y => w ^ y.length) :=
            expect_const_mul p x w (fun y => w ^ y.length)
    have hlen : (a :: x).length = x.length + 1 := List.length_cons
    have hT : transport p w = 1 + p * (w - 1) := rfl
    rw [hlen]
    linear_combination e1 + p * e2 + (p * w + (1 - p)) * ih - (transport p w ^ x.length) * hT

end Clock

section Circle

variable {K : Type*} [NormedField K]

/-- [proved-derived; formal-checked] **The image circle's radius** (law 5): in a normed field,
`‖T_p(w) − (1 − p)‖ = ‖p‖ ‖w‖`. -/
theorem norm_transport_sub (p w : K) : ‖transport p w - (1 - p)‖ = ‖p‖ * ‖w‖ := by
  first
    | (rw [transport_sub_one_sub, norm_mul]; done)
    | (rw [transport_sub_one_sub]; exact norm_mul p w)

/-- [proved-derived; formal-checked] **The unit circle goes to the circle of centre `1 − p` and
radius `‖p‖`** (law 5): every `w` with `‖w‖ = 1` is sent to a point at distance `‖p‖` from `1 − p`.
That it passes through the landmark `1` is `transport_landmark_on_circle`. -/
theorem norm_transport_sub_of_norm_one (p w : K) (hw : ‖w‖ = 1) :
    ‖transport p w - (1 - p)‖ = ‖p‖ := by
  rw [norm_transport_sub, hw, mul_one]

/-- [proved-derived; formal-checked] **The image circle passes through the landmark** (law 5): the
point `1` of the unit circle is fixed by every transport (`transport_one`), and it lies on the image
circle, `‖T_p(1) − (1 − p)‖ = ‖p‖`. -/
theorem transport_landmark_on_circle (p : K) : ‖transport p 1 - (1 - p)‖ = ‖p‖ := by
  first
    | exact norm_transport_sub_of_norm_one p 1 norm_one
    | exact norm_transport_sub_of_norm_one p 1 (by simp)

end Circle

/-! ## 3. The moment law and the mean receipt -/

section Moment

variable {α R : Type*} [CommRing R]

/-- [definition] **The generating polynomial of a word**, `P_y(z) = Σ_j φ(y_j) z^j`, in Horner form:
`P_{a :: y}(z) = φ(a) + z P_y(z)`. The reading `φ : α → R` is the alphabet's value in the ring of
weights; the exponent `j` is the position, the phase the receiver's clock is read against. -/
def genPoly (φ : α → R) : List α → R → R
  | [], _ => 0
  | a :: y, z => φ a + z * genPoly φ y z

/-- [proved-derived; formal-checked] The empty word has the zero polynomial. -/
theorem genPoly_nil (φ : α → R) (z : R) : genPoly φ [] z = 0 := by
  first
    | rfl
    | simp [genPoly]

/-- [proved-derived; formal-checked] Horner's step. -/
theorem genPoly_cons (φ : α → R) (a : α) (y : List α) (z : R) :
    genPoly φ (a :: y) z = φ a + z * genPoly φ y z := by
  first
    | rfl
    | simp [genPoly]

/-- [proved-derived; formal-checked] A one-letter word has the constant polynomial `φ(a)`: position
zero carries weight `z^0`. -/
theorem genPoly_singleton (φ : α → R) (a : α) (z : R) : genPoly φ [a] z = φ a := by
  rw [genPoly_cons, genPoly_nil, mul_zero, add_zero]

/-- [proved-derived; formal-checked] **A concatenation shifts its second part**: position `j` of
the second word is position `|y| + j` of the whole, so `P_{y ++ y'}(z) = P_y(z) + z^{|y|} P_{y'}(z)`.
Together with `genPoly_singleton` this is the sum `Σ_j φ(y_j) z^j`. -/
theorem genPoly_append (φ : α → R) (z : R) :
    ∀ (y y' : List α), genPoly φ (y ++ y') z = genPoly φ y z + z ^ y.length * genPoly φ y' z
  | [], y' => by
    first
      | (rw [List.nil_append, genPoly_nil, List.length_nil, pow_zero]; ring1)
      | (simp [genPoly_nil]; done)
  | a :: y, y' => by
    first
      | (rw [List.cons_append, genPoly_cons, genPoly_cons, genPoly_append φ z y y',
          List.length_cons]; ring1)
      | (simp only [List.cons_append, genPoly_cons, genPoly_append φ z y y', List.length_cons]; ring)

/-- [proved-derived; formal-checked] **The moment law** (law 3, owed in #62): the receiver's
expectation of the trace's generating polynomial is `p` times the source's, read through the
transport, `E[P_Y(w)] = p · P_x(T_p(w))`. -/
theorem expect_genPoly (φ : α → R) (p w : R) (x : List α) :
    expect p x (fun y => genPoly φ y w) = p * genPoly φ x (transport p w) := by
  induction x with
  | nil => simp only [expect_nil, genPoly_nil, mul_zero]
  | cons a x ih =>
    have e1 : expect p (a :: x) (fun y => genPoly φ y w)
        = p * expect p x (fun y => genPoly φ (a :: y) w)
          + (1 - p) * expect p x (fun y => genPoly φ y w) :=
      expect_cons p a x _
    have e2 : expect p x (fun y => genPoly φ (a :: y) w)
        = φ a + w * expect p x (fun y => genPoly φ y w) := by
      calc expect p x (fun y => genPoly φ (a :: y) w)
          = expect p x (fun y => φ a + w * genPoly φ y w) :=
            expect_congr p x (fun y => genPoly_cons φ a y w)
        _ = expect p x (fun _ => φ a) + expect p x (fun y => w * genPoly φ y w) :=
            expect_add p x (fun _ => φ a) (fun y => w * genPoly φ y w)
        _ = φ a + w * expect p x (fun y => genPoly φ y w) := by
            rw [expect_const p x (φ a), expect_const_mul p x w (fun y => genPoly φ y w)]
    have hG : genPoly φ (a :: x) (transport p w)
        = φ a + transport p w * genPoly φ x (transport p w) :=
      genPoly_cons φ a x (transport p w)
    have hT : transport p w = 1 + p * (w - 1) := rfl
    rw [hG]
    linear_combination e1 + p * e2 + (p * w + (1 - p)) * ih -
      (p * genPoly φ x (transport p w)) * hT

/-- [proved-derived; formal-checked] **The mean-receipt difference** (law 4): two sources differ in
mean receipt by `p` times the difference of their polynomials at the transported point,
`E[P_Y(w)] − E[P_{Y'}(w)] = p · (P_x(T_p(w)) − P_{x'}(T_p(w)))`. The two sources are separated only
where the difference of their polynomials is not silent at `T_p(w)`. -/
theorem mean_receipt_difference (φ : α → R) (p w : R) (x x' : List α) :
    expect p x (fun y => genPoly φ y w) - expect p x' (fun y => genPoly φ y w)
      = p * (genPoly φ x (transport p w) - genPoly φ x' (transport p w)) := by
  linear_combination (expect_genPoly φ p w x) - (expect_genPoly φ p w x')

end Moment

/-! ## 4. The receivers compose as channels -/

section Flow

variable {α R : Type*} [CommRing R]

/-- [proved-derived; formal-checked] **The receivers compose as channels** (law 6, owed in #62): a
word read by `D_{p₂}` and its trace read by `D_{p₁}` is the word read by `D_{p₁ p₂}`, for every
reading `f` of the final trace. The weights close because
`p₂ (1 − p₁) + (1 − p₂) = 1 − p₁ p₂`. The deletion receivers form a one-parameter flow, with
identity `D_1` (`expect_retain_all`) and zero `D_0` (`expect_delete_all`); `transport_comp` is its
moment shadow (`moment_shadow`). -/
theorem expect_expect (p₁ p₂ : R) (x : List α) :
    ∀ (f : List α → R), expect p₂ x (fun y => expect p₁ y f) = expect (p₁ * p₂) x f := by
  induction x with
  | nil =>
    intro f
    simp only [expect_nil]
  | cons a x ih =>
    intro f
    have e1 : expect p₂ (a :: x) (fun y => expect p₁ y f)
        = p₂ * expect p₂ x (fun y => expect p₁ (a :: y) f)
          + (1 - p₂) * expect p₂ x (fun y => expect p₁ y f) :=
      expect_cons p₂ a x _
    have e2 : expect p₂ x (fun y => expect p₁ (a :: y) f)
        = p₁ * expect p₂ x (fun y => expect p₁ y (fun z => f (a :: z)))
          + (1 - p₁) * expect p₂ x (fun y => expect p₁ y f) := by
      calc expect p₂ x (fun y => expect p₁ (a :: y) f)
          = expect p₂ x (fun y => p₁ * expect p₁ y (fun z => f (a :: z))
              + (1 - p₁) * expect p₁ y f) :=
            expect_congr p₂ x (fun y => expect_cons p₁ a y f)
        _ = expect p₂ x (fun y => p₁ * expect p₁ y (fun z => f (a :: z)))
              + expect p₂ x (fun y => (1 - p₁) * expect p₁ y f) :=
            expect_add p₂ x (fun y => p₁ * expect p₁ y (fun z => f (a :: z)))
              (fun y => (1 - p₁) * expect p₁ y f)
        _ = p₁ * expect p₂ x (fun y => expect p₁ y (fun z => f (a :: z)))
              + (1 - p₁) * expect p₂ x (fun y => expect p₁ y f) := by
            have c1 := expect_const_mul p₂ x p₁ (fun y => expect p₁ y (fun z => f (a :: z)))
            have c2 := expect_const_mul p₂ x (1 - p₁) (fun y => expect p₁ y f)
            linear_combination c1 + c2
    have e3 := ih (fun z => f (a :: z))
    have e4 := ih f
    have e5 := expect_cons (p₁ * p₂) a x f
    linear_combination e1 + p₂ * e2 + p₂ * p₁ * e3 + (p₂ * (1 - p₁) + (1 - p₂)) * e4 - e5

/-- [proved-derived; formal-checked] **A cascade of two receivers is read through the composite
transport** (laws 6 and 3): `E[ E[ P_Z(w) | Y ] ]` over the cascade `D_{p₁}` then `D_{p₂}` is
`p₁ p₂ · P_x(T_{p₁ p₂}(w))`. -/
theorem cascade_moment (φ : α → R) (p₁ p₂ w : R) (x : List α) :
    expect p₂ x (fun y => expect p₁ y (fun z => genPoly φ z w))
      = (p₁ * p₂) * genPoly φ x (transport (p₁ * p₂) w) :=
  (expect_expect p₁ p₂ x (fun z => genPoly φ z w)).trans (expect_genPoly φ (p₁ * p₂) w x)

/-- [proved-derived; formal-checked] **The same cascade read stage by stage** (law 3 twice): the
inner receiver reads through `T_{p₁}`, the outer through `T_{p₂}` at the transported point. -/
theorem cascade_moment_stagewise (φ : α → R) (p₁ p₂ w : R) (x : List α) :
    expect p₂ x (fun y => expect p₁ y (fun z => genPoly φ z w))
      = p₁ * (p₂ * genPoly φ x (transport p₂ (transport p₁ w))) := by
  calc expect p₂ x (fun y => expect p₁ y (fun z => genPoly φ z w))
      = expect p₂ x (fun y => p₁ * genPoly φ y (transport p₁ w)) :=
        expect_congr p₂ x (fun y => expect_genPoly φ p₁ w y)
    _ = p₁ * expect p₂ x (fun y => genPoly φ y (transport p₁ w)) :=
        expect_const_mul p₂ x p₁ (fun y => genPoly φ y (transport p₁ w))
    _ = p₁ * (p₂ * genPoly φ x (transport p₂ (transport p₁ w))) := by
        rw [expect_genPoly φ p₂ (transport p₁ w) x]

/-- [proved-derived; formal-checked] **The transport law is the moment shadow of the channel law**
(laws 5 and 6): reading the cascade stage by stage through `T_{p₂} ∘ T_{p₁}` and at once through
`T_{p₁ p₂}` agree. Derived from the composition of the receivers and the moment law alone, not from
`transport_comp`. -/
theorem moment_shadow (φ : α → R) (p₁ p₂ w : R) (x : List α) :
    p₁ * (p₂ * genPoly φ x (transport p₂ (transport p₁ w)))
      = (p₁ * p₂) * genPoly φ x (transport (p₁ * p₂) w) :=
  (cascade_moment_stagewise φ p₁ p₂ w x).symm.trans (cascade_moment φ p₁ p₂ w x)

end Flow

/-! ## 5. The likelihood counts embeddings -/

section EmptyWeight

variable {α R : Type*} [CommRing R]

/-- [proved-derived; formal-checked] **The weight of the empty trace**: the pattern that deletes
every position of a word of length `n` has weight `p^0 (1 − p)^{n − 0} = (1 − p)^n`, times the
embedding count `e = 1` of the empty trace. Stated over plain variables, so that the likelihood
induction does not normalise `[].length` inside a larger goal. -/
theorem weight_empty (p : R) (n e : ℕ) (he : e = 1) :
    p ^ ([] : List α).length * (1 - p) ^ (n - ([] : List α).length) * (e : R) = (1 - p) ^ n := by
  subst he
  simp only [List.length_nil, Nat.sub_zero, pow_zero, Nat.cast_one, one_mul, mul_one]

end EmptyWeight

section Likelihood

variable {α R : Type*} [CommRing R] [DecidableEq α]

/-- [definition] **The embedding count** `N(x, y)`: the number of index sets `I` of the source `x`
with `x_I = y`, by its recursion over the alignment lattice. Every word embeds the empty trace once
(`embeddings_nil_right`); the empty word embeds no longer trace (`embeddings_nil_cons`); in
`a :: x` against `b :: y`, the head is skipped (`embeddings x (b :: y)`) or, where the symbols
agree, matched (`embeddings x y`) (`embeddings_cons_cons`). -/
def embeddings : List α → List α → ℕ
  | [], [] => 1
  | [], _ :: _ => 0
  | _ :: _, [] => 1
  | a :: x, b :: y => embeddings x (b :: y) + (if a = b then embeddings x y else 0)

/-- [proved-derived; formal-checked] Every word embeds the empty trace exactly once: the pattern
that deletes everything. -/
theorem embeddings_nil_right (x : List α) : embeddings x [] = 1 := by
  cases x with
  | nil => first | rfl | simp [embeddings]
  | cons a x => first | rfl | simp [embeddings]

/-- [proved-derived; formal-checked] The empty word embeds no nonempty trace. -/
theorem embeddings_nil_cons (b : α) (y : List α) : embeddings [] (b :: y) = 0 := by
  first
    | rfl
    | simp [embeddings]

/-- [proved-derived; formal-checked] **The recursion of the alignment lattice**: a diagonal step is
allowed only where the symbols agree. -/
theorem embeddings_cons_cons (a b : α) (x y : List α) :
    embeddings (a :: x) (b :: y)
      = embeddings x (b :: y) + (if a = b then embeddings x y else 0) := by
  first
    | rfl
    | simp [embeddings]

/-- [proved-derived; formal-checked] **A trace longer than its source has no embedding**: the
natural-number subtraction of the likelihood is honest only because of this. -/
theorem embeddings_eq_zero_of_length_lt :
    ∀ (x y : List α), x.length < y.length → embeddings x y = 0
  | [], [], h => by
    first
      | (simp at h; done)
      | exact absurd h (Nat.lt_irrefl _)
  | [], b :: y, _ => embeddings_nil_cons b y
  | _ :: _, [], h => by
    first
      | (simp at h; done)
      | (simp only [List.length_cons, List.length_nil] at h; omega)
  | a :: x, b :: y, h => by
    have h1 : x.length < (b :: y).length := by
      simp only [List.length_cons] at h ⊢
      omega
    have h2 : x.length < y.length := by
      simp only [List.length_cons] at h
      omega
    rw [embeddings_cons_cons, embeddings_eq_zero_of_length_lt x (b :: y) h1,
      embeddings_eq_zero_of_length_lt x y h2]
    first
      | (simp; done)
      | (rw [ite_self, add_zero]; done)

/-- [proved-derived; formal-checked] The recursion of the embedding count in the ring of weights,
with the agreement of the symbols as a weight `c ∈ {0, 1}`. -/
theorem cast_embeddings_cons_cons (a b : α) (x y : List α) :
    ((embeddings (a :: x) (b :: y) : ℕ) : R)
      = (embeddings x (b :: y) : R) + (if a = b then (1 : R) else 0) * (embeddings x y : R) := by
  rw [embeddings_cons_cons, Nat.cast_add]
  by_cases hab : a = b
  · first
      | (rw [if_pos hab, if_pos hab, one_mul]; done)
      | (simp [hab]; done)
  · first
      | (rw [if_neg hab, if_neg hab, Nat.cast_zero, zero_mul]; done)
      | (simp [hab]; done)

/-- [proved-derived; formal-checked] The head of a trace in the indicator of a word: the indicator
of `{Y = b :: y}` at `a :: t` is the agreement of the heads times the indicator of `{Y = y}` at
`t`. -/
theorem ind_cons (a b : α) (t y : List α) :
    (if a :: t = b :: y then (1 : R) else 0)
      = (if a = b then (1 : R) else 0) * (if t = y then (1 : R) else 0) := by
  by_cases hab : a = b
  · by_cases hty : t = y
    · have hc : a :: t = b :: y := by rw [hab, hty]
      first
        | (rw [if_pos hc, if_pos hab, if_pos hty, one_mul]; done)
        | (simp [hab, hty]; done)
    · have hc : ¬ (a :: t = b :: y) := fun h => hty (List.cons.inj h).2
      first
        | (rw [if_neg hc, if_pos hab, if_neg hty, mul_zero]; done)
        | (simp [hab, hty]; done)
  · have hc : ¬ (a :: t = b :: y) := fun h => hab (List.cons.inj h).1
    first
      | (rw [if_neg hc, if_neg hab, zero_mul]; done)
      | (simp [hab]; done)

/-- [proved-derived; formal-checked] **The algebra of one step of the likelihood induction**, over
plain variables. `E1` is the likelihood of `b :: y` under `a :: x`, split by whether the head
survives (`E2`, the likelihood of `y` under `x`, scaled by the agreement `c` of the heads) or is
deleted (`E3`, the likelihood of `b :: y` under `x`). `lx` and `ly` are the lengths of `x` and `y`,
and `u`, `v` the embedding counts `N(x, b :: y)`, `N(x, y)`. The subtraction `lx − (ly + 1)` is the
natural one: when the trace `b :: y` is longer than `x`, `u = 0`. -/
theorem trace_step {p c E1 E2 E3 E4 u v emb : R} {lx ly : ℕ}
    (h1 : E1 = p * E2 + (1 - p) * E3) (h2 : E2 = c * E4)
    (hA : E4 = p ^ ly * (1 - p) ^ (lx - ly) * v)
    (hB : E3 = p ^ (ly + 1) * (1 - p) ^ (lx - (ly + 1)) * u)
    (hz : lx < ly + 1 → u = 0) (hemb : emb = u + c * v) :
    E1 = p ^ (ly + 1) * (1 - p) ^ (lx + 1 - (ly + 1)) * emb := by
  have hexp : lx + 1 - (ly + 1) = lx - ly := by omega
  rw [hexp]
  have hq : (1 - p) * (p ^ (ly + 1) * (1 - p) ^ (lx - (ly + 1)) * u)
      = p ^ (ly + 1) * (1 - p) ^ (lx - ly) * u := by
    by_cases hk : ly + 1 ≤ lx
    · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hk
      have h3 : lx - (ly + 1) = m := by omega
      have h4 : lx - ly = m + 1 := by omega
      rw [h3, h4]
      ring
    · have hu : u = 0 := hz (by omega)
      rw [hu]
      ring
  linear_combination h1 + p * h2 + p * c * hA + (1 - p) * hB + hq -
    (p ^ (ly + 1) * (1 - p) ^ (lx - ly)) * hemb

/-- [proved-derived; formal-checked] **The algebra of the step where the trace is empty**: the head
of the source survives only to a nonempty trace, so only the deletion branch remains. -/
theorem trace_step_nil {p E1 E2 E3 : R} {n : ℕ}
    (h1 : E1 = p * E2 + (1 - p) * E3) (h2 : E2 = 0) (h3 : E3 = (1 - p) ^ n) :
    E1 = (1 - p) ^ (n + 1) := by
  linear_combination h1 + p * h2 + (1 - p) * h3

/-- [proved-derived; formal-checked] **The likelihood counts embeddings** (law 7): for every word
`x` and trace `y`, over any commutative ring of weights,

`Pr[Y = y | x] = p^{|y|} (1 − p)^{n − |y|} N(x, y)`,

where `n = |x|`, the subtraction is the natural one, and `N = embeddings`. Each deletion pattern
returning `y` has exactly `|y|` survivors, so its weight depends only on `|y|` and `n`. -/
theorem expect_trace (p : R) (x y : List α) :
    expect p x (fun t => if t = y then (1 : R) else 0)
      = p ^ y.length * (1 - p) ^ (x.length - y.length) * (embeddings x y : R) := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil =>
      first
        | (simp [expect_nil, embeddings_nil_right]; done)
        | (rw [expect_nil, if_pos rfl, embeddings_nil_right]; simp only [List.length_nil, Nat.sub_self, pow_zero, Nat.cast_one, mul_one]; done)
    | cons b y =>
      first
        | (simp [expect_nil, embeddings_nil_cons]; done)
        | (rw [expect_nil, embeddings_nil_cons, Nat.cast_zero, mul_zero]; exact if_neg (List.cons_ne_nil b y).symm)
  | cons a x ih =>
    cases y with
    | nil =>
      have e1 : expect p (a :: x) (fun t => if t = ([] : List α) then (1 : R) else 0)
          = p * expect p x (fun t => if a :: t = ([] : List α) then (1 : R) else 0)
            + (1 - p) * expect p x (fun t => if t = ([] : List α) then (1 : R) else 0) :=
        expect_cons p a x _
      have h0 : expect p x (fun t => if a :: t = ([] : List α) then (1 : R) else 0) = 0 := by
        calc expect p x (fun t => if a :: t = ([] : List α) then (1 : R) else 0)
            = expect p x (fun _ => (0 : R)) :=
              expect_congr p x (fun t => if_neg (List.cons_ne_nil a t))
          _ = 0 := expect_const p x 0
      have ih0 : expect p x (fun t => if t = ([] : List α) then (1 : R) else 0)
          = (1 - p) ^ x.length := by
        rw [ih []]
        exact weight_empty p x.length _ (embeddings_nil_right x)
      have hr := weight_empty (α := α) p (a :: x).length _ (embeddings_nil_right (a :: x))
      exact (trace_step_nil e1 h0 ih0).trans hr.symm
    | cons b y =>
      have e1 : expect p (a :: x) (fun t => if t = b :: y then (1 : R) else 0)
          = p * expect p x (fun t => if a :: t = b :: y then (1 : R) else 0)
            + (1 - p) * expect p x (fun t => if t = b :: y then (1 : R) else 0) :=
        expect_cons p a x _
      have e2 : expect p x (fun t => if a :: t = b :: y then (1 : R) else 0)
          = (if a = b then (1 : R) else 0) *
            expect p x (fun t => if t = y then (1 : R) else 0) := by
        calc expect p x (fun t => if a :: t = b :: y then (1 : R) else 0)
            = expect p x (fun t => (if a = b then (1 : R) else 0) *
                (if t = y then (1 : R) else 0)) :=
              expect_congr p x (fun t => ind_cons a b t y)
          _ = (if a = b then (1 : R) else 0) *
                expect p x (fun t => if t = y then (1 : R) else 0) :=
              expect_const_mul p x (if a = b then (1 : R) else 0)
                (fun t => if t = y then (1 : R) else 0)
      have iha : expect p x (fun t => if t = y then (1 : R) else 0)
          = p ^ y.length * (1 - p) ^ (x.length - y.length) * (embeddings x y : R) :=
        ih y
      have ihb : expect p x (fun t => if t = b :: y then (1 : R) else 0)
          = p ^ (y.length + 1) * (1 - p) ^ (x.length - (y.length + 1))
            * (embeddings x (b :: y) : R) :=
        ih (b :: y)
      have hz : x.length < y.length + 1 → (embeddings x (b :: y) : R) = 0 := by
        intro h
        have hlt : x.length < (b :: y).length := h
        rw [embeddings_eq_zero_of_length_lt x (b :: y) hlt, Nat.cast_zero]
      have key := trace_step (lx := x.length) (ly := y.length) e1 e2 iha ihb hz
        (cast_embeddings_cons_cons (R := R) a b x y)
      first
        | exact key
        | simpa only [List.length_cons] using key

/-- [proved-derived; formal-checked] **A trace longer than its source has probability zero**
(law 7): the natural subtraction in the exponent is then truncated, and the embedding count
vanishes. -/
theorem expect_trace_of_length_lt (p : R) {x y : List α} (h : x.length < y.length) :
    expect p x (fun t => if t = y then (1 : R) else 0) = 0 := by
  rw [expect_trace, embeddings_eq_zero_of_length_lt x y h, Nat.cast_zero, mul_zero]

/-- [proved-derived; formal-checked] **Two sources of one length compare through their embedding
counts** (law 7): the weight `p^{|y|} (1 − p)^{n − |y|}` depends only on `|y|` and `n`, so the
likelihoods of `y` under `x` and `x'` are in the ratio of `N(x, y)` to `N(x', y)`, whatever `p`.
Stated by cross-multiplication, with no division. -/
theorem trace_likelihood_cross (p : R) {x x' : List α} (y : List α)
    (h : x.length = x'.length) :
    expect p x (fun t => if t = y then (1 : R) else 0) * (embeddings x' y : R)
      = expect p x' (fun t => if t = y then (1 : R) else 0) * (embeddings x y : R) := by
  have e1 := expect_trace p x y
  have e2 := expect_trace p x' y
  rw [e1, e2, h]
  ring

end Likelihood

/-! ## 6. The relaxed covector, algebraically -/

section Covector

variable {ι K : Type*} [Fintype ι] [Field K]

/-- [definition] **The relaxed count** `Ñ = A + Σ_b s_b B_b`, affine in the soft constituent
`s : ι → K`: `A` collects the paths that delete the position, and `B b` the paths that read the
class `b` there. -/
def normalizer (s : ι → K) (A : K) (B : ι → K) : K := A + ∑ b, s b * B b

/-- [definition] **The posterior mass** that the position survives and reads the class `b`,
`r_b = s_b B_b / Ñ`. -/
def posterior (s : ι → K) (A : K) (B : ι → K) (b : ι) : K := s b * B b / normalizer s A B

/-- [definition] **The survival posterior** `ρ = Σ_b r_b`. -/
def survival (s : ι → K) (A : K) (B : ι → K) : K := ∑ b, posterior s A B b

/-- [proved-derived; formal-checked] The posterior mass in terms of the count. -/
theorem posterior_eq (s : ι → K) (A : K) (B : ι → K) (b : ι) :
    posterior s A B b = s b * B b / normalizer s A B :=
  rfl

/-- [proved-derived; formal-checked] The survival posterior is the read mass over the count,
`ρ = (Σ_b s_b B_b) / Ñ`. -/
theorem survival_eq (s : ι → K) (A : K) (B : ι → K) :
    survival s A B = (∑ b, s b * B b) / normalizer s A B := by
  first
    | (unfold survival posterior; rw [Finset.sum_div]; done)
    | (simp only [survival, posterior, Finset.sum_div]; done)

/-- [proved-derived; formal-checked] **The numerator of the covector** (law 8): with the softmax
Jacobian column `s_b (δ_ab − s_a)` (not formalized here) against `B`,
`Σ_b s_b (δ_ab − s_a) B_b = s_a B_a − s_a Σ_b s_b B_b`. -/
theorem covector_numerator [DecidableEq ι] (s B : ι → K) (a : ι) :
    ∑ b, s b * ((if a = b then (1 : K) else 0) - s a) * B b
      = s a * B a - s a * ∑ b, s b * B b := by
  have h1 : ∀ b, s b * ((if a = b then (1 : K) else 0) - s a) * B b
      = (if a = b then s b * B b else 0) - s a * (s b * B b) := by
    intro b
    by_cases hab : a = b
    · first
        | (rw [if_pos hab, if_pos hab]; ring1)
        | (simp [hab] <;> ring)
    · first
        | (rw [if_neg hab, if_neg hab]; ring1)
        | (simp [hab] <;> ring)
  calc ∑ b, s b * ((if a = b then (1 : K) else 0) - s a) * B b
      = ∑ b, ((if a = b then s b * B b else 0) - s a * (s b * B b)) :=
        Finset.sum_congr rfl (fun b _ => h1 b)
    _ = (∑ b, (if a = b then s b * B b else 0)) - ∑ b, s a * (s b * B b) :=
        Finset.sum_sub_distrib _ _
    _ = s a * B a - s a * ∑ b, s b * B b := by
        first
          | (rw [Fintype.sum_ite_eq, Finset.mul_sum]; done)
          | (simp only [Fintype.sum_ite_eq, Finset.mul_sum]; done)
          | simp [Finset.mul_sum]

/-- [proved-derived; formal-checked] **The relaxed covector** (law 8): for each class `a`,

`(Σ_b s_b (δ_ab − s_a) B_b) / Ñ = r_a − ρ s_a`.

With the softmax Jacobian column `∂ s_b / ∂ λ_a = s_b (δ_ab − s_a)` (the standard derivative, not
formalized here) and `∂Ñ/∂s_b = B_b`, the left side is `∂ log Ñ / ∂ λ(a)`: the surviving posterior
mass `r_a` less the predicted mass `ρ s_a`. The identity holds for the formal inverse; it needs
neither `Σ_b s_b = 1` nor `Ñ ≠ 0`. -/
theorem covector_column [DecidableEq ι] (s B : ι → K) (A : K) (a : ι) :
    (∑ b, s b * ((if a = b then (1 : K) else 0) - s a) * B b) / normalizer s A B
      = posterior s A B a - survival s A B * s a := by
  rw [covector_numerator s B a, survival_eq, posterior_eq]
  ring

/-- [proved-derived; formal-checked] **The covector sums to zero** (law 8): for a soft constituent
of total mass one, `Σ_a (r_a − ρ s_a) = ρ − ρ · 1 = 0`. -/
theorem covector_sum_zero (s : ι → K) (A : K) (B : ι → K) (hs : ∑ b, s b = 1) :
    ∑ a, (posterior s A B a - survival s A B * s a) = 0 := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs, mul_one]
  first
    | exact sub_self _
    | (unfold survival; exact sub_self _)
    | simp [survival]

/-- [proved-derived; formal-checked] **The role of `Ñ ≠ 0`** (law 8): the survival posterior is one
less the posterior mass of the paths that delete the position, `ρ = 1 − A / Ñ`. -/
theorem survival_eq_one_sub (s : ι → K) (A : K) (B : ι → K) (hN : normalizer s A B ≠ 0) :
    survival s A B = 1 - A / normalizer s A B := by
  have hS : (∑ b, s b * B b) = normalizer s A B - A := by
    unfold normalizer
    ring
  rw [survival_eq, hS]
  first
    | exact same_sub_div hN
    | (rw [sub_div, div_self hN]; done)

end Covector

end Holonics.Transport.DeletionReceiver

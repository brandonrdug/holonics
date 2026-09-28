import Holonics.Compression.Landmark.Context.LocalWeighing
import Holonics.Computation.HolonicAdjointNormalization
import Holonics.Foundation.ReceiverRelease

/-!
# The egg population: the static mixture with death, and survivor filtering

[definition; agent-inferred] A population is a receiver's mixture over candidate eggs: declared
navigator families, each with its own predictive face and a declared prior (Rust
`receiver::population`; `docs/ELEMENTARY_OBJECTS.md`, "The egg: a generator read as a whole").
`LocalWeighing.static_mixture` states the Bayes mixture of faces for **positive** faces. A
population's families may give a received cell zero (a deterministic family whose surviving keys
emit another class), so this module states the same mixture with **nonnegative** faces:

* `population_mixture` [proved-derived; formal-checked]: while some family with positive prior keeps
  a positive likelihood, every forward total is positive, the mixture's product telescopes to
  `Σ_x π_x A_x(n)`, a family whose face of a cell is zero keeps weight zero from the next cell on
  (death: `HolonicAdjointNormalization.replicator_eq_zero_iff` is its one-step form), and the
  population codes within `−log₂ π_x` of every living family.
* `population_mixture_enclosed` [proved-derived; formal-checked]: a family read through an
  enclosure of its faces, `lo ≤ f ≤ hi`, keeps the population's product between the priors'
  mixtures of the endpoints' products (Rust `receiver::population::port`, a face in `ℚ(θ)` read at
  a port through its exact enclosure; an exactly zero face is its own enclosure, so death stays
  exact).
* `executed_face_within_population`, `executed_mixture_within_population` [proved-derived;
  formal-checked] (over `two_face_skew`, `execRatio_eq`, `max_inv_eq_mul`): the receiving face
  (THE_REBUILD U1). The two-family population at ½/½ is the sequential mixture
  (`LocalWeighing.two_face_prior`); its execution through a carried ratio stepped with chart factors
  `ρ_t` (`Tree.execRatio`) stays within `max(k_t, k_t⁻¹)`, `k_t = ∏_(s<t) ρ_s`, of the population's
  face at every cell, and within `∏_t max(ρ_t, ρ_t⁻¹)` of its product `½ A_n + ½ B_n` over the
  passage: in bits, `|Σ_(s<t) log₂ ρ_s|` and `Σ_t |log₂ ρ_t|`.
* `survivor_code` [proved-derived; formal-checked]: a finite key space of deterministic emitters
  under the uniform prior. The survivors `S_t` are the keys agreeing with every cell before `t`; the
  mixture's face of the received cell is `#S_(t+1)/#S_t`, its product is `#S_n/|K|`, and its code is
  `log₂ |K| − log₂ #S_n`: the key description less the surviving fibre.
* `survivors_product` [proved-derived; formal-checked]: a key space that is a product, emitting the
  pair of its factors' classes, keeps the product of the factors' survivors, so its count is the
  product and its code the sum of the factors' codes (the sheet tuple read per ring; the Rust cell is
  the pair's injective mixed-radix code).
* `escaped_fibre_is_mode` [proved-derived; formal-checked]: a deterministic key's **escaped** face
  (`1 − η` on its own class, `δ` elsewhere) keeps faces positive; a key surviving to `n` has
  likelihood `(1 − η)^n` (`seqLik_escaped_survivor`), and with `0 < δ < 1 − η` it strictly exceeds
  every contradicted key's, so under the uniform prior the families of greatest posterior are exactly
  the survivors (Rust `receiver::population::ChaseFamily`, the chase terrain's reception).
* `survivors_share_one_likelihood` [proved-derived; formal-checked]: every survivor has the same
  escaped likelihood, so under the uniform prior the log-odds between two members of the selected
  fibre are identically zero. A sequential test on accumulated log-odds reads nothing inside the
  fibre and crosses a threshold of at most one contradiction exactly when one member survives
  (THE_REBUILD F6's action law, amended by U3's second loop; Rust `receiver::population::chaser`).
* `partitionInformation`, `partitionInformation_lt_iff` [proved-derived; formal-checked]: **the
  probe's criterion.** An observation partitions a uniform fibre of `N` members into classes of
  sizes `c`, and its information is `log N − (1/N) Σ_c c log c`. Over one fibre a partition carries
  strictly more information than another exactly when `∏_c c^c` is strictly smaller: a comparison
  of natural numbers, with no logarithm formed (Rust `receiver::release::ProbePartition`, the
  chaser's `Ask`).
* `death_is_an_exchange` [proved-derived; formal-checked] (a corollary of
  `HolonicAdjointNormalization.sum_replicator`): death is an exchange, never a deletion. At a cell
  whose likelihood is zero for the dying families and positive in total, each dying family's weight
  goes to zero, the survivors' new weights sum to one, and the survivors' total gain is exactly the
  dead mass. [definition] Each dead family's mass `w_f` is attributed to the survivors as
  `w_f w′_g`; under that attribution each dead family's mass is received whole, and a survivor's new
  weight reads as its share of the living mass plus its attributed shares of the dead (Rust
  `receiver::population::DeathReceipt`: the population's total mass is conserved across a death).
* `certified_inverseCDF_class` [proved-derived; formal-checked]: interval face bounds certify a
  draw's class when its lower cumulative mass through that class exceeds the draw and its upper
  cumulative mass before that class does not. An unresolved draw remains unresolved.
* `certified_draw_is_released_at_zero_tolerance`, `plural_draw_is_held` [proved-derived;
  formal-checked]: **the certified draw is the release law at tolerance zero** (THE_REBUILD U3; Rust
  `receiver::release::draw`). The draw's class reading `drawReading` (`1` where the key lands in
  class `i`, `0` elsewhere) is constant over every finite family of faces inside certifying
  bounds, so `Foundation/ReceiverRelease.holdingLaw` at tolerance zero returns `released`; where
  two compatible faces part at the key, its width is at least one and the same law holds. A
  declared draw and a threshold commit are different acts (the draw has a key; it emits a class,
  not the face), joined by this one law.
* `local_telescope`, `local_mixture_code`, `local_of_constant` [proved-derived; formal-checked]: a
  family wins where it is closest (F0's second candidate; its Rust
  `receiver::population::LocalMixture` was measured, not adopted and retired September 28). A gating map `γ` places each cell in a context; the local
  mixture weighs the families at cell `t` by the posterior of `γ t` alone, each context's weights
  its prior times the family's faces over the context's earlier cells. With positive faces its faces
  telescope to the product of the contexts' totals (a context not met holds its prior, total one),
  so it codes within `Σ_(c met) (−log₂ π_(g c) − log₂ L_(g c)(c))` for every choice `g` of one family
  per context; one context (a constant gating map) is the static mixture.

The computational object is the helical pair interaction read as a receiver's population of
candidate eggs; of the winding guide's six general objects this module touches **faces and
placement** (each family's face and the mixture's face); the helix, pair, cell holonomy, tube and
tower thread stay attached through the families' own owners.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Compression.Landmark.Context.Population

open Finset
open Holonics.Compression.Landmark.Context.Tree
open Holonics.Compression.Landmark.Context.LocalWeighing

section CertifiedRelease

/-- A draw lies in one class of a finite exact face, with the left boundary included. -/
def InverseCDFClass {n : ℕ} (q : Fin n → ℚ) (draw : ℚ) (i : Fin n) : Prop :=
  (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), q j) ≤ draw ∧
    draw < ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ i.val), q j

/-- [proved-derived; formal-checked] The outward bounds used by Rust's certified inverse-CDF
selector suffice for every compatible exact receiving face. This theorem preserves the unresolved
draw region: it does not turn a selectively emitted submeasure into the full mixture. -/
theorem certified_inverseCDF_class {n : ℕ} (lower upper q : Fin n → ℚ)
    (draw : ℚ) (i : Fin n) (hlower : ∀ j, lower j ≤ q j)
    (hupper : ∀ j, q j ≤ upper j)
    (hbefore : (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), upper j) ≤ draw)
    (hthrough : draw < ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ i.val), lower j) :
    InverseCDFClass q draw i := by
  constructor
  · exact le_trans (Finset.sum_le_sum fun j _ => hupper j) hbefore
  · exact lt_of_lt_of_le hthrough (Finset.sum_le_sum fun j _ => hlower j)

open Classical in
/-- [definition] **The draw's class reading**: `1` where the key lands in class `i` of the exact
face `q`, `0` elsewhere. A class has no grain coarser than itself, so the reading is decided at
tolerance zero. -/
def drawReading {n : ℕ} (draw : ℚ) (i : Fin n) (q : Fin n → ℚ) : ℚ :=
  if InverseCDFClass q draw i then 1 else 0

/-- [proved-derived; formal-checked] **A certified draw is a release at tolerance zero.** Over any
finite family of exact faces inside the interval bounds, the certificate lands the key in class `i`
for every member, so the class reading is constant and the holding law at tolerance zero returns
`released` (`width_eq_zero_iff`). -/
theorem certified_draw_is_released_at_zero_tolerance {n : ℕ} {Probe Coarser : Type*}
    (lower upper : Fin n → ℚ) (draw : ℚ) (i : Fin n) (F : Finset (Fin n → ℚ)) (hF : F.Nonempty)
    (hlower : ∀ q ∈ F, ∀ j, lower j ≤ q j) (hupper : ∀ q ∈ F, ∀ j, q j ≤ upper j)
    (hbefore : (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), upper j) ≤ draw)
    (hthrough : draw < ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ i.val), lower j) :
    (Foundation.ReceiverRelease.holdingLaw (Fin n → ℚ) Probe Coarser 0).decide F hF
        (drawReading draw i) = Foundation.ReceiverRelease.ReleaseReturn.released := by
  have hconst : ∀ q ∈ F, drawReading draw i q = 1 := by
    intro q hq
    unfold drawReading
    rw [if_pos (certified_inverseCDF_class lower upper q draw i (hlower q hq) (hupper q hq)
      hbefore hthrough)]
  have hwidth : Foundation.ReceiverRelease.width F hF (drawReading draw i) = 0 := by
    rw [Foundation.ReceiverRelease.width_eq_zero_iff]
    intro x hx y hy
    rw [hconst x hx, hconst y hy]
  simp [Foundation.ReceiverRelease.holdingLaw, hwidth]

/-- [proved-derived; formal-checked] **A plural draw is held.** Where two compatible faces part at
the key (one lands it in class `i`, the other does not), the class reading's width is at least one
(`abs_sub_le_width`), so the holding law at tolerance zero returns `hold`: the draw mass stays
unresolved, and no class is emitted. -/
theorem plural_draw_is_held {n : ℕ} {Probe Coarser : Type*} (draw : ℚ) (i : Fin n)
    (F : Finset (Fin n → ℚ)) (hF : F.Nonempty) {q q' : Fin n → ℚ} (hq : q ∈ F) (hq' : q' ∈ F)
    (hin : InverseCDFClass q draw i) (hout : ¬ InverseCDFClass q' draw i) :
    (Foundation.ReceiverRelease.holdingLaw (Fin n → ℚ) Probe Coarser 0).decide F hF
        (drawReading draw i) = Foundation.ReceiverRelease.ReleaseReturn.hold := by
  have h1 : drawReading draw i q = 1 := by
    unfold drawReading
    rw [if_pos hin]
  have h0 : drawReading draw i q' = 0 := by
    unfold drawReading
    rw [if_neg hout]
  have hle := Foundation.ReceiverRelease.abs_sub_le_width hF (drawReading draw i) hq hq'
  rw [h1, h0] at hle
  have hpos : ¬ Foundation.ReceiverRelease.width F hF (drawReading draw i) ≤ 0 := by
    norm_num at hle
    linarith
  simp [Foundation.ReceiverRelease.holdingLaw, hpos]

end CertifiedRelease

/-- A likelihood that reaches zero stays zero. -/
theorem seqLik_eq_zero_of_le {a : ℕ → ℚ} {t n : ℕ} (h : seqLik a t = 0) (htn : t ≤ n) :
    seqLik a n = 0 := by
  induction n, htn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => rw [seqLik_succ, ih, zero_mul]

theorem seqLik_nonneg {a : ℕ → ℚ} (ha : ∀ t, 0 ≤ a t) (n : ℕ) : 0 ≤ seqLik a n :=
  prod_nonneg fun t _ => ha t

section Mixture

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The static mixture's forward weight is the prior times the prequential likelihood, whatever
the faces' signs. -/
theorem fwd_id (π : ι → ℚ) (f : ι → ℕ → ℚ) :
    ∀ t x, fwd π f idKernel t x = π x * seqLik (f x) t := by
  intro t
  induction t with
  | zero => intro x; simp [fwd_zero, seqLik_zero]
  | succ n ih =>
    intro x
    simp only [fwd_succ, idKernel, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true,
      ih, seqLik_succ]
    ring

/-- [proved-derived; formal-checked] **`population_mixture`: the static mixture with death.** For a
prior `π` and nonnegative faces `f`, if some family keeps `π_x A_x(n) > 0`:
* every forward total up to `n` is positive (the mixture's face is defined at every cell);
* the mixture's product telescopes, `∏_(t<n) q_t = Σ_x π_x A_x(n)`;
* a family whose face of cell `t` is zero has forward weight zero at every later cell (death);
* the mixture codes within `−log₂ π_x` of every living family:
  `−log₂ ∏ q ≤ −log₂ π_x − log₂ A_x(n)`. -/
theorem population_mixture {π : ι → ℚ} {f : ι → ℕ → ℚ} (hπ : IsPrior π)
    (hf : ∀ x t, 0 ≤ f x t) (n : ℕ) (hlive : 0 < ∑ x, π x * seqLik (f x) n) :
    (∀ t ≤ n, 0 < ∑ x, fwd π f idKernel t x) ∧
      ∏ t ∈ range n, fwdMix π f idKernel t = ∑ x, π x * seqLik (f x) n ∧
      (∀ x t, f x t = 0 → ∀ m, t < m → fwd π f idKernel m x = 0) ∧
      ∀ x, 0 < π x → 0 < seqLik (f x) n →
        -Real.logb 2 ((∏ t ∈ range n, fwdMix π f idKernel t : ℚ) : ℝ) ≤
          -Real.logb 2 (π x : ℝ) - Real.logb 2 (seqLik (f x) n : ℝ) := by
  have hfwd := fwd_id π f
  have hnn : ∀ t x, 0 ≤ fwd π f idKernel t x :=
    fwd_nonneg hπ.1 hf idKernel_stochastic.1
  obtain ⟨y, -, hy⟩ := exists_lt_of_sum_lt (s := univ) (f := fun _ => (0 : ℚ))
    (g := fun x => π x * seqLik (f x) n) (by simpa using hlive)
  have hπy : 0 < π y := lt_of_le_of_ne (hπ.1 y) fun h => by
    rw [← h, zero_mul] at hy; exact lt_irrefl _ hy
  have hLy : ∀ t ≤ n, 0 < seqLik (f y) t := fun t ht =>
    lt_of_le_of_ne (seqLik_nonneg (hf y) t) fun h => by
      rw [seqLik_eq_zero_of_le h.symm ht, mul_zero] at hy; exact lt_irrefl _ hy
  have htot : ∀ t ≤ n, 0 < ∑ x, fwd π f idKernel t x := fun t ht =>
    lt_of_lt_of_le (by rw [hfwd]; exact mul_pos hπy (hLy t ht))
      (single_le_sum (f := fun x => fwd π f idKernel t x) (fun x _ => hnn t x) (mem_univ y))
  have htel : ∀ m ≤ n, ∏ t ∈ range m, fwdMix π f idKernel t = ∑ x, fwd π f idKernel m x := by
    intro m hm
    induction m with
    | zero => simp [fwd_zero, hπ.2]
    | succ m ih =>
      rw [prod_range_succ, ih (by omega), fwd_sum_succ idKernel_stochastic, fwdMix,
        mul_div_cancel₀ _ (htot m (by omega)).ne']
  have hprod : ∏ t ∈ range n, fwdMix π f idKernel t = ∑ x, π x * seqLik (f x) n := by
    rw [htel n le_rfl]
    exact sum_congr rfl fun x _ => hfwd n x
  refine ⟨htot, hprod, fun x t h0 m htm => ?_, fun x hx hA => ?_⟩
  · have hz : seqLik (f x) (t + 1) = 0 := by rw [seqLik_succ, h0, mul_zero]
    rw [hfwd, seqLik_eq_zero_of_le hz htm, mul_zero]
  · have hle : π x * seqLik (f x) n ≤ ∏ t ∈ range n, fwdMix π f idKernel t := by
      rw [htel n le_rfl, ← hfwd n x]
      exact single_le_sum (f := fun y => fwd π f idKernel n y) (fun y _ => hnn n y) (mem_univ _)
    have hb := neg_logb_le_of_le (a := ((π x * seqLik (f x) n : ℚ) : ℝ))
      (b := ((∏ t ∈ range n, fwdMix π f idKernel t : ℚ) : ℝ)) (by exact_mod_cast mul_pos hx hA)
      (by exact_mod_cast hle)
    push_cast at hb
    rw [Real.logb_mul (by exact_mod_cast hx.ne') (by exact_mod_cast hA.ne')] at hb
    push_cast
    linarith

/-- [proved-derived; formal-checked] **`population_mixture_enclosed`: a family read through an
enclosure of its faces.** When each family's faces lie between declared bounds `lo ≤ f ≤ hi`
(a face in `ℚ(θ)` read through its exact enclosure, Rust `receiver::population::port`), the
population's product lies between the priors' mixtures of the bounds' products:
`Σ_x π_x ∏_t lo_x(t) ≤ ∏_(t<n) q_t ≤ Σ_x π_x ∏_t hi_x(t)`. A face that is exactly zero is its own
enclosure, so death stays exact. -/
theorem population_mixture_enclosed {π : ι → ℚ} {lo f hi : ι → ℕ → ℚ} (hπ : IsPrior π)
    (hlo : ∀ x t, 0 ≤ lo x t) (hlof : ∀ x t, lo x t ≤ f x t) (hfhi : ∀ x t, f x t ≤ hi x t)
    (n : ℕ) (hlive : 0 < ∑ x, π x * seqLik (f x) n) :
    ∑ x, π x * seqLik (lo x) n ≤ ∏ t ∈ range n, fwdMix π f idKernel t ∧
      ∏ t ∈ range n, fwdMix π f idKernel t ≤ ∑ x, π x * seqLik (hi x) n := by
  have hf : ∀ x t, 0 ≤ f x t := fun x t => le_trans (hlo x t) (hlof x t)
  rw [(population_mixture hπ hf n hlive).2.1]
  refine ⟨sum_le_sum fun x _ => ?_, sum_le_sum fun x _ => ?_⟩
  · exact mul_le_mul_of_nonneg_left
      (prod_le_prod (fun t _ => hlo x t) fun t _ => hlof x t) (hπ.1 x)
  · exact mul_le_mul_of_nonneg_left
      (prod_le_prod (fun t _ => hf x t) fun t _ => hfhi x t) (hπ.1 x)

end Mixture

section Survivors

variable {κ C : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq C]

/-- [definition] **The survivors** at tick `t`: the keys whose emissions agree with every received
cell before `t`. -/
def survivors (e : κ → ℕ → C) (x : ℕ → C) (t : ℕ) : Finset κ :=
  univ.filter fun k => ∀ s < t, e k s = x s

/-- [definition] **A deterministic key's face of the received cell**: one where it emits the cell,
zero elsewhere. -/
def emits (e : κ → ℕ → C) (x : ℕ → C) : κ → ℕ → ℚ :=
  fun k t => if e k t = x t then 1 else 0

/-- [definition] **The uniform prior** over the keys. -/
def uniformPrior : κ → ℚ := fun _ => 1 / (Fintype.card κ : ℚ)

omit [DecidableEq κ] in
theorem uniformPrior_isPrior [Nonempty κ] : IsPrior (uniformPrior (κ := κ)) := by
  refine ⟨fun _ => by unfold uniformPrior; positivity, ?_⟩
  have hc : (Fintype.card κ : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [uniformPrior, sum_const, card_univ, nsmul_eq_mul, hc]

omit [DecidableEq κ] in
theorem survivors_succ (e : κ → ℕ → C) (x : ℕ → C) (t : ℕ) :
    survivors e x (t + 1) = (survivors e x t).filter fun k => e k t = x t := by
  ext k
  simp only [survivors, mem_filter, mem_univ, true_and]
  constructor
  · intro h
    exact ⟨fun s hs => h s (by omega), h t (by omega)⟩
  · rintro ⟨h, ht⟩ s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
    · exact h s hs
    · exact ht

omit [DecidableEq κ] in
theorem survivors_zero (e : κ → ℕ → C) (x : ℕ → C) : survivors e x 0 = univ := by
  ext k; simp [survivors]

omit [DecidableEq κ] in
theorem survivors_antitone (e : κ → ℕ → C) (x : ℕ → C) {t n : ℕ} (h : t ≤ n) :
    survivors e x n ⊆ survivors e x t := by
  intro k hk
  simp only [survivors, mem_filter, mem_univ, true_and] at hk ⊢
  exact fun s hs => hk s (by omega)

/-- A key's likelihood is one while it survives and zero once it has emitted another class. -/
theorem seqLik_emits (e : κ → ℕ → C) (x : ℕ → C) (k : κ) (t : ℕ) :
    seqLik (emits e x k) t = if k ∈ survivors e x t then 1 else 0 := by
  induction t with
  | zero => simp [seqLik_zero, survivors_zero]
  | succ t ih =>
    rw [seqLik_succ, ih, survivors_succ]
    by_cases hk : k ∈ survivors e x t <;> by_cases he : e k t = x t <;> simp [emits, hk, he]

/-- `Σ_k [k ∈ S] = #S`. -/
theorem sum_indicator (S : Finset κ) : ∑ k, (if k ∈ S then (1 : ℚ) else 0) = S.card := by
  rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, mul_one]

/-- [proved-derived; formal-checked] **`survivor_code`: survivor filtering is uniform Bayes.** Under
the uniform prior, while a key survives to `n`:
* the mixture's face of the received cell at every `t < n` is the surviving fraction
  `#S_(t+1)/#S_t`;
* its product over the passage is `#S_n/|K|`;
* its code is `log₂ |K| − log₂ #S_n`. -/
theorem survivor_code [Nonempty κ] (e : κ → ℕ → C) (x : ℕ → C) (n : ℕ)
    (hS : (survivors e x n).Nonempty) :
    (∀ t < n, fwdMix uniformPrior (emits e x) idKernel t =
        ((survivors e x (t + 1)).card : ℚ) / (survivors e x t).card) ∧
      ∏ t ∈ range n, fwdMix uniformPrior (emits e x) idKernel t =
        ((survivors e x n).card : ℚ) / Fintype.card κ ∧
      -Real.logb 2 ((∏ t ∈ range n, fwdMix uniformPrior (emits e x) idKernel t : ℚ) : ℝ) =
        Real.logb 2 (Fintype.card κ) - Real.logb 2 (survivors e x n).card := by
  have hc : (Fintype.card κ : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hf : ∀ k t, 0 ≤ emits e x k t := fun k t => by unfold emits; split_ifs <;> norm_num
  have hweight : ∀ t, ∑ k, uniformPrior k * seqLik (emits e x k) t =
      ((survivors e x t).card : ℚ) / Fintype.card κ := by
    intro t
    simp only [seqLik_emits, uniformPrior, mul_ite, mul_one, mul_zero]
    rw [← sum_indicator, sum_div]
    exact sum_congr rfl fun k _ => by split_ifs <;> simp
  have hcardpos : 0 < ((survivors e x n).card : ℚ) := by exact_mod_cast hS.card_pos
  have hlive : 0 < ∑ k, uniformPrior k * seqLik (emits e x k) n := by
    rw [hweight]; exact div_pos hcardpos (by exact_mod_cast Fintype.card_pos)
  obtain ⟨-, hprod, -, -⟩ := population_mixture uniformPrior_isPrior hf n hlive
  refine ⟨fun t ht => ?_, by rw [hprod, hweight], ?_⟩
  · have hSt : ((survivors e x t).card : ℚ) ≠ 0 := by
      have := (hS.mono (survivors_antitone e x ht.le)).card_pos
      exact_mod_cast this.ne'
    have hnum : ∑ k, fwd uniformPrior (emits e x) idKernel t k * emits e x k t =
        ((survivors e x (t + 1)).card : ℚ) / Fintype.card κ := by
      rw [← hweight (t + 1)]
      refine sum_congr rfl fun k _ => ?_
      rw [fwd_id, seqLik_succ]; ring
    have hden : ∑ k, fwd uniformPrior (emits e x) idKernel t k =
        ((survivors e x t).card : ℚ) / Fintype.card κ := by
      rw [← hweight t]
      exact sum_congr rfl fun k _ => fwd_id _ _ t k
    rw [fwdMix, hnum, hden]
    field_simp
  · rw [hprod, hweight]
    have hcard : (0 : ℝ) < (survivors e x n).card := by exact_mod_cast hS.card_pos
    have hK : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
    push_cast
    rw [Real.logb_div hcard.ne' hK.ne']
    ring

/-- [proved-derived; formal-checked] **`survivors_product`: a product key space keeps the product
of its factors' survivors.** Keys `(k₁, k₂)` emitting the pair of their factors' classes survive
exactly when each factor's key survives on its component of the cells, so the count is the product
and the code is the sum of the factors' codes. -/
theorem survivors_product {κ₁ κ₂ C₁ C₂ : Type*} [Fintype κ₁] [Fintype κ₂] [DecidableEq κ₁]
    [DecidableEq κ₂] [DecidableEq C₁] [DecidableEq C₂] [Nonempty κ₁] [Nonempty κ₂]
    (e₁ : κ₁ → ℕ → C₁) (e₂ : κ₂ → ℕ → C₂) (x₁ : ℕ → C₁) (x₂ : ℕ → C₂) (t : ℕ) :
    survivors (fun (k : κ₁ × κ₂) s => (e₁ k.1 s, e₂ k.2 s)) (fun s => (x₁ s, x₂ s)) t =
        survivors e₁ x₁ t ×ˢ survivors e₂ x₂ t ∧
      (survivors (fun (k : κ₁ × κ₂) s => (e₁ k.1 s, e₂ k.2 s)) (fun s => (x₁ s, x₂ s)) t).card =
        (survivors e₁ x₁ t).card * (survivors e₂ x₂ t).card ∧
      ((survivors e₁ x₁ t).Nonempty → (survivors e₂ x₂ t).Nonempty →
        Real.logb 2 (Fintype.card (κ₁ × κ₂)) -
            Real.logb 2 (survivors (fun (k : κ₁ × κ₂) s => (e₁ k.1 s, e₂ k.2 s))
              (fun s => (x₁ s, x₂ s)) t).card =
          (Real.logb 2 (Fintype.card κ₁) - Real.logb 2 (survivors e₁ x₁ t).card) +
            (Real.logb 2 (Fintype.card κ₂) - Real.logb 2 (survivors e₂ x₂ t).card)) := by
  have hset : survivors (fun (k : κ₁ × κ₂) s => (e₁ k.1 s, e₂ k.2 s)) (fun s => (x₁ s, x₂ s)) t =
      survivors e₁ x₁ t ×ˢ survivors e₂ x₂ t := by
    ext ⟨k₁, k₂⟩
    simp only [survivors, mem_filter, mem_univ, true_and, mem_product, Prod.mk.injEq]
    exact ⟨fun h => ⟨fun s hs => (h s hs).1, fun s hs => (h s hs).2⟩,
      fun h s hs => ⟨h.1 s hs, h.2 s hs⟩⟩
  have hcard := congrArg card hset
  rw [card_product] at hcard
  refine ⟨hset, hcard, fun h₁ h₂ => ?_⟩
  have p₁ : (0 : ℝ) < (survivors e₁ x₁ t).card := by exact_mod_cast h₁.card_pos
  have p₂ : (0 : ℝ) < (survivors e₂ x₂ t).card := by exact_mod_cast h₂.card_pos
  have q₁ : (0 : ℝ) < Fintype.card κ₁ := by exact_mod_cast Fintype.card_pos
  have q₂ : (0 : ℝ) < Fintype.card κ₂ := by exact_mod_cast Fintype.card_pos
  rw [hcard, Fintype.card_prod]
  push_cast
  rw [Real.logb_mul q₁.ne' q₂.ne', Real.logb_mul p₁.ne' p₂.ne']
  ring

/-- [definition] **A deterministic key's escaped face** of the received cell: `1 − η` where it emits
the cell, the escape `δ` elsewhere (Rust `receiver::population::ChaseFamily`, `δ = η/(A − 1)` on an
alphabet of `A` letters), so the face stays positive and a contradicted key pays instead of
dying. -/
def escaped (e : κ → ℕ → C) (x : ℕ → C) (η δ : ℚ) : κ → ℕ → ℚ :=
  fun k t => if e k t = x t then 1 - η else δ

omit [Fintype κ] [DecidableEq κ] in
/-- A key that survives to `n` has escaped likelihood `(1 − η)^n`. -/
theorem seqLik_escaped_survivor (e : κ → ℕ → C) (x : ℕ → C) (η δ : ℚ) {k : κ} {n : ℕ}
    (hk : ∀ s < n, e k s = x s) : seqLik (escaped e x η δ k) n = (1 - η) ^ n := by
  have hface : ∀ t ∈ range n, escaped e x η δ k t = 1 - η := fun t ht => by
    simp [escaped, hk t (mem_range.mp ht)]
  unfold seqLik
  rw [prod_congr rfl hface, prod_const, card_range]

omit [DecidableEq κ] in
/-- [proved-derived; formal-checked] **`escaped_fibre_is_mode`: the escaped population selects the
surviving fibre.** With `0 < δ < 1 − η`, every key that survives to `n` has strictly greater
escaped likelihood than every key the passage contradicted before `n`; so under the uniform prior
the families of greatest posterior are exactly the survivors whenever one survives (Rust
`receiver::population::selected_fibre` against `holarchy::terrain::Chase::fibre`). -/
theorem escaped_fibre_is_mode (e : κ → ℕ → C) (x : ℕ → C) {η δ : ℚ} (hδ : 0 < δ)
    (hlt : δ < 1 - η) {k j : κ} {n : ℕ} (hk : k ∈ survivors e x n)
    (hj : j ∉ survivors e x n) :
    seqLik (escaped e x η δ j) n < seqLik (escaped e x η δ k) n := by
  simp only [survivors, mem_filter, mem_univ, true_and, not_forall] at hk hj
  obtain ⟨s, hs, hne⟩ := hj
  have hη : 0 < 1 - η := lt_trans hδ hlt
  have hconst : (1 - η) ^ n = ∏ _t ∈ range n, (1 - η) := by rw [prod_const, card_range]
  rw [seqLik_escaped_survivor e x η δ hk, hconst]
  unfold seqLik
  refine Finset.prod_lt_prod (R := ℚ) (fun t _ => ?_) (fun t _ => ?_)
    ⟨s, mem_range.mpr hs, ?_⟩
  · unfold escaped; split_ifs
    · exact hη
    · exact hδ
  · unfold escaped; split_ifs
    · exact le_rfl
    · exact hlt.le
  · simp only [escaped, hne, if_false]
    exact hlt

omit [DecidableEq κ] in
/-- [proved-derived; formal-checked] **`survivors_share_one_likelihood`: the log-odds inside the
surviving fibre vanish.** Two keys that both survive to `n` have the same escaped likelihood
`(1 − η)^n`, so under the uniform prior their posterior log-odds are exactly zero: a sequential test
on accumulated log-odds separates no two members of the selected fibre, and crosses any threshold of
at most one contradiction exactly when one member survives (Rust `receiver::population::chaser`,
THE_REBUILD F6's amended action law). -/
theorem survivors_share_one_likelihood (e : κ → ℕ → C) (x : ℕ → C) (η δ : ℚ) {k j : κ} {n : ℕ}
    (hk : k ∈ survivors e x n) (hj : j ∈ survivors e x n) :
    seqLik (escaped e x η δ k) n = seqLik (escaped e x η δ j) n := by
  simp only [survivors, mem_filter, mem_univ, true_and] at hk hj
  rw [seqLik_escaped_survivor e x η δ hk, seqLik_escaped_survivor e x η δ hj]

end Survivors

section ProbePartition

/-! ## The probe's criterion: a partition compared by its product -/

/-- [definition] **The information of a partition** of a uniform fibre of `c.sum` members into
classes of sizes `c`: `log N − (1/N) Σ_c c log c`, the mutual information between the member and
its class (natural logarithm; every base orders alike). -/
def partitionInformation (c : List ℕ) : ℝ :=
  Real.log (c.sum : ℝ) - (c.map (fun k : ℕ => (k : ℝ) * Real.log k)).sum / (c.sum : ℝ)

/-- `exp (k log k) = k^k` on the naturals, `0^0 = 1` included. -/
theorem exp_mul_log_self (k : ℕ) : Real.exp ((k : ℝ) * Real.log k) = ((k ^ k : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hk)]
    push_cast
    ring

/-- `exp (Σ_c c log c) = ∏_c c^c`. -/
theorem exp_sum_mul_log_self (c : List ℕ) :
    Real.exp (c.map (fun k : ℕ => (k : ℝ) * Real.log k)).sum =
      (((c.map (fun k : ℕ => k ^ k)).prod : ℕ) : ℝ) := by
  induction c with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.prod_cons, Real.exp_add, ih,
      exp_mul_log_self, Nat.cast_mul]

/-- [proved-derived; formal-checked] **`partitionInformation_lt_iff`: the probe's criterion is an
integer comparison.** Over one nonempty fibre, the partition `c` carries strictly more information
than `c'` exactly when `∏_c c^c < ∏_c' c'^c'` (Rust `receiver::release::ProbePartition`). -/
theorem partitionInformation_lt_iff (c c' : List ℕ) (hsum : c.sum = c'.sum) (hpos : 0 < c.sum) :
    partitionInformation c' < partitionInformation c ↔
      (c.map (fun k : ℕ => k ^ k)).prod < (c'.map (fun k : ℕ => k ^ k)).prod := by
  unfold partitionInformation
  rw [← hsum]
  have hN : (0 : ℝ) < (c.sum : ℝ) := by exact_mod_cast hpos
  rw [sub_lt_sub_iff_left, div_lt_div_iff_of_pos_right hN, ← Real.exp_lt_exp,
    exp_sum_mul_log_self, exp_sum_mul_log_self, Nat.cast_lt]

end ProbePartition

section Exchange

open Holonics.Computation.HolonicAdjointNormalization.NormalizedExponential

/-- [proved-derived; formal-checked] **`death_is_an_exchange`: the dead mass is the survivors'
gain.** With normalized nonnegative weights `w`, nonnegative likelihoods `L` of the received cell and
a positive total, the dying families (`L_f = 0`) keep weight zero after the replicator, and, with
`w′ = replicator w L` over the survivors (`L_g ≠ 0`):
* `Σ_g w′_g = 1`: the population's mass is conserved;
* `Σ_g (w′_g − w_g) = Σ_f w_f`: the survivors' total gain is exactly the dead mass.

Bayes fixes only these totals. [definition] **The per-survivor attribution**: dead family `f`'s
mass `w_f` is attributed to survivor `g` as `w_f w′_g` (`w_f · w_g L_g / Σ_(h alive) w_h L_h`, Bayes'
normalization stated as the transfer). Under it:
* `Σ_g w_f w′_g = w_f` for every dead `f`: each dead family's mass is received whole;
* `w′_g = (Σ_(h alive) w_h) w′_g + Σ_(f dead) w_f w′_g`: a survivor's new weight read as its share
  of the living mass and its attributed shares of the dead (the identity `Σ_i w_i = 1`, not a
  further law). -/
theorem death_is_an_exchange {ι : Type*} [Fintype ι] {w L : ι → ℝ} (hsum : ∑ i, w i = 1)
    (hZ : 0 < ∑ j, w j * L j) :
    (∀ f, L f = 0 → replicator w L f = 0) ∧
      ∑ g ∈ univ.filter (fun i => ¬ L i = 0), replicator w L g = 1 ∧
      ∑ g ∈ univ.filter (fun i => ¬ L i = 0), (replicator w L g - w g) =
        ∑ f ∈ univ.filter (fun i => L i = 0), w f ∧
      (∀ f, L f = 0 → ∑ g ∈ univ.filter (fun i => ¬ L i = 0), w f * replicator w L g = w f) ∧
      ∀ g, replicator w L g =
        (∑ h ∈ univ.filter (fun i => ¬ L i = 0), w h) * replicator w L g +
          ∑ f ∈ univ.filter (fun i => L i = 0), w f * replicator w L g := by
  classical
  have hdead : ∀ f, L f = 0 → replicator w L f = 0 := fun f hf => by
    simp [replicator, hf]
  have hdead_sum : ∑ f ∈ univ.filter (fun i => L i = 0), replicator w L f = 0 :=
    sum_eq_zero fun f hf => hdead f (mem_filter.mp hf).2
  have hsplit := sum_filter_add_sum_filter_not univ (fun i => L i = 0) (replicator w L)
  have halive : ∑ g ∈ univ.filter (fun i => ¬ L i = 0), replicator w L g = 1 := by
    rw [hdead_sum, zero_add, sum_replicator hZ] at hsplit
    exact hsplit
  have hw_split := sum_filter_add_sum_filter_not univ (fun i => L i = 0) w
  rw [hsum] at hw_split
  refine ⟨hdead, halive, ?_, fun f _ => ?_, fun g => ?_⟩
  · rw [sum_sub_distrib, halive]
    linarith
  · rw [← mul_sum, halive, mul_one]
  · rw [← sum_mul, ← add_mul, add_comm, hw_split, one_mul]

end Exchange

section LocalMixture

/-! ## The local mixture: a family wins where it is closest -/

variable {ι C : Type*} [Fintype ι] [Fintype C] [DecidableEq C]

/-- [definition] **A family's likelihood within a context**: the product of its faces over the
cells before `n` that the gating map `γ` places in context `c`. -/
def ctxLik (a : ℕ → ℚ) (γ : ℕ → C) (c : C) (n : ℕ) : ℚ :=
  ∏ t ∈ (range n).filter (fun t => γ t = c), a t

/-- [definition] **A context's total**, `Σ_x π_x L_x(c, n)`. -/
def ctxTotal (π : ι → ℚ) (f : ι → ℕ → ℚ) (γ : ℕ → C) (c : C) (n : ℕ) : ℚ :=
  ∑ x, π x * ctxLik (f x) γ c n

/-- [definition] **The local mixture's face** of cell `t`: the families' faces of it weighed by
the posterior of cell `t`'s context, `Σ_x π_x L_x(γ t, t) f_x(t) / Σ_x π_x L_x(γ t, t)`. -/
def localFace (π : ι → ℚ) (f : ι → ℕ → ℚ) (γ : ℕ → C) (t : ℕ) : ℚ :=
  (∑ x, π x * ctxLik (f x) γ (γ t) t * f x t) / ctxTotal π f γ (γ t) t

omit [Fintype C] in
theorem ctxLik_succ (a : ℕ → ℚ) (γ : ℕ → C) (c : C) (n : ℕ) :
    ctxLik a γ c (n + 1) = if γ n = c then ctxLik a γ c n * a n else ctxLik a γ c n := by
  unfold ctxLik
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [prod_insert (by simp), mul_comm]
  · rfl

omit [Fintype C] in
theorem ctxLik_pos {a : ℕ → ℚ} (ha : ∀ t, 0 < a t) (γ : ℕ → C) (c : C) (n : ℕ) :
    0 < ctxLik a γ c n :=
  prod_pos fun t _ => ha t

omit [Fintype C] in
theorem ctxTotal_pos {π : ι → ℚ} {f : ι → ℕ → ℚ} (hπ : IsPrior π) (hf : ∀ x t, 0 < f x t)
    (γ : ℕ → C) (c : C) (n : ℕ) : 0 < ctxTotal π f γ c n := by
  obtain ⟨y, -, hy⟩ := exists_lt_of_sum_lt (s := univ) (f := fun _ => (0 : ℚ)) (g := π)
    (by simp [hπ.2])
  exact lt_of_lt_of_le (mul_pos hy (ctxLik_pos (hf y) γ c n))
    (single_le_sum (f := fun x => π x * ctxLik (f x) γ c n)
      (fun x _ => mul_nonneg (hπ.1 x) (ctxLik_pos (hf x) γ c n).le) (mem_univ y))

omit [Fintype C] in
/-- The context of cell `n` moves by that cell's faces. -/
theorem ctxTotal_succ_same (π : ι → ℚ) (f : ι → ℕ → ℚ) (γ : ℕ → C) (n : ℕ) :
    ctxTotal π f γ (γ n) (n + 1) = ∑ x, π x * ctxLik (f x) γ (γ n) n * f x n := by
  unfold ctxTotal
  refine sum_congr rfl fun x _ => ?_
  rw [ctxLik_succ, if_pos rfl, mul_assoc]

omit [Fintype C] in
/-- Every other context stands still. -/
theorem ctxTotal_succ_other (π : ι → ℚ) (f : ι → ℕ → ℚ) (γ : ℕ → C) {c : C} {n : ℕ}
    (h : γ n ≠ c) : ctxTotal π f γ c (n + 1) = ctxTotal π f γ c n := by
  unfold ctxTotal
  refine sum_congr rfl fun x _ => ?_
  rw [ctxLik_succ, if_neg h]

omit [Fintype C] in
/-- The local face is its context's total after the cell over its total before. -/
theorem localFace_eq (π : ι → ℚ) (f : ι → ℕ → ℚ) (γ : ℕ → C) (t : ℕ) :
    localFace π f γ t = ctxTotal π f γ (γ t) (t + 1) / ctxTotal π f γ (γ t) t := by
  rw [localFace, ctxTotal_succ_same]

omit [Fintype C] in
/-- A context the passage has not met holds its prior: its total is one. -/
theorem ctxTotal_unmet {π : ι → ℚ} (hπ : IsPrior π) (f : ι → ℕ → ℚ) (γ : ℕ → C) {c : C}
    {n : ℕ} (hc : c ∉ (range n).image γ) : ctxTotal π f γ c n = 1 := by
  have hempty : (range n).filter (fun t => γ t = c) = ∅ := by
    ext t
    simp only [mem_filter, mem_range, notMem_empty, iff_false, not_and]
    intro ht h
    exact hc (mem_image.mpr ⟨t, mem_range.mpr ht, h⟩)
  simp [ctxTotal, ctxLik, hempty, hπ.2]

/-- [proved-derived; formal-checked] **`local_telescope`: the local mixture telescopes context by
context.** With a prior and positive faces, `∏_(t<n) q_t = ∏_c Σ_x π_x L_x(c, n)`: each cell moves
only its own context's total, by its local face. -/
theorem local_telescope {π : ι → ℚ} {f : ι → ℕ → ℚ} (hπ : IsPrior π) (hf : ∀ x t, 0 < f x t)
    (γ : ℕ → C) (n : ℕ) :
    ∏ t ∈ range n, localFace π f γ t = ∏ c, ctxTotal π f γ c n := by
  induction n with
  | zero =>
    rw [range_zero, prod_empty]
    exact (prod_eq_one fun c _ => ctxTotal_unmet hπ f γ (by simp)).symm
  | succ n ih =>
    have hne := (ctxTotal_pos hπ hf γ (γ n) n).ne'
    have hrest : ∏ c ∈ univ.erase (γ n), ctxTotal π f γ c (n + 1) =
        ∏ c ∈ univ.erase (γ n), ctxTotal π f γ c n :=
      prod_congr rfl fun c hc => ctxTotal_succ_other π f γ (Ne.symm (ne_of_mem_erase hc))
    rw [prod_range_succ, ih, localFace_eq,
      ← mul_prod_erase univ (fun c => ctxTotal π f γ c n) (mem_univ (γ n)),
      ← mul_prod_erase univ (fun c => ctxTotal π f γ c (n + 1)) (mem_univ (γ n)), hrest]
    field_simp

/-- [proved-derived; formal-checked] **`local_mixture_code`: a family wins where it is closest.**
With a prior and positive faces the local mixture codes within, for every choice `g` of one family
per context with a positive prior, the contexts met each paying that family's prior code and its
code on the context's cells:
`−log₂ ∏_(t<n) q_t ≤ Σ_(c ∈ γ[range n]) (−log₂ π_(g c) − log₂ L_(g c)(c, n))`. Under the uniform
prior over `M` families this is `Σ_(c met) (min_f code_f(c) + log₂ M)`. -/
theorem local_mixture_code {π : ι → ℚ} {f : ι → ℕ → ℚ} (hπ : IsPrior π)
    (hf : ∀ x t, 0 < f x t) (γ : ℕ → C) (n : ℕ) (g : C → ι) (hg : ∀ c, 0 < π (g c)) :
    -Real.logb 2 ((∏ t ∈ range n, localFace π f γ t : ℚ) : ℝ) ≤
      ∑ c ∈ (range n).image γ,
        (-Real.logb 2 (π (g c) : ℝ) - Real.logb 2 (ctxLik (f (g c)) γ c n : ℝ)) := by
  have hmet : ∏ t ∈ range n, localFace π f γ t =
      ∏ c ∈ (range n).image γ, ctxTotal π f γ c n := by
    rw [local_telescope hπ hf γ n]
    exact (prod_subset (subset_univ _) fun c _ hc => ctxTotal_unmet hπ f γ hc).symm
  rw [hmet, Rat.cast_prod, Real.logb_prod _ _ fun c _ => by
    exact_mod_cast (ctxTotal_pos hπ hf γ c n).ne', ← sum_neg_distrib]
  refine sum_le_sum fun c _ => ?_
  have hA := ctxLik_pos (hf (g c)) γ c n
  have hle : π (g c) * ctxLik (f (g c)) γ c n ≤ ctxTotal π f γ c n :=
    single_le_sum (f := fun x => π x * ctxLik (f x) γ c n)
      (fun x _ => mul_nonneg (hπ.1 x) (ctxLik_pos (hf x) γ c n).le) (mem_univ (g c))
  have hb := neg_logb_le_of_le (a := ((π (g c) * ctxLik (f (g c)) γ c n : ℚ) : ℝ))
    (b := ((ctxTotal π f γ c n : ℚ) : ℝ)) (by exact_mod_cast mul_pos (hg c) hA)
    (by exact_mod_cast hle)
  push_cast at hb
  rw [Real.logb_mul (by exact_mod_cast (hg c).ne') (by exact_mod_cast hA.ne')] at hb
  linarith

omit [Fintype C] in
/-- [proved-derived; formal-checked] **`local_of_constant`: one context is whole-passage Bayes.**
Under a constant gating map the local face is the static mixture's face. -/
theorem local_of_constant [DecidableEq ι] (π : ι → ℚ) (f : ι → ℕ → ℚ) {γ : ℕ → C} {c : C}
    (hγ : ∀ t, γ t = c) (t : ℕ) : localFace π f γ t = fwdMix π f idKernel t := by
  have hlik : ∀ x m, ctxLik (f x) γ c m = seqLik (f x) m := by
    intro x m
    unfold ctxLik seqLik
    rw [filter_true_of_mem fun s _ => hγ s]
  simp only [localFace, fwdMix, ctxTotal, hγ, hlik, fwd_id]

end LocalMixture

/-! ## The receiving face: the two-family population against the executed ratio chart

THE_REBUILD U1: the HNN's receiving face is the population over the tree's face `a` and the combined
face `b` at the matched prior ½/½, which is the sequential mixture (`LocalWeighing.two_face_prior`
at `π = ½`: `priorMix (1/2) = seqMix`, a static forward mixture over `Bool`). The retired
`hnn::receiving::Mixture` executed it through a carried ratio `β̂_(t+1) = β̂_t a_t/(b_t ρ_t)`
(`Tree.execRatio`), `ρ_t` the chart's factor at cell `t`. These two statements bound that execution
against the population, cell by cell and over the passage, by the chart's factors alone: in bits,
`log₂ max(ρ, ρ⁻¹) = |log₂ ρ|`, so the per-cell faces differ by at most `|Σ_(s<t) log₂ ρ_s|` and the
passage codes by at most `Σ_(t<n) |log₂ ρ_t|`, the retired chart's certified drift. -/

section ReceivingFace

/-- **One cell's face under two weight ratios**: moving the second face's weight by a factor `k`
moves the two-face mixture by at most `max(k, k⁻¹)` either way. -/
theorem two_face_skew {x y u v k : ℚ} (hx : 0 < x) (hy : 0 < y) (hu : 0 < u) (hv : 0 < v)
    (hk : 0 < k) :
    (x + y) / (u + v) ≤ max k k⁻¹ * ((x + k * y) / (u + k * v)) ∧
      (x + k * y) / (u + k * v) ≤ max k k⁻¹ * ((x + y) / (u + v)) := by
  have huv : 0 < u + v := by positivity
  have hukv : 0 < u + k * v := by positivity
  have hxu := mul_pos hx hu
  have hxv := mul_pos hx hv
  have hyu := mul_pos hy hu
  have hyv := mul_pos hy hv
  rcases le_total 1 k with h | h
  · have hm : max k k⁻¹ = k := max_eq_left (le_trans (inv_le_one_of_one_le₀ h) h)
    have h0 : 0 ≤ k - 1 := sub_nonneg.mpr h
    rw [hm, ← mul_div_assoc, ← mul_div_assoc]
    constructor
    · rw [div_le_div_iff₀ huv hukv]
      nlinarith [mul_nonneg h0 hxu.le, mul_nonneg (mul_nonneg h0 (by linarith : (0 : ℚ) ≤ k + 1))
        hyu.le, mul_nonneg (mul_nonneg hk.le h0) hyv.le]
    · rw [div_le_div_iff₀ hukv huv]
      nlinarith [mul_nonneg h0 hxu.le, mul_nonneg (mul_nonneg h0 (by linarith : (0 : ℚ) ≤ k + 1))
        hxv.le, mul_nonneg (mul_nonneg hk.le h0) hyv.le]
  · have hinv : 1 ≤ k⁻¹ := one_le_inv₀ hk |>.mpr h
    have hm : max k k⁻¹ = k⁻¹ := max_eq_right (le_trans h hinv)
    have h0 : 0 ≤ 1 - k := sub_nonneg.mpr h
    rw [hm]
    constructor
    · -- `k (x + y)/(u + v) ≤ (x + k y)/(u + k v)`, then multiply by `k⁻¹`.
      have key : k * ((x + y) / (u + v)) ≤ (x + k * y) / (u + k * v) := by
        rw [← mul_div_assoc, div_le_div_iff₀ huv hukv]
        nlinarith [mul_nonneg h0 hxu.le, mul_nonneg (mul_nonneg h0 (by linarith : (0 : ℚ) ≤ 1 + k))
          hxv.le, mul_nonneg (mul_nonneg hk.le h0) hyv.le]
      calc (x + y) / (u + v) = k⁻¹ * (k * ((x + y) / (u + v))) := by
            rw [← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul]
        _ ≤ k⁻¹ * ((x + k * y) / (u + k * v)) :=
            mul_le_mul_of_nonneg_left key (inv_pos.mpr hk).le
    · have key : k * ((x + k * y) / (u + k * v)) ≤ (x + y) / (u + v) := by
        rw [← mul_div_assoc, div_le_div_iff₀ hukv huv]
        nlinarith [mul_nonneg h0 hxu.le, mul_nonneg (mul_nonneg h0 (by linarith : (0 : ℚ) ≤ 1 + k))
          hyu.le, mul_nonneg (mul_nonneg hk.le h0) hyv.le]
      calc (x + k * y) / (u + k * v) = k⁻¹ * (k * ((x + k * y) / (u + k * v))) := by
            rw [← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul]
        _ ≤ k⁻¹ * ((x + y) / (u + v)) := mul_le_mul_of_nonneg_left key (inv_pos.mpr hk).le

/-- The carried ratio is the first face's likelihood over the second's times the chart's factors:
`β̂_t = A_t/(B_t ∏_(s<t) ρ_s)`. -/
theorem execRatio_eq {a b ρ : ℕ → ℚ} (hb : ∀ t, 0 < b t) (hρ : ∀ t, 0 < ρ t) (t : ℕ) :
    execRatio a b ρ t = seqLik a t / (seqLik b t * seqLik ρ t) := by
  induction t with
  | zero => simp [execRatio, seqLik_zero]
  | succ t ih =>
    have hB := seqLik_pos hb t
    have hk := seqLik_pos hρ t
    have := hb t
    have := hρ t
    rw [execRatio, ih, seqLik_succ, seqLik_succ, seqLik_succ]
    field_simp

/-- [proved-derived; formal-checked] **`executed_face_within_population`: one cell.** The executed
face `q̂_t` (the carried ratio's) and the two-family population's face `q_t = seqMix` at ½/½ differ
by at most the factor `max(k_t, k_t⁻¹)`, `k_t = ∏_(s<t) ρ_s` the chart's accumulated factor: in
bits, `|log₂ q̂_t − log₂ q_t| ≤ |Σ_(s<t) log₂ ρ_s|`. -/
theorem executed_face_within_population {a b ρ : ℕ → ℚ} (ha : ∀ t, 0 < a t)
    (hb : ∀ t, 0 < b t) (hρ : ∀ t, 0 < ρ t) (t : ℕ) :
    seqMix a b t ≤ max (seqLik ρ t) (seqLik ρ t)⁻¹ * execMix a b ρ t ∧
      execMix a b ρ t ≤ max (seqLik ρ t) (seqLik ρ t)⁻¹ * seqMix a b t := by
  have hA := seqLik_pos ha t
  have hB := seqLik_pos hb t
  have hk := seqLik_pos hρ t
  have hexec : execMix a b ρ t = (seqLik a t * a t + seqLik ρ t * (seqLik b t * b t)) /
      (seqLik a t + seqLik ρ t * seqLik b t) := by
    rw [execMix, execRatio_eq hb hρ]
    have := ha t
    have := hb t
    field_simp
    ring
  have hseq : seqMix a b t = (seqLik a t * a t + seqLik b t * b t) /
      (seqLik a t + seqLik b t) := by
    have hAB : seqLik a t + seqLik b t ≠ 0 := by positivity
    simp only [seqMix]
    field_simp
    ring
  rw [hexec, hseq]
  exact two_face_skew (mul_pos hA (ha t)) (mul_pos hB (hb t)) hA hB hk

/-- `max(ρ, ρ⁻¹) = max(1, ρ) · max(1, ρ⁻¹)` for `ρ > 0`. -/
theorem max_inv_eq_mul {ρ : ℚ} (hρ : 0 < ρ) : max ρ ρ⁻¹ = max 1 ρ * max 1 ρ⁻¹ := by
  rcases le_total 1 ρ with h | h
  · have hi : ρ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
    rw [max_eq_left (le_trans hi h), max_eq_right h, max_eq_left hi, mul_one]
  · have hi : 1 ≤ ρ⁻¹ := one_le_inv₀ hρ |>.mpr h
    rw [max_eq_right (le_trans h hi), max_eq_left h, max_eq_right hi, one_mul]

/-- [proved-derived; formal-checked] **`executed_mixture_within_population`: the passage.** The
executed product `∏_(t<n) q̂_t` and the two-family population's product `½ A_n + ½ B_n` (the
telescope at ½/½) differ by at most the factor `K_n = ∏_(t<n) max(ρ_t, ρ_t⁻¹)`: in bits,
`|log₂ ∏ q̂ − log₂(½ A_n + ½ B_n)| ≤ Σ_(t<n) |log₂ ρ_t|`, the chart's certified drift. -/
theorem executed_mixture_within_population {a b ρ : ℕ → ℚ} (ha : ∀ t, 0 < a t)
    (hb : ∀ t, 0 < b t) (hρ : ∀ t, 0 < ρ t) (n : ℕ) :
    seqLik a n / 2 + seqLik b n / 2 ≤
        (∏ t ∈ range n, max (ρ t) (ρ t)⁻¹) * ∏ t ∈ range n, execMix a b ρ t ∧
      ∏ t ∈ range n, execMix a b ρ t ≤
        (∏ t ∈ range n, max (ρ t) (ρ t)⁻¹) * (seqLik a n / 2 + seqLik b n / 2) := by
  set Bh : ℕ → ℚ := seqLik (fun t => b t * ρ t) with hBh
  have hbρ : ∀ t, 0 < b t * ρ t := fun t => mul_pos (hb t) (hρ t)
  have hmix : ∀ t, execMix a b ρ t =
      (seqLik a t * a t + Bh t * b t) / (seqLik a t + Bh t) := by
    intro t
    have hA := seqLik_pos ha t
    have hB : 0 < Bh t := seqLik_pos hbρ t
    have hsplit : seqLik b t * seqLik ρ t = Bh t := by
      simp only [hBh, seqLik, prod_mul_distrib]
    rw [execMix, execRatio_eq hb hρ, hsplit]
    field_simp
    ring
  have hq : ∀ t, 0 < execMix a b ρ t := fun t => by
    rw [hmix]
    have := seqLik_pos ha t; have := seqLik_pos hbρ t; have := ha t; have := hb t
    positivity
  have hone : ∀ t, 1 ≤ max 1 (ρ t) := fun t => le_max_left _ _
  have hone' : ∀ t, 1 ≤ max 1 (ρ t)⁻¹ := fun t => le_max_left _ _
  -- The two invariants on `A_n + B̂_n`.
  have hlo : ∀ n, seqLik a n + Bh n ≤
      2 * (∏ t ∈ range n, max 1 (ρ t)) * ∏ t ∈ range n, execMix a b ρ t := by
    intro n
    induction n with
    | zero => simp [hBh, seqLik_zero]; norm_num
    | succ n ih =>
      have hA := seqLik_pos ha n
      have hB : 0 < Bh n := seqLik_pos hbρ n
      have hAB : 0 < seqLik a n + Bh n := by positivity
      have hm : 0 ≤ max 1 (ρ n) := le_trans zero_le_one (hone n)
      rw [prod_range_succ, prod_range_succ, seqLik_succ, hBh, seqLik_succ, ← hBh]
      have step : seqLik a n * a n + Bh n * (b n * ρ n) ≤
          max 1 (ρ n) * ((seqLik a n + Bh n) * execMix a b ρ n) := by
        rw [hmix, mul_div_cancel₀ _ hAB.ne']
        have h1 : seqLik a n * a n ≤ max 1 (ρ n) * (seqLik a n * a n) :=
          le_mul_of_one_le_left (mul_pos hA (ha n)).le (hone n)
        have h2 : Bh n * (b n * ρ n) ≤ max 1 (ρ n) * (Bh n * b n) := by
          have e : Bh n * (b n * ρ n) = ρ n * (Bh n * b n) := by ring
          rw [e]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_pos hB (hb n)).le
        nlinarith
      calc seqLik a n * a n + Bh n * (b n * ρ n)
          ≤ max 1 (ρ n) * ((seqLik a n + Bh n) * execMix a b ρ n) := step
        _ ≤ max 1 (ρ n) * ((2 * (∏ t ∈ range n, max 1 (ρ t)) *
              ∏ t ∈ range n, execMix a b ρ t) * execMix a b ρ n) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ih (hq n).le) hm
        _ = 2 * ((∏ t ∈ range n, max 1 (ρ t)) * max 1 (ρ n)) *
              ((∏ t ∈ range n, execMix a b ρ t) * execMix a b ρ n) := by ring
  have hhi : ∀ n, 2 * ∏ t ∈ range n, execMix a b ρ t ≤
      (∏ t ∈ range n, max 1 (ρ t)⁻¹) * (seqLik a n + Bh n) := by
    intro n
    induction n with
    | zero => simp [hBh, seqLik_zero]; norm_num
    | succ n ih =>
      have hA := seqLik_pos ha n
      have hB : 0 < Bh n := seqLik_pos hbρ n
      have hAB : 0 < seqLik a n + Bh n := by positivity
      have hV : 0 ≤ ∏ t ∈ range n, max 1 (ρ t)⁻¹ :=
        prod_nonneg fun t _ => le_trans zero_le_one (hone' t)
      rw [prod_range_succ, prod_range_succ, seqLik_succ, hBh, seqLik_succ, ← hBh]
      -- `B̂ b ≤ max(1, ρ⁻¹) B̂ b ρ`, since `ρ max(1, ρ⁻¹) ≥ 1`.
      have hρm : 1 ≤ ρ n * max 1 (ρ n)⁻¹ := by
        rcases le_total 1 (ρ n)⁻¹ with h | h
        · rw [max_eq_right h, mul_inv_cancel₀ (hρ n).ne']
        · rw [max_eq_left h, mul_one]
          have := (inv_le_one₀ (hρ n)).mp h
          exact this
      have step : seqLik a n * a n + Bh n * b n ≤
          max 1 (ρ n)⁻¹ * (seqLik a n * a n + Bh n * (b n * ρ n)) := by
        have h1 : seqLik a n * a n ≤ max 1 (ρ n)⁻¹ * (seqLik a n * a n) :=
          le_mul_of_one_le_left (mul_pos hA (ha n)).le (hone' n)
        have h2 : Bh n * b n ≤ max 1 (ρ n)⁻¹ * (Bh n * (b n * ρ n)) := by
          have e : max 1 (ρ n)⁻¹ * (Bh n * (b n * ρ n)) =
              (ρ n * max 1 (ρ n)⁻¹) * (Bh n * b n) := by ring
          rw [e]
          exact le_mul_of_one_le_left (mul_pos hB (hb n)).le hρm
        nlinarith
      have hqn : (seqLik a n + Bh n) * execMix a b ρ n = seqLik a n * a n + Bh n * b n := by
        rw [hmix, mul_div_cancel₀ _ hAB.ne']
      calc 2 * ((∏ t ∈ range n, execMix a b ρ t) * execMix a b ρ n)
          = (2 * ∏ t ∈ range n, execMix a b ρ t) * execMix a b ρ n := by ring
        _ ≤ ((∏ t ∈ range n, max 1 (ρ t)⁻¹) * (seqLik a n + Bh n)) * execMix a b ρ n :=
          mul_le_mul_of_nonneg_right ih (hq n).le
        _ = (∏ t ∈ range n, max 1 (ρ t)⁻¹) * (seqLik a n * a n + Bh n * b n) := by
          rw [mul_assoc, hqn]
        _ ≤ (∏ t ∈ range n, max 1 (ρ t)⁻¹) *
              (max 1 (ρ n)⁻¹ * (seqLik a n * a n + Bh n * (b n * ρ n))) :=
          mul_le_mul_of_nonneg_left step hV
        _ = (∏ t ∈ range n, max 1 (ρ t)⁻¹) * max 1 (ρ n)⁻¹ *
              (seqLik a n * a n + Bh n * (b n * ρ n)) := by ring
  -- `K = U V`, `R ≤ U`, `R⁻¹ ≤ V`, `1 ≤ U`, `1 ≤ V`, with `B̂_n = B_n R`.
  set U := ∏ t ∈ range n, max 1 (ρ t) with hU
  set V := ∏ t ∈ range n, max 1 (ρ t)⁻¹ with hV
  set R := ∏ t ∈ range n, ρ t with hR
  have hK : ∏ t ∈ range n, max (ρ t) (ρ t)⁻¹ = U * V := by
    rw [hU, hV, ← prod_mul_distrib]
    exact prod_congr rfl fun t _ => max_inv_eq_mul (hρ t)
  have hU1 : 1 ≤ U := by
    have := prod_le_prod (s := range n) (f := fun _ => (1 : ℚ)) (g := fun t => max 1 (ρ t))
      (fun _ _ => zero_le_one) fun t _ => hone t
    simpa using this
  have hV1 : 1 ≤ V := by
    have := prod_le_prod (s := range n) (f := fun _ => (1 : ℚ)) (g := fun t => max 1 (ρ t)⁻¹)
      (fun _ _ => zero_le_one) fun t _ => hone' t
    simpa using this
  have hRU : R ≤ U := prod_le_prod (fun t _ => (hρ t).le) fun t _ => le_max_right _ _
  have hRV : R⁻¹ ≤ V := by
    rw [hR, ← prod_inv_distrib]
    exact prod_le_prod (fun t _ => (inv_pos.mpr (hρ t)).le) fun t _ => le_max_right _ _
  have hRpos : 0 < R := prod_pos fun t _ => hρ t
  have hBR : Bh n = seqLik b n * R := by
    simp only [hBh, hR, seqLik, prod_mul_distrib]
  have hA := seqLik_pos ha n
  have hB := seqLik_pos hb n
  have hP : 0 < ∏ t ∈ range n, execMix a b ρ t := prod_pos fun t _ => hq t
  set P := ∏ t ∈ range n, execMix a b ρ t with hPdef
  rw [hK]
  have h1 := hlo n
  have h2 := hhi n
  rw [hBR] at h1 h2
  constructor
  · -- `A + B ≤ V (A + B R) ≤ 2 U V P`.
    have hBle : seqLik b n ≤ V * (seqLik b n * R) := by
      have e : V * (seqLik b n * R) = (R * V) * seqLik b n := by ring
      rw [e]
      have : 1 ≤ R * V := by
        have := mul_le_mul_of_nonneg_left hRV hRpos.le
        rwa [mul_inv_cancel₀ hRpos.ne'] at this
      exact le_mul_of_one_le_left hB.le this
    have hAle : seqLik a n ≤ V * seqLik a n := le_mul_of_one_le_left hA.le hV1
    have hV0 : 0 ≤ V := le_trans zero_le_one hV1
    have := mul_le_mul_of_nonneg_left h1 hV0
    nlinarith
  · -- `2 P ≤ V (A + B R) ≤ U V (A + B)`.
    have hBle : seqLik b n * R ≤ U * seqLik b n := by
      rw [mul_comm U]
      exact mul_le_mul_of_nonneg_left hRU hB.le
    have hAle : seqLik a n ≤ U * seqLik a n := le_mul_of_one_le_left hA.le hU1
    have hV0 : 0 ≤ V := le_trans zero_le_one hV1
    have hsum : seqLik a n + seqLik b n * R ≤ U * (seqLik a n + seqLik b n) := by linarith
    have := mul_le_mul_of_nonneg_left hsum hV0
    nlinarith

end ReceivingFace

section Audit

#print axioms seqLik_eq_zero_of_le
#print axioms seqLik_nonneg
#print axioms fwd_id
#print axioms population_mixture
#print axioms uniformPrior_isPrior
#print axioms survivors_succ
#print axioms survivors_zero
#print axioms survivors_antitone
#print axioms seqLik_emits
#print axioms sum_indicator
#print axioms survivor_code
#print axioms survivors_product
#print axioms seqLik_escaped_survivor
#print axioms escaped_fibre_is_mode
#print axioms survivors_share_one_likelihood
#print axioms exp_mul_log_self
#print axioms exp_sum_mul_log_self
#print axioms partitionInformation_lt_iff
#print axioms death_is_an_exchange
#print axioms certified_inverseCDF_class
#print axioms certified_draw_is_released_at_zero_tolerance
#print axioms plural_draw_is_held
#print axioms ctxLik_succ
#print axioms ctxTotal_pos
#print axioms ctxTotal_succ_same
#print axioms ctxTotal_succ_other
#print axioms localFace_eq
#print axioms ctxTotal_unmet
#print axioms local_telescope
#print axioms local_mixture_code
#print axioms local_of_constant
#print axioms population_mixture_enclosed
#print axioms two_face_skew
#print axioms execRatio_eq
#print axioms executed_face_within_population
#print axioms max_inv_eq_mul
#print axioms executed_mixture_within_population

end Audit

end Holonics.Compression.Landmark.Context.Population

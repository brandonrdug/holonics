import Holonics.Transport.HelicalPairInteraction
import Mathlib.Data.Fintype.Perm

/-!
# Locating keys: navigator inference by loop closure is a fibre that pruning shrinks

[definition] Rebuild step 3 (#145) and ELEMENTARY_OBJECTS "Keys, locks and navigation": the key is
the **initial configuration** of the navigators; a menu is a finite family of observed loops over
pair contacts; each loop, under a candidate key, performs an ordered stage word, conjugated by the
unknown boundary map `S` (the plugboard of the Enigma reading). **Learning is locating keys**: the
candidates consistent with the observations are inferred by loop closure. The closure law is
`Transport/HelicalPairInteraction.menu_loop_closure`: a conjugated loop closes at its port `a`
exactly when the known stage word fixes the boundary image `S a`.

[definition] **The consistent keys are the fibre of the loop-closure map** over the true key's
reading (`fibre`, `truth_mem_fibre`). Joined to the closure law: when every menu loop was observed
closed, that fibre is the Bombe's test set `{(k, S) | ∀ loop, (stages k).prod (S a) = S a}`
(`fibre_eq_bombe`, one rewrite by `menu_loop_closure`).

[proved-derived; formal-checked] What is proved.

1. **Adding a loop can only shrink the fibre** (`fibre_cons`, `fibre_append_subset`): pruning is
   compression of the candidate family, and it never discards the true key. The Bombe reads `S`
   only at the menu's ports (`fibre_depends_only_on_port_images`).
2. **The gauge law.** A gauge of a menu is a relabelling `γ` of the keys with a boundary turn `ρ`
   that conjugates every loop's stage word, `stages (γ k) = ρ⁻¹ (stages k) ρ` elementwise. Then the
   loop-closure reading is gauge invariant (`Gauge.closes_iff`, from `menu_loop_closure` and
   `boundary_conj_list_prod`), so **the fibre is a union of gauge orbits**
   (`fibre_gauge_invariant`, `iterate_mem_fibre_iff`) and **no menu separates the true key from its
   gauge image** (`fibre_gauge_truth`): loop closure locates a key only up to the gauge.
3. **The surviving fibre is one gauge orbit** when the gauge reaches every key from the true key
   and the menu pins the boundary at each key (at most one consistent boundary per key)
   (`fibre_eq_orbit`).

[counterexample; formal-checked] **A reflector machine on three ports** (`Machine`): the stage at
rotor position `m` is the reflected return `R_m = ρ^{-m} F ρ^m` of `menu_loop_closure`'s owner, with
`F = swap 0 1` and `ρ` the one-step rotor. The true key is rotor offset `0` with the identity
boundary. Its stages are covariant under `(k, S) ↦ (k + 1, ρ⁻¹ S)` (`Machine.stage_succ`), which is
therefore a gauge of every menu of its loops (`Machine.rotorGauge`).
- One observed loop leaves `6` of the `18` candidates; a second leaves `3`
  (`Machine.pruning_counts`): strict pruning, witnessed by `(0, swap 0 1)`, which the first loop
  admits and the second refutes (`Machine.second_loop_refutes`).
- The fibre stays plural: `(1, ρ⁻¹)` survives both loops (`Machine.plural_fibre`), and the gauge
  carries the fibre onto itself (`Machine.gauge_invariant`, an instance of the gauge law).
- With two loops the boundary is pinned at each key and the three survivors are exactly the gauge
  orbit of the true key (`Machine.two_loop_fibre_is_one_orbit`). With one loop it is not pinned:
  `(0, swap 0 1)` survives with the true key's offset but lies on no gauge image of the true key
  (`Machine.one_loop_fibre_is_not_one_orbit`), so the pinning hypothesis is load-bearing.
- With the boundary known (`S = 1`), one loop already locates the key: `k = 0`
  (`Machine.known_boundary_locates_key`).
-/

namespace Holonics.Compression.Core.Keys

open Holonics.Transport.HelicalPairInteraction

/-! ## 1. Loops, the closure map and its fibre -/

/-- [definition] **A menu loop**: its boundary port and, for every candidate key (the navigators'
initial configuration), the ordered stage word the machine performs along the loop. -/
structure Loop (Key α : Type*) where
  port : α
  stages : Key → List (Equiv.Perm α)

variable {Key α : Type*}

/-- [definition] The loop closes at a candidate `(key, S)`: the stage word conjugated by the
boundary map returns the port to itself. -/
def Loop.Closes (loop : Loop Key α) (candidate : Key × Equiv.Perm α) : Prop :=
  ((loop.stages candidate.1).map fun C => candidate.2⁻¹ * C * candidate.2).prod loop.port =
    loop.port

instance [DecidableEq α] (loop : Loop Key α) (candidate : Key × Equiv.Perm α) :
    Decidable (loop.Closes candidate) := by
  unfold Loop.Closes; infer_instance

/-- [proved-derived; formal-checked] The closure of one loop is the Bombe's test at the boundary
image (`menu_loop_closure`). -/
theorem Loop.closes_iff (loop : Loop Key α) (candidate : Key × Equiv.Perm α) :
    loop.Closes candidate ↔
      (loop.stages candidate.1).prod (candidate.2 loop.port) = candidate.2 loop.port :=
  menu_loop_closure candidate.2 (loop.stages candidate.1) loop.port

variable [DecidableEq α]

/-- [definition] **The loop-closure map**: a candidate's closure reading on every menu loop. -/
def closureMap (menu : List (Loop Key α)) (candidate : Key × Equiv.Perm α) : List Bool :=
  menu.map fun loop => decide (loop.Closes candidate)

/-- [definition] **The consistent candidates**: the fibre of the loop-closure map over the true
key's reading. -/
def fibre (menu : List (Loop Key α)) (truth : Key × Equiv.Perm α) : Set (Key × Equiv.Perm α) :=
  closureMap menu ⁻¹' {closureMap menu truth}

instance (menu : List (Loop Key α)) (truth : Key × Equiv.Perm α) :
    DecidablePred (· ∈ fibre menu truth) := fun candidate =>
  inferInstanceAs (Decidable (closureMap menu candidate = closureMap menu truth))

/-- [definition] The menu was formed from observed closed loops of the true key. -/
def Observed (menu : List (Loop Key α)) (truth : Key × Equiv.Perm α) : Prop :=
  ∀ loop ∈ menu, loop.Closes truth

/-- [definition] The true key is consistent with every menu (by the fibre's definition). -/
theorem truth_mem_fibre (menu : List (Loop Key α)) (truth : Key × Equiv.Perm α) :
    truth ∈ fibre menu truth := rfl

/-- [definition] **The consistent keys of an observed menu are the Bombe's test set**: the
candidates whose known stage words fix the boundary image of every port. This unfolds `fibre`
and applies `menu_loop_closure` once. -/
theorem fibre_eq_bombe {menu : List (Loop Key α)} {truth : Key × Equiv.Perm α}
    (observed : Observed menu truth) :
    fibre menu truth =
      {candidate | ∀ loop ∈ menu,
        (loop.stages candidate.1).prod (candidate.2 loop.port) = candidate.2 loop.port} := by
  ext candidate
  simp only [fibre, Set.mem_preimage, Set.mem_singleton_iff, closureMap, Set.mem_ofPred_eq,
    List.map_inj_left, decide_eq_decide]
  constructor
  · intro h loop hloop
    exact (loop.closes_iff candidate).mp ((h loop hloop).mpr (observed loop hloop))
  · intro h loop hloop
    exact iff_of_true ((loop.closes_iff candidate).mpr (h loop hloop)) (observed loop hloop)

/-- [proved-derived; formal-checked] **Adding a loop intersects the fibre with one constraint.** -/
theorem fibre_cons (loop : Loop Key α) (menu : List (Loop Key α)) (truth : Key × Equiv.Perm α) :
    fibre (loop :: menu) truth =
      fibre menu truth ∩ {candidate | (loop.Closes candidate ↔ loop.Closes truth)} := by
  ext candidate
  simp only [fibre, closureMap, Set.mem_preimage, Set.mem_singleton_iff, List.map_cons,
    List.cons.injEq, Set.mem_inter_iff, Set.mem_ofPred_eq, decide_eq_decide]
  exact and_comm

/-- [proved-derived; formal-checked] **Adding loops can only shrink the fibre**: pruning. -/
theorem fibre_append_subset (extra menu : List (Loop Key α)) (truth : Key × Equiv.Perm α) :
    fibre (extra ++ menu) truth ⊆ fibre menu truth := by
  induction extra with
  | nil => exact le_rfl
  | cons loop extra ih =>
    rw [List.cons_append, fibre_cons]
    exact Set.inter_subset_left.trans ih

/-- [proved-derived; formal-checked] **The Bombe reads the boundary map only at the menu's ports**:
two boundary maps agreeing on every port have the same consistent keys. -/
theorem fibre_depends_only_on_port_images {menu : List (Loop Key α)}
    {truth : Key × Equiv.Perm α} (observed : Observed menu truth) (key : Key)
    {S S' : Equiv.Perm α} (agree : ∀ loop ∈ menu, S loop.port = S' loop.port) :
    (key, S) ∈ fibre menu truth ↔ (key, S') ∈ fibre menu truth := by
  rw [fibre_eq_bombe observed]
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h loop hloop
    rw [← agree loop hloop]
    exact h loop hloop
  · intro h loop hloop
    rw [agree loop hloop]
    exact h loop hloop


/-! ## 2. The gauge law -/

/-- [definition] **A gauge of a menu**: a relabelling of the keys and a boundary turn `ρ` under
which every loop's stage word is conjugated by `ρ`. -/
structure Gauge (menu : List (Loop Key α)) where
  key : Key → Key
  boundary : Equiv.Perm α
  covariant : ∀ loop ∈ menu, ∀ k, loop.stages (key k) =
    (loop.stages k).map fun C => boundary⁻¹ * C * boundary

namespace Gauge

variable {menu : List (Loop Key α)} (g : Gauge menu)

/-- [definition] The gauge's action on candidates: `(k, S) ↦ (γ k, ρ⁻¹ S)`. -/
def act (candidate : Key × Equiv.Perm α) : Key × Equiv.Perm α :=
  (g.key candidate.1, g.boundary⁻¹ * candidate.2)

omit [DecidableEq α] in
/-- [proved-derived; formal-checked] **Loop closure is gauge invariant**: a menu loop closes at a
gauged candidate exactly when it closes at the candidate (`menu_loop_closure`,
`boundary_conj_list_prod`). -/
theorem closes_iff {loop : Loop Key α} (hloop : loop ∈ menu) (candidate : Key × Equiv.Perm α) :
    loop.Closes (g.act candidate) ↔ loop.Closes candidate := by
  rw [Loop.closes_iff, Loop.closes_iff, act, g.covariant loop hloop, boundary_conj_list_prod]
  simp only [Equiv.Perm.mul_apply]
  rw [show ∀ y, g.boundary (g.boundary⁻¹ y) = y from fun y => by simp]
  exact (g.boundary⁻¹).injective.eq_iff

theorem closureMap_act (candidate : Key × Equiv.Perm α) :
    closureMap menu (g.act candidate) = closureMap menu candidate :=
  List.map_congr_left fun loop hloop => by rw [decide_eq_decide, g.closes_iff hloop]

omit [DecidableEq α] in
theorem iterate_key (n : ℕ) (candidate : Key × Equiv.Perm α) :
    (g.act^[n] candidate).1 = g.key^[n] candidate.1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', act, ih]

end Gauge

/-- [proved-derived; formal-checked] **The fibre is gauge invariant**: a candidate is consistent
exactly when its gauge image is. -/
theorem fibre_gauge_invariant {menu : List (Loop Key α)} (g : Gauge menu)
    (truth candidate : Key × Equiv.Perm α) :
    g.act candidate ∈ fibre menu truth ↔ candidate ∈ fibre menu truth := by
  simp only [fibre, Set.mem_preimage, Set.mem_singleton_iff, g.closureMap_act]

/-- [proved-derived; formal-checked] **The fibre is a union of gauge orbits.** -/
theorem iterate_mem_fibre_iff {menu : List (Loop Key α)} (g : Gauge menu)
    (truth candidate : Key × Equiv.Perm α) (n : ℕ) :
    g.act^[n] candidate ∈ fibre menu truth ↔ candidate ∈ fibre menu truth := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', fibre_gauge_invariant, ih]

/-- [proved-derived; formal-checked] **No menu separates the true key from its gauge image**: the
fibre over the gauged truth is the fibre over the truth. -/
theorem fibre_gauge_truth {menu : List (Loop Key α)} (g : Gauge menu)
    (truth : Key × Equiv.Perm α) : fibre menu (g.act truth) = fibre menu truth := by
  ext candidate
  simp only [fibre, Set.mem_preimage, Set.mem_singleton_iff, g.closureMap_act]

/-- [proved-derived; formal-checked] **The surviving fibre is one gauge orbit** when the gauge
reaches every key from the true key and the menu pins the boundary at each key. -/
theorem fibre_eq_orbit {menu : List (Loop Key α)} (g : Gauge menu) (truth : Key × Equiv.Perm α)
    (reach : ∀ k, ∃ n, g.key^[n] truth.1 = k)
    (pinned : ∀ c ∈ fibre menu truth, ∀ c' ∈ fibre menu truth, c.1 = c'.1 → c = c') :
    fibre menu truth = {c | ∃ n, c = g.act^[n] truth} := by
  ext c
  constructor
  · intro hc
    obtain ⟨n, hn⟩ := reach c.1
    refine ⟨n, pinned c hc _ ((iterate_mem_fibre_iff g truth truth n).mpr
      (truth_mem_fibre menu truth)) ?_⟩
    rw [g.iterate_key, hn]
  · rintro ⟨n, rfl⟩
    exact (iterate_mem_fibre_iff g truth truth n).mpr (truth_mem_fibre menu truth)

/-! ## 3. A reflector machine on three ports -/

namespace Machine

/-- The one-step rotor `i ↦ i + 1`. -/
def rotor : Equiv.Perm (Fin 3) := ⟨fun i => i + 1, fun i => i - 1, by decide, by decide⟩

/-- The reflector: fixed material exchanging ports `0` and `1`. -/
def reflector : Equiv.Perm (Fin 3) := Equiv.swap 0 1

/-- The stage at rotor position `m`: the reflected return through the rotor's producing operand. -/
def stage (m : Fin 3) : Equiv.Perm (Fin 3) := reflectedReturn (rotor ^ m.val) reflector

/-- A one-stage loop at port `a`, reached at step `i` after the key's offset. -/
def loopAt (a i : Fin 3) : Loop (Fin 3) (Fin 3) := ⟨a, fun key => [stage (key + i)]⟩

/-- The true key: rotor offset `0`, identity boundary. -/
def truth : Fin 3 × Equiv.Perm (Fin 3) := (0, 1)

def menu₁ : List (Loop (Fin 3) (Fin 3)) := [loopAt 2 0]
def menu₂ : List (Loop (Fin 3) (Fin 3)) := [loopAt 1 1, loopAt 2 0]

theorem stage_fixed_iff : ∀ m y : Fin 3, stage m y = y ↔ y = 2 - m := by decide

theorem rotor_inv_apply : ∀ y : Fin 3, rotor⁻¹ y = y - 1 := by decide

theorem loopAt_closes_iff (a i : Fin 3) (candidate : Fin 3 × Equiv.Perm (Fin 3)) :
    (loopAt a i).Closes candidate ↔ candidate.2 a = 2 - (candidate.1 + i) := by
  rw [Loop.closes_iff]
  simp only [loopAt, List.prod_cons, List.prod_nil, mul_one]
  exact stage_fixed_iff _ _

theorem observed₂ : Observed menu₂ truth := by
  intro loop hloop
  simp only [menu₂, List.mem_cons, List.not_mem_nil, or_false] at hloop
  rcases hloop with rfl | rfl <;> rw [loopAt_closes_iff] <;> decide

theorem observed₁ : Observed menu₁ truth := fun loop hloop =>
  observed₂ loop (by simp only [menu₁, List.mem_singleton] at hloop; simp [menu₂, hloop])

theorem mem_fibre₁ (candidate : Fin 3 × Equiv.Perm (Fin 3)) :
    candidate ∈ fibre menu₁ truth ↔ candidate.2 2 = 2 - candidate.1 := by
  rw [fibre_eq_bombe observed₁]
  simp only [Set.mem_ofPred_eq, menu₁, List.mem_singleton, forall_eq]
  rw [← Loop.closes_iff, loopAt_closes_iff, add_zero]

theorem mem_fibre₂ (candidate : Fin 3 × Equiv.Perm (Fin 3)) :
    candidate ∈ fibre menu₂ truth ↔
      candidate.2 1 = 2 - (candidate.1 + 1) ∧ candidate.2 2 = 2 - candidate.1 := by
  rw [fibre_eq_bombe observed₂]
  simp only [Set.mem_ofPred_eq, menu₂, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  rw [← Loop.closes_iff, ← Loop.closes_iff, loopAt_closes_iff, loopAt_closes_iff, add_zero]

/-- [counterexample; formal-checked] **Pruning counts.** Of the `18` candidates, one observed loop
leaves `6` and two leave `3`. -/
theorem pruning_counts :
    Fintype.card (Fin 3 × Equiv.Perm (Fin 3)) = 18 ∧
      (Finset.univ.filter fun c : Fin 3 × Equiv.Perm (Fin 3) => c ∈ fibre menu₁ truth).card = 6 ∧
      (Finset.univ.filter fun c : Fin 3 × Equiv.Perm (Fin 3) => c ∈ fibre menu₂ truth).card = 3 := by
  refine ⟨by simp [Fintype.card_perm, Nat.factorial], ?_, ?_⟩
  · simp only [mem_fibre₁]; decide
  · simp only [mem_fibre₂]; decide

/-- [counterexample; formal-checked] **The second loop refutes a candidate the first admits.** -/
theorem second_loop_refutes :
    ((0 : Fin 3), Equiv.swap (0 : Fin 3) 1) ∈ fibre menu₁ truth ∧
      ((0 : Fin 3), Equiv.swap (0 : Fin 3) 1) ∉ fibre menu₂ truth := by
  rw [mem_fibre₁, mem_fibre₂]
  decide

/-- [counterexample; formal-checked] **The fibre stays plural**: a candidate with another key
survives both loops. -/
theorem plural_fibre :
    ((1 : Fin 3), rotor⁻¹) ∈ fibre menu₂ truth ∧ ((1 : Fin 3), rotor⁻¹) ≠ truth := by
  rw [mem_fibre₂]
  refine ⟨by rw [rotor_inv_apply, rotor_inv_apply]; decide, ?_⟩
  intro h
  have := congrArg Prod.fst h
  exact absurd this (by decide)

/-- [proved-derived; formal-checked] The machine's stages are covariant under the rotor:
`R_(m+1) = ρ⁻¹ R_m ρ`. -/
theorem stage_succ : ∀ m : Fin 3, stage (m + 1) = rotor⁻¹ * stage m * rotor := by decide

/-- [definition] **The rotor gauge** `(k, S) ↦ (k + 1, ρ⁻¹ S)` of any menu of the machine's
loops. -/
def rotorGauge (menu : List (Loop (Fin 3) (Fin 3))) (h : ∀ loop ∈ menu, ∃ a i, loop = loopAt a i) :
    Gauge menu where
  key k := k + 1
  boundary := rotor
  covariant loop hloop k := by
    obtain ⟨a, i, rfl⟩ := h loop hloop
    simp only [loopAt, List.map_cons, List.map_nil, add_right_comm k 1 i, stage_succ]

theorem menu₂_loops : ∀ loop ∈ menu₂, ∃ a i, loop = loopAt a i := by
  intro loop hloop
  simp only [menu₂, List.mem_cons, List.not_mem_nil, or_false] at hloop
  rcases hloop with rfl | rfl
  · exact ⟨1, 1, rfl⟩
  · exact ⟨2, 0, rfl⟩

theorem menu₁_loops : ∀ loop ∈ menu₁, ∃ a i, loop = loopAt a i := by
  intro loop hloop
  simp only [menu₁, List.mem_singleton] at hloop
  exact ⟨2, 0, hloop⟩

/-- [proved-derived; formal-checked] **Loop closure locates the key up to a gauge**: advancing the
key one step and turning the boundary back one step carries the fibre onto itself (the gauge law
`fibre_gauge_invariant` at the rotor gauge). -/
theorem gauge_invariant (candidate : Fin 3 × Equiv.Perm (Fin 3)) :
    candidate ∈ fibre menu₂ truth ↔ (candidate.1 + 1, rotor⁻¹ * candidate.2) ∈ fibre menu₂ truth :=
  (fibre_gauge_invariant (rotorGauge menu₂ menu₂_loops) truth candidate).symm

theorem perm_three_ext : ∀ S S' : Equiv.Perm (Fin 3), S 1 = S' 1 → S 2 = S' 2 → S = S' := by
  decide

/-- The rotor's step on keys. -/
def keyStep (k : Fin 3) : Fin 3 := k + 1

theorem keyStep_iterate_three : keyStep^[3] = id := by
  funext k
  revert k
  decide

theorem keyStep_iterate_mod (n : ℕ) : keyStep^[n] = keyStep^[n % 3] := by
  conv_lhs => rw [← Nat.div_add_mod n 3, Function.iterate_add, Function.iterate_mul,
    keyStep_iterate_three, Function.iterate_id, Function.id_comp]

theorem rotorGauge_iterate (menu : List (Loop (Fin 3) (Fin 3)))
    (h : ∀ loop ∈ menu, ∃ a i, loop = loopAt a i) (n : ℕ) :
    (rotorGauge menu h).act^[n] truth = (keyStep^[n] 0, rotor⁻¹ ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    simp only [Gauge.act, rotorGauge, keyStep, pow_succ']

/-- [counterexample; formal-checked] **With two loops the fibre is one gauge orbit**: the boundary
is pinned at each key, and the three survivors are the rotor-gauge images of the true key. -/
theorem two_loop_fibre_is_one_orbit :
    fibre menu₂ truth = {c | ∃ n, c = (rotorGauge menu₂ menu₂_loops).act^[n] truth} := by
  apply fibre_eq_orbit
  · intro k
    refine ⟨k.val, ?_⟩
    change keyStep^[k.val] 0 = k
    revert k
    decide
  · rintro ⟨k, S⟩ hc ⟨k', S'⟩ hc' (hk : k = k')
    subst hk
    rw [mem_fibre₂] at hc hc'
    rw [perm_three_ext S S' (hc.1.trans hc'.1.symm) (hc.2.trans hc'.2.symm)]

theorem rotor_inv_pow_three : rotor⁻¹ ^ 3 = 1 := by decide

/-- [counterexample; formal-checked] **With one loop the fibre is not one orbit.** `(0, swap 0 1)`
is consistent with the first loop and shares the true key's offset, yet it is no rotor-gauge image
of the true key: the boundary is not pinned, and the pinning hypothesis of `fibre_eq_orbit` is
load-bearing. -/
theorem one_loop_fibre_is_not_one_orbit :
    ((0 : Fin 3), Equiv.swap (0 : Fin 3) 1) ∈ fibre menu₁ truth ∧
      ∀ n, (rotorGauge menu₁ menu₁_loops).act^[n] truth ≠
        ((0 : Fin 3), Equiv.swap (0 : Fin 3) 1) := by
  refine ⟨second_loop_refutes.1, fun n h => ?_⟩
  rw [rotorGauge_iterate] at h
  have hpow : rotor⁻¹ ^ n = rotor⁻¹ ^ (n % 3) := by
    conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, rotor_inv_pow_three, one_pow, one_mul]
  rw [hpow, keyStep_iterate_mod] at h
  have hlt : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize n % 3 = r at h hlt
  interval_cases r <;> simp_all <;> revert h <;> decide

/-- [proved-derived; formal-checked] **With the boundary known, one loop locates the key.** -/
theorem known_boundary_locates_key (key : Fin 3) :
    (key, (1 : Equiv.Perm (Fin 3))) ∈ fibre menu₁ truth ↔ key = 0 := by
  rw [mem_fibre₁]
  simp only [Equiv.Perm.coe_one, id_eq]
  revert key
  decide

end Machine

section Audit

#print axioms Loop.closes_iff
#print axioms fibre_eq_bombe
#print axioms fibre_cons
#print axioms fibre_append_subset
#print axioms fibre_depends_only_on_port_images
#print axioms Gauge.closes_iff
#print axioms fibre_gauge_invariant
#print axioms iterate_mem_fibre_iff
#print axioms fibre_gauge_truth
#print axioms fibre_eq_orbit
#print axioms Machine.pruning_counts
#print axioms Machine.second_loop_refutes
#print axioms Machine.plural_fibre
#print axioms Machine.gauge_invariant
#print axioms Machine.two_loop_fibre_is_one_orbit
#print axioms Machine.one_loop_fibre_is_not_one_orbit
#print axioms Machine.known_boundary_locates_key

end Audit

end Holonics.Compression.Core.Keys

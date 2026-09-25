import Holonics.HNN.Moment
import Holonics.Compression.Core.Keys

/-!
# HNN.Keys: keys located by loop closure, the Bombe's diagonal board, and selective stepping

[definition] Rebuild step 4, campaign 1, law 7 (`docs/plans/THE_REBUILD.md`, "Step 4 design",
table (b) row 7; the data → menu map of campaign 1). Each HNN ring is a closing rotor of period
`d`: its rotor `ρ = (· + 1)` on the port chart `ℤ/d`, its declared reflector `F` (an involution) and
its stage at rotor position `m`, the reflected return `R_m = ρ^(−m) F ρ^m`
(`Transport/HelicalPairInteraction.reflectedReturn`). **The key is the ring's initial
configuration** (its clock at the opening of an aeon). A menu edge observed at position `i` says
that the plugboard images satisfy `S p' = R_(key + i) (S p)`. **Learning is locating keys**: the
consistent keys are the fibre of the loop-closure map (`Compression/Core/Keys`).

[proved-derived; formal-checked] What is proved.

1. **The general reflector machine.** `stage_succ` (`R_(m+1) = ρ⁻¹ R_m ρ`, generalizing
   `Keys.Machine.stage_succ` to every period and reflector), so `rotorGauge`
   `(k, S) ↦ (k + 1, ρ⁻¹ S)` is a `Keys.Gauge` of every menu of the ring's one-stage loops
   (generalizing `Keys.Machine.rotorGauge`).
2. **Observed contacts close their loops.** A closed walk of menu edges that the true machine
   produced transports each image back to itself, so the walk's loop closes under the true key
   (`walk_transports`, `contact_menu_closes`, via `menu_loop_closure`): the menu formed from the
   data is `Keys.Observed`.
3. **The field's loop fibre** is the Bombe's test set (`Keys.fibre_eq_bombe`), a union of rotor-gauge
   orbits (`Keys.fibre_gauge_invariant`), and contains a candidate at *every* key
   (`field_loop_fibre`): loop closure locates the key only up to the rotor gauge.
4. **Selective stepping is dormant where no lock fits** (`selective_step_dormant`): rings whose
   locks no cell fits keep their positions and phase classes; one fitting cell moves ring `0`
   (`fitting_cell_moves`); a carry moves a ring no cell fits (`carry_moves_an_unfitted_ring`).
5. **The diagonal board** (addition 7, `propagate`): over a traversal-ordered edge list it returns
   `some f` exactly when `f` is an injective assignment of images on the component's ports with the
   seed image that satisfies every edge (`propagation_eq_edge_fibre`), so such an assignment is
   unique (`consistent_unique`); a full plugboard satisfying every edge is a survivor
   (`permutation_survives`), and every closed walk of edges transports a survivor's image back to
   itself (`survivor_closes_walks`). Witnesses: a conflicting edge and a repeated image refuse.
6. **Gauge fixing.** Each rotor-gauge orbit has exactly one member with `S p₀ = 0`
   (`gauge_fix_unique`).
7. **Re-keying keeps the winding.** Publishing a key at an aeon boundary sets the ring's phase
   class and keeps its winding, and leaves the open moment's counts, offset counts and window
   untouched (`rekey_keeps_winding`).

[open] That the survivors of `propagate` equal the fibre of the component's fundamental-cycle menu
(the converse of `survivor_closes_walks`: a candidate closing every fundamental cycle satisfies
every edge) is not proved here; nor is key location for continuous keys (#62).

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.Keys

open Holonics.Compression.Core.Keys
open Holonics.Transport.HelicalPairInteraction
open Holonics.HNN.Moment

/-! ## 1. The reflector machine of one ring -/

section Machine

variable {d : ℕ} [NeZero d]

/-- [definition] The rotor `ρ = (· + 1)` of a ring of period `d`, on its port chart `ℤ/d`. -/
def rotor (d : ℕ) : Equiv.Perm (ZMod d) := Equiv.addRight 1

omit [NeZero d] in
theorem rotor_pow (k : ℕ) : rotor d ^ k = Equiv.addRight (k : ZMod d) := by
  induction k with
  | zero => ext x; simp
  | succ k ih =>
      ext x
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      simp only [rotor, Equiv.coe_addRight, Nat.cast_succ]
      ring

/-- [definition] **The stage at rotor position `m`**: the reflected return `R_m = ρ^(−m) F ρ^m`
through the rotor's producing operand. -/
def stage (F : Equiv.Perm (ZMod d)) (m : ZMod d) : Equiv.Perm (ZMod d) :=
  reflectedReturn (rotor d ^ m.val) F

theorem stage_eq (F : Equiv.Perm (ZMod d)) (m : ZMod d) :
    stage F m = (Equiv.addRight m)⁻¹ * F * Equiv.addRight m := by
  rw [stage, reflectedReturn, rotor_pow, ZMod.natCast_zmod_val]

/-- [proved-derived; formal-checked] **The stages are rotor-covariant**:
`R_(m+1) = ρ⁻¹ R_m ρ`, for every period and every reflector. -/
theorem stage_succ (F : Equiv.Perm (ZMod d)) (m : ZMod d) :
    stage F (m + 1) = (rotor d)⁻¹ * stage F m * rotor d := by
  have hsplit : (Equiv.addRight (m + 1) : Equiv.Perm (ZMod d)) =
      Equiv.addRight m * rotor d := by
    ext x; simp [rotor, add_assoc, add_comm]
  rw [stage_eq, stage_eq, hsplit, mul_inv_rev]
  group

omit [NeZero d] in
/-- [proved-derived; formal-checked] An involutive reflector gives an involutive stage at every
position (`reflectedReturn_involutive`), so a menu edge can be traversed either way. -/
theorem stage_involutive {F : Equiv.Perm (ZMod d)} (hF : F * F = 1) (m : ZMod d) :
    stage F m * stage F m = 1 :=
  reflectedReturn_involutive _ F hF

/-- [definition] A one-stage menu loop at port `a`, reached `i` positions after the key. -/
def loopAt (F : Equiv.Perm (ZMod d)) (a i : ZMod d) : Loop (ZMod d) (ZMod d) :=
  ⟨a, fun key => [stage F (key + i)]⟩

/-- [definition] **The rotor gauge** `(k, S) ↦ (k + 1, ρ⁻¹ S)` of every menu of one-stage loops. -/
def rotorGauge (F : Equiv.Perm (ZMod d)) (menu : List (Loop (ZMod d) (ZMod d)))
    (h : ∀ loop ∈ menu, ∃ a i, loop = loopAt F a i) : Gauge menu where
  key k := k + 1
  boundary := rotor d
  covariant loop hloop k := by
    obtain ⟨a, i, rfl⟩ := h loop hloop
    simp only [loopAt, List.map_cons, List.map_nil, add_right_comm k 1 i, stage_succ]

/-- [definition] The rotor gauge's action on candidates. -/
def rotorAct (c : ZMod d × Equiv.Perm (ZMod d)) : ZMod d × Equiv.Perm (ZMod d) :=
  (c.1 + 1, (rotor d)⁻¹ * c.2)

theorem rotorGauge_act (F : Equiv.Perm (ZMod d)) (menu : List (Loop (ZMod d) (ZMod d)))
    (h : ∀ loop ∈ menu, ∃ a i, loop = loopAt F a i) :
    (rotorGauge F menu h).act = rotorAct := rfl

omit [NeZero d] in
theorem rotorAct_iterate (n : ℕ) (c : ZMod d × Equiv.Perm (ZMod d)) :
    rotorAct^[n] c = (c.1 + n, (Equiv.addRight (n : ZMod d))⁻¹ * c.2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, rotorAct]
      refine Prod.ext (by simp [add_assoc]) ?_
      simp only [← mul_assoc, ← mul_inv_rev]
      congr 2
      ext x
      simp only [Equiv.Perm.mul_apply, rotor, Equiv.coe_addRight, Nat.cast_succ]
      ring

/-- [proved-derived; formal-checked] **The field's loop fibre (Bombe).** For an observed menu of the
ring's one-stage loops, the consistent candidates are the Bombe's test set; the fibre is a union of
rotor-gauge orbits; and it contains a candidate at every key `k ∈ ℤ/d`. So loop closure alone
locates the key only up to the rotor gauge. -/
theorem field_loop_fibre (F : Equiv.Perm (ZMod d)) (menu : List (Loop (ZMod d) (ZMod d)))
    (h : ∀ loop ∈ menu, ∃ a i, loop = loopAt F a i) (truth : ZMod d × Equiv.Perm (ZMod d))
    (observed : Observed menu truth) :
    fibre menu truth =
        {c | ∀ loop ∈ menu, (loop.stages c.1).prod (c.2 loop.port) = c.2 loop.port} ∧
      (∀ c n, rotorAct^[n] c ∈ fibre menu truth ↔ c ∈ fibre menu truth) ∧
      ∀ k : ZMod d, ∃ S, (k, S) ∈ fibre menu truth := by
  refine ⟨fibre_eq_bombe observed, fun c n => ?_, fun k => ?_⟩
  · rw [← rotorGauge_act F menu h]
    exact iterate_mem_fibre_iff _ truth c n
  · have hmem : rotorAct^[(k - truth.1).val] truth ∈ fibre menu truth := by
      rw [← rotorGauge_act F menu h]
      exact (iterate_mem_fibre_iff _ truth truth _).mpr (truth_mem_fibre menu truth)
    have hkey : (rotorAct^[(k - truth.1).val] truth).1 = k := by
      rw [rotorAct_iterate, ZMod.natCast_zmod_val]; ring
    refine ⟨(rotorAct^[(k - truth.1).val] truth).2, ?_⟩
    have heq : (k, (rotorAct^[(k - truth.1).val] truth).2) =
        rotorAct^[(k - truth.1).val] truth := Prod.ext hkey.symm rfl
    rw [heq]
    exact hmem

/-- [proved-derived; formal-checked] **Gauge fixing is unique.** Each rotor-gauge orbit has exactly
one member whose boundary image of the port `p₀` is `0`: the published convention
`S_g(p₀) = 0` picks one member per orbit. -/
theorem gauge_fix_unique (c : ZMod d × Equiv.Perm (ZMod d)) (p₀ : ZMod d) :
    ∃ n, (rotorAct^[n] c).2 p₀ = 0 ∧
      ∀ m, (rotorAct^[m] c).2 p₀ = 0 → rotorAct^[m] c = rotorAct^[n] c := by
  have hval : ∀ m : ℕ, (rotorAct^[m] c).2 p₀ = c.2 p₀ - m := by
    intro m
    rw [rotorAct_iterate]
    simp [Equiv.Perm.mul_apply, sub_eq_add_neg]
  refine ⟨(c.2 p₀).val, by rw [hval, ZMod.natCast_zmod_val, sub_self], fun m hm => ?_⟩
  rw [hval, sub_eq_zero] at hm
  rw [rotorAct_iterate, rotorAct_iterate, ZMod.natCast_zmod_val, ← hm]

end Machine

/-! ## 2. Observed contacts close their loops -/

section Walks

variable {Key α : Type*}

/-- [definition] **A menu edge**: two ports and a stage per key; it holds at a candidate when the
stage maps the source port's image to the target port's image. -/
structure MenuEdge (Key α : Type*) where
  src : α
  dst : α
  stage : Key → Equiv.Perm α

/-- [definition] The edge holds at a candidate `(key, S)`: `S dst = W_key (S src)`. -/
def MenuEdge.Holds (e : MenuEdge Key α) (c : Key × Equiv.Perm α) : Prop :=
  c.2 e.dst = e.stage c.1 (c.2 e.src)

/-- [definition] The edges chain from port `p` to port `q`. -/
def Chain : α → List (MenuEdge Key α) → α → Prop
  | p, [], q => p = q
  | p, e :: es, q => e.src = p ∧ Chain e.dst es q

/-- [definition] **The loop of a walk**: its port and, per key, its stage word, last edge first. -/
def walkLoop (p : α) (es : List (MenuEdge Key α)) : Loop Key α :=
  ⟨p, fun k => (es.map fun e : MenuEdge Key α => e.stage k).reverse⟩

/-- [proved-derived; formal-checked] **A walk transports images.** Along a chain of edges that
hold at a candidate, the walk's stage word carries the image of the first port to the image of the
last. -/
theorem walk_transports (c : Key × Equiv.Perm α) :
    ∀ {p q : α} (es : List (MenuEdge Key α)), Chain p es q → (∀ e ∈ es, e.Holds c) →
      ((es.map fun e : MenuEdge Key α => e.stage c.1).reverse.prod) (c.2 p) = c.2 q
  | p, q, [], hchain, _ => by simp only [Chain] at hchain; subst hchain; simp
  | p, q, e :: es, hchain, hholds => by
      obtain ⟨hsrc, hrest⟩ := hchain
      have ih := walk_transports c es hrest fun e' he' => hholds e' (List.mem_cons_of_mem e he')
      simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons,
        List.prod_nil, mul_one, Equiv.Perm.mul_apply]
      rw [← hsrc, ← hholds e List.mem_cons_self]
      exact ih

/-- [proved-derived; formal-checked] **Observed contacts close their loops.** When every edge of
the data's menu holds at the true key, each closed walk of those edges, as a loop, closes under the
true key (`Loop.closes_iff`, `menu_loop_closure`): the menu is `Observed`. -/
theorem contact_menu_closes (truth : Key × Equiv.Perm α)
    (walks : List (α × List (MenuEdge Key α)))
    (hclosed : ∀ w ∈ walks, Chain w.1 w.2 w.1) (hholds : ∀ w ∈ walks, ∀ e ∈ w.2, e.Holds truth) :
    Observed (walks.map fun w => walkLoop w.1 w.2) truth := by
  intro loop hloop
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hloop
  rw [Loop.closes_iff]
  exact walk_transports truth w.2 (hclosed w hw) (hholds w hw)

/-- [definition] The ring's menu edge observed at position `i`: the stage is the machine's
reflected return at rotor position `key + i`. -/
def machineEdge {d : ℕ} [NeZero d] (F : Equiv.Perm (ZMod d)) (p q i : ZMod d) :
    MenuEdge (ZMod d) (ZMod d) :=
  ⟨p, q, fun key => stage F (key + i)⟩

/-- [proved-derived; formal-checked] A one-edge closed walk of the machine is its one-stage loop. -/
theorem walkLoop_machineEdge {d : ℕ} [NeZero d] (F : Equiv.Perm (ZMod d)) (a i : ZMod d) :
    walkLoop a [machineEdge F a a i] = loopAt F a i := rfl

end Walks

/-! ## 3. Selective stepping is dormant where no lock fits -/

section Dormant

variable {Cell : Type*} (D : SelectiveDecl Cell)

theorem dormant_step (x : Cell) (τ : ℕ → ℕ) (g : ℕ) (hno : ∀ h ≤ g, ¬ D.Fits h x) :
    ∀ h ≤ g, D.carryIn x τ h = 0 ∧ D.advance x τ h = τ h := by
  intro h hh
  induction h with
  | zero =>
      refine ⟨rfl, ?_⟩
      simp [SelectiveDecl.advance, SelectiveDecl.step, hno 0 hh, SelectiveDecl.carryIn]
  | succ h ih =>
      obtain ⟨hc, _⟩ := ih (by omega)
      have hstep : D.step h x = 0 := by simp [SelectiveDecl.step, hno h (by omega)]
      have hc' : D.carryIn x τ (h + 1) = 0 := by
        simp [SelectiveDecl.carryIn, hstep, hc]
      refine ⟨hc', ?_⟩
      simp [SelectiveDecl.advance, SelectiveDecl.step, hno (h + 1) hh, hc']

/-- [proved-derived; formal-checked] **A ring whose lock no input fits keeps its configuration.**
If no cell fits the locks of rings `0, …, g`, those rings receive no carry and keep their positions,
hence their phase classes: a dormant mode waits for a fitting antecedent. -/
theorem selective_step_dormant (cells : List Cell) (τ : ℕ → ℕ) (g : ℕ)
    (hno : ∀ x ∈ cells, ∀ h ≤ g, ¬ D.Fits h x) :
    ∀ h ≤ g, D.run cells τ h = τ h ∧ D.run cells τ h % D.period h = τ h % D.period h := by
  induction cells generalizing τ with
  | nil => intro h _; exact ⟨rfl, rfl⟩
  | cons x cells ih =>
      intro h hh
      have hrest := ih (D.advance x τ) (fun y hy => hno y (List.mem_cons_of_mem x hy)) h hh
      have hx := (dormant_step D x τ g (hno x List.mem_cons_self) h hh).2
      simp only [SelectiveDecl.run_cons]
      rw [hrest.1, hx]
      exact ⟨rfl, rfl⟩

/-- [proved-derived; formal-checked] One fitting cell moves ring `0` by one tick. -/
theorem fitting_cell_moves (x : Cell) (τ : ℕ → ℕ) (hfit : D.Fits 0 x) :
    D.run [x] τ 0 = τ 0 + 1 := by
  simp [SelectiveDecl.run, SelectiveDecl.advance, SelectiveDecl.step, hfit,
    SelectiveDecl.carryIn]

/-- [counterexample; formal-checked] **The carry is load-bearing.** Ring `1` of `twoRing` has an
empty lock, so no cell fits it, yet one cell moves it by the carry of ring `0`'s wrap: dormancy
needs the earlier rings dormant too. -/
theorem carry_moves_an_unfitted_ring :
    (∀ x, ¬ twoRing.Fits 1 x) ∧ twoRing.run [()] (fun _ => 1) 1 = 2 := by
  refine ⟨fun x h => by simp [SelectiveDecl.Fits, twoRing] at h, ?_⟩
  simp [SelectiveDecl.run, SelectiveDecl.advance, SelectiveDecl.carryIn, SelectiveDecl.step,
    SelectiveDecl.Fits, SelectiveDecl.port, twoRing]

end Dormant

/-! ## 4. The diagonal board: propagation over the menu's edges -/

section Propagation

variable {Key α : Type*} [DecidableEq α] [Fintype α]

/-- [definition] One propagation step at key `k`: the edge's source image must be assigned; its
target is assigned the stage image, refused on a conflict or a repeated image. -/
def propStep (k : Key) (f : α → Option α) (e : MenuEdge Key α) : Option (α → Option α) :=
  match f e.src with
  | none => none
  | some x =>
    match f e.dst with
    | some y => if y = e.stage k x then some f else none
    | none => if ∃ p, f p = some (e.stage k x) then none
        else some (Function.update f e.dst (some (e.stage k x)))

/-- [definition] **Propagation** (the Bombe's diagonal board) from the seed image `s₀` of the seed
port `p₀`, over an edge list, at key `k`. -/
def propagate (k : Key) (p₀ s₀ : α) (es : List (MenuEdge Key α)) : Option (α → Option α) :=
  es.foldl (fun acc e => acc.bind fun f => propStep k f e)
    (some (Function.update (fun _ => none) p₀ (some s₀)))

/-- [definition] The ports the seed and the edges visit. -/
def InPorts (p₀ : α) (es : List (MenuEdge Key α)) (p : α) : Prop :=
  p = p₀ ∨ ∃ e ∈ es, p = e.src ∨ p = e.dst

/-- [definition] The edge list is traversal ordered: each edge's source is the seed or an endpoint
of an earlier edge. -/
def TraversalOrdered (p₀ : α) (es : List (MenuEdge Key α)) : Prop :=
  ∀ pre e suf, es = pre ++ e :: suf → InPorts p₀ pre e.src

/-- [definition] **A consistent assignment**: defined exactly on the visited ports, with the seed
image, satisfying every edge, and injective (a plugboard's images). -/
structure Consistent (k : Key) (p₀ s₀ : α) (es : List (MenuEdge Key α)) (f : α → Option α) :
    Prop where
  dom : ∀ p, (f p).isSome ↔ InPorts p₀ es p
  seed : f p₀ = some s₀
  edges : ∀ e ∈ es, ∃ x, f e.src = some x ∧ f e.dst = some (e.stage k x)
  inj : ∀ p q x, f p = some x → f q = some x → p = q

theorem propagate_append_one (k : Key) (p₀ s₀ : α) (es : List (MenuEdge Key α))
    (e : MenuEdge Key α) :
    propagate k p₀ s₀ (es ++ [e]) = (propagate k p₀ s₀ es).bind fun f => propStep k f e := by
  simp [propagate, List.foldl_append]

omit [DecidableEq α] [Fintype α] in
theorem TraversalOrdered.of_append {p₀ : α} {es : List (MenuEdge Key α)} {e : MenuEdge Key α}
    (h : TraversalOrdered p₀ (es ++ [e])) : TraversalOrdered p₀ es ∧ InPorts p₀ es e.src := by
  refine ⟨fun pre e' suf hsplit => h pre e' (suf ++ [e]) (by rw [hsplit]; simp), ?_⟩
  exact h es e [] rfl

omit [DecidableEq α] [Fintype α] in
theorem inPorts_append_one {p₀ : α} {es : List (MenuEdge Key α)} {e : MenuEdge Key α} {p : α} :
    InPorts p₀ (es ++ [e]) p ↔ InPorts p₀ es p ∨ p = e.src ∨ p = e.dst := by
  simp only [InPorts, List.mem_append, List.mem_singleton]
  constructor
  · rintro (h | ⟨e', he' | rfl, hp⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨e', he', hp⟩)
    · exact Or.inr hp
  · rintro ((h | ⟨e', he', hp⟩) | hp)
    · exact Or.inl h
    · exact Or.inr ⟨e', Or.inl he', hp⟩
    · exact Or.inr ⟨e, Or.inr rfl, hp⟩

omit [Fintype α] in
theorem consistent_nil (k : Key) (p₀ s₀ : α) (f : α → Option α) :
    Consistent k p₀ s₀ [] f ↔ f = Function.update (fun _ => none) p₀ (some s₀) := by
  constructor
  · intro hc
    funext p
    by_cases hp : p = p₀
    · subst hp; rw [hc.seed]; simp
    · rw [Function.update_of_ne hp]
      have := (hc.dom p).not.mpr (by simp [InPorts, hp])
      simpa using this
  · rintro rfl
    refine ⟨fun p => ?_, by simp, by simp, fun p q x hp hq => ?_⟩
    · by_cases hp : p = p₀ <;> simp [InPorts, hp]
    · by_cases hp' : p = p₀ <;> by_cases hq' : q = p₀ <;> simp_all

/-- [proved-derived; formal-checked] **Propagation equals the edge fibre (addition 7).** Over a
traversal-ordered edge list, propagation from the seed image returns `some f` exactly when `f` is a
consistent assignment: defined on the visited ports, with the seed image, satisfying every menu
edge, and injective. The survivors of the diagonal board are exactly the edge-consistent
candidates with injective images; no enumeration of plugboards is needed. -/
theorem propagation_eq_edge_fibre (k : Key) (p₀ s₀ : α) :
    ∀ (es : List (MenuEdge Key α)), TraversalOrdered p₀ es → ∀ f,
      (propagate k p₀ s₀ es = some f ↔ Consistent k p₀ s₀ es f) := by
  intro es
  induction es using List.reverseRecOn with
  | nil =>
      intro _ f
      rw [consistent_nil]
      simp [propagate, eq_comm]
  | append_singleton es e ih =>
      intro hord f'
      obtain ⟨hord', hsrc⟩ := hord.of_append
      rw [propagate_append_one]
      constructor
      · -- soundness
        intro hprop
        obtain ⟨f, hf, hstep⟩ := Option.bind_eq_some_iff.mp hprop
        have hc := (ih hord' f).mp hf
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ((hc.dom e.src).mpr hsrc)
        cases hdst : f e.dst with
        | some y =>
            simp only [propStep, hx, hdst] at hstep
            by_cases hy : y = e.stage k x
            · rw [if_pos hy] at hstep
              cases hstep
              have hdstIn : InPorts p₀ es e.dst := (hc.dom e.dst).mp (by simp [hdst])
              refine ⟨fun p => ?_, hc.seed, fun e' he' => ?_, hc.inj⟩
              · rw [hc.dom p, inPorts_append_one]
                constructor
                · exact Or.inl
                · rintro (h | rfl | rfl)
                  · exact h
                  · exact hsrc
                  · exact hdstIn
              · rcases List.mem_append.mp he' with he' | he'
                · exact hc.edges e' he'
                · rw [List.mem_singleton.mp he']
                  exact ⟨x, hx, by rw [hdst, hy]⟩
            · rw [if_neg hy] at hstep
              exact absurd hstep (by simp)
        | none =>
            simp only [propStep, hx, hdst] at hstep
            by_cases hrep : ∃ p, f p = some (e.stage k x)
            · rw [if_pos hrep] at hstep
              exact absurd hstep (by simp)
            · rw [if_neg hrep] at hstep
              cases hstep
              have hne : ∀ p, InPorts p₀ es p → p ≠ e.dst := fun p hp hpe => by
                have := (hc.dom p).mpr hp
                rw [hpe, hdst] at this
                exact absurd this (by simp)
              refine ⟨fun p => ?_, ?_, fun e' he' => ?_, fun p q y hp hq => ?_⟩
              · rw [inPorts_append_one]
                by_cases hpe : p = e.dst
                · subst hpe; simp
                · rw [Function.update_of_ne hpe, hc.dom p]
                  constructor
                  · exact Or.inl
                  · rintro (h | rfl | h)
                    · exact h
                    · exact hsrc
                    · exact absurd h hpe
              · rw [Function.update_of_ne (hne p₀ (Or.inl rfl)), hc.seed]
              · rcases List.mem_append.mp he' with he' | he'
                · obtain ⟨z, hz1, hz2⟩ := hc.edges e' he'
                  refine ⟨z, ?_, ?_⟩
                  · rw [Function.update_of_ne (hne _ (Or.inr ⟨e', he', Or.inl rfl⟩)), hz1]
                  · rw [Function.update_of_ne (hne _ (Or.inr ⟨e', he', Or.inr rfl⟩)), hz2]
                · rw [List.mem_singleton.mp he']
                  refine ⟨x, ?_, by simp⟩
                  rw [Function.update_of_ne (hne _ hsrc), hx]
              · by_cases hpe : p = e.dst <;> by_cases hqe : q = e.dst
                · rw [hpe, hqe]
                · rw [hpe, Function.update_self] at hp
                  rw [Function.update_of_ne hqe] at hq
                  exact absurd ⟨q, hq.trans hp.symm⟩ hrep
                · rw [hqe, Function.update_self] at hq
                  rw [Function.update_of_ne hpe] at hp
                  exact absurd ⟨p, hp.trans hq.symm⟩ hrep
                · rw [Function.update_of_ne hpe] at hp
                  rw [Function.update_of_ne hqe] at hq
                  exact hc.inj p q y hp hq
      · -- completeness
        intro hc'
        classical
        let f : α → Option α := fun p => if InPorts p₀ es p then f' p else none
        have hfp : ∀ p, InPorts p₀ es p → f p = f' p := fun p hp => by simp [f, hp]
        have hfn : ∀ p, ¬ InPorts p₀ es p → f p = none := fun p hp => by simp [f, hp]
        obtain ⟨x, hx', hdst'⟩ := hc'.edges e (by simp)
        have hout : ∀ p, ¬ InPorts p₀ (es ++ [e]) p → f' p = none := fun p hp => by
          have := (hc'.dom p).not.mpr hp
          simpa using this
        have hdom_f : ∀ p, (f p).isSome ↔ InPorts p₀ es p := by
          intro p
          by_cases hp : InPorts p₀ es p
          · rw [hfp p hp, iff_true_intro hp, iff_true]
            exact (hc'.dom p).mpr (inPorts_append_one.mpr (Or.inl hp))
          · rw [hfn p hp]
            simp [hp]
        have hc : Consistent k p₀ s₀ es f := by
          refine ⟨hdom_f, ?_, fun e' he' => ?_, fun p q y hp hq => ?_⟩
          · rw [hfp p₀ (Or.inl rfl)]
            exact hc'.seed
          · obtain ⟨z, hz1, hz2⟩ := hc'.edges e' (List.mem_append_left _ he')
            refine ⟨z, ?_, ?_⟩
            · rw [hfp _ (Or.inr ⟨e', he', Or.inl rfl⟩)]
              exact hz1
            · rw [hfp _ (Or.inr ⟨e', he', Or.inr rfl⟩)]
              exact hz2
          · have hpin : InPorts p₀ es p := by
              by_contra h; rw [hfn p h] at hp; exact absurd hp (by simp)
            have hqin : InPorts p₀ es q := by
              by_contra h; rw [hfn q h] at hq; exact absurd hq (by simp)
            rw [hfp p hpin] at hp
            rw [hfp q hqin] at hq
            exact hc'.inj p q y hp hq
        rw [(ih hord' f).mpr hc, Option.bind_some]
        have hfx : f e.src = some x := by rw [hfp _ hsrc]; exact hx'
        by_cases hdin : InPorts p₀ es e.dst
        · have hfd : f e.dst = some (e.stage k x) := by rw [hfp _ hdin]; exact hdst'
          simp only [propStep, hfx, hfd, if_true]
          congr 1
          funext p
          by_cases hp : InPorts p₀ es p
          · exact hfp p hp
          · rw [hfn p hp]
            refine (hout p ?_).symm
            rw [inPorts_append_one]
            rintro (h | rfl | rfl)
            · exact hp h
            · exact hp hsrc
            · exact hp hdin
        · have hfd : f e.dst = none := hfn _ hdin
          simp only [propStep, hfx, hfd]
          have hnrep : ¬ ∃ p, f p = some (e.stage k x) := by
            rintro ⟨p, hp⟩
            have hpin : InPorts p₀ es p := by
              by_contra h; rw [hfn p h] at hp; exact absurd hp (by simp)
            rw [hfp p hpin] at hp
            have := hc'.inj p e.dst _ hp hdst'
            exact hdin (this ▸ hpin)
          rw [if_neg hnrep]
          congr 1
          funext p
          by_cases hpe : p = e.dst
          · subst hpe; rw [Function.update_self, hdst']
          · rw [Function.update_of_ne hpe]
            by_cases hp : InPorts p₀ es p
            · exact hfp p hp
            · rw [hfn p hp]
              refine (hout p ?_).symm
              rw [inPorts_append_one]
              rintro (h | rfl | h)
              · exact hp h
              · exact hp hsrc
              · exact hpe h

/-- [proved-derived; formal-checked] The consistent assignment of a traversal-ordered component is
unique: the seed image and the edges determine every image. -/
theorem consistent_unique {k : Key} {p₀ s₀ : α} {es : List (MenuEdge Key α)}
    (hord : TraversalOrdered p₀ es) {f g : α → Option α} (hf : Consistent k p₀ s₀ es f)
    (hg : Consistent k p₀ s₀ es g) : f = g := by
  have h1 := (propagation_eq_edge_fibre k p₀ s₀ es hord f).mpr hf
  have h2 := (propagation_eq_edge_fibre k p₀ s₀ es hord g).mpr hg
  rw [h1] at h2
  exact Option.some.inj h2

/-- [proved-derived; formal-checked] **A plugboard satisfying every edge survives.** Its restriction
to the visited ports is the propagation from its seed image. -/
theorem permutation_survives (k : Key) (p₀ : α) (es : List (MenuEdge Key α))
    (hord : TraversalOrdered p₀ es) (S : Equiv.Perm α) (hholds : ∀ e ∈ es, e.Holds (k, S)) :
    open Classical in
    propagate k p₀ (S p₀) es = some fun p => if InPorts p₀ es p then some (S p) else none := by
  classical
  rw [propagation_eq_edge_fibre k p₀ (S p₀) es hord]
  refine ⟨fun p => ?_, by simp [InPorts], fun e he => ⟨S e.src, ?_, ?_⟩, fun p q x hp hq => ?_⟩
  · by_cases hp : InPorts p₀ es p <;> simp [hp]
  · simp [show InPorts p₀ es e.src from Or.inr ⟨e, he, Or.inl rfl⟩]
  · simp only [show InPorts p₀ es e.dst from Or.inr ⟨e, he, Or.inr rfl⟩, if_true]
    exact congrArg some (hholds e he)
  · by_cases hpin : InPorts p₀ es p <;> by_cases hqin : InPorts p₀ es q <;> simp_all
    exact S.injective (hp.trans hq.symm)

omit [DecidableEq α] [Fintype α] in
/-- [proved-derived; formal-checked] **A survivor closes every walk of the menu.** Along a chain of
menu edges, a consistent assignment carries the image of the first port to the image of the last;
on a closed walk it returns the image to itself (the survivor lies in the Bombe's fibre of every
loop the menu's edges close). -/
theorem survivor_closes_walks {k : Key} {p₀ s₀ : α} {es : List (MenuEdge Key α)}
    {f : α → Option α} (hf : Consistent k p₀ s₀ es f) :
    ∀ {p q : α} (ws : List (MenuEdge Key α)), (∀ e ∈ ws, e ∈ es) → Chain p ws q →
      ∀ x, f p = some x → f q = some ((ws.map fun e : MenuEdge Key α => e.stage k).reverse.prod x)
  | p, q, [], _, hchain, x, hx => by simp only [Chain] at hchain; subst hchain; simpa using hx
  | p, q, e :: ws, hsub, hchain, x, hx => by
      obtain ⟨hsrc, hrest⟩ := hchain
      obtain ⟨z, hz1, hz2⟩ := hf.edges e (hsub e List.mem_cons_self)
      rw [hsrc, hx] at hz1
      cases hz1
      have := survivor_closes_walks hf ws (fun e' he' => hsub e' (List.mem_cons_of_mem e he'))
        hrest _ hz2
      simpa [List.prod_append, Equiv.Perm.mul_apply] using this

end Propagation

/-! ### Witnesses: the diagonal board refuses conflicts and repeated images -/

/-- [definition] The identity stage on `Fin 3`. -/
def idEdge (p q : Fin 3) : MenuEdge Unit (Fin 3) := ⟨p, q, fun _ => 1⟩

/-- [counterexample; formal-checked] **A conflicting cycle refuses.** Edges `0 → 1`, `1 → 2`
(identity stages) then `2 → 0` through the swap `(0 1)`: the cycle does not close, and propagation
from any seed image refuses. -/
theorem conflict_refuses :
    propagate () (0 : Fin 3) 0 [idEdge 0 1, idEdge 1 2, ⟨2, 0, fun _ => Equiv.swap 0 1⟩] = none := by
  decide

/-- [counterexample; formal-checked] **A repeated image refuses.** Two identity edges from port `0`
would give ports `1` and `2` the same image; injectivity (a plugboard) refuses it. -/
theorem repeated_image_refuses :
    propagate () (0 : Fin 3) 0 [idEdge 0 1, idEdge 0 2] = none := by
  decide

/-- [counterexample; formal-checked] A consistent menu survives with its images. -/
theorem consistent_survives :
    (propagate () (0 : Fin 3) 0 [⟨0, 1, fun _ => Equiv.swap 0 1⟩]).isSome = true := by
  decide

/-! ## 5. Re-keying keeps the winding -/

section Rekey

variable {A : Type*} {D : SourceDecl A}

/-- [definition] **Re-keying ring `g` at an aeon boundary**: its phase class is set to the
published key and its winding kept; nothing else changes. -/
def rekey (g key : ℕ) (s : D.StreamState) : D.StreamState :=
  { s with lift := Function.update s.lift g (D.period g * (s.lift g / D.period g) + key) }

/-- [proved-derived; formal-checked] **Re-keying moves only the phase class.** With
`key < d_g`: the ring's winding `⌊λ_g / d_g⌋` is kept and its phase class becomes the key; every
other ring's clock is unchanged; the open moment's counts, offset counts and window are untouched
(publication re-configures and never rewrites the past). -/
theorem rekey_keeps_winding (g key : ℕ) (hkey : key < D.period g) (s : D.StreamState) :
    (rekey g key s).lift g / D.period g = s.lift g / D.period g ∧
      (rekey g key s).lift g % D.period g = key ∧
      (∀ h ≠ g, (rekey g key s).lift h = s.lift h) ∧
      (rekey g key s).bins = s.bins ∧ (rekey g key s).pairBins = s.pairBins ∧
      (rekey g key s).window = s.window := by
  have hd : 0 < D.period g := by omega
  refine ⟨?_, ?_, fun h hh => ?_, rfl, rfl, rfl⟩
  · simp only [rekey, Function.update_self]
    rw [add_comm, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hkey, zero_add]
  · simp only [rekey, Function.update_self]
    rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hkey]
  · simp only [rekey, Function.update_of_ne hh]

end Rekey

section Audit
#print axioms stage_succ
#print axioms field_loop_fibre
#print axioms gauge_fix_unique
#print axioms walk_transports
#print axioms contact_menu_closes
#print axioms selective_step_dormant
#print axioms carry_moves_an_unfitted_ring
#print axioms propagation_eq_edge_fibre
#print axioms consistent_unique
#print axioms permutation_survives
#print axioms survivor_closes_walks
#print axioms conflict_refuses
#print axioms repeated_image_refuses
#print axioms rekey_keeps_winding
end Audit

end Holonics.HNN.Keys

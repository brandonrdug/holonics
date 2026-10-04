import Holonics.HNN.LoadedMedium
import Holonics.HNN.CarriedMotion

/-!
# HNN.LoadedMotion: the resonator's motion released on the loaded blocks

[definition] #62 (owed by `HNN/CarriedMotion` and `HNN/LoadedMedium`: the concrete release of a
resonator's motion on the loaded blocks, stated as `CarriedMotion.releaseMotion` is for channels).
A releasing collapse releases the motion each released locus's material held
(`hnn::word::ReceptionCarry::released`): a released channel's state `[u, w]` and momentum, and a
released resonator's state, phase and momentum. Arrivals and ring storage waves are held by the
declared conductances and admittances and stay.

On the loaded blocks of `HNN/LoadedMedium` a ring block is `(x, (u, w))`. The resonator's phase is
the field's absolute tick read through its operands (`phaseAt P t`), and its momentum `C w` is its
operands applied to its state, so releasing its operands (`resRelease`) and zeroing `(u, w)`
(`loadedReleaseMotion`) releases all three.

[proved-derived; formal-checked] What is proved.

1. **The tick-indexed chain** (`chainEndAt`): each word `(c, τ, n, u)` runs `n` ticks of the family
   at class `c` opened at the field's tick `τ`, from the last word's end plus the source moment `u`.
   Families that agree on every walk edge give chain ends that agree on every observing block
   (`chainAt_agrees_on_walk`) and the same admitted readings of every later word at every epoch
   (`chainAt_release_indistinguishable`). This is `Retention.chain_agrees_on_walk` with the
   operator read at the tick.
2. **The loaded operator agrees on every walk edge** (`loadedOp_agree_on_walk`) when the medium's
   operator does and every resonator whose ring's self-edge is on a walk is kept: off the self-edge
   the load is zero, and on it the load reads only the element edge and the ring's operands.
3. **The loaded motion release agrees on every observing block** (`loadedReleaseMotion_agrees`)
   when the medium part's release does and every released resonator's ring is off every walk.
4. **On the concrete medium** (`loaded_motion_release_indistinguishable`): releasing the channels
   and resonators the continuing rule does not keep, material and motion together, changes no
   admitted reading of any later word of any tick-indexed chain, at any class, pump phase and
   epoch. A resonator is kept with its ring's element (`Diamond::retains(Resonator(g))`), which the
   continuing rule keeps whenever the ring's self-edge is on a walk
   (`LocusMap.retained_of_reads`).

The resonator's momentum held across a deposit is `HNN/LoadedMedium`'s held crossing
(`heldCross_momentum`).

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.LoadedMotion

open Holonics.HNN.Propagation Holonics.HNN.Retention
open Holonics.HNN.TickFamily
open Holonics.HNN.Word Holonics.HNN.TickBlocks Holonics.HNN.LocusMap
open Holonics.HNN.CarriedMotion Holonics.HNN.LoadedMedium
open Holonics.HNN.LoadedRing

universe u

/-! ## 1. The tick-indexed chain -/

section Chain

variable {B : Type*} [Fintype B] {adj : B → B → Prop}
variable {K : Type*} [Field K] {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]
variable {Cls : Type*}

/-- [definition] **The end of a tick-indexed chain**: each word `(c, τ, n, u)` runs `n` ticks of
the family at class `c` opened at the field's tick `τ`, from the last word's end plus the source
moment `u`. -/
def chainEndAt (A : Cls → ℕ → BlockOp K M) :
    ((b : B) → M b) → List (Cls × ℕ × ℕ × ((b : B) → M b)) → (b : B) → M b
  | x, [] => x
  | x, w :: ws => chainEndAt A (trajectoryAt (shiftOp (A w.1) w.2.1) (x + w.2.2.2) w.2.2.1) ws

/-- [proved-derived; formal-checked] **Tick-indexed chains agree on every observing block** when
their families agree on every walk edge, from changes on the reached blocks that agree on the
observing ones. -/
theorem chainAt_agrees_on_walk {A A' : Cls → ℕ → BlockOp K M} (hA : ∀ c k, Sparse adj (A c k))
    (hA' : ∀ c k, Sparse adj (A' c k)) {S R : Set B}
    (hagree : ∀ c k y z, OnWalk adj S R z y → A c k y z = A' c k y z)
    (ws : List (Cls × ℕ × ℕ × ((b : B) → M b))) (hws : ∀ w ∈ ws, SupportedIn w.2.2.2 S)
    {x x' : (b : B) → M b} (hx : SupportedIn x (reachAll adj S))
    (hx' : SupportedIn x' (reachAll adj S)) (hxx : ∀ b, ObservesAll adj R b → x b = x' b) :
    SupportedIn (chainEndAt A x ws) (reachAll adj S) ∧
      SupportedIn (chainEndAt A' x' ws) (reachAll adj S) ∧
      ∀ b, ObservesAll adj R b → chainEndAt A x ws b = chainEndAt A' x' ws b := by
  induction ws generalizing x x' with
  | nil => exact ⟨hx, hx', hxx⟩
  | cons w ws ih =>
    have hu : SupportedIn w.2.2.2 (reachAll adj S) := fun b hb =>
      hws w List.mem_cons_self b fun hbS => hb (subset_reachAll S hbS)
    have hadd : ∀ v : (b : B) → M b, SupportedIn v (reachAll adj S) →
        SupportedIn (v + w.2.2.2) (reachAll adj S) := fun v hv b hb => by
      simp [hv b hb, hu b hb]
    have h := trajectoryAt_agrees_on_walk (fun k => hA w.1 (w.2.1 + k))
      (fun k => hA' w.1 (w.2.1 + k)) (fun k y z hw => hagree w.1 (w.2.1 + k) y z hw)
      (hadd x hx) (hadd x' hx') (fun b hb => by simp [hxx b hb]) w.2.2.1
    exact ih (fun v hv => hws v (List.mem_cons_of_mem _ hv)) h.1 h.2.1 h.2.2

/-- [proved-derived; formal-checked] **Releasing material and motion is indistinguishable along a
tick-indexed chain**: two families that agree on every walk edge, run from a carried change and
its release, give every later word of any chain the same admitted readings at every class, opening
tick and epoch. -/
theorem chainAt_release_indistinguishable {A A' : Cls → ℕ → BlockOp K M}
    (hA : ∀ c k, Sparse adj (A c k)) (hA' : ∀ c k, Sparse adj (A' c k)) {S R : Set B}
    (hagree : ∀ c k y z, OnWalk adj S R z y → A c k y z = A' c k y z)
    {x x' : (b : B) → M b} (hx : SupportedIn x (reachAll adj S))
    (hx' : SupportedIn x' (reachAll adj S)) (hxx : ∀ b, ObservesAll adj R b → x b = x' b)
    (ws : List (Cls × ℕ × ℕ × ((b : B) → M b))) (hws : ∀ w ∈ ws, SupportedIn w.2.2.2 S) (c : Cls)
    (τ : ℕ) {u : (b : B) → M b} (hu : SupportedIn u S) (t : ℕ)
    {g : (b : B) → Module.Dual K (M b)} (hg : SupportedIn g R) :
    pair g (trajectoryAt (shiftOp (A' c) τ) (chainEndAt A' x' ws + u) t) =
      pair g (trajectoryAt (shiftOp (A c) τ) (chainEndAt A x ws + u) t) := by
  have hch := chainAt_agrees_on_walk hA hA' hagree ws hws hx hx' hxx
  have hu' : SupportedIn u (reachAll adj S) := fun b hb =>
    hu b fun hbS => hb (subset_reachAll S hbS)
  have hadd : ∀ v : (b : B) → M b, SupportedIn v (reachAll adj S) →
      SupportedIn (v + u) (reachAll adj S) := fun v hv b hb => by simp [hv b hb, hu' b hb]
  exact (readings_agree_on_walk (fun k => hA c (τ + k)) (fun k => hA' c (τ + k))
    (fun k y z hw => hagree c (τ + k) y z hw) (hadd _ hch.1) (hadd _ hch.2.1)
    (fun b hb => by rw [Pi.add_apply, Pi.add_apply, hch.2.2 b hb]) hg t).symm

end Chain

/-! ## 2. The loaded operator and the motion release on walks -/

section Loaded

variable {Ring Contact : Type u} [DecidableEq Ring] [DecidableEq Contact]
variable {endRing : Contact × Bool → Ring}
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)]

open Classical in
/-- [definition] **The released resonators**: a ring's operands where `keep` holds, zero
elsewhere (`LoadedMedium.loadedLaw`'s release). -/
def resRelease (keep : Ring → Prop) (res : (g : Ring) → ResOp (V g)) (g : Ring) : ResOp (V g) :=
  if keep g then res g else ResOp.zero (V g)

open Classical in
/-- [definition] **The carried motion on the loaded blocks across a releasing collapse**
(`ReceptionCarry::released`): the medium part by the medium's release `rel`, and the resonator's
state `(u, w)` zeroed at every ring whose resonator is released. -/
def loadedReleaseMotion
    (rel : ((b : Ring ⊕ Contact) → BlockM endRing V Ch b) → (b : Ring ⊕ Contact) →
      BlockM endRing V Ch b)
    (keep : Ring → Prop) (x : (b : Ring ⊕ Contact) → LoadedM endRing V Ch b) :
    (b : Ring ⊕ Contact) → LoadedM endRing V Ch b
  | .inl g => (rel (fun b => (x b).1) (.inl g),
      if keep g then (x (.inl g)).2 else (0 : ResState (Contact := Contact) V (.inl g)))
  | .inr a => (rel (fun b => (x b).1) (.inr a), (x (.inr a)).2)

/-- [proved-derived; formal-checked] **The loaded operator agrees on every walk edge** when the
medium's operator does and every resonator whose ring's self-edge is on a walk is kept. -/
theorem loadedOp_agree_on_walk {adj : Ring ⊕ Contact → Ring ⊕ Contact → Prop}
    {S R : Set (Ring ⊕ Contact)}
    {T T' : BlockOp ℝ (BlockM endRing V Ch)} {res res' : (g : Ring) → ResOp (V g)}
    (hT : ∀ y z, OnWalk adj S R z y → T y z = T' y z)
    (hres : ∀ g, OnWalk adj S R (.inl g) (.inl g) → res g = res' g) (h : ℝ) (t : ℕ)
    (y z : Ring ⊕ Contact) (hw : OnWalk adj S R z y) :
    loadedOp T res h t y z = loadedOp T' res' h t y z := by
  have hl : liftOp T y z = liftOp T' y z := by simp only [liftOp, hT y z hw]
  rw [loadedOp, loadedOp, hl]
  congr 1
  by_cases hzy : z = y
  · subst hzy
    rw [diagOp_self, diagOp_self]
    cases z with
    | inl g => simp only [loadCorr, resStep, elemMap, hT _ _ hw, hres g hw]
    | inr a => rfl
  · rw [diagOp_ne _ hzy, diagOp_ne _ hzy]

omit [DecidableEq Ring] [DecidableEq Contact] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ a, NormedAddCommGroup (Ch a)] [∀ a, InnerProductSpace ℝ (Ch a)] in
/-- [proved-derived; formal-checked] **The loaded motion release agrees on every observing block**
when the medium part's release does and every released resonator's ring is off every walk. -/
theorem loadedReleaseMotion_agrees {adj : Ring ⊕ Contact → Ring ⊕ Contact → Prop}
    {S R : Set (Ring ⊕ Contact)}
    {rel : ((b : Ring ⊕ Contact) → BlockM endRing V Ch b) → (b : Ring ⊕ Contact) →
      BlockM endRing V Ch b} {keep : Ring → Prop}
    (hrel : ∀ x b, b ∈ reachAll adj S → ObservesAll adj R b → rel x b = x b)
    (hkeep : ∀ g, (.inl g : Ring ⊕ Contact) ∈ reachAll adj S → ObservesAll adj R (.inl g) → keep g)
    (x : (b : Ring ⊕ Contact) → LoadedM endRing V Ch b) (b : Ring ⊕ Contact)
    (hr : b ∈ reachAll adj S) (ho : ObservesAll adj R b) :
    loadedReleaseMotion rel keep x b = x b := by
  cases b with
  | inl g =>
    simp only [loadedReleaseMotion, if_pos (hkeep g hr ho), hrel _ _ hr ho]
  | inr a =>
    simp only [loadedReleaseMotion, hrel _ _ hr ho]

omit [DecidableEq Ring] [DecidableEq Contact] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ a, InnerProductSpace ℝ (Ch a)] in
/-- The loaded motion release keeps zero blocks zero when the medium part's release does. -/
theorem loadedReleaseMotion_supported {S : Set (Ring ⊕ Contact)}
    {rel : ((b : Ring ⊕ Contact) → BlockM endRing V Ch b) → (b : Ring ⊕ Contact) →
      BlockM endRing V Ch b} {keep : Ring → Prop}
    (hrel : ∀ x : (b : Ring ⊕ Contact) → BlockM endRing V Ch b, SupportedIn x S →
      SupportedIn (rel x) S)
    {x : (b : Ring ⊕ Contact) → LoadedM endRing V Ch b} (hx : SupportedIn x S) :
    SupportedIn (loadedReleaseMotion rel keep x) S := by
  have hx1 : SupportedIn (fun b => (x b).1) S := fun b hb => by simp [hx b hb]
  intro b hb
  cases b with
  | inl g =>
    simp only [loadedReleaseMotion, hrel _ hx1 _ hb, hx _ hb]
    split_ifs <;> rfl
  | inr a =>
    simp only [loadedReleaseMotion, hrel _ hx1 _ hb, hx _ hb]
    rfl

end Loaded

/-! ## 3. The concrete medium loaded -/

section Concrete

variable {Ring Contact ρ : Type u} [Fintype Ring] [DecidableEq Ring] [Fintype Contact]
  [DecidableEq Contact] [Fintype ρ]
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ r, FiniteDimensional ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)] [∀ a, FiniteDimensional ℝ (Ch a)]
variable {endRing : Contact × Bool → Ring}

/-- [definition] **The concrete medium loaded**: at the sheet classes `c` and the field's tick
`t`, the medium's tick operator with every ring's element edge loaded by its resonator at the
phase `t mod P_g`. -/
def loadedFamily (μ : Medium endRing V Ch ρ) (res : (g : Ring) → ResOp (V g)) (h : ℝ) :
    (Ring → ρ → ℝ) → ℕ → BlockOp ℝ (LoadedM endRing V Ch) :=
  fun c t => loadedOp (readOp mediumOp c (fun _ _ => μ)) res h t

theorem loadedFamily_sparse (μ : Medium endRing V Ch ρ) (res : (g : Ring) → ResOp (V g)) (h : ℝ)
    (c : Ring → ρ → ℝ) (t : ℕ) : Sparse (blockAdj endRing) (loadedFamily μ res h c t) :=
  loadedOp_sparse blockAdj_refl (sparse_readOp (lociSparse_uniform μ) c) res h t

omit [DecidableEq Ring] [DecidableEq Contact] in
/-- [proved-derived; formal-checked] **A ring whose self-edge is on a walk keeps its element**
under the continuing rule, hence its resonator (`Diamond::retains(Resonator(g))`). -/
theorem element_retained_of_walk {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) {g : Ring}
    (hw : OnWalk (blockAdj endRing) S R (.inl g) (.inl g)) :
    Retained endRing S R (2 * Fintype.card (Ring ⊕ Contact)) (.element g) :=
  retained_of_reads hS hR (ℓ := .element g) ⟨rfl, rfl⟩
    ((inDiamond_continuing_iff (adj := blockAdj endRing) S R _ _).mpr hw)

set_option hygiene false in
/-- The continuing rule at `e_last = 2|B|`, at the sources `S` and receivers `R` in scope. -/
local notation "RET" => Retained endRing S R (2 * Fintype.card (Ring ⊕ Contact))

/-- [proved-derived; formal-checked] **The carried motion released with its material is
indistinguishable on the loaded medium** (#62; `ReceptionCarry::released`, `Reference::close_aeon`).
From any carried change on the blocks the sources reach, releasing the channels the continuing rule
does not keep (`LocusMap.release`) and the resonators whose ring's element it does not keep
(`resRelease`), together with the motion they held (`releaseMotion` on the medium part, the
resonator's `(u, w)` zeroed), then running any tick-indexed chain of later words each opened on the
last one's end plus a source moment, changes no admitted reading of any later word at any class,
pump phase and epoch. Arrivals and ring storage waves stay. -/
theorem loaded_motion_release_indistinguishable {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible)
    {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) (res : (g : Ring) → ResOp (V g)) (h : ℝ)
    {x : (b : Ring ⊕ Contact) → LoadedM endRing V Ch b}
    (hx : SupportedIn x (reachAll (blockAdj endRing) S))
    (ws : List ((Ring → ρ → ℝ) × ℕ × ℕ × ((b : Ring ⊕ Contact) → LoadedM endRing V Ch b)))
    (hws : ∀ w ∈ ws, SupportedIn w.2.2.2 S) (c : Ring → ρ → ℝ) (τ : ℕ)
    {u : (b : Ring ⊕ Contact) → LoadedM endRing V Ch b} (hu : SupportedIn u S) (t : ℕ)
    {g : (b : Ring ⊕ Contact) → Module.Dual ℝ (LoadedM endRing V Ch b)} (hg : SupportedIn g R) :
    pair g (trajectoryAt
        (shiftOp (loadedFamily (release RET μ) (resRelease (fun r => RET (.element r)) res) h c) τ)
        (chainEndAt (loadedFamily (release RET μ) (resRelease (fun r => RET (.element r)) res) h)
          (loadedReleaseMotion (releaseMotion RET) (fun r => RET (.element r)) x) ws + u) t) =
      pair g (trajectoryAt (shiftOp (loadedFamily μ res h c) τ)
        (chainEndAt (loadedFamily μ res h) x ws + u) t) := by
  have hx' := loadedReleaseMotion_supported (rel := releaseMotion RET)
    (keep := fun r => RET (.element r)) (fun _ hv => releaseMotion_supported hv) hx
  have hwalk := loadedReleaseMotion_agrees (rel := releaseMotion RET)
    (keep := fun r => RET (.element r))
    (fun v b hr ho => releaseMotion_agrees hS hR (fun _ h => h) v b hr ho)
    (fun r hr ho => element_retained_of_walk hS hR ⟨hr, ho⟩) x
  refine chainAt_release_indistinguishable (loadedFamily_sparse _ _ _) (loadedFamily_sparse _ _ _)
    (fun c k y z hw => ?_) hx hx' (fun b hb => (motion_release_agrees hx hx' hwalk b hb).symm)
    ws hws c τ hu t hg
  refine loadedOp_agree_on_walk (fun y z hw => (mediumOp_release_on_walk hμ hS hR c y z hw).symm)
    (fun r hw => ?_) h k y z hw
  simp only [resRelease, if_pos (element_retained_of_walk hS hR hw)]

end Concrete

end Holonics.HNN.LoadedMotion

#print axioms Holonics.HNN.LoadedMotion.chainAt_agrees_on_walk
#print axioms Holonics.HNN.LoadedMotion.chainAt_release_indistinguishable
#print axioms Holonics.HNN.LoadedMotion.loadedOp_agree_on_walk
#print axioms Holonics.HNN.LoadedMotion.loadedReleaseMotion_agrees
#print axioms Holonics.HNN.LoadedMotion.loadedReleaseMotion_supported
#print axioms Holonics.HNN.LoadedMotion.loadedFamily_sparse
#print axioms Holonics.HNN.LoadedMotion.element_retained_of_walk
#print axioms Holonics.HNN.LoadedMotion.loaded_motion_release_indistinguishable

import Holonics.Foundation.Standing
import Holonics.Foundation.ReceiverQuotient
import Holonics.Foundation.GeneratorModeQuotient
import Holonics.Objects.Pairing
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Exact.Basic

/-!
# The face map of a navigator against terrain: kernel, cokernel and the exact sequence

[definition] Rebuild step 3 (#145), the line *compression is intelligence is navigation*
(`docs/plans/THE_REBUILD.md`). Terrain is a configuration space `X`; the navigator family acts on
it by linear transports `T_g`, composed along ordered words (`Foundation/TransportWord`,
right-to-left); an admitted receiver family reads faces `ρ : X → V`. The **face map** sends a
terrain configuration to its complete joint future face:

```text
F : X → (Receiver × Navigator* → V),     F x (ρ, w) = ρ(T_w x)
```

This is the additive causal signature of `Foundation/Standing.causalSignature`. Nothing here founds
a second kernel, quotient or retention: the kernel is `Foundation/CausalRelevance.futureCollapsed`,
the quotient's lawfulness is `Foundation/Standing.standingLaw_exists_iff_future_factors`, and the
cocycle reading of the cokernel is `Objects/Pairing.annihilates_range_iff_mem_dualAnnihilator`.

[proved-standard; formal-checked] **Kernel.** `ker F` is exactly the relevance kernel
(`ker_faceMap_eq_relevanceKernel`): the kernel of a product map is the meet of the kernels of its
components, read as `CausalRelevance.futureCollapsed`, the differences no admitted future receiver
distinguishes after any word.

[proved-derived; formal-checked] What is proved beyond the definitions.

1. **Retention.** The quotient `X ⧸ ker F` carries a lawful retention (`Standing.StandingLaw`), and
   every lawful retention (any retention map, linear or not) is at least as fine: the kernel
   quotient is the coarsest future-sufficient retention (`kernelQuotient_is_coarsest_retention`),
   and its classes are exactly future agreement (`kernelQuotient_eq_iff_futureAgreement`). It is a
   receiver-exact quotient of the complete future family (`kernelReceiverQuotient`,
   `Foundation/ReceiverQuotient`), and every navigator descends to it, so the navigator runs on
   retention (`kernelHistoryCompression`, `kernelClass_after_word`,
   `Foundation/ReceiverHistoryCompression`). A mode dependent at the future receiver differs from
   its elimination by a kernel element, and the elimination changes no future face
   (`redundant_mode_in_kernel`, `eliminated_mode_same_future`, `Foundation/GeneratorModeQuotient`).
2. **Finitely many observations read the kernel.** The horizon-`n` blind subspaces decrease, and
   once two consecutive ones agree they agree forever (`horizonBlind_stable_forever`). In finite
   dimension this happens by `n = dim X − 1`: either the present receivers are blind to all of `X`
   and the chain is stable at `0`, or each strict step lowers `dim H_n` from at most `dim X − 1`
   (`exists_stable_le_finrank_pred`). So words of length at most `dim X − 1` already read the whole
   relevance kernel, for any family of noncommuting navigators
   (`horizonBlind_finrank_pred_eq_ker`, `horizonBlind_eq_ker_of_le`,
   `ker_horizonFaceMap_finrank_pred_eq_relevanceKernel`). This generalizes the single-navigator
   Cayley–Hamilton horizon `Objects/RelativeCompleteness.observabilityKernel_eq_horizonKernel_finrank`
   (words of length `< dim X`) by a stabilization count instead of a characteristic polynomial.
3. **The ledger.** For the finite face map `F_N` (finite receivers and navigators, words of length
   at most `N`): `rank + dim ker = dim X` (`rank_nullity_ledger`), the face space has dimension
   `#requests · dim V` (`finrank_faces`), and the cokernel has dimension `dim faces − rank`
   (`cokernel_ledger`). The cokernel is horizon-relative: it is stated with its horizon `N` and its
   declared request set.
4. **Reachability.** A face is reached by the navigator's image exactly when its cokernel class is
   zero, exactly when every cocycle (a coholon annihilating the image) vanishes on it
   (`reachable_iff_cokernelClass_zero`, `reachable_iff_cocycles_vanish`, over
   `Objects/Pairing`).

[proved-standard; formal-checked] `0 → ker F → X → faces → coker F → 0` is exact
(`exact_sequence`), as for every linear map (Mathlib).

[counterexample; formal-checked] **The ramp** (`Ramp`): terrain `(a, b, c)`, one navigator
`(a, b, c) ↦ (a + b, b, c)`, one receiver reading `a`. After `n` steps the face is `a + n b`.
- `c` is released: it spans the relevance kernel (`Ramp.relevanceKernel_eq_span`), and
  `(0, 0, 0)`, `(0, 0, 1)` share one retained class (`Ramp.released_pair_one_class`).
- `b` is dormant: blind now and seen after one step, so the present-blind subgroup is strictly
  larger than the kernel (`Ramp.dormant_direction_not_released`).
- At horizon `3` the ledger reads `rank 2 + ker 1 = 3`, faces `4`, cokernel `2` (`Ramp.ledger`).
- The face `(0, 0, 0, 1)` on the four words is unreachable: its cokernel class is not zero
  (`Ramp.unreachable_face`). It is residual that must be emanated or retained.

[counterexample; formal-checked] **The bound `dim X − 1` is attained** (`Shift.horizon_sharp`):
for the shift `(a, b, c) ↦ (b, c, 0)` read at `a`, `(0, 0, 1)` is blind to every word of length at
most `1 = dim X − 2`, yet the word of length `2` reads it.

[definition] Integral (ℤ-module) face maps, where a class may be reachable only in a multiple, are
joined in `HolonicsResearch/Landmarks/IntegralCokernel` (`reachableOnlyInMultiple_iff`: reachable
only in the multiple `m` exactly when the cokernel class is nonzero `m`-torsion; over ℤ the cocycle
test above fails and torsion coefficients are needed), over `Foundation/LatticeTransport` and
`HolonicsResearch/Millennium/CokernelCalculus`.
-/

namespace Holonics.Compression.Core.FaceMap

open Holonics.Millennium.Chronology
open Holonics.Millennium.Receiver
open Holonics.Foundation.CausalRelevance
open Holonics.Foundation.CausalRelevance.NonLinear
open Holonics.Foundation.Standing
open Holonics.Objects.Pairing

universe u

section Linear

variable {K : Type*} [Field K]
variable {Navigator Receiver X V : Type u}
  [AddCommGroup X] [Module K X] [AddCommGroup V] [Module K V]
  (read : Receiver → X →ₗ[K] V) (transport : Navigator → X →ₗ[K] X)

/-! ## 1. The face map -/

/-- [definition] The linear transport of an ordered navigator word, read right to left as in
`transportWord`: the last letter acts first. -/
def wordMap : List Navigator → X →ₗ[K] X
  | [] => LinearMap.id
  | g :: w => transport g ∘ₗ wordMap w

theorem wordMap_apply (w : List Navigator) (x : X) :
    wordMap transport w x = transportWord (fun g y => transport g y) w x := by
  induction w with
  | nil => rfl
  | cons g w ih => simp [wordMap, ih]

theorem wordMap_append_singleton (w : List Navigator) (g : Navigator) (x : X) :
    wordMap transport (w ++ [g]) x = wordMap transport w (transport g x) := by
  induction w with
  | nil => rfl
  | cons h w ih => simp only [List.cons_append, wordMap, LinearMap.comp_apply, ih]

/-- [definition] **The face map** of the navigator family against the terrain: every admitted
receiver's reading after every ordered navigator word. -/
def faceMap : X →ₗ[K] (Receiver × List Navigator → V) :=
  LinearMap.pi fun request => read request.1 ∘ₗ wordMap transport request.2

theorem faceMap_apply (x : X) (request : Receiver × List Navigator) :
    faceMap read transport x request =
      read request.1 (transportWord (fun g y => transport g y) request.2 x) := by
  simp [faceMap, wordMap_apply]

/-- [proved-derived; formal-checked] The face map is the causal signature of `Standing`. -/
theorem causalSignature_eq_faceMap (x : X) :
    causalSignature (fun r y => read r y) (fun g y => transport g y) x =
      faceMap read transport x := by
  funext request
  simp [causalSignature, faceMap_apply]

/-! ## 2. The kernel is the relevance kernel, and its quotient is retention -/

/-- [proved-standard; formal-checked] **The kernel of the face map is the relevance kernel** of
`CausalRelevance`: the kernel of a product map is the meet of its components' kernels, which is
the set of differences invisible to every admitted receiver after every word. -/
theorem ker_faceMap_eq_relevanceKernel :
    (LinearMap.ker (faceMap read transport)).toAddSubgroup =
      futureCollapsed (fun r => (read r).toAddMonoidHom) (fun g => (transport g).toAddMonoidHom) := by
  ext x
  rw [mem_futureCollapsed_iff]
  simp only [Submodule.mem_toAddSubgroup, LinearMap.mem_ker]
  constructor
  · intro h r w
    have := congrFun h (r, w)
    simpa [faceMap_apply] using this
  · intro h
    funext request
    simpa [faceMap_apply] using h request.1 request.2

/-- [proved-derived; formal-checked] Two configurations have one kernel class exactly when they
agree at every admitted receiver after every word (`CausalRelevance.futureAgreement`). -/
theorem kernelQuotient_eq_iff_futureAgreement (left right : X) :
    (LinearMap.ker (faceMap read transport)).mkQ left =
        (LinearMap.ker (faceMap read transport)).mkQ right ↔
      futureAgreement (fun r y => read r y) (fun g y => transport g y) left right := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, LinearMap.sub_mem_ker_iff,
    ← causalSignature_eq_iff_futureAgreement, causalSignature_eq_faceMap,
    causalSignature_eq_faceMap]

/-- [proved-derived; formal-checked] **Quotienting by the kernel is retention, and it is the
coarsest retention.** The kernel quotient carries a lawful `StandingLaw` (every admitted future
observation factors through it), and every lawful retention, by any retention map whatever,
separates at least what the kernel quotient separates. -/
theorem kernelQuotient_is_coarsest_retention :
    (∃ L : StandingLaw Navigator Receiver X (X ⧸ LinearMap.ker (faceMap read transport)) V,
        L.transport = (fun g y => transport g y) ∧ L.observe = (fun r y => read r y) ∧
          L.retain = (LinearMap.ker (faceMap read transport)).mkQ) ∧
      ∀ {Retained : Type u} (retain : X → Retained),
        (∃ L : StandingLaw Navigator Receiver X Retained V,
            L.transport = (fun g y => transport g y) ∧ L.observe = (fun r y => read r y) ∧
              L.retain = retain) →
          ∀ left right, retain left = retain right →
            (LinearMap.ker (faceMap read transport)).mkQ left =
              (LinearMap.ker (faceMap read transport)).mkQ right := by
  constructor
  · apply (standingLaw_exists_iff_future_factors _ _ _).mpr
    intro left right h
    rw [kernelQuotient_eq_iff_futureAgreement] at h
    exact (causalSignature_eq_iff_futureAgreement _ _ _ _).mpr h
  · intro Retained retain hL left right h
    rw [kernelQuotient_eq_iff_futureAgreement]
    exact (causalSignature_eq_iff_futureAgreement _ _ _ _).mp
      ((standingLaw_exists_iff_future_factors _ _ retain).mp hL left right h)

/-- [definition] **The kernel quotient as a receiver-exact quotient** (`ReceiverQuotient`) of the
complete future receiver family: every future face factors through the kernel class. -/
def kernelReceiverQuotient :
    Holonics.Foundation.ReceiverCompression.ReceiverQuotient (Receiver × List Navigator) X
      (X ⧸ LinearMap.ker (faceMap read transport)) V where
  quotient := (LinearMap.ker (faceMap read transport)).mkQ
  receiver := fun request x => faceMap read transport x request
  factor := fun request => (LinearMap.ker (faceMap read transport)).liftQ
    (LinearMap.proj request ∘ₗ faceMap read transport) (fun x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [LinearMap.comp_apply, hx]
      rfl)
  exact := fun _ _ => rfl

/-- [proved-derived; formal-checked] **The relevance kernel is carried by every navigator**: the
face after `g` is the face of the word extended by `g`. -/
theorem ker_faceMap_invariant (g : Navigator) :
    LinearMap.ker (faceMap read transport) ≤
      (LinearMap.ker (faceMap read transport)).comap (transport g) := by
  intro x hx
  rw [Submodule.mem_comap, LinearMap.mem_ker]
  rw [LinearMap.mem_ker] at hx
  funext request
  have := congrFun hx (request.1, request.2 ++ [g])
  rw [faceMap_apply, ← wordMap_apply, wordMap_append_singleton, wordMap_apply] at this
  rw [faceMap_apply]
  exact this

/-- [definition] A navigator descended to the retained quotient. -/
def descendedNavigator (g : Navigator) :
    (X ⧸ LinearMap.ker (faceMap read transport)) →ₗ[K]
      (X ⧸ LinearMap.ker (faceMap read transport)) :=
  (LinearMap.ker (faceMap read transport)).mapQ (LinearMap.ker (faceMap read transport))
    (transport g) (ker_faceMap_invariant read transport g)

/-- [definition] **Retention carries the navigators** (`ReceiverHistoryCompression`): the present
receivers factor through the kernel quotient, and every navigator descends to it. -/
def kernelHistoryCompression :
    Holonics.Millennium.LineageCompression.ReceiverHistoryCompression Navigator Receiver X
      (X ⧸ LinearMap.ker (faceMap read transport)) V where
  present :=
    { quotient := (LinearMap.ker (faceMap read transport)).mkQ
      receiver := fun r x => read r x
      factor := fun r => (LinearMap.ker (faceMap read transport)).liftQ (read r) (fun x hx => by
        rw [LinearMap.mem_ker] at hx ⊢
        have := congrFun hx (r, [])
        rw [faceMap_apply] at this
        exact this)
      exact := fun _ _ => rfl }
  sourceTransport := fun g x => transport g x
  quotientTransport := fun g q => descendedNavigator read transport g q
  generatorExact := fun _ _ => rfl

/-- [proved-derived; formal-checked] **The navigator runs on retention**: the kernel class of the
configuration after any ordered word is the descended word applied to the kernel class
(`ReceiverHistoryCompression.quotientCommutesWithEveryOrderedWord`). -/
theorem kernelClass_after_word (w : List Navigator) (x : X) :
    (LinearMap.ker (faceMap read transport)).mkQ
        (transportWord (fun g y => transport g y) w x) =
      transportWord (fun g q => descendedNavigator read transport g q) w
        ((LinearMap.ker (faceMap read transport)).mkQ x) :=
  (kernelHistoryCompression read transport).quotientCommutesWithEveryOrderedWord w x

/-! ## 3. Finitely many observations read the kernel -/

/-- [definition] The horizon-`n` blind subspace: blind to every receiver after every word of length
at most `n`. Recursively, blind now and carried by every navigator into the horizon-`n` blind
subspace. -/
def horizonBlind : ℕ → Submodule K X
  | 0 => ⨅ r, LinearMap.ker (read r)
  | n + 1 => (⨅ r, LinearMap.ker (read r)) ⊓ ⨅ g, (horizonBlind n).comap (transport g)

theorem horizonBlind_succ (n : ℕ) :
    horizonBlind read transport (n + 1) =
      horizonBlind read transport 0 ⊓
        ⨅ g, (horizonBlind read transport n).comap (transport g) := rfl

theorem mem_horizonBlind_zero (x : X) :
    x ∈ horizonBlind read transport 0 ↔ ∀ r, read r x = 0 := by
  simp [horizonBlind, Submodule.mem_iInf]

/-- [proved-derived; formal-checked] The horizon-`n` blind subspace is exactly the configurations
no receiver reads after any word of length at most `n`. -/
theorem mem_horizonBlind_iff (n : ℕ) (x : X) :
    x ∈ horizonBlind read transport n ↔
      ∀ r (w : List Navigator), w.length ≤ n → read r (wordMap transport w x) = 0 := by
  induction n generalizing x with
  | zero =>
    rw [mem_horizonBlind_zero]
    constructor
    · intro h r w hw
      rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hw)]
      exact h r
    · intro h r
      exact h r [] le_rfl
  | succ n ih =>
    rw [horizonBlind_succ, Submodule.mem_inf, mem_horizonBlind_zero, Submodule.mem_iInf]
    simp only [Submodule.mem_comap, ih]
    constructor
    · rintro ⟨hnow, hlater⟩ r w hw
      rcases List.eq_nil_or_concat w with rfl | ⟨w', g, rfl⟩
      · exact hnow r
      · rw [List.concat_eq_append, wordMap_append_singleton]
        rw [List.length_concat] at hw
        exact hlater g r w' (by omega)
    · intro h
      refine ⟨fun r => h r [] (Nat.zero_le _), fun g r w hw => ?_⟩
      rw [← wordMap_append_singleton]
      exact h r (w ++ [g]) (by rw [List.length_append, List.length_singleton]; omega)

theorem horizonBlind_succ_le (n : ℕ) :
    horizonBlind read transport (n + 1) ≤ horizonBlind read transport n := by
  intro x hx
  rw [mem_horizonBlind_iff] at hx ⊢
  exact fun r w hw => hx r w (by omega)

theorem horizonBlind_antitone {m n : ℕ} (h : m ≤ n) :
    horizonBlind read transport n ≤ horizonBlind read transport m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (horizonBlind_succ_le read transport _).trans ih

/-- [proved-derived; formal-checked] **Once two consecutive horizons agree, they agree forever.** -/
theorem horizonBlind_stable_forever {n : ℕ}
    (h : horizonBlind read transport n = horizonBlind read transport (n + 1)) (j : ℕ) :
    horizonBlind read transport n = horizonBlind read transport (n + j) := by
  have step : ∀ j, horizonBlind read transport (n + j) =
      horizonBlind read transport (n + j + 1) := by
    intro j
    induction j with
    | zero => simpa using h
    | succ j ih =>
      rw [show n + (j + 1) = n + j + 1 by omega, horizonBlind_succ read transport (n + j + 1),
        ← ih, ← horizonBlind_succ]
      exact ih
  induction j with
  | zero => rfl
  | succ j ih => rw [ih, step j]; rfl

/-- [proved-derived; formal-checked] The full face map's kernel is the meet of all horizons. -/
theorem ker_faceMap_eq_iInf_horizonBlind :
    LinearMap.ker (faceMap read transport) = ⨅ n, horizonBlind read transport n := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_iInf, mem_horizonBlind_iff]
  constructor
  · intro h n r w _
    have := congrFun h (r, w)
    simpa [faceMap_apply, wordMap_apply] using this
  · intro h
    funext request
    have := h request.2.length request.1 request.2 le_rfl
    simpa [faceMap_apply, wordMap_apply] using this

/-- [proved-derived; formal-checked] A stable horizon reads the whole kernel: if `H_m = H_(m+1)`,
then `ker F = H_m`. -/
theorem ker_faceMap_eq_of_stable {m : ℕ}
    (h : horizonBlind read transport m = horizonBlind read transport (m + 1)) :
    LinearMap.ker (faceMap read transport) = horizonBlind read transport m := by
  have forever := horizonBlind_stable_forever read transport h
  rw [ker_faceMap_eq_iInf_horizonBlind]
  apply le_antisymm
  · exact iInf_le _ _
  · apply le_iInf
    intro n
    by_cases hn : n ≤ m
    · exact horizonBlind_antitone read transport hn
    · rw [forever (n - m), show m + (n - m) = n by omega]

/-- [proved-derived; formal-checked] **In finite dimension the horizons stabilize by
`dim X − 1`.** If the present receivers are blind to all of `X`, the chain is stable at `0`;
otherwise `dim H_0 ≤ dim X − 1` and each strict step lowers the dimension by at least one. -/
theorem exists_stable_le_finrank_pred [FiniteDimensional K X] :
    ∃ m ≤ Module.finrank K X - 1,
      horizonBlind read transport m = horizonBlind read transport (m + 1) := by
  by_cases htop : horizonBlind read transport 0 = ⊤
  · refine ⟨0, Nat.zero_le _, ?_⟩
    rw [horizonBlind_succ, htop]
    simp [Submodule.comap_top]
  have hlt : Module.finrank K (horizonBlind read transport 0) < Module.finrank K X :=
    Submodule.finrank_lt htop
  have count : ∀ n, (∃ m < n, horizonBlind read transport m =
      horizonBlind read transport (m + 1)) ∨
      Module.finrank K (horizonBlind read transport n) + n ≤
        Module.finrank K (horizonBlind read transport 0) := by
    intro n
    induction n with
    | zero => exact Or.inr (by simp)
    | succ n ih =>
      rcases ih with ⟨m, hm, heq⟩ | hn
      · exact Or.inl ⟨m, by omega, heq⟩
      · by_cases heq : horizonBlind read transport n = horizonBlind read transport (n + 1)
        · exact Or.inl ⟨n, by omega, heq⟩
        · right
          have hlt' : horizonBlind read transport (n + 1) < horizonBlind read transport n :=
            lt_of_le_of_ne (horizonBlind_succ_le read transport n) (fun h => heq h.symm)
          have := Submodule.finrank_lt_finrank_of_lt hlt'
          omega
  rcases count (Module.finrank K (horizonBlind read transport 0) + 1) with ⟨m, hm, heq⟩ | hn
  · exact ⟨m, by omega, heq⟩
  · omega

/-- [proved-derived; formal-checked] **Every horizon at least `dim X − 1` reads exactly the
relevance kernel**, for any family of possibly noncommuting navigators. -/
theorem horizonBlind_eq_ker_of_le [FiniteDimensional K X] {n : ℕ}
    (hn : Module.finrank K X - 1 ≤ n) :
    horizonBlind read transport n = LinearMap.ker (faceMap read transport) := by
  obtain ⟨m, hm, heq⟩ := exists_stable_le_finrank_pred read transport
  rw [ker_faceMap_eq_of_stable read transport heq, horizonBlind_stable_forever read transport heq
    (n - m), show m + (n - m) = n by omega]

/-- [proved-derived; formal-checked] **Words of length at most `dim X − 1` read the whole
relevance kernel.** -/
theorem horizonBlind_finrank_pred_eq_ker [FiniteDimensional K X] :
    horizonBlind read transport (Module.finrank K X - 1) =
      LinearMap.ker (faceMap read transport) :=
  horizonBlind_eq_ker_of_le read transport le_rfl

/-! ## 4. The finite face map and its ledger -/

/-- [definition] Ordered navigator words of length at most `N`, as a finite index when the
navigator family is finite. -/
abbrev BoundedWord (Navigator : Type u) (N : ℕ) : Type u :=
  Σ n : Fin (N + 1), (Fin n → Navigator)

/-- [definition] The ordered word a bounded word denotes. -/
def BoundedWord.toList {N : ℕ} (w : BoundedWord Navigator N) : List Navigator := List.ofFn w.2

/-- [definition] **The finite face map**: every receiver after every word of length at most `N`. -/
def horizonFaceMap (N : ℕ) : X →ₗ[K] (Receiver × BoundedWord Navigator N → V) :=
  LinearMap.pi fun request => read request.1 ∘ₗ wordMap transport request.2.toList

theorem horizonFaceMap_apply (N : ℕ) (x : X) (request : Receiver × BoundedWord Navigator N) :
    horizonFaceMap read transport N x request =
      read request.1 (wordMap transport request.2.toList x) := rfl

/-- [proved-derived; formal-checked] The finite face map's kernel is the horizon-`N` blind
subspace. -/
theorem ker_horizonFaceMap (N : ℕ) :
    LinearMap.ker (horizonFaceMap read transport N) = horizonBlind read transport N := by
  ext x
  rw [LinearMap.mem_ker, mem_horizonBlind_iff]
  constructor
  · intro h r w hw
    have := congrFun h (r, ⟨⟨w.length, by omega⟩, w.get⟩)
    simpa [horizonFaceMap_apply, BoundedWord.toList, List.ofFn_get] using this
  · intro h
    funext request
    obtain ⟨r, ⟨n, f⟩⟩ := request
    have hlen : (List.ofFn f).length ≤ N := by
      rw [List.length_ofFn]; exact Nat.lt_succ_iff.mp n.isLt
    simpa [horizonFaceMap_apply, BoundedWord.toList] using h r (List.ofFn f) hlen

/-- [proved-derived; formal-checked] **The finite face map at horizon `dim X − 1` has exactly the
relevance kernel.** Finitely many admitted observations suffice for retention. -/
theorem ker_horizonFaceMap_finrank_pred_eq_relevanceKernel [FiniteDimensional K X] :
    (LinearMap.ker (horizonFaceMap read transport (Module.finrank K X - 1))).toAddSubgroup =
      futureCollapsed (fun r => (read r).toAddMonoidHom) (fun g => (transport g).toAddMonoidHom) := by
  rw [ker_horizonFaceMap, horizonBlind_finrank_pred_eq_ker, ker_faceMap_eq_relevanceKernel]

/-- [proved-derived; formal-checked] **The rank–nullity ledger** of the finite face map:
`rank + dim ker = dim terrain`. -/
theorem rank_nullity_ledger [FiniteDimensional K X] (N : ℕ) :
    Module.finrank K (LinearMap.range (horizonFaceMap read transport N)) +
        Module.finrank K (LinearMap.ker (horizonFaceMap read transport N)) =
      Module.finrank K X :=
  LinearMap.finrank_range_add_finrank_ker _

/-- [proved-derived; formal-checked] The face space has dimension `#requests · dim V`. -/
theorem finrank_faces [Fintype Receiver] [Fintype Navigator] [FiniteDimensional K V] (N : ℕ) :
    Module.finrank K (Receiver × BoundedWord Navigator N → V) =
      Fintype.card (Receiver × BoundedWord Navigator N) * Module.finrank K V := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- [proved-derived; formal-checked] **The cokernel ledger**: the residual the navigator's image
cannot reach has dimension `dim faces − rank`. -/
theorem cokernel_ledger [Fintype Receiver] [Fintype Navigator] [FiniteDimensional K V] (N : ℕ) :
    Module.finrank K ((Receiver × BoundedWord Navigator N → V) ⧸
        LinearMap.range (horizonFaceMap read transport N)) =
      Fintype.card (Receiver × BoundedWord Navigator N) * Module.finrank K V -
        Module.finrank K (LinearMap.range (horizonFaceMap read transport N)) := by
  rw [Submodule.finrank_quotient, finrank_faces]

/-- [proved-derived; formal-checked] **A mode dependent at the future receiver differs from its
elimination by a kernel element.** If the future face of `extra` is a combination of the faces of
`modes`, then `extra − Σ relation i • modes i` lies in the relevance kernel. -/
theorem redundant_mode_in_kernel {Mode : Type*} [Fintype Mode] (modes : Mode → X) (extra : X)
    (relation : Mode → K)
    (dependent : faceMap read transport extra =
      ∑ i, relation i • faceMap read transport (modes i)) :
    extra - ∑ i, relation i • modes i ∈ LinearMap.ker (faceMap read transport) := by
  rw [LinearMap.mem_ker, map_sub, map_sum, dependent]
  simp only [map_smul, sub_self]

end Linear

section RealModes

variable {Navigator Receiver X V : Type u}
  [AddCommGroup X] [Module ℝ X] [AddCommGroup V] [Module ℝ V]
  (read : Receiver → X →ₗ[ℝ] V) (transport : Navigator → X →ₗ[ℝ] X)

open Holonics.Foundation.GeneratorModeQuotient in
/-- [proved-derived; formal-checked] **Mode elimination is exact at the face map**
(`GeneratorModeQuotient.eliminate_redundant_mode` with the face map as encoder): replacing a
dependent mode by its relation changes no future face at any receiver after any word. -/
theorem eliminated_mode_same_future {Mode : Type*} [Fintype Mode] (modes : Mode → X) (extra : X)
    (relation coefficients : Mode → ℝ) (amplitude : ℝ)
    (dependent : faceMap read transport extra =
      ∑ i, relation i • faceMap read transport (modes i)) :
    faceMap read transport ((∑ i, coefficients i • modes i) + amplitude • extra) =
      faceMap read transport (∑ i, (coefficients i + amplitude * relation i) • modes i) :=
  eliminate_redundant_mode (faceMap read transport) modes extra relation coefficients amplitude
    dependent

end RealModes

/-! ## 5. The exact sequence and reachability -/

section Exact

variable {K X Y : Type*} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- [proved-standard; formal-checked] **`0 → ker F → X → faces → coker F → 0` is exact**, as for
every linear map (Mathlib's `Submodule.range_subtype`, `Submodule.ker_mkQ`). -/
theorem exact_sequence (F : X →ₗ[K] Y) :
    Function.Injective (LinearMap.ker F).subtype ∧
      Function.Exact (LinearMap.ker F).subtype F ∧
      Function.Exact F (LinearMap.range F).mkQ ∧
      Function.Surjective (LinearMap.range F).mkQ := by
  refine ⟨Submodule.injective_subtype _, ?_, ?_, Submodule.mkQ_surjective _⟩
  · rw [LinearMap.exact_iff, Submodule.range_subtype]
  · rw [LinearMap.exact_iff, Submodule.ker_mkQ]

/-- [proved-derived; formal-checked] A face is reached by the navigator's image exactly when its
cokernel class is zero. -/
theorem reachable_iff_cokernelClass_zero (F : X →ₗ[K] Y) (y : Y) :
    y ∈ LinearMap.range F ↔ (LinearMap.range F).mkQ y = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- [proved-derived; formal-checked] **A face is reached exactly when every cocycle vanishes on
it**: every coholon `ω` with `F* ω = 0` (`Pairing.annihilates_range_iff_mem_dualAnnihilator`)
reads zero on the face. An unreachable face is certified by one such cocycle. -/
theorem reachable_iff_cocycles_vanish (F : X →ₗ[K] Y) (y : Y) :
    y ∈ LinearMap.range F ↔ ∀ ω : Coholon K Y, F.dualMap ω = 0 → ω y = 0 := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  simp only [annihilates_range_iff_mem_dualAnnihilator]

end Exact

/-! ## 6. The ramp: a released direction, a dormant direction and an unreachable face -/

namespace Ramp

/-- Terrain: `(a, b, c)`, the read state, a dormant rate, a silent coordinate. -/
abbrev Terrain : Type := ℚ × ℚ × ℚ

/-- The navigator: one step of the ramp `(a, b, c) ↦ (a + b, b, c)`. -/
def step : Unit → Terrain →ₗ[ℚ] Terrain := fun _ =>
  { toFun := fun x => (x.1 + x.2.1, x.2.1, x.2.2)
    map_add' := by intro x y; ext <;> simp; ring
    map_smul' := by intro c x; ext <;> simp; ring }

/-- The receiver: it reads `a`. -/
def readA : Unit → Terrain →ₗ[ℚ] ℚ := fun _ => LinearMap.fst ℚ ℚ (ℚ × ℚ)

theorem wordMap_ramp (w : List Unit) (x : Terrain) :
    wordMap step w x = (x.1 + w.length * x.2.1, x.2.1, x.2.2) := by
  induction w with
  | nil => simp [wordMap]
  | cons g w ih =>
    simp only [wordMap, LinearMap.comp_apply, ih, List.length_cons]
    simp [step]
    ring

theorem mem_ker_iff (x : Terrain) :
    x ∈ LinearMap.ker (faceMap readA step) ↔ x.1 = 0 ∧ x.2.1 = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have h0 := congrFun h ((), [])
    have h1 := congrFun h ((), [()])
    simp [faceMap, wordMap_ramp, readA] at h0 h1
    exact ⟨h0, by linarith⟩
  · rintro ⟨ha, hb⟩
    funext request
    simp [faceMap, wordMap_ramp, readA, ha, hb]

/-- [proved-derived; formal-checked] **The silent coordinate is released**: the relevance kernel is
the span of `(0, 0, 1)`. -/
theorem relevanceKernel_eq_span :
    LinearMap.ker (faceMap readA step) = ℚ ∙ ((0, 0, 1) : Terrain) := by
  ext x
  rw [mem_ker_iff, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨x.2.2, by ext <;> simp [ha, hb]⟩
  · rintro ⟨c, rfl⟩
    simp

/-- [counterexample; formal-checked] **The dormant direction is not released.** `(0, 1, 0)` is
blind to the present receiver, yet one step makes it visible: the present-blind subgroup is
strictly larger than the relevance kernel. -/
theorem dormant_direction_not_released :
    ((0, 1, 0) : Terrain) ∈ collapsedPopulation (fun r => (readA r).toAddMonoidHom) ∧
      ((0, 1, 0) : Terrain) ∉
        futureCollapsed (fun r => (readA r).toAddMonoidHom) (fun g => (step g).toAddMonoidHom) := by
  constructor
  · simp [collapsedPopulation, readA]
  · rw [← ker_faceMap_eq_relevanceKernel, Submodule.mem_toAddSubgroup, mem_ker_iff]
    simp

/-- [counterexample; formal-checked] **Retention is not injective**: `(0, 0, 0)` and `(0, 0, 1)`
share one kernel class, so they lie in one preimage fibre of the kernel receiver quotient. -/
theorem released_pair_one_class :
    (kernelReceiverQuotient readA step).quotient ((0, 0, 0) : Terrain) =
        (kernelReceiverQuotient readA step).quotient ((0, 0, 1) : Terrain) ∧
      ((0, 0, 0) : Terrain) ≠ (0, 0, 1) := by
  refine ⟨?_, by simp⟩
  change (LinearMap.ker (faceMap readA step)).mkQ _ = (LinearMap.ker (faceMap readA step)).mkQ _
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, mem_ker_iff]
  simp

theorem card_requests : Fintype.card (Unit × BoundedWord Unit 3) = 4 := by
  simp [Fintype.card_sigma]

theorem finrank_terrain : Module.finrank ℚ Terrain = 3 := by
  simp

/-- [proved-derived; formal-checked] **The ledger of the ramp** at horizon `3`: kernel `1`,
rank `2`, faces `4`, cokernel `2`. -/
theorem ledger :
    Module.finrank ℚ (LinearMap.ker (horizonFaceMap readA step 3)) = 1 ∧
      Module.finrank ℚ (LinearMap.range (horizonFaceMap readA step 3)) = 2 ∧
      Module.finrank ℚ (Unit × BoundedWord Unit 3 → ℚ) = 4 ∧
      Module.finrank ℚ ((Unit × BoundedWord Unit 3 → ℚ) ⧸
        LinearMap.range (horizonFaceMap readA step 3)) = 2 := by
  have hker : Module.finrank ℚ (LinearMap.ker (horizonFaceMap readA step 3)) = 1 := by
    rw [ker_horizonFaceMap,
      horizonBlind_eq_ker_of_le readA step (by rw [finrank_terrain]; norm_num),
      relevanceKernel_eq_span]
    exact finrank_span_singleton (by simp)
  have hrank : Module.finrank ℚ (LinearMap.range (horizonFaceMap readA step 3)) = 2 := by
    have := rank_nullity_ledger readA step 3
    rw [hker, finrank_terrain] at this
    omega
  have hfaces : Module.finrank ℚ (Unit × BoundedWord Unit 3 → ℚ) = 4 := by
    rw [finrank_faces, card_requests, Module.finrank_self]
  refine ⟨hker, hrank, hfaces, ?_⟩
  rw [cokernel_ledger, card_requests, Module.finrank_self, hrank]

/-- The face that reads `1` after the three-step word and `0` elsewhere. -/
def lateFace : Unit × BoundedWord Unit 3 → ℚ := fun request =>
  if (request.2.1 : ℕ) = 3 then 1 else 0

/-- [counterexample; formal-checked] **An unreachable face.** No terrain configuration reads
`(0, 0, 0, 1)` on the four words: its cokernel class is not zero. -/
theorem unreachable_face :
    lateFace ∉ LinearMap.range (horizonFaceMap readA step 3) ∧
      (LinearMap.range (horizonFaceMap readA step 3)).mkQ lateFace ≠ 0 := by
  have hnot : lateFace ∉ LinearMap.range (horizonFaceMap readA step 3) := by
    rintro ⟨x, hx⟩
    have e0 := congrFun hx ((), ⟨0, Fin.elim0⟩)
    have e1 := congrFun hx ((), ⟨1, fun _ => ()⟩)
    have e3 := congrFun hx ((), ⟨3, fun _ => ()⟩)
    simp [horizonFaceMap_apply, BoundedWord.toList, wordMap_ramp, readA, lateFace] at e0 e1 e3
    linarith
  exact ⟨hnot, fun h => hnot ((reachable_iff_cokernelClass_zero _ _).mpr h)⟩

end Ramp

/-! ## 7. The shift: the bound `dim X − 1` is attained -/

namespace Shift

/-- Terrain: `(a, b, c)`. -/
abbrev Terrain : Type := ℚ × ℚ × ℚ

/-- The navigator: the shift `(a, b, c) ↦ (b, c, 0)`. -/
def step : Unit → Terrain →ₗ[ℚ] Terrain := fun _ =>
  { toFun := fun x => (x.2.1, x.2.2, 0)
    map_add' := by intro x y; ext <;> simp
    map_smul' := by intro c x; ext <;> simp }

/-- The receiver: it reads `a`. -/
def readA : Unit → Terrain →ₗ[ℚ] ℚ := fun _ => LinearMap.fst ℚ ℚ (ℚ × ℚ)

/-- [counterexample; formal-checked] **The horizon `dim X − 1 = 2` cannot be shortened.**
`(0, 0, 1)` is blind to every word of length at most `1`, yet the face map reads it after two
steps: `H_1 ≠ ker F`. -/
theorem horizon_sharp :
    ((0, 0, 1) : Terrain) ∈ horizonBlind readA step 1 ∧
      ((0, 0, 1) : Terrain) ∉ LinearMap.ker (faceMap readA step) ∧
      Module.finrank ℚ Terrain - 1 = 2 := by
  refine ⟨?_, ?_, by simp⟩
  · rw [mem_horizonBlind_iff]
    intro r w hw
    rcases w with _ | ⟨g, _ | ⟨g', w⟩⟩
    · simp [wordMap, readA]
    · simp [wordMap, readA, step]
    · simp at hw
  · rw [LinearMap.mem_ker]
    intro h
    have := congrFun h ((), [(), ()])
    simp [faceMap_apply, readA, step] at this

end Shift

section Audit

#print axioms ker_faceMap_eq_relevanceKernel
#print axioms kernelQuotient_eq_iff_futureAgreement
#print axioms kernelQuotient_is_coarsest_retention
#print axioms ker_faceMap_invariant
#print axioms kernelClass_after_word
#print axioms redundant_mode_in_kernel
#print axioms eliminated_mode_same_future
#print axioms mem_horizonBlind_iff
#print axioms horizonBlind_stable_forever
#print axioms ker_faceMap_eq_of_stable
#print axioms exists_stable_le_finrank_pred
#print axioms horizonBlind_eq_ker_of_le
#print axioms horizonBlind_finrank_pred_eq_ker
#print axioms ker_horizonFaceMap_finrank_pred_eq_relevanceKernel
#print axioms rank_nullity_ledger
#print axioms cokernel_ledger
#print axioms exact_sequence
#print axioms reachable_iff_cocycles_vanish
#print axioms Ramp.relevanceKernel_eq_span
#print axioms Ramp.dormant_direction_not_released
#print axioms Ramp.released_pair_one_class
#print axioms Ramp.ledger
#print axioms Ramp.unreachable_face
#print axioms Shift.horizon_sharp

end Audit

end Holonics.Compression.Core.FaceMap

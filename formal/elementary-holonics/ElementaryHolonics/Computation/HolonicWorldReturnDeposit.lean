import ElementaryHolonics.Computation.NativeMorphologyVariant
import ElementaryHolonics.Computation.HolonicOrientedSiteTransport
import Mathlib.Tactic

/-!
# The world return deposits on the route it crossed

**[proved-derived]** Four laws the `WRD` campaign obeys, each a theorem over the standing owners.

1. **Junction return.** For an incident population `R` and a transmitted population `M`, the
   reflection is `Γ = (R - M)/(R + M)`, the crossing power is `T = 4RM/(R + M)^2`,
   `T + Γ^2 = 1`, `Γ = 0` exactly at a match, and the service rounds `⌈1/T⌉` equal one at a match
   and at least two otherwise.  Termination is the match; no count or threshold halts a cycle.
2. **Route return.** The adjoint of one oriented unit-hand step returns a difference to its
   terminus and removes it from its origin.  Along a chained route the total deposit is zero,
   the deposit vanishes off the route, and on a two-step chain the interior carrier cancels while
   the boundary carriers carry the difference.  This is the spine's telescoping law read as a
   deposit.
3. **Locality.** A three-carrier control inhabits the standing `LocalCausalConeCultivation`
   with a two-carrier route: the carrier outside the cone is unchanged and the changed probe
   meets the cone.
4. **Many receivers.** Two returns with the same kernel face carry different reflections; the
   kernel verdict is one covector of a family and does not determine the deposit.

No string, token, corpus, or diagnostic text occurs in any construction.
-/

namespace Soma.Holonics.Computation.HolonicWorldReturnDeposit

open scoped BigOperators

universe uSite

/-! ## Junction return -/

/-- One junction between what arrived at a boundary and what the boundary transmitted.  Both
populations are positive: a boundary transmitting nothing is a terminus by type. -/
structure JunctionReturn where
  incident : ℕ
  transmitted : ℕ
  incident_pos : 0 < incident
  transmitted_pos : 0 < transmitted

namespace JunctionReturn

variable (j : JunctionReturn)

/-- `Γ = (R - M) / (R + M)`. -/
def reflection : ℚ :=
  ((j.incident : ℚ) - j.transmitted) / ((j.incident : ℚ) + j.transmitted)

/-- `T = 4RM / (R + M)^2`. -/
def transmission : ℚ :=
  4 * (j.incident : ℚ) * j.transmitted / ((j.incident : ℚ) + j.transmitted) ^ 2

/-- `⌈(R + M)^2 / (4RM)⌉`, the engine's own integer form of `⌈1/T⌉`. -/
def serviceRounds : ℕ :=
  ⌈((j.incident : ℚ) + j.transmitted) ^ 2 / (4 * (j.incident : ℚ) * j.transmitted)⌉₊

theorem incident_pos' : (0 : ℚ) < j.incident := by exact_mod_cast j.incident_pos

theorem transmitted_pos' : (0 : ℚ) < j.transmitted := by exact_mod_cast j.transmitted_pos

theorem denominator_pos : (0 : ℚ) < (j.incident : ℚ) + j.transmitted := by
  have h₁ := j.incident_pos'
  have h₂ := j.transmitted_pos'
  linarith

/-- The crossing power and the reflected power exhaust the arrival. -/
theorem transmission_add_reflection_sq : j.transmission + j.reflection ^ 2 = 1 := by
  have hne : ((j.incident : ℚ) + j.transmitted) ≠ 0 := ne_of_gt j.denominator_pos
  unfold transmission reflection
  field_simp
  ring

/-- Nothing reflects exactly when the populations match. -/
theorem reflection_eq_zero_iff : j.reflection = 0 ↔ j.incident = j.transmitted := by
  have hne : ((j.incident : ℚ) + j.transmitted) ≠ 0 := ne_of_gt j.denominator_pos
  unfold reflection
  rw [div_eq_zero_iff, or_iff_left hne, sub_eq_zero]
  exact Nat.cast_inj

theorem transmission_pos : 0 < j.transmission := by
  have h₁ := j.incident_pos'
  have h₂ := j.transmitted_pos'
  unfold transmission
  positivity

theorem transmission_le_one : j.transmission ≤ 1 := by
  have h := j.transmission_add_reflection_sq
  nlinarith [sq_nonneg j.reflection]

theorem transmission_of_matched (h : j.incident = j.transmitted) : j.transmission = 1 := by
  have hne : (j.incident : ℚ) ≠ 0 := ne_of_gt j.incident_pos'
  unfold transmission
  rw [← h]
  field_simp
  ring

theorem serviceRounds_eq_ceil_inv_transmission :
    j.serviceRounds = ⌈(1 : ℚ) / j.transmission⌉₊ := by
  unfold serviceRounds transmission
  rw [one_div, inv_div]

/-- A matched boundary is carried in one pass: the cycle halts. -/
theorem serviceRounds_of_matched (h : j.incident = j.transmitted) : j.serviceRounds = 1 := by
  rw [serviceRounds_eq_ceil_inv_transmission, transmission_of_matched j h]
  simp

theorem one_lt_inv_transmission_of_unmatched (h : j.incident ≠ j.transmitted) :
    (1 : ℚ) < 1 / j.transmission := by
  have hT := j.transmission_pos
  have hsum := j.transmission_add_reflection_sq
  have hΓ : j.reflection ≠ 0 := fun h₀ => h (j.reflection_eq_zero_iff.mp h₀)
  have hsq : 0 < j.reflection ^ 2 := by positivity
  have hlt : j.transmission < 1 := by linarith
  rw [one_lt_div hT]
  exact hlt

/-- An unmatched boundary reflects, and the reflected part re-enters at least once more. -/
theorem serviceRounds_ge_two_of_unmatched (h : j.incident ≠ j.transmitted) :
    2 ≤ j.serviceRounds := by
  rw [serviceRounds_eq_ceil_inv_transmission]
  have hlt := j.one_lt_inv_transmission_of_unmatched h
  have h₁ : (1 : ℕ) < ⌈(1 : ℚ) / j.transmission⌉₊ := by
    rw [Nat.lt_ceil]
    exact_mod_cast hlt
  omega

end JunctionReturn

/-! ## Route return -/

/-- One oriented unit-hand step between two carriers. -/
structure RouteStep (Site : Type uSite) where
  origin : Site
  terminus : Site
  hand : ℤ
  hand_unit : hand = 1 ∨ hand = -1

namespace RouteStep

variable {Site : Type uSite} [DecidableEq Site]

/-- The adjoint of one step returns the difference to its terminus and removes it from its
origin: the exact endpoint-difference transpose. -/
def deposit (δ : ℂ) (step : RouteStep Site) (site : Site) : ℂ :=
  (if site = step.terminus then (step.hand : ℂ) * δ else 0) -
    (if site = step.origin then (step.hand : ℂ) * δ else 0)

theorem deposit_outside (δ : ℂ) (step : RouteStep Site) {site : Site}
    (hOrigin : site ≠ step.origin) (hTerminus : site ≠ step.terminus) :
    step.deposit δ site = 0 := by
  simp [deposit, hOrigin, hTerminus]

/-- One step conserves the total: what the terminus receives, the origin gives. -/
theorem sum_deposit [Fintype Site] (δ : ℂ) (step : RouteStep Site) :
    ∑ site, step.deposit δ site = 0 := by
  simp [deposit, Finset.sum_sub_distrib, Finset.sum_ite_eq']

end RouteStep

/-- The adjoint return along a route is the sum of its step adjoints. -/
def routeDeposit {Site : Type uSite} [DecidableEq Site] (δ : ℂ) (route : List (RouteStep Site))
    (site : Site) : ℂ :=
  (route.map fun step => step.deposit δ site).sum

section Route

variable {Site : Type uSite} [DecidableEq Site]

theorem routeDeposit_nil (δ : ℂ) (site : Site) :
    routeDeposit δ ([] : List (RouteStep Site)) site = 0 := rfl

theorem routeDeposit_cons (δ : ℂ) (step : RouteStep Site) (rest : List (RouteStep Site))
    (site : Site) :
    routeDeposit δ (step :: rest) site = step.deposit δ site + routeDeposit δ rest site := by
  simp [routeDeposit]

/-- A route conserves the total difference: every carrier's gain is another's loss. -/
theorem sum_routeDeposit [Fintype Site] (δ : ℂ) (route : List (RouteStep Site)) :
    ∑ site, routeDeposit δ route site = 0 := by
  induction route with
  | nil => simp [routeDeposit_nil]
  | cons step rest ih =>
    simp only [routeDeposit_cons, Finset.sum_add_distrib, RouteStep.sum_deposit, ih, add_zero]

/-- **Locality.** A carrier no step touches receives nothing. -/
theorem routeDeposit_outside (δ : ℂ) (route : List (RouteStep Site)) {site : Site}
    (outside : ∀ step ∈ route, site ≠ step.origin ∧ site ≠ step.terminus) :
    routeDeposit δ route site = 0 := by
  induction route with
  | nil => rfl
  | cons step rest ih =>
    rw [routeDeposit_cons]
    have h := outside step (by simp)
    rw [step.deposit_outside δ h.1 h.2, zero_add]
    exact ih fun s hs => outside s (by simp [hs])

/-- **Telescoping.** On a two-step chain with one hand, the interior carrier cancels. -/
theorem twoStep_interior_cancels (δ : ℂ) (first second : RouteStep Site)
    (chain : first.terminus = second.origin) (hand : first.hand = second.hand)
    (hOrigin : first.terminus ≠ first.origin) (hTerminus : first.terminus ≠ second.terminus) :
    routeDeposit δ [first, second] first.terminus = 0 := by
  have h₁ : second.origin ≠ first.origin := chain ▸ hOrigin
  have h₂ : second.origin ≠ second.terminus := chain ▸ hTerminus
  simp [routeDeposit, RouteStep.deposit, chain, hand, h₁, h₂]

/-- **Boundary.** On a two-step chain the origin gives the difference and the terminus receives
it; the interior carrier is named in the route and moves nothing. -/
theorem twoStep_boundary_carries (δ : ℂ) (first second : RouteStep Site)
    (chain : first.terminus = second.origin)
    (h₁ : first.origin ≠ first.terminus) (h₂ : first.origin ≠ second.terminus)
    (h₃ : second.terminus ≠ first.terminus) :
    routeDeposit δ [first, second] first.origin = -((first.hand : ℂ) * δ) ∧
      routeDeposit δ [first, second] second.terminus = (second.hand : ℂ) * δ := by
  have hOriginSecond : first.origin ≠ second.origin := by
    rw [← chain]
    exact h₁
  have hTerminusSecond : second.terminus ≠ second.origin := by
    rw [← chain]
    exact h₃
  have h₂' : second.terminus ≠ first.origin := fun h => h₂ h.symm
  constructor
  · simp [routeDeposit, RouteStep.deposit, h₁, h₂, hOriginSecond]
  · simp [routeDeposit, RouteStep.deposit, h₂', h₃, hTerminusSecond]

end Route

/-! ## Locality control on three carriers -/

namespace Control

open Soma.Holonics.Computation.NativeMorphologyVariant

/-- Three carriers; the returned difference crosses the route `0 -> 1`, so carrier `0` gives one
unit, carrier `1` receives one unit, and carrier `2` rests outside the cone. -/
def routeSuccessor : Fin 3 → ℤ := fun site => if site = 0 then -1 else if site = 1 then 1 else 0

def threeSiteCultivationPassage :
    Soma.Holonics.Computation.HolonicIntelligence.CultivationPassage
      (Fin 3 → ℤ) Unit Unit (Fin 3) ℤ Unit (Fin 2) where
  predecessor := fun _ ↦ 0
  emittedOccurrence := 0
  returnedOccurrence := 1
  precedes left right := left ≠ right
  precedesIrreflexive occurrence := by simp
  returnIsLater := by decide
  difference _ _ := ()
  returnedDifference := ()
  returnedDifferenceExact := rfl
  causalAdjoint _ := ()
  applyDelta _ _ := routeSuccessor
  successor := routeSuccessor
  successorIsReturn := rfl
  morphologyChanged := by
    intro equality
    have atOne := congrFun equality 1
    simp [routeSuccessor] at atOne
  conduct morphology probe := morphology probe
  witnessProbe := 1
  changedLaterConduct := by simp [routeSuccessor]
  rest _ := ()
  remount _ := routeSuccessor
  remountExact := rfl
  withdraw _ _ := fun _ ↦ 0
  withdrawalExact := rfl

/-- The route `0 -> 1` is the causal cone; carrier `2` is outside it. -/
def threeSiteRouteCultivation :
    LocalCausalConeCultivation (Fin 3) (Fin 3 → ℤ) ℤ Unit Unit (Fin 3) ℤ Unit (Fin 2) where
  passage := threeSiteCultivationPassage
  causalCone _ := {0, 1}
  probeSite := _root_.id
  localFace morphology site := morphology site
  outsideUnchanged site outside := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at outside
    change routeSuccessor site = 0
    simp [routeSuccessor, outside.1, outside.2]
  outsideConductUnchanged probe outside := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or, id_eq] at outside
    change routeSuccessor probe = 0
    simp [routeSuccessor, outside.1, outside.2]
  restore _ := routeSuccessor
  restorationExact := rfl

theorem threeSiteRouteCultivation_outside_rests :
    threeSiteRouteCultivation.localFace threeSiteRouteCultivation.passage.successor 2 =
      threeSiteRouteCultivation.localFace threeSiteRouteCultivation.passage.predecessor 2 := by
  apply threeSiteRouteCultivation.everyOutsideSiteUnchanged 2
  change (2 : Fin 3) ∉ ({0, 1} : Set (Fin 3))
  simp

theorem threeSiteRouteCultivation_boundary_gives_and_receives :
    threeSiteRouteCultivation.passage.successor 0 = -1 ∧
      threeSiteRouteCultivation.passage.successor 1 = 1 := by
  constructor <;> rfl

theorem threeSiteRouteCultivation_changedProbe_meets_cone :
    threeSiteRouteCultivation.probeSite threeSiteRouteCultivation.passage.witnessProbe ∈
      threeSiteRouteCultivation.causalCone
        (threeSiteRouteCultivation.passage.causalAdjoint
          threeSiteRouteCultivation.passage.returnedDifference) :=
  threeSiteRouteCultivation.changedProbe_meets_causalCone

end Control

/-! ## Many receivers -/

/-- The kernel's face of one return. -/
inductive KernelFace
  | admitted
  | obstructed
  deriving DecidableEq

/-- One return read by two receivers: the kernel verdict and the junction. -/
structure ReturnFaces where
  kernel : KernelFace
  junction : JunctionReturn

/-- Every carried organ survived: a match. -/
def matchedJunction : JunctionReturn := ⟨3, 3, by decide, by decide⟩

/-- One of three carried organs survived: a partial reflection. -/
def partialJunction : JunctionReturn := ⟨3, 1, by decide, by decide⟩

/-- **The kernel verdict does not determine the deposit.** Two returns with equal kernel faces
carry different reflections, so a richer receiver separates what the verdict collapsed. -/
theorem equalKernelFace_differentReflection :
    (ReturnFaces.mk .admitted matchedJunction).kernel =
        (ReturnFaces.mk .admitted partialJunction).kernel ∧
      matchedJunction.reflection ≠ partialJunction.reflection := by
  refine ⟨rfl, ?_⟩
  norm_num [JunctionReturn.reflection, matchedJunction, partialJunction]

theorem matchedJunction_halts : matchedJunction.serviceRounds = 1 :=
  matchedJunction.serviceRounds_of_matched rfl

theorem partialJunction_reenters : 2 ≤ partialJunction.serviceRounds :=
  partialJunction.serviceRounds_ge_two_of_unmatched (by decide)

end Soma.Holonics.Computation.HolonicWorldReturnDeposit

section Audit
open Soma.Holonics.Computation.HolonicWorldReturnDeposit
#print axioms JunctionReturn.transmission_add_reflection_sq
#print axioms JunctionReturn.reflection_eq_zero_iff
#print axioms JunctionReturn.serviceRounds_of_matched
#print axioms JunctionReturn.serviceRounds_ge_two_of_unmatched
#print axioms sum_routeDeposit
#print axioms routeDeposit_outside
#print axioms twoStep_interior_cancels
#print axioms twoStep_boundary_carries
#print axioms Control.threeSiteRouteCultivation_outside_rests
#print axioms Control.threeSiteRouteCultivation_changedProbe_meets_cone
#print axioms equalKernelFace_differentReflection
end Audit

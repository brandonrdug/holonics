import Holonics.HNN.SingleHoleResponse
import Holonics.HNN.ModeQuotient
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# SourceReceiverReturn: a received covector reaches the actual source opening

Refs #62, #73. [agent-inferred; kernel-check pending]

`TickFamily.sweepAt_pairing` already owns the tick-indexed paired return. The missing consumer
was the entire boundary chain: source injection, the ordered producing word, the receiving
anchor, its phase chart and its material map. This file constructs that chain, dualizes those
same operands and consumes the normalized one-hole first/pair source of `SingleHoleResponse`.
The final consumer instantiates the actual `LoadedMedium.loadedOp` at `openedAt + k`.

No inverse step or physical clock reversal is used. A source and receiving ring can coincide
without removing the phase or the intervening word. Source innovation and a received comparison
covector are different types until a separately calibrated metric square joins them. Arbitrary
covectors here describe sensitivity; this file does not authorize a native deposition. Native
learning still admits only its declared RatioCovector and reached comparison partition.

The law is exact and linear. Native rational/real, Encoded source-clock, decoder and lattice
instantiations remain boundary obligations; a nonlinear/charted word needs its actual derivative
and remainder. The entered physical interior is shared and cancels only in a contrast; it is
never reset in the forward law. No old passage or Word is retained.

Computational object: the helical pair interaction. Objects touched: helix, pair, faces and
placement, and tube; declared cell circuits and tower restrictions remain attached. Recorded
failures avoided: dropping the phase/clock in a new consumer; retaining an authored answer;
using an independently varied pair endpoint; assuming unseen truth from a model's constant
face; using a static pump tick or resetting the entered interior.

No axiom, sorry or native_decide. No compiler or scientific job was launched by this owner.
-/

noncomputable section

namespace Holonics.HNN.SourceReceiverReturn

open scoped BigOperators
open Holonics.HNN.Propagation Holonics.HNN.TickFamily
open Holonics.HNN.ModeQuotient

section Boundary

variable {K Source Anchor Logit : Type*} {B : Type} [Field K] [Fintype B]
  {M : B → Type} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]
  [AddCommGroup Source] [Module K Source]
  [AddCommGroup Anchor] [Module K Anchor]
  [AddCommGroup Logit] [Module K Logit]

/-- A linear-map chart of the existing block tick, not another forward law. -/
def blockTick (T : BlockOp K M) : ((b : B) → M b) →ₗ[K] ((b : B) → M b) :=
  LinearMap.pi fun y => ∑ z, (T y z).comp (LinearMap.proj z)

theorem blockTick_apply (T : BlockOp K M) (x : (b : B) → M b) :
    blockTick T x = tick T x := by
  funext y
  simp [blockTick, tick]

/-- The existing ordered cycle of the actual tick family, without a periodicity assumption. -/
def wordMapAt (T : ℕ → BlockOp K M) (t : ℕ) :
    ((b : B) → M b) →ₗ[K] ((b : B) → M b) :=
  cycle (fun k => blockTick (T k)) t

theorem wordMapAt_apply (T : ℕ → BlockOp K M) (t : ℕ) (x : (b : B) → M b) :
    wordMapAt T t x = trajectoryAt T x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change blockTick (T t) (wordMapAt T t x) = tick (T t) (trajectoryAt T x t)
    rw [blockTick_apply, ih]

/-- Source-to-logit map at one actual crossing. The phase and material map are separate operands. -/
def sourceReadAt (T : ℕ → BlockOp K M) (t : ℕ)
    (inject : Source →ₗ[K] ((b : B) → M b))
    (anchor : ((b : B) → M b) →ₗ[K] Anchor)
    (phase : Anchor →ₗ[K] Anchor) (receiving : Anchor →ₗ[K] Logit) :
    Source →ₗ[K] Logit :=
  receiving.comp (phase.comp (anchor.comp ((wordMapAt T t).comp inject)))

/-- Infall as a typed paired return through the producing boundary operands. This covector is
on source opening storage, not on receiving logits or merely the receiving anchor. -/
def sourceReturnAt (T : ℕ → BlockOp K M) (t : ℕ)
    (inject : Source →ₗ[K] ((b : B) → M b))
    (anchor : ((b : B) → M b) →ₗ[K] Anchor)
    (phase : Anchor →ₗ[K] Anchor) (receiving : Anchor →ₗ[K] Logit)
    (g : Module.Dual K Logit) : Module.Dual K Source :=
  inject.dualMap ((wordMapAt T t).dualMap
    (anchor.dualMap (phase.dualMap (receiving.dualMap g))))

/-- The complete paired square consumes the existing tick-indexed trajectory. -/
theorem sourceReturnAt_pairing (T : ℕ → BlockOp K M) (t : ℕ)
    (inject : Source →ₗ[K] ((b : B) → M b))
    (anchor : ((b : B) → M b) →ₗ[K] Anchor)
    (phase : Anchor →ₗ[K] Anchor) (receiving : Anchor →ₗ[K] Logit)
    (g : Module.Dual K Logit) (delta : Source) :
    sourceReturnAt T t inject anchor phase receiving g delta =
      g (receiving (phase (anchor (trajectoryAt T (inject delta) t)))) := by
  simp only [sourceReturnAt, LinearMap.dualMap_apply, wordMapAt_apply]

theorem sourceReturnAt_is_dual_of_sourceRead (T : ℕ → BlockOp K M) (t : ℕ)
    (inject : Source →ₗ[K] ((b : B) → M b))
    (anchor : ((b : B) → M b) →ₗ[K] Anchor)
    (phase : Anchor →ₗ[K] Anchor) (receiving : Anchor →ₗ[K] Logit)
    (g : Module.Dual K Logit) :
    sourceReturnAt T t inject anchor phase receiving g =
      (sourceReadAt T t inject anchor phase receiving).dualMap g := by
  ext delta
  simp only [sourceReturnAt, sourceReadAt, LinearMap.dualMap_apply, LinearMap.comp_apply]

/-- Its pairing with every actual source variation characterizes the return uniquely. -/
theorem sourceReturnAt_unique (T : ℕ → BlockOp K M) (t : ℕ)
    (inject : Source →ₗ[K] ((b : B) → M b))
    (anchor : ((b : B) → M b) →ₗ[K] Anchor)
    (phase : Anchor →ₗ[K] Anchor) (receiving : Anchor →ₗ[K] Logit)
    (g : Module.Dual K Logit) (returned : Module.Dual K Source)
    (h : ∀ delta, returned delta =
      g (receiving (phase (anchor (trajectoryAt T (inject delta) t))))) :
    returned = sourceReturnAt T t inject anchor phase receiving g := by
  ext delta
  exact (h delta).trans (sourceReturnAt_pairing T t inject anchor phase receiving g delta).symm

/-- A half-turn of the receiving chart changes the whole source return. Coincident source and
receiver locations do not license silently dropping their phase. -/
theorem sourceReturnAt_halfTurn (T : ℕ → BlockOp K M) (t : ℕ)
    (inject : Source →ₗ[K] ((b : B) → M b))
    (anchor : ((b : B) → M b) →ₗ[K] Anchor)
    (receiving : Anchor →ₗ[K] Logit) (g : Module.Dual K Logit) :
    sourceReturnAt T t inject anchor (-LinearMap.id) receiving g =
      -sourceReturnAt T t inject anchor LinearMap.id receiving g := by
  ext delta
  simp [sourceReturnAt, LinearMap.dualMap_apply]

/-- Same entered physical interior, two source opens: the contrast reaches the complete paired
return. No forward reset is made and no hidden interior is declared zero. -/
theorem sourceContrast_return (T : ℕ → BlockOp K M) (t : ℕ)
    (inject : Source →ₗ[K] ((b : B) → M b))
    (anchor : ((b : B) → M b) →ₗ[K] Anchor)
    (phase : Anchor →ₗ[K] Anchor) (receiving : Anchor →ₗ[K] Logit)
    (g : Module.Dual K Logit) (entered : (b : B) → M b) (x x' : Source) :
    g (receiving (phase (anchor (trajectoryAt T (entered + inject x) t))) -
      receiving (phase (anchor (trajectoryAt T (entered + inject x') t)))) =
      sourceReturnAt T t inject anchor phase receiving g (x - x') := by
  have hs : trajectoryAt T (entered + inject x) t -
      trajectoryAt T (entered + inject x') t = trajectoryAt T (inject (x - x')) t := by
    rw [trajectoryAt_sub]
    congr 1
    simp only [map_sub]
    abel
  rw [← map_sub receiving, ← map_sub phase, ← map_sub anchor, hs]
  exact (sourceReturnAt_pairing T t inject anchor phase receiving g (x - x')).symm

variable {Crossing : Type*}

/-- Only the declared finite receiving partition contributes. Each crossing keeps its own
relative tick, phase, anchor and receiving chart. Compatible source duals add, not foreign clocks. -/
def partitionReturn (compared : Finset Crossing) (T : ℕ → BlockOp K M)
    (at : Crossing → ℕ) (inject : Source →ₗ[K] ((b : B) → M b))
    (anchor : Crossing → ((b : B) → M b) →ₗ[K] Anchor)
    (phase : Crossing → Anchor →ₗ[K] Anchor)
    (receiving : Crossing → Anchor →ₗ[K] Logit) (g : Crossing → Module.Dual K Logit) :
    Module.Dual K Source :=
  ∑ j ∈ compared, sourceReturnAt T (at j) inject (anchor j) (phase j) (receiving j) (g j)

theorem partitionReturn_pairing (compared : Finset Crossing) (T : ℕ → BlockOp K M)
    (at : Crossing → ℕ) (inject : Source →ₗ[K] ((b : B) → M b))
    (anchor : Crossing → ((b : B) → M b) →ₗ[K] Anchor)
    (phase : Crossing → Anchor →ₗ[K] Anchor)
    (receiving : Crossing → Anchor →ₗ[K] Logit) (g : Crossing → Module.Dual K Logit)
    (delta : Source) :
    partitionReturn compared T at inject anchor phase receiving g delta =
      ∑ j ∈ compared,
        g j (receiving j (phase j (anchor j (trajectoryAt T (inject delta) (at j))))) := by
  simp only [partitionReturn, LinearMap.sum_apply, sourceReturnAt_pairing]

end Boundary

/-! ## The consuming normalized source and actual absolute loaded word -/

section LoadedSource

open Holonics.HNN.SingleHoleResponse Holonics.HNN.LoadedMedium
open Holonics.HNN.Word Holonics.HNN.TickBlocks Holonics.HNN.LoadedRing

variable {Ring Contact : Type} [Fintype Ring] [Fintype Contact]
  [DecidableEq Ring] [DecidableEq Contact] {endRing : Contact × Bool → Ring}
  {V : Ring → Type} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  {Ch : Contact → Type} [∀ a, NormedAddCommGroup (Ch a)] [∀ a, InnerProductSpace ℝ (Ch a)]
  {Station Label X Source Anchor Logit : Type*}
  [Fintype Station] [DecidableEq Station] [Fintype Label] [DecidableEq Label]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Source] [Module ℝ Source]
  [AddCommGroup Anchor] [Module ℝ Anchor] [AddCommGroup Logit] [Module ℝ Logit]

/-- The complete source is constructed from the first and bilinear pair laws, not assumed to
have the desired received contrast. The full first/offset normalizations, shared label, entered
interior, absolute pump opening and producing boundary maps all reach the source covector. -/
theorem normalizedAbsoluteLoaded_sourceReturn
    (edges : Finset (Station × Station)) (hole : Station) (known : Station → Label)
    (basis : Label → X) (c : Label) (offset : Station × Station → ℕ) (nu : ℕ → ℝ)
    (placement : Station → X →ₗ[ℝ] Source)
    (pairPort : Station × Station → X →ₗ[ℝ] X →ₗ[ℝ] Source)
    (pairPlacement : Station × Station → Source →ₗ[ℝ] Source)
    (hedges : ∀ e ∈ edges, e.1 ≠ e.2)
    (T : BlockOp ℝ (BlockM endRing V Ch)) (res : (r : Ring) → ResOp (V r))
    (h : ℝ) (openedAt t : ℕ)
    (inject : Source →ₗ[ℝ] LoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (entered : LoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (anchor : LoadedState (endRing := endRing) (V := V) (Ch := Ch) →ₗ[ℝ] Anchor)
    (phase : Anchor →ₗ[ℝ] Anchor) (receiving : Anchor →ₗ[ℝ] Logit)
    (g : Module.Dual ℝ Logit)
    (hsource : SourceResponseShape (inject
      (responseSource edges hole known basis c (nu (Fintype.card Station)) placement
        pairPort pairPlacement (fun e => nu (Fintype.card Station - offset e))))) :
    let firstWeight := nu (Fintype.card Station)
    let pairWeight := fun e => nu (Fintype.card Station - offset e)
    let full := completeSource edges hole known basis c firstWeight placement pairPort
      pairPlacement pairWeight
    let fixed := fixedSource edges hole known basis firstWeight placement pairPort
      pairPlacement pairWeight
    let response := responseSource edges hole known basis c firstWeight placement pairPort
      pairPlacement pairWeight
    let family := absoluteLoadedFamily T res h openedAt
    SourceResponseShape (inject response) ∧
      g (receiving (phase (anchor (trajectoryAt family (entered + inject full) t))) -
        receiving (phase (anchor (trajectoryAt family (entered + inject fixed) t)))) =
        sourceReturnAt family t inject anchor phase receiving g response := by
  dsimp only
  constructor
  · exact hsource
  · rw [sourceContrast_return]
    have hsplit := populationNormalizedOneHoleSourceExpansion edges hole known basis c
      (Fintype.card Station) offset nu rfl placement pairPort pairPlacement hedges
    rw [hsplit, add_sub_cancel_left]

end LoadedSource

#print axioms blockTick_apply
#print axioms wordMapAt_apply
#print axioms sourceReturnAt_pairing
#print axioms sourceReturnAt_is_dual_of_sourceRead
#print axioms sourceReturnAt_unique
#print axioms sourceReturnAt_halfTurn
#print axioms sourceContrast_return
#print axioms partitionReturn_pairing
#print axioms normalizedAbsoluteLoaded_sourceReturn

end Holonics.HNN.SourceReceiverReturn

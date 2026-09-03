import ElementaryHolonics.Millennium.HolonicEntropyActionInduction

/-!
# Port-resolved finite boundary transport

**[proved-derived]** `CurrentBalance` carries one total outward current.  A source realization such
as a lossy optical cavity must retain which boundary port received each current before that total
is formed.  `PortResolvedBoundaryHistory` supplies precisely that missing refinement and maps back
to the existing balance owner by summing its declared finite port population.

The returned telescope is exact: input current is partitioned between stored difference and every
addressed boundary return.  Under a declared ordered receiver, a null total of nonnegative port
returns is equivalent to nullity of every port return.  No random walk, continuum limit, optical
material law, or biological identity is assumed by these algebraic theorems.

`OcularOpticalPort` is a source chart for the mutually exclusive optical-energy returns used by an
ocular realization.  Heat and neural current are intentionally not sibling optical-energy ports:
they require later constitutive transports from absorptive deposit and photochemical capture into
their own typed quantity lines.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicPortResolvedBoundaryTransport

open scoped BigOperators
open Soma.Holonics.Millennium.HolonicEntropyActionInduction

/-- A chronology-indexed boundary passage whose complete outward current remains resolved by a
finite addressed port population. -/
structure PortResolvedBoundaryHistory
    (Port Quantity : Type*) [Fintype Port] [AddCommGroup Quantity] where
  storage : ℕ → Quantity
  incoming : ℕ → Quantity
  returned : Port → ℕ → Quantity
  localBalance : ∀ k,
    storage (k + 1) - storage k + ∑ port, returned port k = incoming k

namespace PortResolvedBoundaryHistory

variable {Port Quantity : Type*} [Fintype Port] [AddCommGroup Quantity]

/-- The complete outward current at one causal cut, formed only after the port lineage is
retained. -/
def totalReturned (history : PortResolvedBoundaryHistory Port Quantity) (k : ℕ) : Quantity :=
  ∑ port, history.returned port k

/-- Forgetting the port split gives exactly the existing current-balance owner. -/
def toCurrentBalance (history : PortResolvedBoundaryHistory Port Quantity) :
    CurrentBalance Quantity where
  storage := history.storage
  outwardFlux := history.totalReturned
  production := history.incoming
  localBalance := history.localBalance

/-- Exact finite local-to-global ledger: every admitted input occurrence returns either as stored
difference or through an addressed boundary port. -/
theorem telescopes (history : PortResolvedBoundaryHistory Port Quantity) (steps : ℕ) :
    history.storage steps - history.storage 0 +
        ∑ k ∈ Finset.range steps, ∑ port, history.returned port k =
      ∑ k ∈ Finset.range steps, history.incoming k := by
  exact history.toCurrentBalance.telescopes steps

/-- A receiver-null reading of every resolved boundary port is sufficient for the aggregated
boundary current to lie in the same receiver kernel. -/
theorem totalReturned_mem_kernel
    {Reading : Type*} [AddCommGroup Reading]
    (history : PortResolvedBoundaryHistory Port Quantity)
    (receiver : Quantity →+ Reading)
    (port_in_kernel : ∀ port k, history.returned port k ∈ receiver.ker)
    (k : ℕ) :
    history.totalReturned k ∈ receiver.ker := by
  show receiver (∑ port, history.returned port k) = 0
  rw [map_sum]
  exact Finset.sum_eq_zero fun port _hport ↦ port_in_kernel port k

/-- Once every resolved boundary port is null in a receiver, the received stored difference is
exactly the received input current.  Hidden source currents remain present in the port fibre. -/
theorem receiver_difference_eq_input
    {Reading : Type*} [AddCommGroup Reading]
    (history : PortResolvedBoundaryHistory Port Quantity)
    (receiver : Quantity →+ Reading)
    (port_in_kernel : ∀ port k, history.returned port k ∈ receiver.ker)
    (steps : ℕ) :
    receiver (history.storage steps - history.storage 0) =
      ∑ k ∈ Finset.range steps, receiver (history.incoming k) := by
  exact history.toCurrentBalance.receiver_difference_eq_production receiver
    (history.totalReturned_mem_kernel receiver port_in_kernel) steps

/-- In an ordered quantity line, a null total boundary return cannot hide cancellation when every
resolved port current is nonnegative. -/
theorem totalReturned_eq_zero_iff_each
    [LinearOrder Quantity] [IsOrderedAddMonoid Quantity]
    (history : PortResolvedBoundaryHistory Port Quantity)
    (returned_nonnegative : ∀ port k, 0 ≤ history.returned port k)
    (k : ℕ) :
    history.totalReturned k = 0 ↔ ∀ port, history.returned port k = 0 := by
  unfold totalReturned
  constructor
  · intro hzero port
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (s := Finset.univ) (fun port _hport ↦ returned_nonnegative port k)).mp hzero
        port (Finset.mem_univ port)
  · intro hzero
    exact Finset.sum_eq_zero fun port _hport ↦ hzero port

/-- The world-tube version of the preceding nullity law.  A null returned total across all cuts
is equivalent to nullity at every addressed port occurrence in the admitted chronology. -/
theorem totalReturnedThrough_eq_zero_iff_each
    [LinearOrder Quantity] [IsOrderedAddMonoid Quantity]
    (history : PortResolvedBoundaryHistory Port Quantity)
    (returned_nonnegative : ∀ port k, 0 ≤ history.returned port k)
    (steps : ℕ) :
    (∑ k ∈ Finset.range steps, history.totalReturned k) = 0 ↔
      ∀ k ∈ Finset.range steps, ∀ port, history.returned port k = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro hzero k hk port
      exact (history.totalReturned_eq_zero_iff_each returned_nonnegative k).mp
        (hzero k hk) port
    · intro hzero k hk
      exact (history.totalReturned_eq_zero_iff_each returned_nonnegative k).mpr
        (hzero k hk)
  · intro k hk
    unfold totalReturned
    exact Finset.sum_nonneg fun port _hport ↦ returned_nonnegative port k

/-- With no further input, nonnegative resolved boundary return makes stored quantity antitone.
This is an exact order statement, not an exponential-decay estimate. -/
theorem storage_antitone_of_no_input
    [LinearOrder Quantity] [IsOrderedAddMonoid Quantity]
    (history : PortResolvedBoundaryHistory Port Quantity)
    (no_input : ∀ k, history.incoming k = 0)
    (returned_nonnegative : ∀ port k, 0 ≤ history.returned port k) :
    Antitone history.storage := by
  apply antitone_nat_of_succ_le
  intro k
  have hsum : 0 ≤ history.totalReturned k := by
    unfold totalReturned
    exact Finset.sum_nonneg fun port _hport ↦ returned_nonnegative port k
  have hledger :
      history.storage (k + 1) + history.totalReturned k = history.storage k := by
    have hlocal :
        history.storage (k + 1) - history.storage k + history.totalReturned k = 0 := by
      simpa [totalReturned, no_input k] using history.localBalance k
    have hzero :
        history.storage (k + 1) + history.totalReturned k - history.storage k = 0 := by
      calc
        history.storage (k + 1) + history.totalReturned k - history.storage k =
            history.storage (k + 1) - history.storage k + history.totalReturned k := by
          abel
        _ = 0 := hlocal
    exact sub_eq_zero.mp hzero
  calc
    history.storage (k + 1) ≤
        history.storage (k + 1) + history.totalReturned k :=
      le_add_of_nonneg_right hsum
    _ = history.storage k := hledger

/-- The scalar face returned by a chosen receiver after a finite chronology. -/
def receiverFace {Reading : Type*}
    (history : PortResolvedBoundaryHistory Port Quantity)
    (receiver : Quantity → Reading) (steps : ℕ) : Reading :=
  receiver (history.storage steps - history.storage 0)

/-- The complete population of port-resolved histories collapsed by one receiver reading. -/
def preimageFibre {Reading : Type*}
    (receiver : Quantity → Reading) (steps : ℕ) (reading : Reading) :
    Set (PortResolvedBoundaryHistory Port Quantity) :=
  {history | history.receiverFace receiver steps = reading}

@[simp] theorem mem_preimageFibre_iff {Reading : Type*}
    (receiver : Quantity → Reading) (steps : ℕ) (reading : Reading)
    (history : PortResolvedBoundaryHistory Port Quantity) :
    history ∈ preimageFibre receiver steps reading ↔
      history.receiverFace receiver steps = reading := Iff.rfl

end PortResolvedBoundaryHistory

/-! ## Ocular optical-energy source chart -/

/-- Mutually exclusive terminal faces of the optical-energy ledger used by the ocular source
realization.  `unresolvedExterior` is an explicit open port, never silent deletion. -/
inductive OcularOpticalPort where
  | escape
  | retinalPigmentDeposit
  | vascularDeposit
  | photochemicalCapture
  | unresolvedExterior
  deriving DecidableEq

instance : Fintype OcularOpticalPort :=
  Fintype.ofList [.escape, .retinalPigmentDeposit, .vascularDeposit,
    .photochemicalCapture, .unresolvedExterior] <| by
      intro port
      cases port <;> simp

section Audit

#print axioms PortResolvedBoundaryHistory.telescopes
#print axioms PortResolvedBoundaryHistory.totalReturned_mem_kernel
#print axioms PortResolvedBoundaryHistory.receiver_difference_eq_input
#print axioms PortResolvedBoundaryHistory.totalReturned_eq_zero_iff_each
#print axioms PortResolvedBoundaryHistory.totalReturnedThrough_eq_zero_iff_each
#print axioms PortResolvedBoundaryHistory.storage_antitone_of_no_input

end Audit

end Soma.Holonics.Millennium.HolonicPortResolvedBoundaryTransport

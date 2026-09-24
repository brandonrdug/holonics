import ElementaryHolonics.Foundation.HigherDifferenceTransport
import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Proof-bearing annihilator quotients of higher-difference ledgers

HD0 returns every occurrence-level product face.  This owner permits a receiver to remove a face
only together with a proof that its returned value is zero.  It then proves that pruning preserves
the complete ledger sum and that the norm is controlled by the retained active population.
-/

noncomputable section

namespace Soma.Holonics.HigherDifferenceAnnihilator

open Soma.Holonics.HigherDifferenceTransport

universe u v w

variable {Generator : Type u} {State : Type v} {R : Type w}

/-- A decidable active-face receiver together with the exact zero return for every rejected face. -/
structure AnnihilatorCertificate [AddMonoid R] [Mul R]
    (ledger : List (ProductFace Generator State R)) (state : State) where
  /-- The receiver decision retaining an occurrence face. -/
  active : ProductFace Generator State R → Bool
  /-- Rejection is licensed only by an exact zero proof at the declared receiver state. -/
  zero_of_inactive : ∀ face ∈ ledger, active face = false → face.value state = 0

namespace AnnihilatorCertificate

variable [AddMonoid R] [Mul R]
  {ledger : List (ProductFace Generator State R)} {state : State}

/-- The occurrence list retained by the certificate. -/
def activeLedger (certificate : AnnihilatorCertificate ledger state) :
    List (ProductFace Generator State R) :=
  ledger.filter certificate.active

/-- The rejected occurrence population remains inspectable rather than being discarded. -/
def annihilatedLedger (certificate : AnnihilatorCertificate ledger state) :
    List (ProductFace Generator State R) :=
  ledger.filter fun face ↦ !certificate.active face

theorem activeLedger_length_le (certificate : AnnihilatorCertificate ledger state) :
    certificate.activeLedger.length ≤ ledger.length := by
  exact List.length_filter_le _ _

theorem annihilatedLedger_length_le (certificate : AnnihilatorCertificate ledger state) :
    certificate.annihilatedLedger.length ≤ ledger.length := by
  exact List.length_filter_le _ _

end AnnihilatorCertificate

/-! ## Exact pruning -/

/-- Removing only faces proved zero preserves the complete ledger receiver sum. -/
theorem ledgerSum_filter_eq [AddCommMonoid R] [Mul R]
    (ledger : List (ProductFace Generator State R)) (state : State)
    (active : ProductFace Generator State R → Bool)
    (zero_of_inactive : ∀ face ∈ ledger, active face = false → face.value state = 0) :
    ledgerSum ledger state = ledgerSum (ledger.filter active) state := by
  induction ledger with
  | nil => simp [ledgerSum]
  | cons face ledger ih =>
      have htail : ∀ current ∈ ledger, active current = false → current.value state = 0 := by
        intro current hcurrent
        exact zero_of_inactive current (by simp [hcurrent])
      have ih' := ih htail
      cases hactive : active face with
      | false =>
          have hzero := zero_of_inactive face (by simp) hactive
          change face.value state + ledgerSum ledger state =
            ledgerSum (List.filter active (face :: ledger)) state
          rw [hzero, zero_add, show List.filter active (face :: ledger) =
            List.filter active ledger by simp [hactive], ih']
      | true =>
          change face.value state + ledgerSum ledger state =
            ledgerSum (List.filter active (face :: ledger)) state
          rw [show List.filter active (face :: ledger) =
            face :: List.filter active ledger by simp [hactive]]
          simp only [ledgerSum_cons]
          rw [ih']

/-- A proof-bearing certificate returns an exact quotient of the complete ledger sum. -/
theorem ledgerSum_eq_activeLedger [AddCommMonoid R] [Mul R]
    {ledger : List (ProductFace Generator State R)} {state : State}
    (certificate : AnnihilatorCertificate ledger state) :
    ledgerSum ledger state = ledgerSum certificate.activeLedger state :=
  ledgerSum_filter_eq ledger state certificate.active certificate.zero_of_inactive

/-! ## Active-support norm ledger -/

/-- Triangle inequality for the occurrence-level ledger, before any support estimate. -/
theorem norm_ledgerSum_le_sum_norm [NormedRing R]
    (ledger : List (ProductFace Generator State R)) (state : State) :
    ‖ledgerSum ledger state‖ ≤ (ledger.map fun face ↦ ‖face.value state‖).sum := by
  induction ledger with
  | nil => simp [ledgerSum]
  | cons face ledger ih =>
      simp only [ledgerSum_cons, List.map_cons, List.sum_cons]
      exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

/-- A uniform per-face bound sums to list multiplicity times that bound. -/
theorem sum_norm_le_length_mul [NormedRing R]
    (ledger : List (ProductFace Generator State R)) (state : State) (bound : ℝ)
    (faceBound : ∀ face ∈ ledger, ‖face.value state‖ ≤ bound) :
    (ledger.map fun face ↦ ‖face.value state‖).sum ≤ ledger.length * bound := by
  revert faceBound
  induction ledger with
  | nil => intro _; simp
  | cons face ledger ih =>
      intro faceBound
      have hface : ‖face.value state‖ ≤ bound := faceBound face (by simp)
      have htail : ∀ current ∈ ledger, ‖current.value state‖ ≤ bound := by
        intro current hcurrent
        exact faceBound current (by simp [hcurrent])
      have ih' := ih htail
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith

/-- If each active face is bounded by `bound`, the complete norm ledger is bounded by active
multiplicity times `bound`. -/
theorem norm_ledgerSum_le_activeLength_mul [NormedRing R]
    {ledger : List (ProductFace Generator State R)} {state : State}
    (certificate : AnnihilatorCertificate ledger state) (bound : ℝ)
    (faceBound : ∀ face ∈ certificate.activeLedger, ‖face.value state‖ ≤ bound) :
    ‖ledgerSum ledger state‖ ≤ certificate.activeLedger.length * bound := by
  rw [ledgerSum_eq_activeLedger certificate]
  refine (norm_ledgerSum_le_sum_norm certificate.activeLedger state).trans ?_
  exact sum_norm_le_length_mul certificate.activeLedger state bound faceBound

/-- The same bound exposes the active multiplicity separately from the per-face receiver bound. -/
theorem norm_ledgerSum_le_of_activeLength_le [NormedRing R]
    {ledger : List (ProductFace Generator State R)} {state : State}
    (certificate : AnnihilatorCertificate ledger state) (activeBound : ℕ) (faceBoundValue : ℝ)
    (hfaceBoundValue : 0 ≤ faceBoundValue)
    (hactive : certificate.activeLedger.length ≤ activeBound)
    (faceBound : ∀ face ∈ certificate.activeLedger, ‖face.value state‖ ≤ faceBoundValue) :
    ‖ledgerSum ledger state‖ ≤ activeBound * faceBoundValue := by
  refine (norm_ledgerSum_le_activeLength_mul certificate faceBoundValue faceBound).trans ?_
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hactive) hfaceBoundValue

/-! ## Composition of annihilator receivers -/

/-- Two independently proved active receivers compose by intersection. -/
def AnnihilatorCertificate.intersect [AddCommMonoid R] [Mul R]
    {ledger : List (ProductFace Generator State R)} {state : State}
    (first second : AnnihilatorCertificate ledger state) :
    AnnihilatorCertificate ledger state where
  active face := first.active face && second.active face
  zero_of_inactive face hface hinactive := by
    simp only [Bool.and_eq_false_iff] at hinactive
    rcases hinactive with hfirst | hsecond
    · exact first.zero_of_inactive face hface hfirst
    · exact second.zero_of_inactive face hface hsecond

/-- Intersecting certificates cannot enlarge the active occurrence population. -/
theorem AnnihilatorCertificate.intersect_activeLength_le_left [AddCommMonoid R] [Mul R]
    {ledger : List (ProductFace Generator State R)} {state : State}
    (first second : AnnihilatorCertificate ledger state) :
    (first.intersect second).activeLedger.length ≤ first.activeLedger.length := by
  have hsub : (first.intersect second).activeLedger.Sublist first.activeLedger := by
    apply List.monotone_filter_right
    intro face h
    exact (Bool.and_eq_true_iff.mp h).1
  exact hsub.length_le

end Soma.Holonics.HigherDifferenceAnnihilator

section Audit
open Soma.Holonics.HigherDifferenceAnnihilator
#print axioms ledgerSum_eq_activeLedger
#print axioms norm_ledgerSum_le_activeLength_mul
#print axioms norm_ledgerSum_le_of_activeLength_le
#print axioms AnnihilatorCertificate.intersect_activeLength_le_left
end Audit

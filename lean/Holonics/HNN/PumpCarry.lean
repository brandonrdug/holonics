import Holonics.HNN.DepositHold
import Holonics.HNN.ChainedBalance

/-!
# HNN.PumpCarry: the resonator held across a deposit; the chained balance to the crossing

[definition] Rebuild step 4 (#73), the reception carry's clock (record B,
`research/records/2026-10-03_THE_RECEPTION_CARRIES_THE_INTERIOR_CHANGE_THE_SOURCE_PORT_IMPOSES_THE_MOMENT_AND_REST_IS_COMPLETE_ABSORPTION.md`,
§2.4; #62, "Owed by the reception carry's clock", items 2 and 3; item 1, the reception cut, is
`HNN/Retention.reception_cut_composes`). The carry holds the change arriving at a word's last
crossing `T = opened_at + e − 1`; each declared resonator is carried in its state `(u, w)` with the
form phase its last hop left, `φ = phase_at(T − 1)` (`EndChange::resonator_phases`). Its storage
there is `E_φ(u, w) = ½⟨w, C_r w⟩ + ½⟨u, K_φ u⟩` (`ResonatorOperands::energy`), with `K_φ` the
stiffness plus the pump's block at phase `φ` (`pumped_stiffness`). The Rust owners are
`hnn::word::{held_resonator_rate, ReceptionCarry::crossed, PowerForm::held, WordBalance::carried,
ChainedBalance}` (#298); they are cited here, not imported, and every statement below is in its own
terms.

[proved-derived; formal-checked] What is proved.

1. **The resonator crosses a deposit at held momentum** (§1). The resonator's step advances on
   `(u, 2C_r w)` (`ResonatorOperands::step`'s right side `2C w + hβ − hK u`), and holding that
   state, `2C′_r w′_r = 2C_r w_r`, is holding `C′_r w′_r = C_r w_r`. Across a deposit of the
   capacity, the stiffness and the pump's strength, the storage at the carried phase `φ` moves by
   exactly `−½⟨w′, ΔC w′⟩ − ½⟨w − w′, C(w − w′)⟩ + ½⟨u, ΔK_φ u⟩`
   (`resonator_held_momentum`): `HNN/DepositHold.hold_energy`, the held-momentum identity, at the
   stiffness pair `(K_φ, K′_φ)`. A deposit of the stiffness or the pump's strength alone, `C′ = C`,
   does exactly the same-state work `½⟨u, ΔK_φ u⟩` (`resonator_stiffness_deposit`).
2. **The chained balance with resonators, read to the crossing** (§2). With the word's end read at
   its crossing, `P(crossing) = P(end) − last` (the last junction's residual leaves the balance and
   its bound with it, `carried_reads_to_crossing`), and the deposition the held work of the
   contacts and the resonators alike, the opening closes,
   `P_open + R_open = interior + resonator_interior + deposition + ingest + E_S(s)`, with
   `interior = P(crossing) − E_S(x)` and `resonator_interior` the carried resonators' storage under
   word `k`'s constitution (`resonator_opening_closes`). With the next word's balance
   `P_end + R_end = P_open + R_open − split − L + ported + residual`, `L ≥ 0`,
   `|residual| ≤ bound`, each reception is dissipative,
   `P_end + R_end ≤ interior + resonator_interior + supplied − split + bound`
   (`resonator_reception_dissipative`), and over a chain read at every crossing the field's and the
   resonators' storage together never exceeds the first interior plus the supply plus the bounds
   (`resonator_chain_dissipative`), the resonators absorbed nowhere.

[definition; agent-inferred] The hypotheses read from the owners: the deposit and the ingest keep
the source coordinates (as in `HNN/ChainedBalance`); the ingest moves the lift, hence the contacts'
conductances, and reads every carried resonator's storage unchanged (`R_(m″) = R_(m′)` on the held
resonator); the certified bound is the sum of the ticks' and the last junction's, each bounding its
own residual. `L ≥ 0` and `|residual| ≤ bound` are the next word's certificates. The ingest's
hypothesis (`hlift` of `resonator_opening_closes`) is not proved here. Two Rust tests pin it:
`tests/reference.rs` `the_chained_balance_closes_on_a_pumped_field`, whose `ChainedBalance::closes`
is exact and reads the carried resonators' storage under the next opening's form, nonzero from the
third reception on; and `tests/word.rs` `a_carried_change_crosses_the_next_openings_references`,
where `ReceptionCarry::crossed` keeps `u` exactly and, at an unchanged capacity, the whole state.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.PumpCarry

open Holonics.HNN.Propagation
open Holonics.HNN.DepositHold
open Holonics.HNN.ChainedBalance
open scoped BigOperators

/-! ## 1. The resonator crosses a deposit at held momentum -/

section Resonator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [proved-derived; formal-checked] **The resonator crosses a deposit at held momentum** (#62
item 2; record B §2.4). The resonator's canonical state is `(u, 2C_r w)`; holding it across a
deposit `C_r → C′_r`, `K → K′` (stiffness and pump strength) is `C′_r w′_r = C_r w_r`, and the
storage at the carried phase `φ` moves by exactly the deposit term at the stiffness pair
`(K_φ, K′_φ)`: `−½⟨w′, ΔC w′⟩ − ½⟨w − w′, C(w − w′)⟩ + ½⟨u, ΔK_φ u⟩`. -/
theorem resonator_held_momentum {Φ : Type*} (C C' : E →L[ℝ] E) (Kφ Kφ' : Φ → E →L[ℝ] E) (φ : Φ)
    (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y)) (u w w' : E)
    (hheld : (2 : ℝ) • C' w' = (2 : ℝ) • C w) :
    C' w' = C w ∧
      contactEnergy C' (Kφ' φ) u w' - contactEnergy C (Kφ φ) u w =
        -((1 / 2) * inner ℝ w' ((C' - C) w') + (1 / 2) * inner ℝ (w - w') (C (w - w'))) +
          (1 / 2) * inner ℝ u ((Kφ' φ - Kφ φ) u) := by
  have h : C' w' = C w := smul_right_injective E (two_ne_zero) hheld
  exact ⟨h, hold_energy C C' (Kφ φ) (Kφ' φ) hC u w w' h⟩

/-- [proved-derived; formal-checked] **A stiffness or pump-strength deposit at held momentum does
the same-state work**: with the capacity unchanged, the held resonator's storage at the carried
phase moves by exactly `½⟨u, ΔK_φ u⟩`. -/
theorem resonator_stiffness_deposit {Φ : Type*} (C : E →L[ℝ] E) (Kφ Kφ' : Φ → E →L[ℝ] E) (φ : Φ)
    (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y)) (u w w' : E)
    (hheld : (2 : ℝ) • C w' = (2 : ℝ) • C w) :
    contactEnergy C (Kφ' φ) u w' - contactEnergy C (Kφ φ) u w =
      (1 / 2) * inner ℝ u ((Kφ' φ - Kφ φ) u) := by
  obtain ⟨h, hE⟩ := resonator_held_momentum C C Kφ Kφ' φ hC u w w' hheld
  have hz : C (w - w') = 0 := by rw [map_sub, h, sub_self]
  rw [hE, hz, sub_self]
  simp

end Resonator

/-! ## 2. The chained balance with resonators, read to the crossing -/

section Chain

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] **The word read to its crossing** (`WordBalance::carried`).
The full word closes with the last junction's residual `last` among its residuals,
`P(end) = P_open − split − L + ported + (residual + last)`, its bound the ticks' `b` plus the last
junction's `b_last`. Read at the crossing the carry holds, `P(crossing) = P(end) − last` closes with
the ticks' residual alone, within the bound less `b_last`. -/
theorem carried_reads_to_crossing {Pend Popen spl L Pt res last b bl : K}
    (hend : Pend = Popen - spl - L + Pt + (res + last)) :
    Pend - last = Popen - spl - L + Pt + res ∧ (b + bl) - bl = b := by
  exact ⟨by rw [hend]; ring, by ring⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] **The opening closes with the resonators** (#62 item 3;
`ChainedBalance::closes`). The change `x` held at the crossing (`P_m(x) = P(end) − last`) and the
resonators `r` carried at their phase cross the deposit `m → m′` at held momentum (`x′`, `r′`) and
the ingest `m′ → m″` (`x″`), both keeping the source coordinates, the ingest reading the held
resonators unchanged. With the deposition the held work of the contacts and the resonators alike,
`P_open + R_open = (P(crossing) − E_S(x)) + R_m(r) + deposition + ingest + E_S(s)`. -/
theorem resonator_opening_closes {S I Med Rs : Type*} (ES : S → K) (R : Med → I → K)
    (Rr : Med → Rs → K) {m m' m'' : Med} {x x' x'' : S × I} {r r' : Rs}
    (s : S) (h₁ : x'.1 = x.1) (h₂ : x''.1 = x'.1) (hlift : Rr m'' r' = Rr m' r')
    {Pend last : K} (hcross : power ES R m x = Pend - last) :
    power ES R m'' (s, x''.2) + Rr m'' r' =
      ((Pend - last) - ES x.1) + Rr m r +
        ((power ES R m' x' + Rr m' r') - (power ES R m x + Rr m r)) +
        (power ES R m'' x'' - power ES R m' x') + ES s := by
  rw [hlift, ← hcross]
  simp only [power, h₂, h₁]
  ring

/-- [proved-derived; formal-checked] **Each reception is dissipative with the resonators**
(`ChainedBalance::dissipative`). With the opening closing as `resonator_opening_closes` states and
the next word's balance `P_end + R_end = P_open + R_open − split − L + ported + residual`, `L ≥ 0`,
`|residual| ≤ bound`:
`P_end + R_end ≤ interior + resonator_interior + supplied − split + bound`, the supply
`deposition + ingest + imposed + ported`. -/
theorem resonator_reception_dissipative
    {int rint dep ing imp Pt spl L res b Popen Ropen Pend Rend : K}
    (hclose : Popen + Ropen = int + rint + dep + ing + imp)
    (hend : Pend + Rend = Popen + Ropen - spl - L + Pt + res) (hL : 0 ≤ L) (hres : |res| ≤ b) :
    Pend + Rend ≤ int + rint + (dep + ing + imp + Pt) - spl + b := by
  have := le_of_abs_le hres
  linarith

/-- [proved-derived; formal-checked] **The chain with resonators is dissipative, read at every
crossing.** Word `k` ends at its crossing with field power `P k` and resonator storage `R k`; its
source rings hold `A k` there, absorbed at the reception, while its resonators are carried whole
(`resonator_interior = R k`). If each reception closes and the next word balances as above, the
field's and the resonators' storage at the crossing after `n + 1` receptions is within the first
interior `P 0 − A 0 + R 0` plus every reception's supply less its split plus its bound. -/
theorem resonator_chain_dissipative (P R A dep ing imp spl L Pt res b : ℕ → K)
    (hstep : ∀ k, P (k + 1) + R (k + 1) =
      (P k - A k) + R k + dep k + ing k + imp k - spl k - L k + Pt k + res k)
    (hA : ∀ k, 0 ≤ A k) (hL : ∀ k, 0 ≤ L k) (hres : ∀ k, |res k| ≤ b k) (n : ℕ) :
    P (n + 1) + R (n + 1) ≤ P 0 - A 0 + R 0 +
        ∑ k ∈ Finset.range (n + 1), (dep k + ing k + imp k - spl k + Pt k + b k) := by
  have h := chain_dissipative (fun k => P k + R k) A dep ing imp spl L Pt res b
    (fun k => by rw [hstep k]; ring) hA hL hres n
  beta_reduce at h
  linarith

end Chain

section Audit

#print axioms resonator_held_momentum
#print axioms resonator_stiffness_deposit
#print axioms carried_reads_to_crossing
#print axioms resonator_opening_closes
#print axioms resonator_reception_dissipative
#print axioms resonator_chain_dissipative

end Audit

end Holonics.HNN.PumpCarry

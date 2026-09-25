import Holonics.Aeon.Clock.Groupoid
import Holonics.Aeon.Clock.Reading
import Holonics.Aeon.Clock.Winding
import Holonics.Aeon.Clock.Lock
import Holonics.Aeon.Clock.Epoch
import Holonics.Aeon.Clock.CarryWord

/-!
# Aeon clocks: the groupoid, the pairing, windings, two-clock locks and epoch towers

[definition] `docs/ELEMENTARY_OBJECTS.md` §12 and
`research/records/2026-09-24_THE_AEON_EPOCH_AND_CYCLE_STANDARDIZE_THE_PASSAGE_OF_TIME.md`,
Lean obligations 1, 2, 7 and 8. Elapsed time is the pairing `t_R(γ) = ⟨ω_R | γ⟩ = n_R + r_R` of
a receiver's clock with an aeon; no clock is privileged.

- `Aeon/Clock/Groupoid`: the parametric complex, aeons as chained words, concatenation and
  reversal, homotopy, and the aeon groupoid (`instGroupoid`).
- `Aeon/Clock/Reading`: clocks as closed forms, readings additive and odd, homotopy invariance
  exactly characterizing closedness, Stokes and gauge, cycle readings through the
  `Objects/Pairing` class pairing, rates as undivided pairs composing exactly, projective equality
  only through admitted (not `(0 : 0)`) ratios; the filled-triangle counterexample.
- `Aeon/Clock/Winding`: the lift `clockLift ι` of the clock torus of any navigator family,
  whole windings and open phase,
  the carry cocycle, agreement with `Geometry/PhaseCarry`, the rational clock passage and
  `Objects/Parametron` ticks, and the navigator's lossless jumps (`Holon/Generator`).
- `Aeon/Clock/Lock`: two clocks, the Farey lock with the pair contact's no-slip reading, a
  two-clock cycle as a closed loop of the clock torus, and the convergent near-returns with the
  `Geometry/PairResonance` mediant cost.
- `Aeon/Clock/Epoch`: epochs as the partition cut by a certified section, coarsening towers,
  the epochs of an aeon at a receiver's cut clock, count as **oriented** flux (forward minus
  backward crossings, the change of whole windings), the Odometer as a tower, and the barring
  counterexamples.
- `Aeon/Clock/CarryWord`: the carry word of a rate-`α` clock read at the unit clock's sections,
  `s_n = windings α + Winding.carry (n α + ρ) α`; it is the aeon's epoch reading (its ones are the
  arrivals of a certified section, and the epoch count is the winding; at rate `1/n` it is the
  Odometer's digit section), it is eventually periodic
  with period `T` exactly when `Lock.jointReading α T` is a cycle (a crystal at the Farey lock; an
  irrational rate has no cycle, the quasicrystal), with balance, the tube and window, the physical
  projection, the golden approximants and the Beatty/Wythoff positions.

One aeon: the Hodge split (`Aeon/Production/HodgeTime.Matches`), the lock
(`Lock.isCycle_iff_torus_closes`), the epochs (`Epoch.aeonSection`), the Markov paths
(`Aeon/Production/PathReversal.pathAeon`) and the Holarchy's parametric orientation
(`Holarchy/Join.Holarchy.parametric`) all read aeons of `Groupoid.Aeon`.

Kac's mean-return ratio and the production clocks are owned by `Aeon/Production`.
-/

section Audit

#print axioms Holonics.Aeon.Clock.Groupoid.instGroupoid
#print axioms Holonics.Aeon.Clock.Reading.homotopy_invariant_iff_closed
#print axioms Holonics.Aeon.Clock.Reading.cycle_reading_factors_through_homology
#print axioms Holonics.Aeon.Clock.Reading.homologous_cycles_read_alike
#print axioms Holonics.Aeon.Clock.Reading.nonclosed_form_is_not_homotopy_invariant
#print axioms Holonics.Aeon.Clock.Reading.rate_through
#print axioms Holonics.Aeon.Clock.Reading.rate_through_projectivelyEq
#print axioms Holonics.Aeon.Clock.Reading.rate_iterate
#print axioms Holonics.Aeon.Clock.Reading.projectivelyEq_trans
#print axioms Holonics.Aeon.Clock.Reading.undetermined_breaks_transitivity
#print axioms Holonics.Aeon.Clock.Winding.windings_add
#print axioms Holonics.Aeon.Clock.Winding.carry_cocycle
#print axioms Holonics.Aeon.Clock.Winding.carry_of_microsteps
#print axioms Holonics.Aeon.Clock.Winding.ratio_split
#print axioms Holonics.Aeon.Clock.Winding.torus_cycle_reads_whole_windings
#print axioms Holonics.Aeon.Clock.Winding.lift_retains_winding
#print axioms Holonics.Aeon.Clock.Lock.lock_at_address
#print axioms Holonics.Aeon.Clock.Lock.cycle_iff_period_dvd
#print axioms Holonics.Aeon.Clock.Lock.isCycle_iff_torus_closes
#print axioms Holonics.Aeon.Clock.Lock.turnReading_eq_jointReading
#print axioms Holonics.Aeon.Clock.Lock.convergent_near_return
#print axioms Holonics.Aeon.Clock.Lock.convergent_near_return_lt
#print axioms Holonics.Aeon.Clock.Lock.between_consecutive_convergents_costs_the_mediant
#print axioms Holonics.Aeon.Clock.Lock.rational_ratio_locks_at_a_convergent
#print axioms Holonics.Aeon.Clock.Epoch.epochs_attained
#print axioms Holonics.Aeon.Clock.Epoch.coarse_epoch_is_union_of_fine
#print axioms Holonics.Aeon.Clock.Epoch.ring_count_is_flux
#print axioms Holonics.Aeon.Clock.Epoch.reading_eq_crossings
#print axioms Holonics.Aeon.Clock.Epoch.crossings_concat
#print axioms Holonics.Aeon.Clock.Epoch.aeon_epochs_attained
#print axioms Holonics.Aeon.Clock.Epoch.sectionForm_eq_exactForm
#print axioms Holonics.Aeon.Clock.Epoch.signed_count_is_flux
#print axioms Holonics.Aeon.Clock.Epoch.monotone_count_is_flux
#print axioms Holonics.Aeon.Clock.Epoch.unsigned_count_is_not_flux
#print axioms Holonics.Aeon.Clock.Epoch.odometer_tower
#print axioms Holonics.Aeon.Clock.Epoch.declared_ticks_do_not_partition
#print axioms Holonics.Aeon.Clock.Epoch.nontransversal_subsection_does_not_coarsen
#print axioms Holonics.Aeon.Clock.CarryWord.carry_eq_windings_add_carry
#print axioms Holonics.Aeon.Clock.CarryWord.eventually_periodic_iff_isCycle
#print axioms Holonics.Aeon.Clock.CarryWord.never_locks_iff_irrational
#print axioms Holonics.Aeon.Clock.CarryWord.epochOf_carrySection_eq_windings
#print axioms Holonics.Aeon.Clock.CarryWord.carrySection_epochs_attained
#print axioms Holonics.Aeon.Clock.CarryWord.odometer_counts_carrySection_epochs
#print axioms Holonics.Aeon.Clock.CarryWord.carry_rational_eq_phaseCarry

end Audit

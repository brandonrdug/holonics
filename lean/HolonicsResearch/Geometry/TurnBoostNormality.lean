import Holonics.Geometry.Motion

/-!
# The spectrum reads the response exactly when the turn and the boost commute

[proved-derived; formal-checked] October 5
([record](../../../research/records/2026-10-05_THE_GHOST_LIVES_IN_THE_GAP_THE_JOINTS_OF_THE_LENS.md) §J6).
Against a receiver of metric `G` a rate `A` splits into its turn `T = ½(A − A♯)` and its boost
`B = ½(A + A♯)` (`Geometry/Motion`). The adjoint is `A♯ = B − T`
(`adjointIn_eq_boost_sub_turn`), and the rate's failure to commute with its adjoint is twice the
failure of the turn and the boost to commute:

```text
A A♯ − A♯ A = 2 (T B − B T)          (commutator_adjointIn)
A A♯ = A♯ A  ⇔  T B = B T            (commute_adjointIn_iff_commute_turn_boost)
```

The receiver's energy rate along `ẋ = A x` is `2⟨x, G B x⟩` (`energy_rate_is_boost`): the turn
does no work, so the fastest initial growth of the receiver's energy is read on the boost alone,
whatever the eigenvalues of `A`. When the turn and the boost commute (a `G`-normal rate), the
boost's readings are the real parts of `A`'s eigenvalues and the spectrum reads the response. When
they do not, the eigenvalues can all decay while the boost grows the energy for a while: transient
amplification through modes that are not `G`-orthogonal (plane Couette flow is linearly stable at
every Reynolds number, Romanov 1973, and is turbulent in experiment; Trefethen, Trefethen, Reddy
and Driscoll 1993). This is the motion owner's form of `Foundation/CausalChord`'s
`spectrum_does_not_determine_response`.
-/

namespace Holonics.Geometry.Motion

open Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K] [Invertible (2 : K)]

/-- [proved-derived; formal-checked] The adjoint is the boost less the turn: `A♯ = B − T`. -/
theorem adjointIn_eq_boost_sub_turn (G A : Matrix n n K) :
    adjointIn G A = boost G A - turn G A := by
  rw [boost, turn, ← smul_sub,
    show A + adjointIn G A - (A - adjointIn G A) = adjointIn G A + adjointIn G A by abel,
    smul_add, ← add_smul, invOf_two_add_invOf_two, one_smul]

/-- [proved-derived; formal-checked] **A rate's commutator with its adjoint is twice its turn's
commutator with its boost:** `A A♯ − A♯ A = 2 (T B − B T)`. -/
theorem commutator_adjointIn (G A : Matrix n n K) :
    A * adjointIn G A - adjointIn G A * A =
      (2 : K) • (turn G A * boost G A - boost G A * turn G A) := by
  have hA := turn_add_boost G A
  rw [adjointIn_eq_boost_sub_turn]
  generalize turn G A = T at hA ⊢
  generalize boost G A = B at hA ⊢
  subst hA
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, two_smul]
  abel

/-- [proved-derived; formal-checked] **A rate commutes with its receiver's adjoint exactly when
its turn and its boost commute.** -/
theorem commute_adjointIn_iff_commute_turn_boost (G A : Matrix n n K) :
    Commute A (adjointIn G A) ↔ Commute (turn G A) (boost G A) := by
  have h := commutator_adjointIn G A
  constructor
  · intro hc
    rw [hc.eq, sub_self] at h
    have h2 : (⅟2 : K) • ((2 : K) • (turn G A * boost G A - boost G A * turn G A)) = 0 := by
      rw [← h, smul_zero]
    rw [smul_smul, invOf_mul_self, one_smul] at h2
    exact sub_eq_zero.mp h2
  · intro hc
    rw [hc.eq, sub_self, smul_zero] at h
    exact sub_eq_zero.mp h

end Holonics.Geometry.Motion

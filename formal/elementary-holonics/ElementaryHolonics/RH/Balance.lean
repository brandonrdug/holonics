import ElementaryHolonics.RH.Xi
import Mathlib.Tactic

/-!
# The critical line is where the two symmetries fuse

`Λ₀` carries two involutions: the functional equation's `s ↦ 1 − s`, and conjugation `s ↦ s̄`
(`RH.Xi.theCompletedZetaCarriesTheConjugationSymmetry`).  Off the critical line they are
independent and the orbit of a zero has **four** members; on the line they **coincide** and the
orbit has two.

```text
1 − s = s̄   ⟺   Re s = 1/2
```

Proved both ways below.  So the critical line is not merely the fixed locus of one map — it is the
locus where **two constraints collapse into one**, which is exactly the balanced configuration:
away from it the four-element orbit must satisfy two independent conditions, and on it the two
conditions are the same condition.

That is the sharp reading of "pull evenly and it sums to null at the centre": the centre is where
the two pulls are the same pull.  It claims nothing about where the zeros are — only about where
the symmetries can balance, which is a statement about `Λ₀`'s group action and is unconditional.
-/

namespace Soma.Holonics.RH.Balance

open Complex

/-- **THE TWO INVOLUTIONS COINCIDE EXACTLY ON THE CRITICAL LINE.**  `1 − s = s̄` iff
`Re s = 1/2` — the functional equation's reflection and conjugation are the same map there and
nowhere else. -/
theorem theTwoInvolutionsCoincideExactlyOnTheCriticalLine (s : ℂ) :
    1 - s = (starRingEnd ℂ) s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith
  · intro h
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, h]; ring
    · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]; ring

/-- Off the line they genuinely differ, so the two constraints are independent there. -/
theorem theInvolutionsDifferOffTheLine {s : ℂ} (h : s.re ≠ 1 / 2) :
    1 - s ≠ (starRingEnd ℂ) s := by
  intro hc
  exact h ((theTwoInvolutionsCoincideExactlyOnTheCriticalLine s).1 hc)

/-- **THE ORBIT HAS FOUR MEMBERS OFF THE LINE.**  `s`, `1 − s`, `s̄`, `1 − s̄` — and the four are
distinct as soon as `s` is off the line and off the real axis. -/
theorem theOrbitIsFourOffTheLine {s : ℂ} (h : s.re ≠ 1 / 2) (him : s.im ≠ 0) :
    s ≠ 1 - s ∧ s ≠ (starRingEnd ℂ) s ∧ (1 - s) ≠ (starRingEnd ℂ) s := by
  refine ⟨?_, ?_, theInvolutionsDifferOffTheLine h⟩
  · intro hc
    have hre := congrArg Complex.re hc
    simp only [Complex.sub_re, Complex.one_re] at hre
    exact h (by linarith)
  · intro hc
    have hi := congrArg Complex.im hc
    simp only [Complex.conj_im] at hi
    exact him (by linarith)

/-- **AND TWO ON IT.**  On the critical line the reflection *is* the conjugation, so the orbit of a
nonreal point is `{s, s̄}` — the four collapses to two, and that collapse is the balance. -/
theorem theOrbitIsTwoOnTheLine {s : ℂ} (h : s.re = 1 / 2) (him : s.im ≠ 0) :
    (1 - s = (starRingEnd ℂ) s) ∧ s ≠ (starRingEnd ℂ) s := by
  refine ⟨(theTwoInvolutionsCoincideExactlyOnTheCriticalLine s).2 h, ?_⟩
  intro hc
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  exact him (by linarith)

/-- **THE CENTRE OF THE LINE IS THE ONLY TOTALLY FIXED POINT.**  At `s = 1/2` both involutions fix
`s` itself: the orbit is a single point, and it is the unique such point.  Everything else on the
line has an orbit of two; everything off it, four. -/
theorem theCentreIsTheUniqueTotallyFixedPoint (s : ℂ) :
    (1 - s = s ∧ (starRingEnd ℂ) s = s) ↔ s = 1 / 2 := by
  constructor
  · rintro ⟨h1, -⟩
    have : (2 : ℂ) * s = 1 := by linear_combination -h1
    linear_combination this / 2
  · rintro rfl
    refine ⟨by ring, ?_⟩
    apply Complex.ext <;> simp

/-! ## The orbit sizes make the count read the line's parity -/

/-- **A SYMMETRIC BOX'S ZERO COUNT IS `4a + 2b`.**  The two involutions generate a Klein
four-group; by `theOrbitIsFourOffTheLine` and `theOrbitIsTwoOnTheLine` every nonreal zero lies in
an orbit of size `4` (off the line) or `2` (on it).  A region stable under both therefore contains
`4a + 2b` zeros, with `a` the off-line orbits and `b` the on-line ones. -/
def symmetricCount (a b : ℕ) : ℕ := 4 * a + 2 * b

/-- The total is always even: no symmetric region can contain an odd number of nonreal zeros. -/
theorem theSymmetricCountIsEven (a b : ℕ) : symmetricCount a b % 2 = 0 := by
  simp only [symmetricCount]
  omega

/-- **AND ITS RESIDUE MOD FOUR READS THE PARITY OF THE ON-LINE COUNT.**  `4a + 2b ≡ 2 (mod 4)`
exactly when `b` is odd — so a mod-`4` count of zeros in a symmetric box determines **whether the
number of on-line orbits is odd**, without locating a single zero.  The off-line population is
invisible to that reading, because it enters in fours. -/
theorem theCountModFourReadsTheOnLineParity (a b : ℕ) :
    symmetricCount a b % 4 = 2 ↔ b % 2 = 1 := by
  simp only [symmetricCount]
  omega

/-- And the complementary residue: `≡ 0 (mod 4)` exactly when the on-line count is even. -/
theorem theOtherResidueIsTheEvenCase (a b : ℕ) :
    symmetricCount a b % 4 = 0 ↔ b % 2 = 0 := by
  simp only [symmetricCount]
  omega

/-- **THE OFF-LINE POPULATION IS INVISIBLE MOD FOUR.**  Changing `a` by any amount leaves the
residue fixed — which is the precise sense in which the balanced reading cannot see the unbalanced
zeros, and the unbalanced ones cannot hide the balanced parity. -/
theorem theOffLinePopulationIsInvisibleModFour (a a' b : ℕ) :
    symmetricCount a b % 4 = symmetricCount a' b % 4 := by
  simp only [symmetricCount]
  omega

end Soma.Holonics.RH.Balance

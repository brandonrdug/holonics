import Mathlib.Tactic

/-!
# FamilyHalving: the halving closes at every modulus

**The coordinate core of the family descent's exactness.**  On every congruent-number
curve `y² = x³ − n²x`, a point whose slot square-roots exist is halved by the same
assembly that closed the kernel at five:

```text
u = (r + s)(r − t),   v = u·(s − t),   with   s² = r² − n,   t² = r² + n,
```

and the four returns are certified by polynomial identities **uniform in the
modulus** — verified symbolically with residual zero before formalization, their
cofactors specializing to the five-instance certificates at `n = 5`:

* **`theHalfPointLiesOnTheCurveAtEveryModulus`** — `v² = u³ − n²u`;
* **`theHalfPointFactorsDoNotVanishAtEveryModulus`** — the assembling factors are
  nonzero whenever the modulus is;
* **`theTangentSquareLawAtEveryModulus`** — `(3u² − n²)² = (r² + u + u)·(2v)²`,
  the abscissa of the tangent double returning `r²`;
* **`theTangentOrdinateLawAtEveryModulus`** — `(3u² − n²)(r² − u) + 2v² = 2rst·v`,
  the ordinate returning `−rst`.

The point-level assembly through the group law is the named next deed; nothing in
these identities depends on the instance.  Every `theorem` is discharged and none
depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.FamilyHalving

/-- **The half point lies on the curve at every modulus.** -/
theorem theHalfPointLiesOnTheCurveAtEveryModulus {n r s t : ℚ}
    (hs2 : s ^ 2 = r ^ 2 - n) (ht2 : t ^ 2 = r ^ 2 + n) :
    ((r + s) * (r - t) * (s - t)) ^ 2
      = ((r + s) * (r - t)) ^ 3 - n ^ 2 * ((r + s) * (r - t)) := by
  linear_combination
    (-n * t ^ 2 + t ^ 4 - s * t ^ 3 + s ^ 2 * t ^ 2 + 2 * n * r * t - 3 * r * t ^ 3
      + 3 * r * s * t ^ 2 - 2 * r * s ^ 2 * t - n * r ^ 2 + 2 * r ^ 2 * t ^ 2
      - 3 * r ^ 2 * s * t + r ^ 2 * s ^ 2 + r ^ 3 * t + r ^ 3 * s - r ^ 4) * hs2
    + (-n * t ^ 2 + n * s * t + 3 * n * r * t - n * r * s + 2 * r * s * t ^ 2
      - 2 * n * r ^ 2 + 2 * r ^ 2 * t ^ 2 - 4 * r ^ 2 * s * t - 4 * r ^ 3 * t
      + 2 * r ^ 3 * s + 2 * r ^ 4) * ht2

/-- **The assembling factors do not vanish at every modulus**: each vanishing would
collapse the modulus itself. -/
theorem theHalfPointFactorsDoNotVanishAtEveryModulus {n r s t : ℚ} (hn : n ≠ 0)
    (hs2 : s ^ 2 = r ^ 2 - n) (ht2 : t ^ 2 = r ^ 2 + n) :
    r + s ≠ 0 ∧ r - t ≠ 0 ∧ s - t ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro hc
    apply hn
    have h1 : s = -r := by linarith
    have h2 : s ^ 2 = r ^ 2 := by rw [h1]; ring
    linarith [hs2, h2]
  · intro hc
    apply hn
    have h1 : t = r := by linarith
    have h2 : t ^ 2 = r ^ 2 := by rw [h1]
    linarith [ht2, h2]
  · intro hc
    apply hn
    have h1 : s = t := by linarith
    have h2 : s ^ 2 = t ^ 2 := by rw [h1]
    linarith [hs2, ht2, h2]

/-- **The tangent square law at every modulus**: the abscissa of the tangent double
of the half point returns `r²`. -/
theorem theTangentSquareLawAtEveryModulus {n r s t : ℚ}
    (hs2 : s ^ 2 = r ^ 2 - n) (ht2 : t ^ 2 = r ^ 2 + n) :
    (3 * ((r + s) * (r - t)) ^ 2 - n ^ 2) ^ 2
      = (r ^ 2 + (r + s) * (r - t) + (r + s) * (r - t))
        * (2 * ((r + s) * (r - t) * (s - t))) ^ 2 := by
  linear_combination
    (-6 * n ^ 2 * t ^ 2 + 7 * n * t ^ 4 - 8 * n * s * t ^ 3 + 8 * s * t ^ 5
      - 7 * s ^ 2 * t ^ 4 + 8 * s ^ 3 * t ^ 3 + 12 * n ^ 2 * r * t
      - 36 * n * r * t ^ 3 + 24 * r * t ^ 5 + 24 * n * r * s * t ^ 2
      - 36 * r * s * t ^ 4 + 36 * r * s ^ 2 * t ^ 3 - 24 * r * s ^ 3 * t ^ 2
      - 6 * n ^ 2 * r ^ 2 + 70 * n * r ^ 2 * t ^ 2 - 77 * r ^ 2 * t ^ 4
      - 24 * n * r ^ 2 * s * t + 64 * r ^ 2 * s * t ^ 3 - 70 * r ^ 2 * s ^ 2 * t ^ 2
      + 24 * r ^ 2 * s ^ 3 * t - 60 * n * r ^ 3 * t + 68 * r ^ 3 * t ^ 3
      + 8 * n * r ^ 3 * s - 56 * r ^ 3 * s * t ^ 2 + 60 * r ^ 3 * s ^ 2 * t
      - 8 * r ^ 3 * s ^ 3 + 19 * n * r ^ 4 + 22 * r ^ 4 * t ^ 2
      + 24 * r ^ 4 * s * t - 19 * r ^ 4 * s ^ 2 - 60 * r ^ 5 * t - 4 * r ^ 5 * s
      + 23 * r ^ 6) * hs2
    + (-n ^ 3 - 7 * n ^ 2 * t ^ 2 - 8 * n * s * t ^ 3 + 12 * n ^ 2 * r * t
      - 24 * n * r * t ^ 3 + 36 * n * r * s * t ^ 2 - 5 * n ^ 2 * r ^ 2
      + 84 * n * r ^ 2 * t ^ 2 - 48 * n * r ^ 2 * s * t + 32 * r ^ 2 * s * t ^ 3
      - 96 * n * r ^ 3 * t + 32 * r ^ 3 * t ^ 3 + 20 * n * r ^ 3 * s
      - 96 * r ^ 3 * s * t ^ 2 + 36 * n * r ^ 4 - 96 * r ^ 4 * t ^ 2
      + 96 * r ^ 4 * s * t + 96 * r ^ 5 * t - 32 * r ^ 5 * s - 32 * r ^ 6) * ht2

/-- **The tangent ordinate law at every modulus**: the ordinate of the tangent double
of the half point returns `−rst`. -/
theorem theTangentOrdinateLawAtEveryModulus {n r s t : ℚ}
    (hs2 : s ^ 2 = r ^ 2 - n) (ht2 : t ^ 2 = r ^ 2 + n) :
    (3 * ((r + s) * (r - t)) ^ 2 - n ^ 2) * (r ^ 2 - (r + s) * (r - t))
      + 2 * ((r + s) * (r - t) * (s - t)) ^ 2
      = 2 * (r * s * t) * ((r + s) * (r - t) * (s - t)) := by
  linear_combination
    (-2 * n * t ^ 2 + 2 * t ^ 4 - s * t ^ 3 + 2 * s ^ 2 * t ^ 2 + 4 * n * r * t
      - 5 * r * t ^ 3 + 5 * r * s * t ^ 2 - 4 * r * s ^ 2 * t - 2 * n * r ^ 2
      + 2 * r ^ 2 * t ^ 2 - 5 * r ^ 2 * s * t + 2 * r ^ 2 * s ^ 2 + 3 * r ^ 3 * t
      + r ^ 3 * s - 2 * r ^ 4) * hs2
    + (-2 * n * t ^ 2 + n * s * t + 5 * n * r * t - n * r * s + 4 * r * s * t ^ 2
      - 2 * n * r ^ 2 + 4 * r ^ 2 * t ^ 2 - 6 * r ^ 2 * s * t - 6 * r ^ 3 * t
      + 2 * r ^ 3 * s + 2 * r ^ 4) * ht2

end Soma.Holonics.Millennium.FamilyHalving

import ElementaryHolonics.Millennium.AnalyticParity

/-!
# FunctionalEquationParity: the reflection law, freed of its L-function

`AnalyticParity` proved that the order of vanishing of a completed L-function at the
center of `Λ(2−s) = w·Λ(s)` has the parity of the sign.  Nothing in that argument used
the number `2`, the conductor, the Euler product, or the curve.  It used **one
reflection**.

This file states the law at an arbitrary functional equation

```text
Λ(ω − s) = ε · Λ(s)
```

so it reads on every object in the Millennium line that carries one:

* **`theCenterIsTheFixedPointOfTheReflection`** — the center `ω/2` is the unique
  fixed point of `s ↦ ω − s`.  The "center" is not a convention; it is the fixed
  locus.
* **`theSignIsAnInvolution`** — a nonvanishing `Λ` forces `ε² = 1`.
* **`theOrderAtTheCenterHasTheParityOfTheSign`** — `(−1)^(order at ω/2) = ε`.
* **`theCriticalLineIsTheFixedLocusOfTheAntilinearReflection`** — and the same
  mechanism one level up: the critical line `Re s = 1/2` is exactly the fixed locus of
  the **anti-linear** involution `s ↦ 1 − s̄`, and the Weil circle `‖z‖ = √q` is
  exactly the fixed locus of `z ↦ q/z̄`.  Placement is the fixed locus of the
  involution — the same sentence in both cases, now checkable.

The Birch–Swinnerton-Dyer reading is the instance `ω = 2`, centre `1`; the Riemann
reading is `ω = 1`, centre `1/2`.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FunctionalEquationParity

open Complex

/-! ## 1. The center is the fixed point -/

/-- **THE CENTER IS THE FIXED POINT OF THE REFLECTION**: `ω − s = s` exactly at
`s = ω/2`.  The center of a functional equation is not a convention. -/
theorem theCenterIsTheFixedPointOfTheReflection (ω s : ℂ) :
    ω - s = s ↔ s = ω / 2 := by
  constructor
  · intro h
    linear_combination (-1 / 2 : ℂ) * h
  · intro h
    rw [h]
    ring

/-! ## 2. The sign is an involution -/

/-- **THE SIGN IS AN INVOLUTION**: applying the reflection twice returns `ε²·Λ`, so
any `Λ` that does not vanish identically forces `ε² = 1`. -/
theorem theSignIsAnInvolution {Λ : ℂ → ℂ} {ω ε : ℂ}
    (hfe : ∀ s, Λ (ω - s) = ε * Λ s) {z : ℂ} (hz : Λ z ≠ 0) : ε ^ 2 = 1 := by
  have h1 := hfe (ω - z)
  have h2 := hfe z
  rw [show ω - (ω - z) = z from by ring, h2] at h1
  have hkey : (ε ^ 2 - 1) * Λ z = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp hkey with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hz


/-! ## 3. The parity law at an arbitrary functional equation -/

set_option maxHeartbeats 800000 in
/-- **THE ORDER AT THE CENTER HAS THE PARITY OF THE SIGN**, for any entire `Λ` with
any functional equation `Λ(ω − s) = ε·Λ(s)`.

Factor `Λ(z) = (z − ω/2)^r · g(z)` with `g(ω/2) ≠ 0`.  The reflection sends
`z − ω/2` to `−(z − ω/2)`, so the same factorization reads
`(−1)^r · g(ω − z) = ε · g(z)` once the `r`-th power cancels off the center, and
continuity where `g` does not vanish gives `(−1)^r = ε`.

Nothing here knows what `Λ` is. -/
theorem theOrderAtTheCenterHasTheParityOfTheSign {Λ : ℂ → ℂ} {ω ε : ℂ}
    (hΛ : Differentiable ℂ Λ) (hfe : ∀ s, Λ (ω - s) = ε * Λ s) {r : ℕ}
    (hord : analyticOrderAt Λ (ω / 2) = (r : ℕ∞)) :
    ((-1 : ℂ)) ^ r = ε := by
  set c : ℂ := ω / 2 with hc
  have hrefl : ∀ z : ℂ, ω - z - c = -(z - c) := by
    intro z
    rw [hc]
    ring
  have hana : AnalyticAt ℂ Λ c := hΛ.analyticAt c
  obtain ⟨g, hg, hg0, hev⟩ := hana.analyticOrderAt_eq_natCast.mp hord
  set A : ℂ → ℂ := fun z => ((-1 : ℂ)) ^ r * g (ω - z) with hA
  set B : ℂ → ℂ := fun z => ε * g z with hB
  have hmap : Filter.Tendsto (fun z : ℂ => ω - z) (nhds c) (nhds c) := by
    have hcont : Continuous (fun z : ℂ => ω - z) := by fun_prop
    have h := hcont.tendsto c
    have hfix : ω - c = c := by rw [hc]; ring
    rwa [hfix] at h
  have hleft : ∀ᶠ z in nhds c, Λ (ω - z) = (z - c) ^ r * A z := by
    filter_upwards [hmap.eventually hev] with z hz
    rw [hz, hA, hrefl z, neg_pow, smul_eq_mul]
    ring
  have hright : ∀ᶠ z in nhds c, Λ (ω - z) = (z - c) ^ r * B z := by
    filter_upwards [hev] with z hz
    rw [hfe z, hz, hB, smul_eq_mul]
    ring
  have hpunct : ∀ᶠ z in nhdsWithin c {c}ᶜ, A z = B z := by
    rw [Filter.eventually_iff] at hleft hright ⊢
    rw [mem_nhdsWithin]
    obtain ⟨U, hU, hUo, hU1⟩ := mem_nhds_iff.mp (Filter.inter_mem hleft hright)
    refine ⟨U, hUo, hU1, ?_⟩
    rintro z ⟨hzU, hz1⟩
    obtain ⟨h1, h2⟩ := hU hzU
    have hne : (z - c) ^ r ≠ 0 :=
      pow_ne_zero r (sub_ne_zero.mpr (by simpa using hz1))
    exact mul_left_cancel₀ hne (h1.symm.trans h2)
  have hgA : AnalyticAt ℂ A c := by
    refine analyticAt_const.mul ?_
    have hin : AnalyticAt ℂ (fun z : ℂ => ω - z) c := analyticAt_const.sub analyticAt_id
    have hg' : AnalyticAt ℂ g ((fun z : ℂ => ω - z) c) := by
      have hfix : ω - c = c := by rw [hc]; ring
      simpa [hfix] using hg
    exact hg'.comp hin
  have hgB : AnalyticAt ℂ B c := analyticAt_const.mul hg
  have hcA : Filter.Tendsto A (nhdsWithin c {c}ᶜ) (nhds (A c)) :=
    hgA.continuousAt.continuousWithinAt
  have hcB : Filter.Tendsto B (nhdsWithin c {c}ᶜ) (nhds (B c)) :=
    hgB.continuousAt.continuousWithinAt
  have heq : A c = B c := tendsto_nhds_unique (hcA.congr' hpunct) hcB
  have hfix : ω - c = c := by rw [hc]; ring
  simp only [hA, hB, hfix] at heq
  exact mul_right_cancel₀ hg0 heq

/-! ## 4. Placement is the fixed locus of the involution -/

/-- **THE CRITICAL LINE IS THE FIXED LOCUS**: `Re s = 1/2` is exactly the fixed locus
of the anti-linear involution `s ↦ 1 − s̄`.  The line is not a coincidence of the
functional equation; it is where the reflection that equation carries has its fixed
points. -/
theorem theCriticalLineIsTheFixedLocusOfTheAntilinearReflection (s : ℂ) :
    1 - (starRingEnd ℂ) s = s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith
  · intro h
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]
      ring

/-- **THE WEIL CIRCLE IS THE FIXED LOCUS**: for `q > 0`, the circle `‖z‖ = √q` is
exactly the fixed locus of `z ↦ q/z̄`.  Same sentence, different involution — the
placement `|α| = √q` is where the involution a realizer induced has its fixed
points. -/
theorem theWeilCircleIsTheFixedLocusOfTheNormReflection {q : ℝ} (hq : 0 < q)
    (z : ℂ) (hz : z ≠ 0) :
    ((q : ℂ)) / (starRingEnd ℂ) z = z ↔ ‖z‖ = Real.sqrt q := by
  have hzc : (starRingEnd ℂ) z ≠ 0 := by
    simpa using hz
  rw [div_eq_iff hzc]
  constructor
  · intro h
    have hnorm : ‖z‖ ^ 2 = q := by
      have h1 : z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
        rw [mul_comm, Complex.conj_mul']
        push_cast
        ring
      rw [h1] at h
      exact_mod_cast h.symm
    rw [← hnorm, Real.sqrt_sq (norm_nonneg z)]
  · intro h
    have hnorm : ‖z‖ ^ 2 = q := by
      rw [h, Real.sq_sqrt hq.le]
    have h1 : z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.conj_mul']
      push_cast
      ring
    rw [h1, hnorm]

end Soma.Holonics.Millennium.FunctionalEquationParity

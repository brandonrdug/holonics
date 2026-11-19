import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues

/-!
# Certified capture, outward rounding, and ζ and η with their remainders

The box of #410 "`series.log-atanh`, `series.log-atanh-exp`, `series.common-continued-fraction`,
`analytic.certified-capture`, `analytic.euler-maclaurin-eta` (constants as navigators, parked in
#409)" owes the Lean statements of five atlas rows (`docs/atlas/arithmetic.tsv`). The first three
stand in `HolonicsResearch/Mathematics/ConstantNavigators`, whose "What is not claimed" leaves
`analytic.certified-capture` ("relaxed release of a complex source box into a capture square, with
mean-value inclusion"), `analytic.euler-maclaurin-eta` ("ζ and η with their Euler–Maclaurin
remainders and jets") and "the owner's rounding of each enclosure out to a bit grain"; this file
takes them. Their only owners were the retired `crates/holonics/src/geometry/exact_analysis`
(`navigation.rs`: `certify_capture`, `mean_value_release`, `propagate_to_capture`,
`PropagationStatus`; `special.rs`: `ComplexJet2::relaxed_release`, `zeta_euler_maclaurin`,
`euler_maclaurin_remainder_bound`; `types.rs`: `RatInterval::round_out`;
[history](https://github.com/brandonrdug/holonics/tree/13f8c734/crates/holonics/src/geometry/exact_analysis),
removed at `d329cb541`), whose open paragraph reads "Source-driven analytic navigation over
certified complex receiver boxes". The guide `docs/ANALYTIC_FLUX_AND_RECEIVING_BASINS.md`
("Executable receiving regions in rationals") states the owner's law: a capture square `B∞(m, r)`
with `q ≥ |Re N′| + |Im N′|` on it, `β ≥ |N(m) − m|∞` and `β + q r < r`; the propagation
`N(X) ⊆ N(m) + N′(X)(X − m)` with the midpoint an explicit proof anchor; and capture, domain
obstruction and horizon exhaustion each returning the current face. The record
`research/records/2026-09-14_ANALYTIC_RELEASE_AND_RECURSIVE_RECEIVING_POPULATIONS.md` built it. The
release map of the row's `uses:analytic.residual-release` is `newtonMap` of
`Holonics/Mathematics/AnalyticNavigation` (`z − λ f z/f′ z`, derivative `1 − λ + λ f f″/f′²` by
`hasDerivAt_newtonMap`); here any source map `g` takes its place. The precision law of `CLAUDE.md`
gives the reading: a number is read at a declared width, a term is released only by partition at a
declared tolerance with its remainder accounted, and rounding is a section, which commutes when it
stands once, outward.

[proved-standard; formal-checked] What is proved.

1. **Mean-value inclusion** (`analytic.certified-capture`). On a convex `B` where `f` is complex
   differentiable with `‖f′‖ ≤ M`, `‖f z − f m‖ ≤ M ‖z − m‖` (`norm_sub_le_of_deriv_le`, from
   Mathlib's `Convex.norm_image_sub_le_of_norm_deriv_le`), so `B ⊆ closedBall m r` puts `f(B)` in
   `closedBall (f m) (M r)` (`image_subset_closedBall`). On the owner's square `box c r` (`B∞(c, r)`,
   `convex_box`) the bound is read part by part: multiplication by `d` moves each part of `w` by at
   most `(|Re d| + |Im d|) ‖w‖∞` (`abs_mul_re_im_le`), so with `|Re f′| + |Im f′| ≤ q` on the box
   each part of `f z − f m` is at most `q ‖z − m‖∞` (`box_mean_value`, the real mean value theorem
   on each part along the segment). From an anchor `c′` within `β` of `f c` in each part,
   `f(box c r) ⊆ box c′ r′` once `β + q r ≤ r′` (`image_box_subset_box`): the anchor's value and
   the whole box's derivative bound enclose the image, and no midpoint replaces the box. At
   `c′ = c`, `r′ = r` it is the owner's capture square, which holds every later release
   (`box_capture_square`, `box_capture_square_iterate`; [proved-derived; formal-checked], the
   guide's grade).
2. **Capture at a declared grain** ([proved-derived; formal-checked]). The reading of `w` at grain
   `u > 0` is `(⌊Re w/u⌋, ⌊Im w/u⌋)` (`reading`), and a cell is a fibre of the reading (`cell`,
   `mem_cell_iff`). An enclosure of `f(B)` inside one cell certifies the reading of `f z` for every
   `z ∈ B` (`capture_certifies`); an enclosure holding two readings lies in no cell
   (`not_subset_cell_of_two_readings`), and two source points whose images read apart obstruct every
   enclosure (`no_enclosure_certifies`). On a box the test is read at its ends: equal floors at both
   ends of each side capture it (`floor_div_eq_of_mem`, `box_subset_cell`), and otherwise the box
   holds two points of different readings, `w ± ρ` or `w ± ρ i` (`box_capture_or_obstruction`).
3. **Relaxed release over a finite horizon** ([proved-derived; formal-checked]). A law on faces
   (`ReleaseLaw`: what a face encloses, a step that returns `none` where the law cannot proceed, and
   a test that names a capture target) is run by `release` for at most `H` steps, and its outcome
   (`Outcome`) is a capture, an obstruction or an exhaustion, each with its depth and the face it
   retains. When each step's face holds the image of the last under the source map `g`
   (`ReleaseLaw.Follows`), the retained face at depth `d ≤ H` holds `g^[d]` of the whole source face
   (`release_face`); a capture is returned only on a face that passed the test
   (`release_capture_test`), an obstruction only where the step returned `none`
   (`release_obstruction_step`), and an exhaustion only at depth `H` (`release_exhaustion_depth`).
   With a test sound for its targets (`ReleaseLaw.TestSound`), a capture at depth `d` puts `g^[d] z`
   in its target for every point `z` of the source face (`release_capture_sound`), and a target that
   `g` maps into itself, such as the owner's capture squares of item 1 (the owner's
   `Captured { index }` names one of them), holds every later release (`release_capture_stays`).
   With the grain's cells as targets, the box law (`boxTest`, `boxLaw`) has a sound test at every
   positive grain (`boxLaw_testSound`), and with its steps certified by item 1 a capture certifies
   the reading of `g^[d] z` on the whole source box (`boxLaw_capture_sound`). As the guide says, the
   depth bounds each member's arrival; it does not say that each member first arrives there.
4. **Outward rounding to the bit grain `2^(−k)`**. Over any ordered field with a floor (the owner's
   rationals, or ℝ), `roundDown k x = ⌊x 2^k⌋/2^k ≤ x ≤ ⌈x 2^k⌉/2^k = roundUp k x`, each end moved
   by less than `2^(−k)` (`roundDown_le`, `sub_roundDown_lt`, `le_roundUp`, `roundUp_sub_lt`). An
   enclosure rounded outward keeps every value it held and widens by less than two grains
   (`roundOut_mem`, `roundOut_width`), and a point of the grain is its own rounding, so the rounding
   is a section of the grain (`round_grain`). A complex enclosure rounds at its corners, part by
   part (`cbox`, `roundDownC`, `roundUpC`, `cbox_subset_roundOut`).
5. **η by its alternating series** (`analytic.euler-maclaurin-eta`). For real `s > 0`, `η(s)` is
   the limit of `S_N = Σ_(n<N) (−1)^n (n + 1)^(−s)` (`etaTerm`, `etaPartial`, `eta`,
   `tendsto_etaPartial`, by Mathlib's alternating series test); the partial sums bracket it,
   `S_(2N) ≤ η(s) ≤ S_(2N+1)` (`eta_mem_enclosure`), and `|η(s) − S_N| ≤ (N + 1)^(−s)`
   (`abs_eta_sub_le`).
6. **ζ with its first-order Euler–Maclaurin remainder**. Mathlib's `riemannZeta` at real `s > 1` is
   `Σ_n n^(−s)` (`zetaR`, `riemannZeta_ofReal`), a head of `N` terms and a tail (`zetaHead`,
   `zetaTail`, `zetaR_eq_head_add_tail`). A trapezoid of a function whose derivative is monotone
   lies above the function's integral by at most `(b − a)²/8 (f′ b − f′ a)` (`trapezoid_bracket_mid`,
   `trapezoid_bracket`, by comparing derivatives about the midpoint against a named primitive, with
   no integral taken). On `x^(−s)` over unit steps (`rpow_trapezoid_step`) the bounds telescope
   (`trapezoid_telescope`), and in the limit
   `0 ≤ Σ_(n≥N) n^(−s) − N^(1−s)/(s − 1) − N^(−s)/2 ≤ s N^(−s−1)/8` for `N ≥ 1`
   (`zetaTail_euler_maclaurin`), so `ζ(s)` lies between the head plus the two Euler–Maclaurin terms
   and that plus `s N^(−s−1)/8` (`zeta_mem_enclosure`).
7. **η against ζ, and two witnesses**. `η(s) = (1 − 2^(1−s)) ζ(s)` for real `s > 1`
   (`eta_eq_mul_zeta`, by splitting the even and odd terms). Four terms read
   `473/288 ≤ π²/6 ≤ 473/288 + 1/256` (`zeta_two_enclosure`, against Mathlib's `hasSum_zeta_two`).
   The even partial sums of `η(1)` are `H_(2n) − H_n` (`etaPartial_one_two_mul`), so `η(1) = log 2`
   (`eta_one`, from Mathlib's `Real.tendsto_harmonic_sub_log`) and `S_(2N) ≤ log 2 ≤ S_(2N+1)`,
   within `(N + 1)⁻¹` of `S_N` (`log_two_mem_eta_enclosure`). Read against
   `ConstantNavigators.log_two_enclosure`, whose four atanh terms hold `log 2` within `1/78732`, the
   alternating navigator's stated remainder reaches that width only from `N = 78731` terms on.

What is not claimed. The jets of `analytic.euler-maclaurin-eta` (the first and second derivatives
in `s` of ζ and η, the owner's `ComplexJet2` and `HeadJet`, and their uniform derivative bounds);
complex `s` off the real line (the owner's `ComplexReceiverBox` and its rising-product remainder);
the Euler–Maclaurin terms of higher order with their Bernoulli numbers, and the start `N` derived
from a declared grain (`derive_euler_maclaurin_start`); and the propagation of enclosures through
sums, products and reciprocals as interval arithmetic, beyond the rounding of item 4. The relaxed
release is stated on the points a face encloses; the owner's rational evaluation of a source over
a box, which supplies `M`, `q` and `β`, is the caller's. The guide's contraction (with `q < 1`, a
unique fixed point, a zero of the source when `λ ≠ 0`) is not proved; the self-map needs only
`β + q r ≤ r`. `η(s)` is the limit of its partial sums, since for `0 < s ≤ 1` the series is not
summable in Lean's unconditional sense; it is the `tsum` for `s > 1` (inside `eta_eq_mul_zeta`).

The computational object is the helical pair interaction, read on a certified receiver box. The
release carries the pair (the anchor's value, the derivative bound over the whole box) one step per
tick and transports the box with its remainder named, so the face it retains is a face of the
source, never a sample of it; capture is the receiver's grain reading, and obstruction and
exhaustion are retained faces with their depths. ζ and η are navigators of the same kind: the head
is the declared term count, the Euler–Maclaurin terms and their remainder are the released tail,
and the alternating series carries the pair (current term, partial sum) whose consecutive faces
bracket the value. Of the winding guide's six general objects this touches faces and placement (a
grain cell is a face read at a declared width, and outward rounding a section placed once), the
pair (anchor and box, the even and odd faces of η, the head and the tail of ζ) and the tube (the
horizon of releases is a clocked span whose ticks are the depths); the helix, the cell holonomy and
the tower thread stay attached.

Consumers: the atlas rows `analytic.certified-capture` and `analytic.euler-maclaurin-eta`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Mathematics.CertifiedCapture

open Set Filter Topology Finset

/-! ## 1. Mean-value inclusion -/

section MeanValue

/-- [definition] The closed square box of half-width `r` about `c` (the owner's `B∞(c, r)`). -/
def box (c : ℂ) (r : ℝ) : Set ℂ := {z | |z.re - c.re| ≤ r ∧ |z.im - c.im| ≤ r}

/-- [proved-standard; formal-checked] A box is convex. -/
theorem convex_box (c : ℂ) (r : ℝ) : Convex ℝ (box c r) := by
  intro z hz w hw a b ha hb hab
  have key : ∀ x y m : ℝ, |x - m| ≤ r → |y - m| ≤ r → |a * x + b * y - m| ≤ r := by
    intro x y m hx hy
    have h : a * x + b * y - m = a * (x - m) + b * (y - m) := by
      linear_combination m * hab
    rw [h]
    calc |a * (x - m) + b * (y - m)| ≤ |a * (x - m)| + |b * (y - m)| := abs_add_le _ _
      _ = a * |x - m| + b * |y - m| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * r + b * r := by gcongr
      _ = r := by rw [← add_mul, hab, one_mul]
  constructor
  · simpa using key z.re w.re c.re hz.1 hw.1
  · simpa using key z.im w.im c.im hz.2 hw.2

/-- [proved-standard; formal-checked] The centre lies in its box when the half-width is nonnegative. -/
theorem mem_box_self (c : ℂ) {r : ℝ} (hr : 0 ≤ r) : c ∈ box c r := by
  simp [box, hr]

/-- [proved-standard; formal-checked] **Mean-value inclusion**: `‖f z − f m‖ ≤ M ‖z − m‖` on a convex `B`. -/
theorem norm_sub_le_of_deriv_le {f : ℂ → ℂ} {B : Set ℂ} {M : ℝ} {m z : ℂ} (hB : Convex ℝ B)
    (hf : ∀ w ∈ B, DifferentiableAt ℂ f w) (hM : ∀ w ∈ B, ‖deriv f w‖ ≤ M) (hm : m ∈ B)
    (hz : z ∈ B) : ‖f z - f m‖ ≤ M * ‖z - m‖ :=
  hB.norm_image_sub_le_of_norm_deriv_le hf hM hm hz

/-- [proved-standard; formal-checked] The image of a convex `B ⊆ closedBall m r` lies in `closedBall (f m) (M r)`. -/
theorem image_subset_closedBall {f : ℂ → ℂ} {B : Set ℂ} {M r : ℝ} {m : ℂ} (hB : Convex ℝ B)
    (hf : ∀ w ∈ B, DifferentiableAt ℂ f w) (hM : ∀ w ∈ B, ‖deriv f w‖ ≤ M) (hm : m ∈ B)
    (hBr : B ⊆ Metric.closedBall m r) : f '' B ⊆ Metric.closedBall (f m) (M * r) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM m hm)
  rintro _ ⟨z, hz, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hzr : ‖z - m‖ ≤ r := by simpa [dist_eq_norm] using hBr hz
  calc ‖f z - f m‖ ≤ M * ‖z - m‖ := norm_sub_le_of_deriv_le hB hf hM hm hz
    _ ≤ M * r := by gcongr

/-- [proved-standard; formal-checked] Multiplication by `d` moves each part by at most `(|Re d| + |Im d|) ‖w‖∞`. -/
theorem abs_mul_re_im_le (d w : ℂ) :
    |(d * w).re| ≤ (|d.re| + |d.im|) * max |w.re| |w.im| ∧
      |(d * w).im| ≤ (|d.re| + |d.im|) * max |w.re| |w.im| := by
  have h1 := le_max_left |w.re| |w.im|
  have h2 := le_max_right |w.re| |w.im|
  have hre := abs_nonneg d.re
  have him := abs_nonneg d.im
  rw [Complex.mul_re, Complex.mul_im]
  constructor
  · calc |d.re * w.re - d.im * w.im| ≤ |d.re * w.re| + |d.im * w.im| := abs_sub _ _
      _ = |d.re| * |w.re| + |d.im| * |w.im| := by rw [abs_mul, abs_mul]
      _ ≤ |d.re| * max |w.re| |w.im| + |d.im| * max |w.re| |w.im| := by gcongr
      _ = _ := by ring
  · calc |d.re * w.im + d.im * w.re| ≤ |d.re * w.im| + |d.im * w.re| := abs_add_le _ _
      _ = |d.re| * |w.im| + |d.im| * |w.re| := by rw [abs_mul, abs_mul]
      _ ≤ |d.re| * max |w.re| |w.im| + |d.im| * max |w.re| |w.im| := by gcongr
      _ = _ := by ring

/-- [proved-standard; formal-checked] **Mean-value inclusion on a box**: each part of `f z − f m` is `≤ q ‖z − m‖∞`. -/
theorem box_mean_value {f : ℂ → ℂ} {c : ℂ} {r q : ℝ}
    (hf : ∀ w ∈ box c r, DifferentiableAt ℂ f w)
    (hq : ∀ w ∈ box c r, |(deriv f w).re| + |(deriv f w).im| ≤ q) {z m : ℂ}
    (hz : z ∈ box c r) (hm : m ∈ box c r) :
    |(f z - f m).re| ≤ q * max |(z - m).re| |(z - m).im| ∧
      |(f z - f m).im| ≤ q * max |(z - m).re| |(z - m).im| := by
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, m + (t : ℂ) * (z - m) ∈ box c r := by
    intro t ht
    have h := convex_box c r hm hz (sub_nonneg.mpr ht.2) ht.1 (by ring)
    convert h using 1
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hγ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => f (m + (t : ℂ) * (z - m)))
      (deriv f (m + (t : ℂ) * (z - m)) * (z - m)) t := by
    intro t ht
    have h1 : HasDerivAt (fun u : ℂ => m + u * (z - m)) (z - m) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const (z - m)).const_add m
    exact ((hf _ (hseg t ht)).hasDerivAt.comp (t : ℂ) h1).comp_ofReal
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      |(deriv f (m + (t : ℂ) * (z - m)) * (z - m)).re| ≤ q * max |(z - m).re| |(z - m).im| ∧
        |(deriv f (m + (t : ℂ) * (z - m)) * (z - m)).im| ≤ q * max |(z - m).re| |(z - m).im| := by
    intro t ht
    have hd := abs_mul_re_im_le (deriv f (m + (t : ℂ) * (z - m))) (z - m)
    have hM : 0 ≤ max |(z - m).re| |(z - m).im| := le_max_of_le_left (abs_nonneg _)
    have hqt := hq _ (hseg t ht)
    exact ⟨hd.1.trans (by gcongr), hd.2.trans (by gcongr)⟩
  have hend : ∀ t : ℝ, t = 1 → m + (t : ℂ) * (z - m) = z := by
    rintro t rfl
    simp
  constructor
  · have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun t : ℝ => (f (m + (t : ℂ) * (z - m))).re)
      (f' := fun t => (deriv f (m + (t : ℂ) * (z - m)) * (z - m)).re) (C := q * max |(z - m).re| |(z - m).im|)
      (fun t ht => by
        simpa [Function.comp_def] using ((Complex.reCLM.hasFDerivAt).comp_hasDerivAt t (hγ t ht)).hasDerivWithinAt)
      (fun t ht => by simpa using (hbound t (Ico_subset_Icc_self ht)).1) 1 ⟨zero_le_one, le_rfl⟩
    simpa [hend] using h
  · have h := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun t : ℝ => (f (m + (t : ℂ) * (z - m))).im)
      (f' := fun t => (deriv f (m + (t : ℂ) * (z - m)) * (z - m)).im) (C := q * max |(z - m).re| |(z - m).im|)
      (fun t ht => by
        simpa [Function.comp_def] using ((Complex.imCLM.hasFDerivAt).comp_hasDerivAt t (hγ t ht)).hasDerivWithinAt)
      (fun t ht => by simpa using (hbound t (Ico_subset_Icc_self ht)).2) 1 ⟨zero_le_one, le_rfl⟩
    simpa [hend] using h

/-- [proved-standard; formal-checked] **The released box**: an anchor `c′` within `β` of `f c` and `β + q r ≤ r′`. -/
theorem image_box_subset_box {f : ℂ → ℂ} {c c' : ℂ} {r r' q β : ℝ}
    (hf : ∀ w ∈ box c r, DifferentiableAt ℂ f w)
    (hq : ∀ w ∈ box c r, |(deriv f w).re| + |(deriv f w).im| ≤ q)
    (hβ : |(f c - c').re| ≤ β ∧ |(f c - c').im| ≤ β) (hr' : β + q * r ≤ r') :
    MapsTo f (box c r) (box c' r') := by
  intro z hz
  have hr : 0 ≤ r := (abs_nonneg _).trans hz.1
  have hq0 : 0 ≤ q := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hq c (mem_box_self c hr))
  obtain ⟨h1, h2⟩ := box_mean_value hf hq hz (mem_box_self c hr)
  have hM : max |(z - c).re| |(z - c).im| ≤ r := by
    simpa using max_le hz.1 hz.2
  have hqM : q * max |(z - c).re| |(z - c).im| ≤ q * r := mul_le_mul_of_nonneg_left hM hq0
  have e1 : (f z).re - c'.re = (f z - f c).re + (f c - c').re := by simp
  have e2 : (f z).im - c'.im = (f z - f c).im + (f c - c').im := by simp
  constructor
  · rw [e1]
    exact (abs_add_le _ _).trans (by linarith [hβ.1])
  · rw [e2]
    exact (abs_add_le _ _).trans (by linarith [hβ.2])

/-- [proved-derived; formal-checked] **The owner's capture square**: `β + q r ≤ r` maps `box c r` into itself. -/
theorem box_capture_square {g : ℂ → ℂ} {c : ℂ} {r q β : ℝ}
    (hg : ∀ w ∈ box c r, DifferentiableAt ℂ g w)
    (hq : ∀ w ∈ box c r, |(deriv g w).re| + |(deriv g w).im| ≤ q)
    (hβ : |(g c - c).re| ≤ β ∧ |(g c - c).im| ≤ β) (hmargin : β + q * r ≤ r) :
    MapsTo g (box c r) (box c r) :=
  image_box_subset_box hg hq hβ hmargin

/-- [proved-derived; formal-checked] A capture square holds every later release: `g^[n]` maps it into itself. -/
theorem box_capture_square_iterate {g : ℂ → ℂ} {c : ℂ} {r q β : ℝ}
    (hg : ∀ w ∈ box c r, DifferentiableAt ℂ g w)
    (hq : ∀ w ∈ box c r, |(deriv g w).re| + |(deriv g w).im| ≤ q)
    (hβ : |(g c - c).re| ≤ β ∧ |(g c - c).im| ≤ β) (hmargin : β + q * r ≤ r) (n : ℕ) :
    MapsTo g^[n] (box c r) (box c r) :=
  (box_capture_square hg hq hβ hmargin).iterate n

end MeanValue

/-! ## 2. Capture at a declared grain -/

section Capture

/-- [definition] The grain reading of `w` at grain `u`: `(⌊Re w/u⌋, ⌊Im w/u⌋)`. -/
noncomputable def reading (u : ℝ) (w : ℂ) : ℤ × ℤ := (⌊w.re / u⌋, ⌊w.im / u⌋)

/-- [definition] The cell of the grain `u` with reading `p` (the brief's capture square). -/
def cell (u : ℝ) (p : ℤ × ℤ) : Set ℂ := {w | reading u w = p}

/-- [proved-derived; formal-checked] Membership in a cell is the pair of floor equations. -/
theorem mem_cell_iff {u : ℝ} {w : ℂ} {a b : ℤ} :
    w ∈ cell u (a, b) ↔ ⌊w.re / u⌋ = a ∧ ⌊w.im / u⌋ = b := by
  simp [cell, reading]

/-- [proved-derived; formal-checked] **Capture certifies the reading** of every point of the source box. -/
theorem capture_certifies {f : ℂ → ℂ} {B E : Set ℂ} {u : ℝ} {p : ℤ × ℤ} (hE : f '' B ⊆ E)
    (hcell : E ⊆ cell u p) {z : ℂ} (hz : z ∈ B) : reading u (f z) = p :=
  hcell (hE ⟨z, hz, rfl⟩)

/-- [proved-derived; formal-checked] **Obstruction**: an enclosure holding two readings lies in no cell. -/
theorem not_subset_cell_of_two_readings {E : Set ℂ} {u : ℝ} {w₁ w₂ : ℂ} (h₁ : w₁ ∈ E)
    (h₂ : w₂ ∈ E) (hne : reading u w₁ ≠ reading u w₂) (p : ℤ × ℤ) : ¬ E ⊆ cell u p := by
  intro h
  exact hne ((h h₁).trans (h h₂).symm)

/-- [proved-derived; formal-checked] Two source points with two readings obstruct every enclosure. -/
theorem no_enclosure_certifies {f : ℂ → ℂ} {B E : Set ℂ} {u : ℝ} {z₁ z₂ : ℂ} (h₁ : z₁ ∈ B)
    (h₂ : z₂ ∈ B) (hne : reading u (f z₁) ≠ reading u (f z₂)) (hE : f '' B ⊆ E) (p : ℤ × ℤ) :
    ¬ E ⊆ cell u p :=
  not_subset_cell_of_two_readings (hE ⟨z₁, h₁, rfl⟩) (hE ⟨z₂, h₂, rfl⟩) hne p

/-- [proved-standard; formal-checked] Ends with one floor: every point between them has that floor. -/
theorem floor_div_eq_of_mem {u lo hi x : ℝ} (hu : 0 < u) (h : ⌊lo / u⌋ = ⌊hi / u⌋)
    (hlo : lo ≤ x) (hhi : x ≤ hi) : ⌊x / u⌋ = ⌊lo / u⌋ :=
  le_antisymm (h ▸ Int.floor_mono (div_le_div_of_nonneg_right hhi hu.le))
    (Int.floor_mono (div_le_div_of_nonneg_right hlo hu.le))

/-- [proved-derived; formal-checked] **The box test**: equal floors at both ends of each side capture the box. -/
theorem box_subset_cell {u ρ : ℝ} {w : ℂ} (hu : 0 < u)
    (hre : ⌊(w.re - ρ) / u⌋ = ⌊(w.re + ρ) / u⌋) (him : ⌊(w.im - ρ) / u⌋ = ⌊(w.im + ρ) / u⌋) :
    box w ρ ⊆ cell u (⌊(w.re - ρ) / u⌋, ⌊(w.im - ρ) / u⌋) := by
  intro z hz
  obtain ⟨h1, h2⟩ := abs_le.mp hz.1
  obtain ⟨h3, h4⟩ := abs_le.mp hz.2
  rw [mem_cell_iff]
  exact ⟨floor_div_eq_of_mem hu hre (by linarith) (by linarith),
    floor_div_eq_of_mem hu him (by linarith) (by linarith)⟩

/-- [proved-derived; formal-checked] **Capture or obstruction**: a box lies in one cell, or holds two readings. -/
theorem box_capture_or_obstruction {u ρ : ℝ} (w : ℂ) (hu : 0 < u) (hρ : 0 ≤ ρ) :
    (∃ p, box w ρ ⊆ cell u p) ∨
      ∃ z₁ ∈ box w ρ, ∃ z₂ ∈ box w ρ, reading u z₁ ≠ reading u z₂ := by
  by_cases hre : ⌊(w.re - ρ) / u⌋ = ⌊(w.re + ρ) / u⌋
  · by_cases him : ⌊(w.im - ρ) / u⌋ = ⌊(w.im + ρ) / u⌋
    · exact Or.inl ⟨_, box_subset_cell hu hre him⟩
    · refine Or.inr ⟨w - ρ * Complex.I, ?_, w + ρ * Complex.I, ?_, ?_⟩
      · simp [box, abs_of_nonneg hρ, hρ]
      · simp [box, abs_of_nonneg hρ, hρ]
      · intro h
        apply him
        simpa [reading] using congrArg Prod.snd h
  · refine Or.inr ⟨w - ρ, ?_, w + ρ, ?_, ?_⟩
    · simp [box, abs_of_nonneg hρ, hρ]
    · simp [box, abs_of_nonneg hρ, hρ]
    · intro h
      apply hre
      simpa [reading] using congrArg Prod.fst h

end Capture

/-! ## 3. Relaxed release over a finite horizon -/

section Release

/-- [definition] A release law on faces `α` with captures indexed by `ι`: an enclosure, a step and a test. -/
structure ReleaseLaw (α ι : Type*) where
  /-- The set of complex points a face encloses. -/
  den : α → Set ℂ
  /-- One release of a face; `none` is an obstruction. -/
  step : α → Option α
  /-- The capture test: `some i` claims the face lies in the capture target `i`. -/
  test : α → Option ι

/-- [definition] The three outcomes of a release, each with its depth and the face it retains. -/
inductive Outcome (α ι : Type*) where
  /-- The face at this depth passed the capture test with target `i`. -/
  | capture (depth : ℕ) (face : α) (i : ι)
  /-- The law could not release the face at this depth. -/
  | obstruction (depth : ℕ) (face : α)
  /-- The horizon was spent with the face uncaptured. -/
  | exhaustion (depth : ℕ) (face : α)

namespace Outcome

variable {α ι : Type*}

/-- [definition] The depth an outcome was returned at. -/
def depth : Outcome α ι → ℕ
  | capture d _ _ => d
  | obstruction d _ => d
  | exhaustion d _ => d

/-- [definition] The face an outcome retains. -/
def face : Outcome α ι → α
  | capture _ E _ => E
  | obstruction _ E => E
  | exhaustion _ E => E

end Outcome

variable {α ι : Type*}

/-- [definition] **The relaxed release**: from depth `d`, test the face, else release it, for at most `H` steps. -/
def release (L : ReleaseLaw α ι) : ℕ → ℕ → α → Outcome α ι
  | d, 0, E =>
    match L.test E with
    | some p => .capture d E p
    | none => .exhaustion d E
  | d, H + 1, E =>
    match L.test E with
    | some p => .capture d E p
    | none =>
      match L.step E with
      | none => .obstruction d E
      | some E' => release L (d + 1) H E'

/-- [definition] A law's steps follow the source map `g`: each released face holds the image of the last. -/
def ReleaseLaw.Follows (L : ReleaseLaw α ι) (g : ℂ → ℂ) : Prop :=
  ∀ E E', L.step E = some E' → g '' L.den E ⊆ L.den E'

/-- [definition] A law's capture test is sound for the targets `T`: a passed test puts the face in its target. -/
def ReleaseLaw.TestSound (L : ReleaseLaw α ι) (T : ι → Set ℂ) : Prop :=
  ∀ E i, L.test E = some i → L.den E ⊆ T i

/-- [proved-derived; formal-checked] **The retained face** holds the `n`-th release of the source face, `n ≤ H`. -/
theorem release_face {L : ReleaseLaw α ι} {g : ℂ → ℂ} (hL : L.Follows g) :
    ∀ (H d : ℕ) (E : α), ∃ n, (release L d H E).depth = d + n ∧ n ≤ H ∧
      g^[n] '' L.den E ⊆ L.den (release L d H E).face := by
  intro H
  induction H with
  | zero =>
    intro d E
    refine ⟨0, ?_, le_rfl, ?_⟩ <;> cases h : L.test E <;> simp [release, h, Outcome.depth, Outcome.face]
  | succ H ih =>
    intro d E
    cases ht : L.test E with
    | some p => exact ⟨0, by simp [release, ht, Outcome.depth], by omega, by simp [release, ht, Outcome.face]⟩
    | none =>
      cases hs : L.step E with
      | none =>
        exact ⟨0, by simp [release, ht, hs, Outcome.depth], by omega,
          by simp [release, ht, hs, Outcome.face]⟩
      | some E' =>
        obtain ⟨n, hn, hnH, himg⟩ := ih (d + 1) E'
        refine ⟨n + 1, ?_, by omega, ?_⟩
        · simp only [release, ht, hs]
          rw [hn]
          ring
        · simp only [release, ht, hs]
          refine Subset.trans ?_ himg
          rw [Function.iterate_succ, Set.image_comp]
          exact Set.image_mono (hL E E' hs)

/-- [proved-derived; formal-checked] A capture is returned only on a face that passed the test. -/
theorem release_capture_test {L : ReleaseLaw α ι} :
    ∀ (H d : ℕ) (E : α) {d' : ℕ} {E' : α} {p : ι},
      release L d H E = .capture d' E' p → L.test E' = some p := by
  intro H
  induction H with
  | zero =>
    intro d E d' E' p h
    cases ht : L.test E <;> simp [release, ht] at h
    obtain ⟨-, rfl, rfl⟩ := h
    exact ht
  | succ H ih =>
    intro d E d' E' p h
    cases ht : L.test E with
    | some q =>
      simp [release, ht] at h
      obtain ⟨-, rfl, rfl⟩ := h
      exact ht
    | none =>
      cases hs : L.step E with
      | none => simp [release, ht, hs] at h
      | some E'' =>
        simp only [release, ht, hs] at h
        exact ih (d + 1) E'' h

/-- [proved-derived; formal-checked] **Exhaustion is returned only at the horizon**: its depth is `d + H`. -/
theorem release_exhaustion_depth {L : ReleaseLaw α ι} :
    ∀ (H d : ℕ) (E : α) {d' : ℕ} {E' : α}, release L d H E = .exhaustion d' E' → d' = d + H := by
  intro H
  induction H with
  | zero =>
    intro d E d' E' h
    cases ht : L.test E <;> simp [release, ht] at h
    omega
  | succ H ih =>
    intro d E d' E' h
    cases ht : L.test E with
    | some q => simp [release, ht] at h
    | none =>
      cases hs : L.step E with
      | none => simp [release, ht, hs] at h
      | some E'' =>
        simp only [release, ht, hs] at h
        have := ih (d + 1) E'' h
        omega

/-- [proved-derived; formal-checked] An obstruction is returned only on a face the law could not release. -/
theorem release_obstruction_step {L : ReleaseLaw α ι} :
    ∀ (H d : ℕ) (E : α) {d' : ℕ} {E' : α}, release L d H E = .obstruction d' E' → L.step E' = none := by
  intro H
  induction H with
  | zero =>
    intro d E d' E' h
    cases ht : L.test E <;> simp [release, ht] at h
  | succ H ih =>
    intro d E d' E' h
    cases ht : L.test E with
    | some q => simp [release, ht] at h
    | none =>
      cases hs : L.step E with
      | none =>
        simp [release, ht, hs] at h
        obtain ⟨-, rfl⟩ := h
        exact hs
      | some E'' =>
        simp only [release, ht, hs] at h
        exact ih (d + 1) E'' h

/-- [proved-derived; formal-checked] **Soundness**: a capture at depth `d` puts `g^[d] z` in its target for all `z`. -/
theorem release_capture_sound {L : ReleaseLaw α ι} {g : ℂ → ℂ} {T : ι → Set ℂ} (hL : L.Follows g)
    (hT : L.TestSound T) {H : ℕ} {E₀ E : α} {d : ℕ} {i : ι}
    (h : release L 0 H E₀ = .capture d E i) {z : ℂ} (hz : z ∈ L.den E₀) :
    g^[d] z ∈ T i ∧ d ≤ H := by
  obtain ⟨n, hn, hnH, himg⟩ := release_face hL H 0 E₀
  rw [h] at hn himg
  simp only [Outcome.depth, zero_add] at hn
  subst hn
  exact ⟨hT E i (release_capture_test H 0 E₀ h) (himg ⟨z, hz, rfl⟩), hnH⟩

/-- [proved-derived; formal-checked] A capture into a target `g` maps into itself holds every later release. -/
theorem release_capture_stays {L : ReleaseLaw α ι} {g : ℂ → ℂ} {T : ι → Set ℂ} (hL : L.Follows g)
    (hT : L.TestSound T) {H : ℕ} {E₀ E : α} {d : ℕ} {i : ι}
    (h : release L 0 H E₀ = .capture d E i) (hself : MapsTo g (T i) (T i)) {z : ℂ}
    (hz : z ∈ L.den E₀) (n : ℕ) : g^[n + d] z ∈ T i := by
  rw [Function.iterate_add_apply]
  exact hself.iterate n (release_capture_sound hL hT h hz).1

/-- [definition] The box test at grain `u` on a face `(w, ρ)`: capture when both sides have equal end floors. -/
noncomputable def boxTest (u : ℝ) (E : ℂ × ℝ) : Option (ℤ × ℤ) :=
  if ⌊(E.1.re - E.2) / u⌋ = ⌊(E.1.re + E.2) / u⌋ ∧ ⌊(E.1.im - E.2) / u⌋ = ⌊(E.1.im + E.2) / u⌋ then
    some (⌊(E.1.re - E.2) / u⌋, ⌊(E.1.im - E.2) / u⌋)
  else none

/-- [definition] The box law: faces are `(centre, half-width)`, tested by `boxTest`, released by the caller's step. -/
noncomputable def boxLaw (u : ℝ) (step : ℂ × ℝ → Option (ℂ × ℝ)) : ReleaseLaw (ℂ × ℝ) (ℤ × ℤ) where
  den E := box E.1 E.2
  step := step
  test := boxTest u

/-- [proved-derived; formal-checked] The box test is sound at a positive grain. -/
theorem boxLaw_testSound {u : ℝ} (hu : 0 < u) (step : ℂ × ℝ → Option (ℂ × ℝ)) :
    (boxLaw u step).TestSound (cell u) := by
  intro E p h
  simp only [boxLaw, boxTest] at h
  split_ifs at h with hc
  cases h
  exact box_subset_cell hu hc.1 hc.2

/-- [proved-derived; formal-checked] A capture of the box law certifies the reading of `g^[d] z` on the source box. -/
theorem boxLaw_capture_sound {u : ℝ} (hu : 0 < u) {g : ℂ → ℂ} {step : ℂ × ℝ → Option (ℂ × ℝ)}
    (hstep : ∀ E E', step E = some E' → MapsTo g (box E.1 E.2) (box E'.1 E'.2)) {H d : ℕ}
    {E₀ E : ℂ × ℝ} {p : ℤ × ℤ} (h : release (boxLaw u step) 0 H E₀ = .capture d E p) {z : ℂ}
    (hz : z ∈ box E₀.1 E₀.2) : reading u (g^[d] z) = p :=
  (release_capture_sound (fun E E' hE => (hstep E E' hE).image_subset) (boxLaw_testSound hu step) h
    hz).1

end Release

/-! ## 4. Outward rounding to a bit grain -/

section Rounding

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- [definition] The lower end rounded down to the grain `2^(−k)`: `⌊x 2^k⌋/2^k`. -/
def roundDown (k : ℕ) (x : K) : K := ⌊x * 2 ^ k⌋ / 2 ^ k

/-- [definition] The upper end rounded up to the grain `2^(−k)`: `⌈x 2^k⌉/2^k`. -/
def roundUp (k : ℕ) (x : K) : K := ⌈x * 2 ^ k⌉ / 2 ^ k

omit [FloorRing K] in
/-- [proved-standard; formal-checked] The grain's denominator is positive. -/
private theorem two_pow_pos' (k : ℕ) : (0 : K) < 2 ^ k := by positivity

/-- [proved-standard; formal-checked] Rounding down keeps the value above: `roundDown k x ≤ x`. -/
theorem roundDown_le (k : ℕ) (x : K) : roundDown k x ≤ x := by
  rw [roundDown, div_le_iff₀ (two_pow_pos' k)]
  exact Int.floor_le _

/-- [proved-standard; formal-checked] Rounding down moves the end by less than one grain. -/
theorem sub_roundDown_lt (k : ℕ) (x : K) : x - roundDown k x < 1 / 2 ^ k := by
  have h := Int.sub_one_lt_floor (x * 2 ^ k)
  have hp := two_pow_pos' (K := K) k
  rw [roundDown, sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ hp]
  linarith

/-- [proved-standard; formal-checked] Rounding up keeps the value below: `x ≤ roundUp k x`. -/
theorem le_roundUp (k : ℕ) (x : K) : x ≤ roundUp k x := by
  rw [roundUp, le_div_iff₀ (two_pow_pos' k)]
  exact Int.le_ceil _

/-- [proved-standard; formal-checked] Rounding up moves the end by less than one grain. -/
theorem roundUp_sub_lt (k : ℕ) (x : K) : roundUp k x - x < 1 / 2 ^ k := by
  have h := Int.ceil_lt_add_one (x * 2 ^ k)
  have hp := two_pow_pos' (K := K) k
  rw [roundUp, sub_lt_iff_lt_add, div_lt_iff₀ hp, add_mul, one_div, inv_mul_cancel₀ hp.ne']
  linarith

/-- [proved-standard; formal-checked] **A section**: a point of the grain is its own rounding, down and up. -/
theorem round_grain (k : ℕ) (m : ℤ) :
    roundDown k ((m : K) / 2 ^ k) = m / 2 ^ k ∧ roundUp k ((m : K) / 2 ^ k) = m / 2 ^ k := by
  have hp := (two_pow_pos' (K := K) k).ne'
  simp [roundDown, roundUp, div_mul_cancel₀ _ hp]

/-- [proved-standard; formal-checked] **Outward rounding keeps the enclosure**: `lo ≤ v ≤ hi` survives it. -/
theorem roundOut_mem {k : ℕ} {lo hi v : K} (hlo : lo ≤ v) (hhi : v ≤ hi) :
    roundDown k lo ≤ v ∧ v ≤ roundUp k hi :=
  ⟨(roundDown_le k lo).trans hlo, hhi.trans (le_roundUp k hi)⟩

/-- [proved-standard; formal-checked] The rounded enclosure is less than two grains wider than the enclosure. -/
theorem roundOut_width (k : ℕ) (lo hi : K) :
    roundUp k hi - roundDown k lo < hi - lo + 2 / 2 ^ k := by
  have h1 := sub_roundDown_lt k lo
  have h2 := roundUp_sub_lt k hi
  have : (2 : K) / 2 ^ k = 1 / 2 ^ k + 1 / 2 ^ k := by ring
  linarith

/-- [definition] A complex enclosure by its corners: `lo.re ≤ Re z ≤ hi.re` and `lo.im ≤ Im z ≤ hi.im`. -/
def cbox (lo hi : ℂ) : Set ℂ := {z | lo.re ≤ z.re ∧ z.re ≤ hi.re ∧ lo.im ≤ z.im ∧ z.im ≤ hi.im}

/-- [definition] The lower corner rounded down componentwise. -/
noncomputable def roundDownC (k : ℕ) (z : ℂ) : ℂ := ⟨roundDown k z.re, roundDown k z.im⟩

/-- [definition] The upper corner rounded up componentwise. -/
noncomputable def roundUpC (k : ℕ) (z : ℂ) : ℂ := ⟨roundUp k z.re, roundUp k z.im⟩

/-- [proved-standard; formal-checked] **Complex outward rounding keeps the box**, each side widened by under a grain. -/
theorem cbox_subset_roundOut (k : ℕ) (lo hi : ℂ) :
    cbox lo hi ⊆ cbox (roundDownC k lo) (roundUpC k hi) ∧
      lo.re - (roundDownC k lo).re < 1 / 2 ^ k ∧ (roundUpC k hi).re - hi.re < 1 / 2 ^ k ∧
      lo.im - (roundDownC k lo).im < 1 / 2 ^ k ∧ (roundUpC k hi).im - hi.im < 1 / 2 ^ k := by
  refine ⟨?_, sub_roundDown_lt k _, roundUp_sub_lt k _, sub_roundDown_lt k _, roundUp_sub_lt k _⟩
  rintro z ⟨h1, h2, h3, h4⟩
  exact ⟨(roundOut_mem h1 h2).1, (roundOut_mem h1 h2).2, (roundOut_mem h3 h4).1,
    (roundOut_mem h3 h4).2⟩

end Rounding

/-! ## 5. η by its alternating series -/

section Eta

/-- [definition] The `n`-th magnitude of η's series: `(n + 1)^(−s)`. -/
noncomputable def etaTerm (s : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-s)

/-- [definition] η's partial navigator: `S_N = Σ_(n<N) (−1)^n (n + 1)^(−s)`. -/
noncomputable def etaPartial (s : ℝ) (N : ℕ) : ℝ := ∑ n ∈ range N, (-1) ^ n * etaTerm s n

/-- [definition] Dirichlet's η at real `s`, the limit of its partial navigator. -/
noncomputable def eta (s : ℝ) : ℝ := limUnder atTop (etaPartial s)

/-- [proved-standard; formal-checked] η's magnitudes are nonnegative. -/
theorem etaTerm_nonneg (s : ℝ) (n : ℕ) : 0 ≤ etaTerm s n := by
  unfold etaTerm
  positivity

/-- [proved-standard; formal-checked] η's magnitudes decrease for `s ≥ 0`. -/
theorem etaTerm_antitone {s : ℝ} (hs : 0 ≤ s) : Antitone (etaTerm s) := by
  intro m n hmn
  unfold etaTerm
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (by gcongr) (neg_nonpos.mpr hs)

/-- [proved-standard; formal-checked] η's magnitudes tend to `0` for `s > 0`. -/
theorem tendsto_etaTerm {s : ℝ} (hs : 0 < s) : Tendsto (etaTerm s) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hs).comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

/-- [proved-standard; formal-checked] For `s > 0` the alternating series converges to `eta s`. -/
theorem tendsto_etaPartial {s : ℝ} (hs : 0 < s) : Tendsto (etaPartial s) atTop (𝓝 (eta s)) :=
  tendsto_nhds_limUnder
    ((etaTerm_antitone hs.le).tendsto_alternating_series_of_tendsto_zero (tendsto_etaTerm hs))

/-- [proved-standard; formal-checked] **η's enclosure**: `S_(2N) ≤ η(s) ≤ S_(2N+1)` for `s > 0`. -/
theorem eta_mem_enclosure {s : ℝ} (hs : 0 < s) (N : ℕ) :
    etaPartial s (2 * N) ≤ eta s ∧ eta s ≤ etaPartial s (2 * N + 1) :=
  ⟨(etaTerm_antitone hs.le).alternating_series_le_tendsto (tendsto_etaPartial hs) N,
    (etaTerm_antitone hs.le).tendsto_le_alternating_series (tendsto_etaPartial hs) N⟩

/-- [proved-standard; formal-checked] **η's remainder**: `|η(s) − S_N| ≤ (N + 1)^(−s)` for `s > 0`. -/
theorem abs_eta_sub_le {s : ℝ} (hs : 0 < s) (N : ℕ) : |eta s - etaPartial s N| ≤ etaTerm s N := by
  have hsucc : ∀ n, etaPartial s (n + 1) = etaPartial s n + (-1) ^ n * etaTerm s n := fun n => by
    simp [etaPartial, sum_range_succ]
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' N
  · obtain ⟨h1, h2⟩ := eta_mem_enclosure hs k
    rw [hsucc, pow_mul] at h2
    simp only [neg_one_sq, one_pow, one_mul] at h2
    rw [abs_le]
    constructor <;> linarith [etaTerm_nonneg s (2 * k)]
  · obtain ⟨-, h2⟩ := eta_mem_enclosure hs k
    have h1 := (eta_mem_enclosure hs (k + 1)).1
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, hsucc, pow_succ, pow_mul] at h1
    simp only [neg_one_sq, one_pow, one_mul, neg_mul] at h1
    rw [abs_le]
    constructor <;> linarith [etaTerm_nonneg s (2 * k + 1)]

end Eta

/-! ## 6. ζ with its first-order Euler–Maclaurin remainder -/

section Zeta

/-- [definition] The real ζ at `s`: `Σ_(n≥0) n^(−s)` (the `n = 0` term is `0^(−s) = 0`). -/
noncomputable def zetaR (s : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-s)

/-- [definition] ζ's head: `Σ_(n<N) n^(−s)`. -/
noncomputable def zetaHead (s : ℝ) (N : ℕ) : ℝ := ∑ n ∈ range N, (n : ℝ) ^ (-s)

/-- [definition] ζ's tail from `N`: `Σ_(i≥0) (i + N)^(−s)`. -/
noncomputable def zetaTail (s : ℝ) (N : ℕ) : ℝ := ∑' i : ℕ, ((i + N : ℕ) : ℝ) ^ (-s)

/-- [proved-standard; formal-checked] `Σ n^(−s)` is summable for `s > 1`. -/
theorem summable_rpow_neg {s : ℝ} (hs : 1 < s) : Summable (fun n : ℕ => (n : ℝ) ^ (-s)) :=
  Real.summable_nat_rpow.mpr (by linarith)

/-- [proved-standard; formal-checked] Mathlib's `riemannZeta` at real `s > 1` is the real series `zetaR s`. -/
theorem riemannZeta_ofReal {s : ℝ} (hs : 1 < s) : riemannZeta s = zetaR s := by
  rw [zeta_eq_tsum_one_div_nat_cpow (by simpa using hs), zetaR, Complex.ofReal_tsum]
  congr 1
  funext n
  rw [Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_inv,
    Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, one_div]

/-- [proved-standard; formal-checked] The head and the tail make ζ: `ζ(s) = Σ_(n<N) n^(−s) + Σ_(n≥N) n^(−s)`. -/
theorem zetaR_eq_head_add_tail {s : ℝ} (hs : 1 < s) (N : ℕ) :
    zetaR s = zetaHead s N + zetaTail s N :=
  ((summable_rpow_neg hs).sum_add_tsum_nat_add N).symm

/-- [proved-standard; formal-checked] The trapezoid's bracket about a midpoint `m` with half-width `H`. -/
theorem trapezoid_bracket_mid {f f' F : ℝ → ℝ} {m H : ℝ} (hH0 : 0 ≤ H)
    (hF : ∀ x ∈ Icc (m - H) (m + H), HasDerivAt F (f x) x)
    (hf : ∀ x ∈ Icc (m - H) (m + H), HasDerivAt f (f' x) x)
    (hmono : MonotoneOn f' (Icc (m - H) (m + H))) :
    0 ≤ H * (f (m - H) + f (m + H)) - (F (m + H) - F (m - H)) ∧
      H * (f (m - H) + f (m + H)) - (F (m + H) - F (m - H)) ≤
        H ^ 2 / 2 * (f' (m + H) - f' (m - H)) := by
  have hin : ∀ h ∈ Icc 0 H, m - h ∈ Icc (m - H) (m + H) ∧ m + h ∈ Icc (m - H) (m + H) := by
    rintro h ⟨h0, h1⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  let φ : ℝ → ℝ := fun h => h * (f (m - h) + f (m + h)) - (F (m + h) - F (m - h))
  have hφ : ∀ h ∈ Icc 0 H, HasDerivAt φ (h * (f' (m + h) - f' (m - h))) h := by
    intro h hh
    obtain ⟨h1, h2⟩ := hin h hh
    have e1 := (hf _ h1).comp_const_sub m h
    have e2 := (hf _ h2).comp_const_add m h
    have e3 := (hF _ h1).comp_const_sub m h
    have e4 := (hF _ h2).comp_const_add m h
    refine (((hasDerivAt_id' h).fun_mul (e1.fun_add e2)).fun_sub (e4.fun_sub e3)).congr_deriv ?_
    ring
  -- the comparison `c h²/2 − φ h` with `c = f′ (m + H) − f′ (m − H)`
  let ψ : ℝ → ℝ := fun h => (f' (m + H) - f' (m - H)) * h ^ 2 / 2 - φ h
  have hψ : ∀ h ∈ Icc 0 H, HasDerivAt ψ
      ((f' (m + H) - f' (m - H)) * h - h * (f' (m + h) - f' (m - h))) h := by
    intro h hh
    refine ((((hasDerivAt_pow 2 h).const_mul (f' (m + H) - f' (m - H))).div_const 2).fun_sub
      (hφ h hh)).congr_deriv ?_
    norm_num
    ring
  have hφ' : ∀ h ∈ interior (Icc 0 H), 0 ≤ h * (f' (m + h) - f' (m - h)) := by
    intro h hh
    rw [interior_Icc] at hh
    obtain ⟨h1, h2⟩ := hin h (Ioo_subset_Icc_self hh)
    have : f' (m - h) ≤ f' (m + h) := hmono h1 h2 (by linarith [hh.1])
    exact mul_nonneg hh.1.le (by linarith)
  have hψ' : ∀ h ∈ interior (Icc 0 H),
      0 ≤ (f' (m + H) - f' (m - H)) * h - h * (f' (m + h) - f' (m - h)) := by
    intro h hh
    rw [interior_Icc] at hh
    obtain ⟨h1, h2⟩ := hin h (Ioo_subset_Icc_self hh)
    have ha : m - H ∈ Icc (m - H) (m + H) := ⟨le_rfl, by linarith⟩
    have hb : m + H ∈ Icc (m - H) (m + H) := ⟨by linarith, le_rfl⟩
    have u1 : f' (m + h) ≤ f' (m + H) := hmono h2 hb h2.2
    have u2 : f' (m - H) ≤ f' (m - h) := hmono ha h1 h1.1
    have : (f' (m + H) - f' (m - H)) * h - h * (f' (m + h) - f' (m - h)) =
        h * ((f' (m + H) - f' (m + h)) + (f' (m - h) - f' (m - H))) := by ring
    rw [this]
    exact mul_nonneg hh.1.le (by linarith)
  have monoφ : MonotoneOn φ (Icc 0 H) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 H)
      (fun h hh => (hφ h hh).continuousAt.continuousWithinAt)
      (fun h hh => (hφ h (interior_subset hh)).hasDerivWithinAt) hφ'
  have monoψ : MonotoneOn ψ (Icc 0 H) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 H)
      (fun h hh => (hψ h hh).continuousAt.continuousWithinAt)
      (fun h hh => (hψ h (interior_subset hh)).hasDerivWithinAt) hψ'
  have h0 : (0 : ℝ) ∈ Icc 0 H := ⟨le_rfl, hH0⟩
  have hHmem : H ∈ Icc 0 H := ⟨hH0, le_rfl⟩
  have l1 := monoφ h0 hHmem hH0
  have l2 := monoψ h0 hHmem hH0
  simp only [φ, ψ, sub_zero, add_zero, zero_mul, sub_self, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, zero_div] at l1 l2
  constructor <;> linarith

/-- [proved-standard; formal-checked] **The trapezoid's bracket** on `[a, b]`, error in `[0, (b − a)²/8 Δf′]`. -/
theorem trapezoid_bracket {f f' F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (f x) x) (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hmono : MonotoneOn f' (Icc a b)) :
    0 ≤ (b - a) / 2 * (f a + f b) - (F b - F a) ∧
      (b - a) / 2 * (f a + f b) - (F b - F a) ≤ (b - a) ^ 2 / 8 * (f' b - f' a) := by
  have e1 : (a + b) / 2 - (b - a) / 2 = a := by ring
  have e2 : (a + b) / 2 + (b - a) / 2 = b := by ring
  have h := trapezoid_bracket_mid (m := (a + b) / 2) (H := (b - a) / 2) (by linarith)
    (by rw [e1, e2]; exact hF) (by rw [e1, e2]; exact hf) (by rw [e1, e2]; exact hmono)
  rw [e1, e2] at h
  have e3 : ((b - a) / 2) ^ 2 / 2 = (b - a) ^ 2 / 8 := by ring
  rw [e3] at h
  exact h


/-- [proved-standard; formal-checked] One trapezoid of `x^(−s)` on `[x, x + 1]`, primitive `x^(1−s)/(1 − s)`. -/
theorem rpow_trapezoid_step {s x : ℝ} (hs : 1 < s) (hx : 0 < x) :
    0 ≤ (x ^ (-s) + (x + 1) ^ (-s)) / 2 - ((x + 1) ^ (1 - s) / (1 - s) - x ^ (1 - s) / (1 - s)) ∧
      (x ^ (-s) + (x + 1) ^ (-s)) / 2 - ((x + 1) ^ (1 - s) / (1 - s) - x ^ (1 - s) / (1 - s)) ≤
        (-s * (x + 1) ^ (-s - 1) - -s * x ^ (-s - 1)) / 8 := by
  have hs1 : (1 : ℝ) - s ≠ 0 := by linarith
  have hpos : ∀ t ∈ Icc x (x + 1), 0 < t := fun t ht => hx.trans_le ht.1
  have hF : ∀ t ∈ Icc x (x + 1), HasDerivAt (fun t : ℝ => t ^ (1 - s) / (1 - s)) (t ^ (-s)) t := by
    intro t ht
    refine ((Real.hasDerivAt_rpow_const (p := 1 - s) (Or.inl (hpos t ht).ne')).div_const
      (1 - s)).congr_deriv ?_
    rw [show 1 - s - 1 = -s by ring]
    field_simp
  have hf : ∀ t ∈ Icc x (x + 1), HasDerivAt (fun t : ℝ => t ^ (-s)) (-s * t ^ (-s - 1)) t :=
    fun t ht => Real.hasDerivAt_rpow_const (Or.inl (hpos t ht).ne')
  have hmono : MonotoneOn (fun t : ℝ => -s * t ^ (-s - 1)) (Icc x (x + 1)) := by
    intro t₁ h₁ t₂ h₂ h12
    exact mul_le_mul_of_nonpos_left
      (Real.rpow_le_rpow_of_nonpos (hpos t₁ h₁) h12 (by linarith)) (by linarith)
  have h := trapezoid_bracket (by linarith) hF hf hmono
  simp only [add_sub_cancel_left, one_pow] at h
  constructor <;> linarith [h.1, h.2]

/-- [proved-standard; formal-checked] **The telescoped trapezoids** from `x₀`, over `K` unit steps. -/
theorem trapezoid_telescope {f F f' : ℝ → ℝ} {x₀ : ℝ}
    (hstep : ∀ i : ℕ,
      0 ≤ (f (x₀ + i) + f (x₀ + i + 1)) / 2 - (F (x₀ + i + 1) - F (x₀ + i)) ∧
        (f (x₀ + i) + f (x₀ + i + 1)) / 2 - (F (x₀ + i + 1) - F (x₀ + i)) ≤
          (f' (x₀ + i + 1) - f' (x₀ + i)) / 8) (K : ℕ) :
    0 ≤ ∑ i ∈ range K, f (x₀ + i) - f x₀ / 2 + f (x₀ + K) / 2 - (F (x₀ + K) - F x₀) ∧
      ∑ i ∈ range K, f (x₀ + i) - f x₀ / 2 + f (x₀ + K) / 2 - (F (x₀ + K) - F x₀) ≤
        (f' (x₀ + K) - f' x₀) / 8 := by
  induction K with
  | zero => simp
  | succ K ih =>
    have e : x₀ + ((K + 1 : ℕ) : ℝ) = x₀ + K + 1 := by push_cast; ring
    rw [sum_range_succ, e]
    obtain ⟨h1, h2⟩ := hstep K
    obtain ⟨i1, i2⟩ := ih
    constructor <;> linarith

/-- [proved-standard; formal-checked] ζ's tail from `N` is summable for `s > 1`. -/
theorem summable_zetaTail {s : ℝ} (hs : 1 < s) (N : ℕ) :
    Summable (fun i : ℕ => ((i + N : ℕ) : ℝ) ^ (-s)) :=
  (summable_nat_add_iff N).mpr (summable_rpow_neg hs)

/-- [proved-standard; formal-checked] **ζ's Euler–Maclaurin remainder** after `N ≥ 1` terms: in `[0, s N^(−s−1)/8]`. -/
theorem zetaTail_euler_maclaurin {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 1 ≤ N) :
    0 ≤ zetaTail s N - (N : ℝ) ^ (1 - s) / (s - 1) - (N : ℝ) ^ (-s) / 2 ∧
      zetaTail s N - (N : ℝ) ^ (1 - s) / (s - 1) - (N : ℝ) ^ (-s) / 2 ≤
        s * (N : ℝ) ^ (-s - 1) / 8 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set f : ℝ → ℝ := fun t => t ^ (-s) with hf
  set F : ℝ → ℝ := fun t => t ^ (1 - s) / (1 - s) with hF
  set f' : ℝ → ℝ := fun t => -s * t ^ (-s - 1) with hf'
  have hstep : ∀ i : ℕ,
      0 ≤ (f (N + i) + f (N + i + 1)) / 2 - (F (N + i + 1) - F (N + i)) ∧
        (f (N + i) + f (N + i + 1)) / 2 - (F (N + i + 1) - F (N + i)) ≤
          (f' (N + i + 1) - f' (N + i)) / 8 :=
    fun i => rpow_trapezoid_step hs (by positivity)
  have htel := trapezoid_telescope hstep
  -- the moving ends tend to zero
  have hgo : Tendsto (fun K : ℕ => (N : ℝ) + K) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hf0 : Tendsto (fun K : ℕ => f (N + K)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < s)).comp hgo
  have hF0 : Tendsto (fun K : ℕ => F (N + K)) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < s - 1)).comp hgo).div_const (1 - s)
    rw [zero_div] at h
    refine h.congr fun K => ?_
    simp only [Function.comp, hF, neg_sub]
  have hf'0 : Tendsto (fun K : ℕ => f' (N + K)) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < s + 1)).comp hgo).const_mul (-s)
    rw [mul_zero] at h
    refine h.congr fun K => ?_
    simp only [Function.comp, hf', neg_add']
  have hsum : Tendsto (fun K : ℕ => ∑ i ∈ range K, f (N + i)) atTop (𝓝 (zetaTail s N)) := by
    have h := (summable_zetaTail hs N).tendsto_sum_tsum_nat
    refine h.congr fun K => sum_congr rfl fun i _ => ?_
    simp only [hf]
    rw [Nat.cast_add, add_comm]
  have hD := ((hsum.sub_const (f N / 2)).add (hf0.div_const 2)).sub (hF0.sub_const (F N))
  have hB := (hf'0.sub_const (f' N)).div_const 8
  have l1 := ge_of_tendsto' hD fun K => (htel K).1
  have l2 := le_of_tendsto_of_tendsto' hD hB fun K => (htel K).2
  have hFN : F N = -((N : ℝ) ^ (1 - s) / (s - 1)) := by
    simp only [hF]
    rw [← div_neg, neg_sub]
  simp only [hf, hf', hFN, zero_div, add_zero, zero_sub] at l1 l2
  constructor <;> linarith

/-- [proved-standard; formal-checked] **ζ's enclosure** at real `s > 1` from a head of `N ≥ 1` terms. -/
theorem zeta_mem_enclosure {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 1 ≤ N) :
    zetaHead s N + (N : ℝ) ^ (1 - s) / (s - 1) + (N : ℝ) ^ (-s) / 2 ≤ (riemannZeta s).re ∧
      (riemannZeta s).re ≤
        zetaHead s N + (N : ℝ) ^ (1 - s) / (s - 1) + (N : ℝ) ^ (-s) / 2 + s * (N : ℝ) ^ (-s - 1) / 8 := by
  rw [riemannZeta_ofReal hs, Complex.ofReal_re, zetaR_eq_head_add_tail hs N]
  obtain ⟨h1, h2⟩ := zetaTail_euler_maclaurin hs hN
  constructor <;> linarith

end Zeta


/-! ## 7. η against ζ, and two witnesses -/

section Witness

/-- [proved-standard; formal-checked] η's magnitudes are summable for `s > 1`. -/
theorem summable_etaTerm {s : ℝ} (hs : 1 < s) : Summable (etaTerm s) := by
  have h := (summable_nat_add_iff 1).mpr (summable_rpow_neg hs)
  refine h.congr fun n => ?_
  simp [etaTerm]

/-- [proved-standard; formal-checked] ζ by the shifted series: `zetaR s = Σ_(n≥0) (n + 1)^(−s)`. -/
theorem zetaR_eq_tsum_etaTerm {s : ℝ} (hs : 1 < s) : zetaR s = ∑' n : ℕ, etaTerm s n := by
  rw [zetaR, (summable_rpow_neg hs).tsum_eq_zero_add]
  simp [etaTerm, Real.zero_rpow (by linarith : -s ≠ 0)]

/-- [proved-standard; formal-checked] **η against ζ**: `η(s) = (1 − 2^(1−s)) ζ(s)` for real `s > 1`. -/
theorem eta_eq_mul_zeta {s : ℝ} (hs : 1 < s) : eta s = (1 - 2 ^ (1 - s)) * (riemannZeta s).re := by
  rw [riemannZeta_ofReal hs, Complex.ofReal_re, zetaR_eq_tsum_etaTerm hs]
  have hsum := summable_etaTerm hs
  have hev : Summable (fun k => etaTerm s (2 * k)) :=
    hsum.comp_injective (fun a b h => by simpa using h)
  have hod : Summable (fun k => etaTerm s (2 * k + 1)) :=
    hsum.comp_injective (fun a b h => by simpa using h)
  have heta : eta s = ∑' n : ℕ, (-1) ^ n * etaTerm s n :=
    tendsto_nhds_unique (tendsto_etaPartial (by linarith)) hsum.tendsto_alternating_series_tsum
  have hE : (fun k : ℕ => (-1 : ℝ) ^ (2 * k) * etaTerm s (2 * k)) = fun k => etaTerm s (2 * k) :=
    funext fun k => by simp [pow_mul]
  have hO : (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) * etaTerm s (2 * k + 1)) =
      fun k => -etaTerm s (2 * k + 1) :=
    funext fun k => by simp [pow_succ, pow_mul]
  have hsplit := tsum_even_add_odd (f := fun n => (-1) ^ n * etaTerm s n)
    (by rw [hE]; exact hev) (by rw [hO]; exact hod.neg)
  rw [hE, hO, tsum_neg] at hsplit
  have hzsplit := tsum_even_add_odd hev hod
  have hodd : ∑' k : ℕ, etaTerm s (2 * k + 1) = 2 ^ (-s) * ∑' n : ℕ, etaTerm s n := by
    rw [← tsum_mul_left]
    congr 1
    funext k
    simp only [etaTerm]
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    push_cast
    ring_nf
  have h2 : (2 : ℝ) ^ (1 - s) = 2 * 2 ^ (-s) := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]
  rw [heta, ← hsplit, h2]
  linear_combination hzsplit - 2 * hodd

/-- [proved-standard; formal-checked] **ζ(2) from four terms**: `473/288 ≤ π²/6 ≤ 473/288 + 1/256`. -/
theorem zeta_two_enclosure :
    (473 / 288 : ℝ) ≤ Real.pi ^ 2 / 6 ∧ Real.pi ^ 2 / 6 ≤ 473 / 288 + 1 / 256 := by
  have hz : zetaR 2 = Real.pi ^ 2 / 6 := by
    rw [zetaR, ← hasSum_zeta_two.tsum_eq]
    congr 1
    funext n
    rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_two, one_div]
  have h := zeta_mem_enclosure (s := 2) (by norm_num) (N := 4) (by norm_num)
  rw [riemannZeta_ofReal (by norm_num), Complex.ofReal_re, hz] at h
  have hhead : zetaHead 2 4 = 49 / 36 := by
    simp [zetaHead, sum_range_succ]
    norm_num
  have e1 : (4 : ℝ) ^ (1 - (2 : ℝ)) = 1 / 4 := by norm_num [Real.rpow_neg_one]
  have e2 : (4 : ℝ) ^ (-(2 : ℝ)) = 1 / 16 := by norm_num [Real.rpow_neg, Real.rpow_two]
  have e3 : (4 : ℝ) ^ (-(2 : ℝ) - 1) = 1 / 64 := by
    rw [show -(2 : ℝ) - 1 = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_natCast]
    norm_num
  push_cast at h
  rw [hhead, e1, e2, e3] at h
  constructor <;> linarith [h.1, h.2]

/-- [proved-standard; formal-checked] At `s = 1` the magnitudes are `(n + 1)⁻¹`. -/
theorem etaTerm_one (n : ℕ) : etaTerm 1 n = ((n : ℝ) + 1)⁻¹ := by
  simp [etaTerm, Real.rpow_neg_one]

/-- [proved-standard; formal-checked] The even partial sums of η(1) are differences of harmonic numbers. -/
theorem etaPartial_one_two_mul (n : ℕ) :
    etaPartial 1 (2 * n) = (harmonic (2 * n) : ℝ) - harmonic n := by
  induction n with
  | zero => simp [etaPartial]
  | succ n ih =>
    have e : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [e, etaPartial, sum_range_succ, sum_range_succ, ← etaPartial, ih, harmonic_succ,
      harmonic_succ, harmonic_succ, etaTerm_one, etaTerm_one]
    push_cast
    simp only [pow_succ, pow_mul]
    field_simp
    ring

/-- [proved-standard; formal-checked] **η(1) = log 2**: the alternating harmonic series reads `log 2`. -/
theorem eta_one : eta 1 = Real.log 2 := by
  have h2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => show n ≤ 2 * n by omega) tendsto_id
  have hH := Real.tendsto_harmonic_sub_log
  have hlim : Tendsto (fun n : ℕ => etaPartial 1 (2 * n)) atTop (𝓝 (Real.log 2)) := by
    have h := ((hH.comp h2).sub hH).const_add (Real.log 2)
    rw [sub_self, add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp only [Function.comp, etaPartial_one_two_mul]
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul two_ne_zero hn0]
    ring
  exact tendsto_nhds_unique ((tendsto_etaPartial one_pos).comp h2) hlim

/-- [proved-standard; formal-checked] **`log 2` by η's faces**: `S_(2N) ≤ log 2 ≤ S_(2N+1)`; `S_N` within `1/(N+1)`. -/
theorem log_two_mem_eta_enclosure (N : ℕ) :
    etaPartial 1 (2 * N) ≤ Real.log 2 ∧ Real.log 2 ≤ etaPartial 1 (2 * N + 1) ∧
      |Real.log 2 - etaPartial 1 N| ≤ ((N : ℝ) + 1)⁻¹ := by
  rw [← eta_one, ← etaTerm_one]
  exact ⟨(eta_mem_enclosure one_pos N).1, (eta_mem_enclosure one_pos N).2, abs_eta_sub_le one_pos N⟩

end Witness

end Holonics.Mathematics.CertifiedCapture

import HolonicsResearch.Mathematics.CertifiedCapture
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# ζ's jets in `s`, ζ and η at complex `s`, and the `B₂` Euler–Maclaurin term

The box of #410 "`series.log-atanh`, `series.log-atanh-exp`, `series.common-continued-fraction`,
`analytic.certified-capture`, `analytic.euler-maclaurin-eta` (constants as navigators, parked in
#409)" is answered in part by `HolonicsResearch/Mathematics/ConstantNavigators` (#1028) and
`HolonicsResearch/Mathematics/CertifiedCapture` (#1032), whose "What is not claimed" leaves "the
jets of `analytic.euler-maclaurin-eta` (the first and second derivatives in `s` of ζ and η, the
owner's `ComplexJet2` and `HeadJet`, and their uniform derivative bounds); complex `s` off the real
line (the owner's `ComplexReceiverBox` and its rising-product remainder); the Euler–Maclaurin terms
of higher order with their Bernoulli numbers, and the start `N` derived from a declared grain
(`derive_euler_maclaurin_start`)". This file takes them, to the `B₂` term. Their owner was the
retired `crates/holonics/src/geometry/exact_analysis/special.rs`
([history](https://github.com/brandonrdug/holonics/tree/13f8c734/crates/holonics/src/geometry/exact_analysis)):
`zeta_euler_maclaurin_jet2_with_head`, `euler_maclaurin_remainder_bound`
(`|B_2m|/(2m)! · Π_(i<2m) (|σ + i| + |τ|) · N^(1−σ−2m)/(σ + 2m − 1)`), `log_power_tail_factor`
(`N^a ∫_N^∞ x^(−a−1) (log x)^k dx = Σ_(t≤k) k!/t! (log N)^t/a^(k−t+1)`),
`zeta_derivative_bound_uniform` and `derive_euler_maclaurin_start`. The guide
`docs/ANALYTIC_FLUX_AND_RECEIVING_BASINS.md` ("Executable receiving regions in rationals") asks a
source's callback to "enclose the same holomorphic source and its first two derivatives throughout
every requested box, including its analytic remainder", and its `q ≥ |Re N′| + |Im N′|` is the
capture square's datum (`CertifiedCapture.box_capture_square`). The atlas row is
`analytic.euler-maclaurin-eta` (`docs/atlas/arithmetic.tsv`), beside `analytic.certified-capture`;
the record that built `CertifiedCapture` is November 19's
`2026-11-19_A_METRICS_JET_BUILDS_THE_TIDE_…_A_RELEASE_CERTIFIES_ITS_CAPTURE_ON_THE_WHOLE_BOX_IN_LEAN.md`.
The precision law of `CLAUDE.md` gives the reading: a number is read at a declared width, and a
term is released only by partition at a declared tolerance with its remainder accounted. Every head
below is a declared count of terms, and every tail is released with its remainder named.

[proved-standard; formal-checked] What is proved.

1. **Complex `s`** (the owner's `ComplexReceiverBox`). For `σ = Re s > 0`, `n^(−s)` lies within
   `‖s‖ ∫_n^(n+1) x^(−σ−1) dx` of `∫_n^(n+1) x^(−s) dx` (`norm_cpow_neg_sub_le`, by Mathlib's fencing
   theorem on the rate `−s x^(−s−1)`, whose norm is `‖s‖ x^(−σ−1)`; `norm_cpow_neg_sub_integral_le`,
   against the primitive `x^(1−s)/(1 − s)`, with no integral taken). Telescoped, for `Re s > 1` and
   `N ≥ 1` ζ's tail `Σ_(n≥N) n^(−s)` lies within `‖s‖ N^(−σ)/σ` of `N^(1−s)/(s − 1)`
   (`norm_zetaTailC_sub_le`), so `riemannZeta s` lies in the disc of that radius about
   `Σ_(n<N) n^(−s) + N^(1−s)/(s − 1)` (`riemannZeta_mem_disc`). For `Re s > 0` η's paired series
   `Σ_k ((2k + 1)^(−s) − (2k + 2)^(−s))` converges absolutely, each pair within
   `‖s‖ ((2k + 1)^(−σ) − (2k + 3)^(−σ))/σ` (`norm_etaPair_le`, `summable_norm_etaPair`), and its tail
   from pair `K` is at most `‖s‖ (2K + 1)^(−σ)/σ` (`norm_tsum_etaPair_tail_le`); for `Re s > 1` it
   is `(1 − 2^(1−s)) ζ(s)` (`tsum_etaPair`), and at real `s > 0` it is the owner's `eta`
   (`ofReal_eta_eq_tsum_etaPair`).
2. **The log-power tails** (the owner's `log_power_tail_factor`). The primitive
   `P_k(σ, x) = ∫_x^∞ (log t)^k t^(−σ) dt` is held by its recursion `P_0 = x^(1−σ)/(σ − 1)`,
   `P_(k+1) = (log x)^(k+1) x^(1−σ)/(σ − 1) + (k + 1)/(σ − 1) · P_k` (`logPrim`), whose rate is
   `−(log x)^k x^(−σ)` (`hasDerivAt_logPrim`); for `σ > 1` it is nonnegative from `x = 1` and tends
   to `0` (`logPrim_nonneg`, `tendsto_logPrim`). The magnitudes `(log x)^k x^(−σ)` decrease from any
   `x₀ ≥ 1` with `k ≤ σ log x₀` (`logTerm_antitoneOn`), so with the mean value theorem on each unit
   step (`logPrim_step`), `P_k(N) ≤ Σ_(n≥N) (log n)^k n^(−σ) ≤ (log N)^k N^(−σ) + P_k(N)` for
   `σ > 1`, `N ≥ 1` and `k ≤ σ log N` (`logTail_bracket`); the whole series is summable
   (`summable_logTerm`).
3. **ζ's jets in `s` with uniform derivative bounds** (the owner's `HeadJet`, `ComplexJet2` and
   `zeta_derivative_bound_uniform`). For `Re s > 1`, `ζ^(k)(s) = (−1)^k Σ (log n)^k n^(−s)`
   (`iteratedDeriv_riemannZeta`, from Mathlib's `LSeries_iteratedDeriv` and
   `LSeries_one_eq_riemannZeta`), so `ζ′(s) = −Σ log n · n^(−s)` and `ζ″(s) = Σ (log n)² n^(−s)`
   (`deriv_riemannZeta_eq`, `iteratedDeriv_two_riemannZeta`). On the half-plane `Re s ≥ σ₀ > 1` the
   jet's tail after `N` terms is at most `(log N)^k N^(−σ₀) + P_k(σ₀, N)` uniformly in `s`
   (`norm_jetTail_le`), a bound that tends to `0` in `N` (`tendsto_jetTailBound`); so `ζ^(k)(s)`
   lies within it of `(−1)^k` times its head (`norm_iteratedDeriv_riemannZeta_sub_le`), and
   `‖ζ^(k)(s)‖ ≤ jetBound k σ₀ N`, the head's magnitudes at `σ₀` plus the tail bound
   (`norm_iteratedDeriv_riemannZeta_le`). Read as the capture square's datum
   ([proved-derived; formal-checked]): on a box `B∞(c, r)` with `c.re − r ≥ σ₀`,
   `|Re ζ′| + |Im ζ′| ≤ 2 jetBound 1 σ₀ N` (`zeta_deriv_capture_datum`), which is the `q` of
   `CertifiedCapture.image_box_subset_box`, so ζ maps the box into `B∞(c′, r′)` from an anchor `c′`
   within `β` of `ζ(c)` in each part once `β + 2 jetBound 1 σ₀ N · r ≤ r′` (`zeta_image_box`).
4. **η′ by its alternating series**. For real `s > 0`, `η′(s)` is read as the limit of
   `S′_N = Σ_(n<N) (−1)^(n+1) log(n + 1) (n + 1)^(−s)` (`etaDerivPartial`, `etaDeriv`,
   `tendsto_etaDerivPartial`). Its magnitudes decrease from `n + 1 ≥ e^(1/s)`
   (`etaLogTerm_antitone`), so from any `M` with `M + 1 ≥ e^(1/s)` consecutive partial sums bracket
   it (`etaDeriv_mem_uIcc`) and `|η′(s) − S′_(M+j)| ≤ log(M + j + 1) (M + j + 1)^(−s)`
   (`abs_etaDeriv_sub_le`). For `s > 1` it is the rate of the owner's `eta` (`hasDerivAt_eta`, by
   Mathlib's `hasDerivAt_tsum_of_isPreconnected` on `x > (1 + s)/2`).
5. **The `B₂` Euler–Maclaurin term and the start from a grain** (the owner's
   `euler_maclaurin_remainder_bound` at order one and `derive_euler_maclaurin_start`). For `f` with
   `f⁗ ≥ 0` on `[a, a + 1]`, the trapezoid with its `B₂` end term,
   `(f(a) + f(a + 1))/2 − (f′(a + 1) − f′(a))/12`, minus `∫_a^(a+1) f` lies in
   `[−(f‴(a + 1) − f‴(a))/384, 0]` (`trapezoid_B2`, by two primitives built on the Peano kernel
   `t²(1 − t)²/24`, whose rates are the kernel times `f⁗` and `1/384` minus the kernel, times `f⁗`,
   with no integral taken). Telescoped
   (`trapezoid_B2_telescope`) on `x^(−s)` (`rpow_trapezoid_B2_step`), for real `s > 1` and
   `N ≥ 1`, `−s(s + 1)(s + 2) N^(−s−3)/384 ≤ Σ_(n≥N) n^(−s) − (N^(1−s)/(s − 1) + N^(−s)/2 +
   s N^(−s−1)/12) ≤ 0` (`emTwo`, `emTwoRem`, `zetaTail_euler_maclaurin_two`), which encloses
   `riemannZeta s` (`zeta_mem_enclosure_two`). The classical constant is `1/720` with the same sign;
   the kernel's maximum gives `1/384`. A start `N ≥ 1` with `2^k s(s + 1)(s + 2) ≤ 384 N⁴` meets the
   declared tolerance `2^(−k)` (`emTwoRem_le_of_pow`), and
   `emStart k s = ⌈(2^k s(s + 1)(s + 2)/384)^(1/4)⌉ + 1` is one ([proved-derived; formal-checked];
   `emStart`, `emStart_spec`).
6. **Witnesses**. At `s = 2 + i`, `ζ(s)` lies within `9/128` of
   `1 + 2^(−s) + 3^(−s) + 4^(1−s)/(s − 1)` (`zeta_two_add_I_disc`: item 1 at `N = 4`, with
   `‖s‖ = √5 ≤ 9/4`). `ζ′(2)` is real and lies in
   `[−(7 log 2/8 + log 3/9 + 1/4), −(3 log 2/4 + log 3/9 + 1/4)]` (`deriv_riemannZeta_two_mem`:
   items 2 and 3 at `N = 4`, an interval of width `log 2/8`). The `B₂` head of ten terms holds
   `π²/6` in `[52229957/31752000 − 1/1600000, 52229957/31752000]`, within `10⁻⁶`
   (`zeta_two_enclosure_ten`); at `s = 2` the remainder bound is `N^(−5)/16`, and ten is the least
   `N` it admits at `10⁻⁶`.

What is not claimed. ζ off `Re s > 1`, through its continuation, beyond η's paired series: the
identity `Σ_k ((2k + 1)^(−s) − (2k + 2)^(−s)) = (1 − 2^(1−s)) ζ(s)` on `0 < Re s ≤ 1` needs it, and
so do the owner's Euler–Maclaurin jets there with `|s − 1| ≥ τ`; the uniform derivative bounds here
are read through the Dirichlet series on `Re s ≥ σ₀ > 1` alone. η's jets at complex `s`, and
`etaDeriv` as η's rate for `0 < s ≤ 1` (the bracket holds there; the rate is proved for `s > 1`).
The Euler–Maclaurin expansion of every order with its Bernoulli numbers and the rising product
`(s)_(2m)` (the owner's general `euler_maclaurin_remainder_bound`), the `B₂` term at complex `s`
(the complex disc of item 1 is first order), the sharp constant `1/720`, and the least start that
the owner's bisection returns (`emStart` is a sufficient start read from the remainder bound). The
owner's interval arithmetic through sums, products and reciprocals, the rounding of the discs'
centres to a grain (each centre holds complex powers, whose reading at a declared width is
`CertifiedCapture`'s outward rounding together with an evaluation of each power), and
`ComplexJet2` as a data structure. The interval of `ζ′(2)` is stated in `log 2` and `log 3`, whose
enclosures are navigators of `ConstantNavigators`.

The computational object is the helical pair interaction, read on ζ's terms. At `s = σ + iτ` each
term `n^(−s) = e^(−σ log n) e^(−iτ log n)` is a helix, a boost by `σ log n` and a turn by
`τ log n`, and the jet's factor `(log n)^k` is its `k`-th rate in `s`. The head is a declared count
of terms; the tail is released against its primitive with its remainder named; η's pairs are pair
contacts (odd term, even term) whose slip is bounded by the primitive of their rate. The receiver
disc is a face read at a declared radius, and the capture box takes the jet's uniform bound as its
`q`. Of the winding guide's six general objects this touches the helix (each term's boost and turn,
and the log-power jets), the pair (head and tail, odd and even, value and rate), faces and
placement (the receiver disc and the capture box, and the start read from the declared tolerance
`2^(−k)`) and the tube (the unit intervals telescoped as a clocked span of the head's length); the
cell holonomy and the tower thread stay attached.

Consumers: the atlas rows `analytic.euler-maclaurin-eta` and `analytic.certified-capture`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Mathematics.ZetaJets

open Set Filter Topology Finset
open Holonics.Mathematics.CertifiedCapture

/-! ## 1. ζ and η at complex `s` -/

/-- [proved-standard; formal-checked] The rate of `y ↦ y^(−s)` on the positive reals is `−s y^(−s−1)`. -/
theorem hasDerivAt_ofReal_cpow_neg {s : ℂ} (hs : 0 < s.re) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) (-s * (t : ℂ) ^ (-s - 1)) t := by
  have hs0 : -s ≠ 0 := by
    intro h
    have : s.re = 0 := by simpa using congrArg Complex.re h
    linarith
  exact hasDerivAt_ofReal_cpow_const ht.ne' hs0

/-- [proved-standard; formal-checked] A power's variation: `‖y^(−s) − a^(−s)‖ ≤ ‖s‖ (a^(−σ) − y^(−σ))/σ` for `a ≤ y`. -/
theorem norm_cpow_neg_sub_le {s : ℂ} (hs : 0 < s.re) {a y : ℝ} (ha : 0 < a) (hay : a ≤ y) :
    ‖(y : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖ ≤ ‖s‖ * (a ^ (-s.re) - y ^ (-s.re)) / s.re := by
  have hpos : ∀ t ∈ Icc a y, 0 < t := fun t ht => ha.trans_le ht.1
  have hf : ∀ t ∈ Icc a y, HasDerivAt (fun t : ℝ => (t : ℂ) ^ (-s) - (a : ℂ) ^ (-s))
      (-s * (t : ℂ) ^ (-s - 1)) t := fun t ht =>
    (hasDerivAt_ofReal_cpow_neg hs (hpos t ht)).sub_const _
  have hB : ∀ t ∈ Icc a y, HasDerivAt (fun t : ℝ => ‖s‖ * (a ^ (-s.re) - t ^ (-s.re)) / s.re)
      (‖s‖ * t ^ (-s.re - 1)) t := by
    intro t ht
    refine ((((Real.hasDerivAt_rpow_const (p := -s.re) (Or.inl (hpos t ht).ne')).const_sub
      (a ^ (-s.re))).const_mul ‖s‖).div_const s.re).congr_deriv ?_
    field_simp
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun t : ℝ => (t : ℂ) ^ (-s) - (a : ℂ) ^ (-s))
    (f' := fun t => -s * (t : ℂ) ^ (-s - 1))
    (B := fun t => ‖s‖ * (a ^ (-s.re) - t ^ (-s.re)) / s.re)
    (B' := fun t => ‖s‖ * t ^ (-s.re - 1))
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hf t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp)
    (fun t ht => (hB t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hB t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => by
      rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (hpos t (Ico_subset_Icc_self ht))]
      simp)
  exact key ⟨hay, le_rfl⟩

/-- [proved-standard; formal-checked] **The unit comparison**: `a^(−s) − ∫_a^(a+1) x^(−s)` within `‖s‖ ∫ x^(−σ−1)`. -/
theorem norm_cpow_neg_sub_integral_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {a : ℝ} (ha : 0 < a) :
    ‖(a : ℂ) ^ (-s) - ((((a + 1 : ℝ) : ℂ)) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s)‖ ≤
      ‖s‖ * (a ^ (-s.re) - (a + 1) ^ (-s.re)) / s.re := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hpos : ∀ t ∈ Icc a (a + 1), 0 < t := fun t ht => ha.trans_le ht.1
  set g : ℝ → ℂ := fun y => (a : ℂ) ^ (-s) * ((y : ℂ) - a) -
    ((y : ℂ) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s) with hg
  have hgd : ∀ t ∈ Icc a (a + 1), HasDerivAt g ((a : ℂ) ^ (-s) - (t : ℂ) ^ (-s)) t := by
    intro t ht
    have e1 : HasDerivAt (fun y : ℝ => (a : ℂ) ^ (-s) * ((y : ℂ) - a)) ((a : ℂ) ^ (-s)) t := by
      have := ((Complex.ofRealCLM.hasDerivAt (x := t)).sub_const (a : ℂ)).const_mul ((a : ℂ) ^ (-s))
      simpa using this
    have e2 := ((hasDerivAt_ofReal_cpow_const (hpos t ht).ne' h1s).sub_const
      ((a : ℂ) ^ (1 - s))).div_const (1 - s)
    refine (e1.sub e2).congr_deriv ?_
    rw [show (1 : ℂ) - s - 1 = -s by ring]
    field_simp
  have hbound : ∀ t ∈ Ico a (a + 1), ‖(a : ℂ) ^ (-s) - (t : ℂ) ^ (-s)‖ ≤
      ‖s‖ * (a ^ (-s.re) - (a + 1) ^ (-s.re)) / s.re := by
    intro t ht
    rw [norm_sub_rev]
    refine (norm_cpow_neg_sub_le hs ha ht.1).trans ?_
    have : (a + 1) ^ (-s.re) ≤ t ^ (-s.re) :=
      Real.rpow_le_rpow_of_nonpos (ha.trans_le ht.1) ht.2.le (by linarith)
    gcongr
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := g)
    (fun t ht => (hgd t ht).hasDerivWithinAt) hbound (a + 1) ⟨by linarith, le_rfl⟩
  have hga : g a = 0 := by simp [hg]
  have hga1 : g (a + 1) = (a : ℂ) ^ (-s) - ((((a + 1 : ℝ) : ℂ)) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s) := by
    simp only [hg]
    push_cast
    ring
  rw [hga, sub_zero, hga1, show a + 1 - a = 1 by ring, mul_one] at key
  exact key

/-- [definition] ζ's head at complex `s`: `Σ_(n<N) n^(−s)`. -/
noncomputable def zetaHeadC (s : ℂ) (N : ℕ) : ℂ := ∑ n ∈ range N, (n : ℂ) ^ (-s)

/-- [definition] ζ's tail from `N` at complex `s`: `Σ_(i≥0) (i + N)^(−s)`. -/
noncomputable def zetaTailC (s : ℂ) (N : ℕ) : ℂ := ∑' i : ℕ, ((i + N : ℕ) : ℂ) ^ (-s)

/-- [proved-standard; formal-checked] `Σ n^(−s)` is summable for `Re s > 1`. -/
theorem summable_cpow_neg {s : ℂ} (hs : 1 < s.re) : Summable (fun n : ℕ => (n : ℂ) ^ (-s)) := by
  have h := Complex.summable_one_div_nat_cpow.mpr hs
  refine h.congr fun n => ?_
  rw [Complex.cpow_neg, one_div]

/-- [proved-standard; formal-checked] Mathlib's `riemannZeta` for `Re s > 1` is `Σ n^(−s)`. -/
theorem riemannZeta_eq_tsum_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, (n : ℂ) ^ (-s) := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  congr 1
  funext n
  rw [Complex.cpow_neg, one_div]

/-- [proved-standard; formal-checked] The head and the tail make ζ at complex `s`, `Re s > 1`. -/
theorem riemannZeta_eq_head_add_tail {s : ℂ} (hs : 1 < s.re) (N : ℕ) :
    riemannZeta s = zetaHeadC s N + zetaTailC s N := by
  rw [riemannZeta_eq_tsum_cpow_neg hs, zetaHeadC, zetaTailC]
  exact ((summable_cpow_neg hs).sum_add_tsum_nat_add N).symm

/-- [proved-standard; formal-checked] **ζ's complex tail** lies within `‖s‖ N^(−σ)/σ` of `N^(1−s)/(s − 1)`. -/
theorem norm_zetaTailC_sub_le {s : ℂ} (hs : 1 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖zetaTailC s N - (N : ℂ) ^ (1 - s) / (s - 1)‖ ≤ ‖s‖ * (N : ℝ) ^ (-s.re) / s.re := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : ∀ i : ℕ, (0 : ℝ) < N + i := fun i => by positivity
  -- the telescoped comparison over `K` unit intervals
  have htel : ∀ K : ℕ, ‖∑ i ∈ range K, (((N + i : ℝ)) : ℂ) ^ (-s) -
      ((((N + K : ℝ)) : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s)‖ ≤
        ‖s‖ * ((N : ℝ) ^ (-s.re) - ((N : ℝ) + K) ^ (-s.re)) / s.re := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      have hstep := norm_cpow_neg_sub_integral_le hs0 hs1 (hx K)
      have e : ((N : ℝ) + ((K + 1 : ℕ) : ℝ)) = (N + K : ℝ) + 1 := by push_cast; ring
      rw [sum_range_succ, e]
      have hsplit : ∑ i ∈ range K, (((N + i : ℝ)) : ℂ) ^ (-s) + (((N + K : ℝ)) : ℂ) ^ (-s) -
          (((((N + K : ℝ) + 1 : ℝ)) : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) =
          (∑ i ∈ range K, (((N + i : ℝ)) : ℂ) ^ (-s) -
            ((((N + K : ℝ)) : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s)) +
          ((((N + K : ℝ)) : ℂ) ^ (-s) -
            (((((N + K : ℝ) + 1 : ℝ)) : ℂ) ^ (1 - s) - (((N + K : ℝ)) : ℂ) ^ (1 - s)) / (1 - s)) := by
        field_simp
        ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      have : ‖s‖ * ((N : ℝ) ^ (-s.re) - ((N : ℝ) + K) ^ (-s.re)) / s.re +
          ‖s‖ * (((N : ℝ) + K) ^ (-s.re) - ((N : ℝ) + K + 1) ^ (-s.re)) / s.re =
          ‖s‖ * ((N : ℝ) ^ (-s.re) - ((N : ℝ) + K + 1) ^ (-s.re)) / s.re := by ring
      rw [← this]
      exact add_le_add ih hstep
  -- the moving end
  have hgo : Tendsto (fun K : ℕ => (N : ℝ) + K) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hend : Tendsto (fun K : ℕ => (((N + K : ℝ)) : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < s.re - 1)).comp hgo
    refine h.congr' ?_
    filter_upwards with K
    simp only [Function.comp]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hx K)]
    congr 1
    simp
  have hsum : Tendsto (fun K : ℕ => ∑ i ∈ range K, (((N + i : ℝ)) : ℂ) ^ (-s)) atTop
      (𝓝 (zetaTailC s N)) := by
    have h := ((summable_nat_add_iff N).mpr (summable_cpow_neg hs)).tendsto_sum_tsum_nat
    refine h.congr fun K => sum_congr rfl fun i _ => ?_
    push_cast
    rw [add_comm]
  have hlim := (hsum.sub ((hend.sub_const ((N : ℂ) ^ (1 - s))).div_const (1 - s))).norm
  have hval : zetaTailC s N - (0 - (N : ℂ) ^ (1 - s)) / (1 - s) =
      zetaTailC s N - (N : ℂ) ^ (1 - s) / (s - 1) := by
    rw [zero_sub, neg_div, ← div_neg, neg_sub]
  rw [hval] at hlim
  refine le_of_tendsto' hlim fun K => (htel K).trans ?_
  have : 0 ≤ ((N : ℝ) + K) ^ (-s.re) := by positivity
  have hn : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs0.le
  rw [mul_sub, sub_div]
  linarith [div_nonneg (mul_nonneg (norm_nonneg s) this) hs0.le]

/-- [proved-standard; formal-checked] **The complex receiver box**: ζ(s) within `‖s‖ N^(−σ)/σ` of head and pole term. -/
theorem riemannZeta_mem_disc {s : ℂ} (hs : 1 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - (zetaHeadC s N + (N : ℂ) ^ (1 - s) / (s - 1))‖ ≤
      ‖s‖ * (N : ℝ) ^ (-s.re) / s.re := by
  rw [riemannZeta_eq_head_add_tail hs N, add_sub_add_left_eq_sub]
  exact norm_zetaTailC_sub_le hs hN

/-- [definition] η's paired term `(2k + 1)^(−s) − (2k + 2)^(−s)`. -/
noncomputable def etaPair (s : ℂ) (k : ℕ) : ℂ :=
  ((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ((2 * k + 2 : ℕ) : ℂ) ^ (-s)

/-- [definition] The odd magnitudes `(2k + 1)^(−σ)`. -/
noncomputable def oddPow (σ : ℝ) (k : ℕ) : ℝ := ((2 * k + 1 : ℕ) : ℝ) ^ (-σ)

/-- [proved-standard; formal-checked] A pair's slip is at most `‖s‖ ((2k + 1)^(−σ) − (2k + 3)^(−σ))/σ`. -/
theorem norm_etaPair_le {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    ‖etaPair s k‖ ≤ ‖s‖ * (oddPow s.re k - oddPow s.re (k + 1)) / s.re := by
  have ha : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
  have h := norm_cpow_neg_sub_le hs ha (y := ((2 * k + 2 : ℕ) : ℝ)) (by push_cast; linarith)
  rw [etaPair, norm_sub_rev]
  have e1 : (((2 * k + 1 : ℕ) : ℝ) : ℂ) = ((2 * k + 1 : ℕ) : ℂ) := by push_cast; ring
  have e2 : (((2 * k + 2 : ℕ) : ℝ) : ℂ) = ((2 * k + 2 : ℕ) : ℂ) := by push_cast; ring
  rw [e1, e2] at h
  refine h.trans ?_
  have hmono : oddPow s.re (k + 1) ≤ ((2 * k + 2 : ℕ) : ℝ) ^ (-s.re) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by linarith)
  rw [oddPow]
  gcongr

/-- [proved-standard; formal-checked] The odd magnitudes are nonnegative. -/
theorem oddPow_nonneg (σ : ℝ) (k : ℕ) : 0 ≤ oddPow σ k := by
  unfold oddPow
  positivity

/-- [proved-standard; formal-checked] The odd magnitudes decrease for `σ ≥ 0`. -/
theorem oddPow_antitone {σ : ℝ} (hσ : 0 ≤ σ) (k : ℕ) : oddPow σ (k + 1) ≤ oddPow σ k :=
  Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by linarith)

/-- [proved-standard; formal-checked] The pair bounds telescope over `J` pairs from `K`. -/
theorem sum_oddPow_tail (c : ℝ) (σ : ℝ) (K J : ℕ) :
    ∑ k ∈ range J, c * (oddPow σ (k + K) - oddPow σ (k + K + 1)) / σ =
      c * (oddPow σ K - oddPow σ (J + K)) / σ := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [sum_range_succ, ih, show J + 1 + K = J + K + 1 by ring]
    ring

/-- [proved-standard; formal-checked] **η's paired series converges absolutely** for `Re s > 0`. -/
theorem summable_norm_etaPair {s : ℂ} (hs : 0 < s.re) : Summable (fun k => ‖etaPair s k‖) := by
  have hd : Summable (fun k => ‖s‖ * (oddPow s.re k - oddPow s.re (k + 1)) / s.re) := by
    refine summable_of_sum_range_le (c := ‖s‖ * oddPow s.re 0 / s.re) (fun k => ?_) (fun J => ?_)
    · have := oddPow_antitone hs.le k
      have : 0 ≤ oddPow s.re k - oddPow s.re (k + 1) := by linarith
      positivity
    · have h := sum_oddPow_tail ‖s‖ s.re 0 J
      simp only [add_zero] at h
      rw [h]
      have := oddPow_nonneg s.re J
      gcongr
      linarith
  exact hd.of_nonneg_of_le (fun k => norm_nonneg _) (norm_etaPair_le hs)

/-- [proved-standard; formal-checked] η's paired series is summable for `Re s > 0`. -/
theorem summable_etaPair {s : ℂ} (hs : 0 < s.re) : Summable (etaPair s) :=
  (summable_norm_etaPair hs).of_norm

/-- [proved-standard; formal-checked] **η's paired tail** from pair `K` is at most `‖s‖ (2K + 1)^(−σ)/σ`. -/
theorem norm_tsum_etaPair_tail_le {s : ℂ} (hs : 0 < s.re) (K : ℕ) :
    ‖∑' k, etaPair s (k + K)‖ ≤ ‖s‖ * (((2 * K + 1 : ℕ) : ℝ)) ^ (-s.re) / s.re := by
  have hsum : Summable (fun k => ‖etaPair s (k + K)‖) :=
    (summable_nat_add_iff K).mpr (summable_norm_etaPair hs)
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  refine Real.tsum_le_of_sum_range_le (fun k => norm_nonneg _) fun J => ?_
  calc ∑ k ∈ range J, ‖etaPair s (k + K)‖
      ≤ ∑ k ∈ range J, ‖s‖ * (oddPow s.re (k + K) - oddPow s.re (k + K + 1)) / s.re :=
        sum_le_sum fun k _ => norm_etaPair_le hs (k + K)
    _ = ‖s‖ * (oddPow s.re K - oddPow s.re (J + K)) / s.re := sum_oddPow_tail _ _ K J
    _ ≤ ‖s‖ * oddPow s.re K / s.re := by
        have := oddPow_nonneg s.re (J + K)
        gcongr
        linarith

/-- [proved-standard; formal-checked] **η against ζ at complex `s`**: the pairs sum to `(1 − 2^(1−s)) ζ(s)`. -/
theorem tsum_etaPair {s : ℂ} (hs : 1 < s.re) :
    ∑' k, etaPair s k = (1 - 2 ^ (1 - s)) * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  have hsum := summable_cpow_neg hs
  have hsh : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℂ) ^ (-s)) := (summable_nat_add_iff 1).mpr hsum
  have e2 : ∀ k : ℕ, 2 * k + 1 + 1 = 2 * k + 2 := fun k => by omega
  have hodd : Summable (fun k : ℕ => ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) :=
    hsh.comp_injective (i := fun k => 2 * k) (fun a b h => by simpa using h)
  have hev : Summable (fun k : ℕ => ((2 * k + 2 : ℕ) : ℂ) ^ (-s)) := by
    have h := hsh.comp_injective (i := fun k => 2 * k + 1) (fun a b h => by simpa using h)
    simpa only [Function.comp_def, e2] using h
  have hz : riemannZeta s = ∑' m : ℕ, ((m + 1 : ℕ) : ℂ) ^ (-s) := by
    rw [riemannZeta_eq_tsum_cpow_neg hs, hsum.tsum_eq_zero_add]
    simp [Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  have hsplit : ∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s) + ∑' k : ℕ, ((2 * k + 2 : ℕ) : ℂ) ^ (-s) =
      riemannZeta s := by
    have h := tsum_even_add_odd (f := fun m : ℕ => ((m + 1 : ℕ) : ℂ) ^ (-s)) hodd
      (by simpa only [e2] using hev)
    simp only [e2] at h
    rw [hz, h]
  have hE : ∑' k : ℕ, ((2 * k + 2 : ℕ) : ℂ) ^ (-s) = 2 ^ (-s) * riemannZeta s := by
    rw [hz, ← tsum_mul_left]
    congr 1
    funext k
    rw [show ((2 * k + 2 : ℕ) : ℂ) = ((2 : ℕ) : ℂ) * ((k + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.natCast_mul_natCast_cpow]
    norm_num
  have h2 : (2 : ℂ) ^ (1 - s) = 2 * 2 ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ two_ne_zero, Complex.cpow_one]
  have hP : ∑' k, etaPair s k =
      ∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s) - ∑' k : ℕ, ((2 * k + 2 : ℕ) : ℂ) ^ (-s) := by
    simp only [etaPair]
    exact hodd.tsum_sub hev
  rw [hP, h2]
  linear_combination hsplit - 2 * hE

/-- [proved-standard; formal-checked] The owner's magnitudes `(n + 1)^(−s)` read in ℂ. -/
theorem ofReal_etaTerm (s : ℝ) (n : ℕ) : ((etaTerm s n : ℝ) : ℂ) = ((n + 1 : ℕ) : ℂ) ^ (-(s : ℂ)) := by
  rw [etaTerm, Complex.ofReal_cpow (by positivity)]
  push_cast
  ring_nf

/-- [proved-standard; formal-checked] The owner's even partial sums are the paired partial sums. -/
theorem ofReal_etaPartial_two_mul (s : ℝ) (K : ℕ) :
    ((etaPartial s (2 * K) : ℝ) : ℂ) = ∑ k ∈ range K, etaPair (s : ℂ) k := by
  induction K with
  | zero => simp [etaPartial]
  | succ K ih =>
    have e : 2 * (K + 1) = 2 * K + 1 + 1 := by ring
    rw [e, etaPartial, sum_range_succ, sum_range_succ, ← etaPartial, sum_range_succ]
    push_cast
    rw [ih, ofReal_etaTerm, ofReal_etaTerm, etaPair, pow_succ, pow_mul]
    simp only [neg_one_sq, one_pow, one_mul, mul_neg, mul_one]
    rw [show 2 * K + 1 + 1 = 2 * K + 2 by ring]
    ring

/-- [proved-standard; formal-checked] **The owner's η is the paired series** at real `s > 0`. -/
theorem ofReal_eta_eq_tsum_etaPair {s : ℝ} (hs : 0 < s) :
    ((eta s : ℝ) : ℂ) = ∑' k, etaPair (s : ℂ) k := by
  have h2 : Tendsto (fun K : ℕ => 2 * K) atTop atTop :=
    tendsto_atTop_mono (fun K => show K ≤ 2 * K by omega) tendsto_id
  have hl := (Complex.continuous_ofReal.tendsto _).comp ((tendsto_etaPartial hs).comp h2)
  have hr := (summable_etaPair (s := (s : ℂ)) (by simpa using hs)).tendsto_sum_tsum_nat
  refine tendsto_nhds_unique hl (hr.congr fun K => ?_)
  simp only [Function.comp]
  rw [ofReal_etaPartial_two_mul]

/-! ## 2. Log-power tails -/

/-- [definition] The log-power magnitude `(log x)^k x^(−σ)`. -/
noncomputable def logTerm (k : ℕ) (σ x : ℝ) : ℝ := Real.log x ^ k * x ^ (-σ)

/-- [definition] The log-power tail primitive (`∫_x^∞ (log t)^k t^(−σ) dt`, by its recursion in `k`). -/
noncomputable def logPrim : ℕ → ℝ → ℝ → ℝ
  | 0, σ, x => x ^ (1 - σ) / (σ - 1)
  | k + 1, σ, x => Real.log x ^ (k + 1) * x ^ (1 - σ) / (σ - 1) + (k + 1) / (σ - 1) * logPrim k σ x

/-- [proved-standard; formal-checked] `x^(1−σ) = x · x^(−σ)` for `x > 0`. -/
theorem rpow_one_sub_eq {x : ℝ} (hx : 0 < x) (σ : ℝ) : x ^ (1 - σ) = x * x ^ (-σ) := by
  rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]

/-- [proved-standard; formal-checked] The tail primitive's rate is `−(log x)^k x^(−σ)` for `x > 0`, `σ ≠ 1`. -/
theorem hasDerivAt_logPrim (k : ℕ) {σ x : ℝ} (hσ : σ ≠ 1) (hx : 0 < x) :
    HasDerivAt (fun y => logPrim k σ y) (-logTerm k σ x) x := by
  have hσ1 : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ
  have hr : HasDerivAt (fun y : ℝ => y ^ (1 - σ)) ((1 - σ) * x ^ (-σ)) x := by
    have := Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hx.ne')
    rwa [show 1 - σ - 1 = -σ by ring] at this
  induction k with
  | zero =>
    refine (hr.div_const (σ - 1)).congr_deriv ?_
    simp only [logTerm, pow_zero, one_mul]
    field_simp
    ring
  | succ k ih =>
    have hl := ((Real.hasDerivAt_log hx.ne').fun_pow (k + 1)).fun_mul hr
    refine ((hl.div_const (σ - 1)).add (ih.const_mul (((k : ℝ) + 1) / (σ - 1)))).congr_deriv ?_
    simp only [logTerm, Nat.add_sub_cancel]
    rw [rpow_one_sub_eq hx]
    push_cast
    field_simp
    ring

/-- [proved-standard; formal-checked] The log-power magnitudes are nonnegative from `x = 1`. -/
theorem logTerm_nonneg (k : ℕ) (σ : ℝ) {x : ℝ} (hx : 1 ≤ x) : 0 ≤ logTerm k σ x := by
  unfold logTerm
  have := Real.log_nonneg hx
  positivity

/-- [proved-standard; formal-checked] The tail primitive is nonnegative from `x = 1` for `σ > 1`. -/
theorem logPrim_nonneg (k : ℕ) {σ x : ℝ} (hσ : 1 < σ) (hx : 1 ≤ x) : 0 ≤ logPrim k σ x := by
  have hl := Real.log_nonneg hx
  have hσ1 : 0 < σ - 1 := by linarith
  have hx0 : 0 < x := by linarith
  induction k with
  | zero =>
    simp only [logPrim]
    positivity
  | succ k ih =>
    simp only [logPrim]
    positivity

/-- [proved-standard; formal-checked] `(log x)^m x^(−r) → 0` for `r > 0`. -/
theorem tendsto_log_pow_mul_rpow_neg (m : ℕ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x : ℝ => Real.log x ^ m * x ^ (-r)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (m : ℝ) hr).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.rpow_natCast, Real.rpow_neg hx.le, div_eq_mul_inv]

/-- [proved-standard; formal-checked] The tail primitive tends to `0` for `σ > 1`. -/
theorem tendsto_logPrim (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun x => logPrim k σ x) atTop (𝓝 0) := by
  have hr : (0 : ℝ) < σ - 1 := by linarith
  have e : ∀ x : ℝ, x ^ (1 - σ) = x ^ (-(σ - 1)) := fun x => by rw [neg_sub]
  induction k with
  | zero =>
    simp only [logPrim, e]
    simpa using (tendsto_rpow_neg_atTop hr).div_const (σ - 1)
  | succ k ih =>
    simp only [logPrim, e]
    have h1 := (tendsto_log_pow_mul_rpow_neg (k + 1) hr).div_const (σ - 1)
    have h2 := ih.const_mul (((k : ℝ) + 1) / (σ - 1))
    simpa using h1.add h2

/-- [proved-standard; formal-checked] The log-power magnitude's rate: `x^(−σ)/x (k (log x)^(k−1) − σ (log x)^k)`. -/
theorem hasDerivAt_logTerm (k : ℕ) (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => logTerm k σ y)
      (x ^ (-σ) / x * ((k : ℝ) * Real.log x ^ (k - 1) - σ * Real.log x ^ k)) x := by
  have hr := Real.hasDerivAt_rpow_const (p := -σ) (Or.inl hx.ne')
  refine (((Real.hasDerivAt_log hx.ne').fun_pow k).fun_mul hr).congr_deriv ?_
  rw [Real.rpow_sub_one hx.ne']
  field_simp
  ring

/-- [proved-standard; formal-checked] The log-power magnitudes decrease from any `x₀ ≥ 1` with `k ≤ σ log x₀`. -/
theorem logTerm_antitoneOn (k : ℕ) {σ x₀ : ℝ} (hσ : 0 < σ) (hx₀ : 1 ≤ x₀)
    (hk : (k : ℝ) ≤ σ * Real.log x₀) : AntitoneOn (fun x => logTerm k σ x) (Ici x₀) := by
  have hpos : ∀ x ∈ Ici x₀, 0 < x := fun x hx => by linarith [mem_Ici.mp hx]
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici x₀)
    (fun x hx => (hasDerivAt_logTerm k σ (hpos x hx)).continuousAt.continuousWithinAt)
    (fun x hx => (hasDerivAt_logTerm k σ (hpos x (interior_subset hx))).hasDerivWithinAt)
    (fun x hx => ?_)
  have hx := interior_subset hx
  have hx0 := hpos x hx
  have hlog : Real.log x₀ ≤ Real.log x := Real.log_le_log (by linarith) (mem_Ici.mp hx)
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith [mem_Ici.mp hx])
  have hc : 0 ≤ x ^ (-σ) / x := by positivity
  refine mul_nonpos_of_nonneg_of_nonpos hc ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [Nat.cast_zero, zero_mul, pow_zero, mul_one, zero_sub, neg_nonpos]
    exact hσ.le
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    have hj : 0 ≤ Real.log x ^ j := pow_nonneg hl0 j
    have : ((j + 1 : ℕ) : ℝ) ≤ σ * Real.log x := hk.trans (by gcongr)
    nlinarith

/-- [proved-standard; formal-checked] One unit step: the magnitudes at `x + 1` and `x` bracket the primitive's drop. -/
theorem logPrim_step (k : ℕ) {σ x₀ x : ℝ} (hσ : 1 < σ) (hx₀ : 1 ≤ x₀)
    (hk : (k : ℝ) ≤ σ * Real.log x₀) (hx : x₀ ≤ x) :
    logTerm k σ (x + 1) ≤ logPrim k σ x - logPrim k σ (x + 1) ∧
      logPrim k σ x - logPrim k σ (x + 1) ≤ logTerm k σ x := by
  have hpos : ∀ y ∈ Icc x (x + 1), 0 < y := fun y hy => by linarith [hy.1]
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun y => -logPrim k σ y)
    (fun y => logTerm k σ y) (by linarith : x < x + 1)
    (fun y hy => (hasDerivAt_logPrim k hσ.ne' (hpos y hy)).fun_neg.continuousAt.continuousWithinAt)
    (fun y hy => (hasDerivAt_logPrim k hσ.ne' (hpos y (Ioo_subset_Icc_self hy))).fun_neg.congr_deriv
      (neg_neg _))
  have hanti := logTerm_antitoneOn k (by linarith) hx₀ hk
  have h1 : logTerm k σ c ≤ logTerm k σ x :=
    hanti (mem_Ici.mpr hx) (mem_Ici.mpr (by linarith [hc.1])) hc.1.le
  have h2 : logTerm k σ (x + 1) ≤ logTerm k σ c :=
    hanti (mem_Ici.mpr (by linarith [hc.1])) (mem_Ici.mpr (by linarith)) hc.2.le
  simp only [add_sub_cancel_left, div_one] at hcd
  constructor <;> linarith

/-- [proved-standard; formal-checked] **The log-power tail** from `N` lies in `[P_k(N), (log N)^k N^(−σ) + P_k(N)]`. -/
theorem logTail_bracket (k : ℕ) {σ : ℝ} (hσ : 1 < σ) {N : ℕ} (hN : 1 ≤ N)
    (hk : (k : ℝ) ≤ σ * Real.log N) :
    Summable (fun i : ℕ => logTerm k σ ((i + N : ℕ) : ℝ)) ∧
      logPrim k σ N ≤ ∑' i : ℕ, logTerm k σ ((i + N : ℕ) : ℝ) ∧
      ∑' i : ℕ, logTerm k σ ((i + N : ℕ) : ℝ) ≤ logTerm k σ N + logPrim k σ N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : ∀ i : ℕ, (((i + 1 + N : ℕ) : ℝ)) = ((i + N : ℕ) : ℝ) + 1 := fun i => by
    push_cast
    ring
  have hx0 : ∀ i : ℕ, (N : ℝ) ≤ ((i + N : ℕ) : ℝ) := fun i => by
    push_cast
    linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have hstep : ∀ i : ℕ,
      logTerm k σ ((i + 1 + N : ℕ) : ℝ) ≤
          logPrim k σ ((i + N : ℕ) : ℝ) - logPrim k σ ((i + 1 + N : ℕ) : ℝ) ∧
        logPrim k σ ((i + N : ℕ) : ℝ) - logPrim k σ ((i + 1 + N : ℕ) : ℝ) ≤
          logTerm k σ ((i + N : ℕ) : ℝ) := fun i => by
    rw [hx1]
    exact logPrim_step k hσ hN1 hk (hx0 i)
  have hnn : ∀ i : ℕ, 0 ≤ logTerm k σ ((i + N : ℕ) : ℝ) :=
    fun i => logTerm_nonneg k σ (hN1.trans (hx0 i))
  have hP0 : ∀ i : ℕ, 0 ≤ logPrim k σ ((i + N : ℕ) : ℝ) :=
    fun i => logPrim_nonneg k hσ (hN1.trans (hx0 i))
  have htel : ∀ K : ℕ, ∑ i ∈ range K,
      (logPrim k σ ((i + N : ℕ) : ℝ) - logPrim k σ ((i + 1 + N : ℕ) : ℝ)) =
        logPrim k σ N - logPrim k σ ((K + N : ℕ) : ℝ) := fun K => by
    have h := sum_range_sub' (fun i : ℕ => logPrim k σ ((i + N : ℕ) : ℝ)) K
    simpa only [zero_add] using h
  have hup : ∀ K : ℕ, ∑ i ∈ range K, logTerm k σ ((i + N : ℕ) : ℝ) ≤
      logTerm k σ N + logPrim k σ N := by
    intro K
    cases K with
    | zero =>
      simp only [range_zero, sum_empty]
      exact add_nonneg (logTerm_nonneg k σ hN1) (logPrim_nonneg k hσ hN1)
    | succ K =>
      rw [sum_range_succ']
      have h := sum_le_sum fun i (_ : i ∈ range K) => (hstep i).1
      rw [htel] at h
      have := hP0 K
      simp only [zero_add] at h ⊢
      linarith
  have hsum := summable_of_sum_range_le hnn hup
  have hlow : ∀ K : ℕ, logPrim k σ N - logPrim k σ ((K + N : ℕ) : ℝ) ≤
      ∑' i : ℕ, logTerm k σ ((i + N : ℕ) : ℝ) := by
    intro K
    have h := sum_le_sum fun i (_ : i ∈ range K) => (hstep i).2
    rw [htel] at h
    exact h.trans (hsum.sum_le_tsum _ fun i _ => hnn i)
  have hgo : Tendsto (fun K : ℕ => ((K + N : ℕ) : ℝ)) atTop atTop := by
    exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat N)
  have hlim : Tendsto (fun K : ℕ => logPrim k σ N - logPrim k σ ((K + N : ℕ) : ℝ)) atTop
      (𝓝 (logPrim k σ N)) := by
    simpa using ((tendsto_logPrim k hσ).comp hgo).const_sub (logPrim k σ N)
  exact ⟨hsum, le_of_tendsto' hlim hlow, Real.tsum_le_of_sum_range_le hnn hup⟩

/-- [proved-standard; formal-checked] A start `N ≥ 1` with `k ≤ σ log N` exists for `σ > 0`. -/
theorem exists_logTerm_start (k : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ N : ℕ, 1 ≤ N ∧ (k : ℝ) ≤ σ * Real.log N := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 (Real.exp (k / σ)))
  refine ⟨N, by exact_mod_cast (le_max_left _ _).trans hN, ?_⟩
  have h := Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hN)
  rw [Real.log_exp] at h
  rw [div_le_iff₀ hσ] at h
  linarith

/-- [proved-standard; formal-checked] `Σ (log n)^k n^(−σ)` is summable for `σ > 1`. -/
theorem summable_logTerm (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => logTerm k σ n) := by
  obtain ⟨N, hN, hk⟩ := exists_logTerm_start k (by linarith : (0 : ℝ) < σ)
  exact (summable_nat_add_iff N).mp (logTail_bracket k hσ hN hk).1

/-! ## 3. ζ's jets in `s` with uniform derivative bounds -/

/-- [definition] The `k`-th jet term at complex `s`: `(log n)^k n^(−s)`. -/
noncomputable def jetTerm (k : ℕ) (s : ℂ) (n : ℕ) : ℂ := ((Real.log n : ℝ) : ℂ) ^ k * (n : ℂ) ^ (-s)

/-- [definition] The `k`-th jet's head: `Σ_(n<N) (log n)^k n^(−s)`. -/
noncomputable def jetHead (k : ℕ) (s : ℂ) (N : ℕ) : ℂ := ∑ n ∈ range N, jetTerm k s n

/-- [definition] The `k`-th jet's tail from `N`: `Σ_(i≥0) (log (i + N))^k (i + N)^(−s)`. -/
noncomputable def jetTail (k : ℕ) (s : ℂ) (N : ℕ) : ℂ := ∑' i : ℕ, jetTerm k s (i + N)

/-- [proved-standard; formal-checked] On `Re s ≥ σ₀ > 0` each jet term is at most its magnitude at `σ₀`. -/
theorem norm_jetTerm_le (k : ℕ) {σ₀ : ℝ} (hσ₀ : 0 < σ₀) {s : ℂ} (hs : σ₀ ≤ s.re) (n : ℕ) :
    ‖jetTerm k s n‖ ≤ logTerm k σ₀ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs0 : -s ≠ 0 := by
      intro h
      have : s.re = 0 := by simpa using congrArg Complex.re h
      linarith
    simp [jetTerm, logTerm, Complex.zero_cpow hs0, Real.zero_rpow (by linarith : -σ₀ ≠ 0)]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    rw [jetTerm, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hn1),
      show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
    unfold logTerm
    have := Real.log_nonneg hn1
    gcongr
    simpa using hs

/-- [proved-standard; formal-checked] Mathlib's terms of `logMul^[k] 1` are the jet terms. -/
theorem term_logMul_iterate (k : ℕ) {s : ℂ} (hs : s ≠ 0) (n : ℕ) :
    LSeries.term (LSeries.logMul^[k] 1) s n = jetTerm k s n := by
  have hlog : ∀ m : ℕ, (LSeries.logMul^[m] (1 : ℕ → ℂ)) n = (Complex.log n) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Function.iterate_succ_apply', LSeries.logMul, ih, pow_succ, mul_comm]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [jetTerm, Complex.zero_cpow (neg_ne_zero.mpr hs)]
  · rw [LSeries.term_of_ne_zero hn.ne', hlog, jetTerm, ← Complex.natCast_log, Complex.cpow_neg,
      div_eq_mul_inv]

/-- [proved-standard; formal-checked] **ζ's jets**: `ζ^(k)(s) = (−1)^k Σ (log n)^k n^(−s)` for `Re s > 1`. -/
theorem iteratedDeriv_riemannZeta (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k riemannZeta s = (-1) ^ k * ∑' n : ℕ, jetTerm k s n := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs
  have hab : LSeries.abscissaOfAbsConv 1 < s.re := by
    rw [LSeries.abscissaOfAbsConv_one]
    exact_mod_cast hs
  have heq : riemannZeta =ᶠ[𝓝 s] LSeries 1 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact (LSeries_one_eq_riemannZeta hz).symm
  rw [heq.iteratedDeriv_eq k, LSeries_iteratedDeriv k hab, LSeries]
  congr 1
  exact tsum_congr fun n => term_logMul_iterate k hs0 n

/-- [proved-standard; formal-checked] **ζ′**: `ζ′(s) = −Σ log n · n^(−s)` for `Re s > 1`. -/
theorem deriv_riemannZeta_eq {s : ℂ} (hs : 1 < s.re) :
    deriv riemannZeta s = -∑' n : ℕ, jetTerm 1 s n := by
  rw [← iteratedDeriv_one, iteratedDeriv_riemannZeta 1 hs, pow_one, neg_one_mul]

/-- [proved-standard; formal-checked] **ζ″**: `ζ″(s) = Σ (log n)² n^(−s)` for `Re s > 1`. -/
theorem iteratedDeriv_two_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv 2 riemannZeta s = ∑' n : ℕ, jetTerm 2 s n := by
  rw [iteratedDeriv_riemannZeta 2 hs]
  norm_num

/-- [proved-standard; formal-checked] The jet series is summable for `Re s > 1`. -/
theorem summable_jetTerm (k : ℕ) {s : ℂ} (hs : 1 < s.re) : Summable (jetTerm k s) :=
  Summable.of_norm_bounded (summable_logTerm k hs) (norm_jetTerm_le k (by linarith) le_rfl)

/-- [proved-standard; formal-checked] The jet series is its head plus its tail. -/
theorem tsum_jetTerm_eq (k : ℕ) {s : ℂ} (hs : 1 < s.re) (N : ℕ) :
    ∑' n : ℕ, jetTerm k s n = jetHead k s N + jetTail k s N :=
  ((summable_jetTerm k hs).sum_add_tsum_nat_add N).symm

/-- [proved-standard; formal-checked] **The uniform jet tail** on `Re s ≥ σ₀` is at most `(log N)^k N^(−σ₀) + P_k`. -/
theorem norm_jetTail_le (k : ℕ) {σ₀ : ℝ} (hσ₀ : 1 < σ₀) {s : ℂ} (hs : σ₀ ≤ s.re) {N : ℕ}
    (hN : 1 ≤ N) (hk : (k : ℝ) ≤ σ₀ * Real.log N) :
    ‖jetTail k s N‖ ≤ logTerm k σ₀ N + logPrim k σ₀ N := by
  obtain ⟨hsum, -, hup⟩ := logTail_bracket k hσ₀ hN hk
  refine (tsum_of_norm_bounded hsum.hasSum fun i => ?_).trans hup
  exact norm_jetTerm_le k (by linarith) hs (i + N)

/-- [proved-standard; formal-checked] The uniform jet tail bound tends to `0` as `N` grows. -/
theorem tendsto_jetTailBound (k : ℕ) {σ₀ : ℝ} (hσ₀ : 1 < σ₀) :
    Tendsto (fun N : ℕ => logTerm k σ₀ N + logPrim k σ₀ N) atTop (𝓝 0) := by
  have h1 := tendsto_log_pow_mul_rpow_neg k (by linarith : (0 : ℝ) < σ₀)
  have h2 := tendsto_logPrim k hσ₀
  simpa [Function.comp_def, logTerm] using (h1.add h2).comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- [definition] The uniform bound on `|ζ^(k)|` over `Re s ≥ σ₀`: the head's magnitudes plus the tail bound. -/
noncomputable def jetBound (k : ℕ) (σ₀ : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, logTerm k σ₀ n + (logTerm k σ₀ N + logPrim k σ₀ N)

/-- [proved-standard; formal-checked] **ζ's jet in its disc**: `ζ^(k)(s)` within the tail bound of `(−1)^k` × head. -/
theorem norm_iteratedDeriv_riemannZeta_sub_le (k : ℕ) {σ₀ : ℝ} (hσ₀ : 1 < σ₀) {s : ℂ}
    (hs : σ₀ ≤ s.re) {N : ℕ} (hN : 1 ≤ N) (hk : (k : ℝ) ≤ σ₀ * Real.log N) :
    ‖iteratedDeriv k riemannZeta s - (-1) ^ k * jetHead k s N‖ ≤ logTerm k σ₀ N + logPrim k σ₀ N := by
  have hs1 : 1 < s.re := hσ₀.trans_le hs
  rw [iteratedDeriv_riemannZeta k hs1, tsum_jetTerm_eq k hs1 N, mul_add, add_sub_cancel_left,
    norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact norm_jetTail_le k hσ₀ hs hN hk

/-- [proved-standard; formal-checked] **The uniform derivative bound** `‖ζ^(k)(s)‖ ≤ jetBound k σ₀ N` on `Re s ≥ σ₀`. -/
theorem norm_iteratedDeriv_riemannZeta_le (k : ℕ) {σ₀ : ℝ} (hσ₀ : 1 < σ₀) {s : ℂ}
    (hs : σ₀ ≤ s.re) {N : ℕ} (hN : 1 ≤ N) (hk : (k : ℝ) ≤ σ₀ * Real.log N) :
    ‖iteratedDeriv k riemannZeta s‖ ≤ jetBound k σ₀ N := by
  have hs1 : 1 < s.re := hσ₀.trans_le hs
  rw [iteratedDeriv_riemannZeta k hs1, tsum_jetTerm_eq k hs1 N, norm_mul, norm_pow, norm_neg,
    norm_one, one_pow, one_mul, jetBound]
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_jetTail_le k hσ₀ hs hN hk))
  exact (norm_sum_le _ _).trans (sum_le_sum fun n _ => norm_jetTerm_le k (by linarith) hs n)

/-- [proved-derived; formal-checked] **The capture datum**: on a box in `Re s ≥ σ₀`, `|Re ζ′| + |Im ζ′| ≤ 2 jetBound` -/
theorem zeta_deriv_capture_datum {σ₀ : ℝ} (hσ₀ : 1 < σ₀) {c : ℂ} {r : ℝ} (hbox : σ₀ ≤ c.re - r)
    {N : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ σ₀ * Real.log N) :
    ∀ w ∈ box c r, |(deriv riemannZeta w).re| + |(deriv riemannZeta w).im| ≤ 2 * jetBound 1 σ₀ N := by
  intro w hw
  have hwre : σ₀ ≤ w.re := by
    have := (abs_le.mp hw.1).1
    linarith
  have h := norm_iteratedDeriv_riemannZeta_le 1 hσ₀ hwre hN (by simpa using hk)
  rw [iteratedDeriv_one] at h
  linarith [Complex.abs_re_le_norm (deriv riemannZeta w), Complex.abs_im_le_norm (deriv riemannZeta w)]

/-- [proved-derived; formal-checked] **ζ releases a box into a box**: an anchor within `β`, `β + 2 jetBound r ≤ r′`. -/
theorem zeta_image_box {σ₀ : ℝ} (hσ₀ : 1 < σ₀) {c c' : ℂ} {r r' β : ℝ} (hbox : σ₀ ≤ c.re - r)
    {N : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ σ₀ * Real.log N)
    (hβ : |(riemannZeta c - c').re| ≤ β ∧ |(riemannZeta c - c').im| ≤ β)
    (hr' : β + 2 * jetBound 1 σ₀ N * r ≤ r') :
    MapsTo riemannZeta (box c r) (box c' r') := by
  refine image_box_subset_box (fun w hw => differentiableAt_riemannZeta ?_)
    (zeta_deriv_capture_datum hσ₀ hbox hN hk) hβ hr'
  intro h
  have := (abs_le.mp hw.1).1
  rw [h] at this
  simp at this
  linarith

/-! ## 4. η′ by its alternating series -/

/-- [definition] η′'s magnitudes: `log(n + 1) (n + 1)^(−s)`. -/
noncomputable def etaLogTerm (s : ℝ) (n : ℕ) : ℝ := logTerm 1 s ((n : ℝ) + 1)

/-- [definition] η′'s partial navigator: `Σ_(n<N) (−1)^(n+1) log(n + 1) (n + 1)^(−s)`. -/
noncomputable def etaDerivPartial (s : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, (-1) ^ (n + 1) * etaLogTerm s n

/-- [definition] η′ at real `s`, the limit of its partial navigator. -/
noncomputable def etaDeriv (s : ℝ) : ℝ := limUnder atTop (etaDerivPartial s)

/-- [proved-standard; formal-checked] η′'s magnitudes are nonnegative. -/
theorem etaLogTerm_nonneg (s : ℝ) (n : ℕ) : 0 ≤ etaLogTerm s n :=
  logTerm_nonneg 1 s (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

/-- [proved-standard; formal-checked] η′'s magnitudes decrease from `n + 1 ≥ e^(1/s)` for `s > 0`. -/
theorem etaLogTerm_antitone {s : ℝ} (hs : 0 < s) {M : ℕ} (hM : Real.exp (1 / s) ≤ M + 1) :
    Antitone (fun j => etaLogTerm s (M + j)) := by
  have hM1 : (1 : ℝ) ≤ M + 1 := by linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hk : ((1 : ℕ) : ℝ) ≤ s * Real.log (M + 1) := by
    have h := Real.log_le_log (Real.exp_pos _) hM
    rw [Real.log_exp, div_le_iff₀ hs] at h
    push_cast
    linarith
  have hanti := logTerm_antitoneOn 1 hs hM1 hk
  intro i j hij
  unfold etaLogTerm
  push_cast
  refine hanti (mem_Ici.mpr ?_) (mem_Ici.mpr ?_) ?_
  · linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  · linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  · have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith

/-- [proved-standard; formal-checked] η′'s magnitudes tend to `0` for `s > 0`. -/
theorem tendsto_etaLogTerm {s : ℝ} (hs : 0 < s) : Tendsto (etaLogTerm s) atTop (𝓝 0) := by
  have h := (tendsto_log_pow_mul_rpow_neg 1 hs).comp
    (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  rw [show etaLogTerm s = fun n : ℕ => Real.log ((n : ℝ) + 1) ^ 1 * ((n : ℝ) + 1) ^ (-s) from rfl]
  simpa [Function.comp_def] using h

/-- [proved-standard; formal-checked] η′'s partial sums past `M` add its alternating tail, signed by `(−1)^(M+1)`. -/
theorem etaDerivPartial_add (s : ℝ) (M j : ℕ) :
    etaDerivPartial s (M + j) = etaDerivPartial s M +
      (-1) ^ (M + 1) * ∑ i ∈ range j, (-1) ^ i * etaLogTerm s (M + i) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← add_assoc, etaDerivPartial, sum_range_succ, ← etaDerivPartial, ih, sum_range_succ]
    ring

/-- [proved-standard; formal-checked] The alternating tail from `M` converges, and with it the partial navigator. -/
theorem etaDeriv_shift {s : ℝ} (hs : 0 < s) {M : ℕ} (hM : Real.exp (1 / s) ≤ M + 1) :
    ∃ l, Tendsto (fun j => ∑ i ∈ range j, (-1) ^ i * etaLogTerm s (M + i)) atTop (𝓝 l) ∧
      Tendsto (etaDerivPartial s) atTop (𝓝 (etaDerivPartial s M + (-1) ^ (M + 1) * l)) := by
  have hanti := etaLogTerm_antitone hs hM
  have h0 : Tendsto (fun j => etaLogTerm s (M + j)) atTop (𝓝 0) :=
    ((tendsto_etaLogTerm hs).comp (tendsto_add_atTop_nat M)).congr fun j => by
      simp [add_comm]
  obtain ⟨l, hl⟩ := hanti.tendsto_alternating_series_of_tendsto_zero h0
  refine ⟨l, hl, ?_⟩
  rw [← tendsto_add_atTop_iff_nat M]
  have h := (hl.const_mul ((-1) ^ (M + 1))).const_add (etaDerivPartial s M)
  refine h.congr fun j => ?_
  rw [add_comm j M, etaDerivPartial_add]

/-- [proved-standard; formal-checked] For `s > 0` η′'s partial navigator converges to `etaDeriv s`. -/
theorem tendsto_etaDerivPartial {s : ℝ} (hs : 0 < s) :
    Tendsto (etaDerivPartial s) atTop (𝓝 (etaDeriv s)) := by
  obtain ⟨M, hM⟩ := exists_nat_ge (Real.exp (1 / s))
  obtain ⟨l, -, h⟩ := etaDeriv_shift hs (M := M) (by linarith)
  exact tendsto_nhds_limUnder ⟨_, h⟩

/-- [proved-standard; formal-checked] **η′'s enclosure**: from `M + 1 ≥ e^(1/s)` consecutive partial sums bracket it. -/
theorem etaDeriv_mem_uIcc {s : ℝ} (hs : 0 < s) {M : ℕ} (hM : Real.exp (1 / s) ≤ M + 1) (j : ℕ) :
    etaDeriv s ∈ uIcc (etaDerivPartial s (M + j)) (etaDerivPartial s (M + j + 1)) := by
  obtain ⟨l, hl, h⟩ := etaDeriv_shift hs hM
  have hanti := etaLogTerm_antitone hs hM
  have hval : etaDeriv s = etaDerivPartial s M + (-1) ^ (M + 1) * l :=
    tendsto_nhds_unique (tendsto_etaDerivPartial hs) h
  set T : ℕ → ℝ := fun j => ∑ i ∈ range j, (-1) ^ i * etaLogTerm s (M + i) with hT
  have hTl : l ∈ uIcc (T j) (T (j + 1)) := by
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
    · exact Set.mem_uIcc.mpr (Or.inl ⟨hanti.alternating_series_le_tendsto hl i,
        hanti.tendsto_le_alternating_series hl i⟩)
    · have h2 := hanti.alternating_series_le_tendsto hl (i + 1)
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring] at h2
      exact Set.mem_uIcc.mpr (Or.inr ⟨h2, hanti.tendsto_le_alternating_series hl i⟩)
  rw [hval, show M + j + 1 = M + (j + 1) by ring, etaDerivPartial_add, etaDerivPartial_add]
  rcases neg_one_pow_eq_or ℝ (M + 1) with h1 | h1 <;> rw [h1] <;> rw [Set.mem_uIcc] at hTl ⊢ <;>
    simp only [hT] at hTl <;> rcases hTl with ⟨a, b⟩ | ⟨a, b⟩
  all_goals first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr ⟨by linarith, by linarith⟩

/-- [proved-standard; formal-checked] **η′'s remainder**: within `log(M + j + 1) (M + j + 1)^(−s)` of `S′_(M+j)`. -/
theorem abs_etaDeriv_sub_le {s : ℝ} (hs : 0 < s) {M : ℕ} (hM : Real.exp (1 / s) ≤ M + 1) (j : ℕ) :
    |etaDeriv s - etaDerivPartial s (M + j)| ≤ etaLogTerm s (M + j) := by
  refine (abs_sub_left_of_mem_uIcc (etaDeriv_mem_uIcc hs hM j)).trans_eq ?_
  rw [etaDerivPartial, sum_range_succ, ← etaDerivPartial, add_sub_cancel_left, abs_mul, abs_pow,
    abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (etaLogTerm_nonneg s _)]

/-- [proved-standard; formal-checked] For `s > 1` the owner's η is the `tsum` of its signed magnitudes. -/
theorem eta_eq_tsum {s : ℝ} (hs : 1 < s) : eta s = ∑' n : ℕ, (-1) ^ n * etaTerm s n :=
  tendsto_nhds_unique (tendsto_etaPartial (by linarith))
    (summable_etaTerm hs).tendsto_alternating_series_tsum

/-- [proved-standard; formal-checked] **η′ is η's rate**: `HasDerivAt eta (etaDeriv s) s` for `s > 1`. -/
theorem hasDerivAt_eta {s : ℝ} (hs : 1 < s) : HasDerivAt eta (etaDeriv s) s := by
  set σ₁ := (1 + s) / 2 with hσ₁
  have hσ₁1 : 1 < σ₁ := by linarith
  have hσ₁s : σ₁ < s := by linarith
  set g : ℕ → ℝ → ℝ := fun n x => (-1) ^ n * etaTerm x n with hg
  set g' : ℕ → ℝ → ℝ := fun n x => (-1) ^ (n + 1) * etaLogTerm x n with hg'
  have hgd : ∀ n y, y ∈ Ioi σ₁ → HasDerivAt (g n) (g' n y) y := by
    intro n y _
    have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h := ((Real.hasStrictDerivAt_const_rpow ha (-y)).hasDerivAt.comp y (hasDerivAt_neg y))
    refine (h.const_mul ((-1) ^ n)).congr_deriv ?_
    simp only [hg', etaLogTerm, logTerm, pow_succ]
    ring
  have hu : Summable (fun n : ℕ => etaLogTerm σ₁ n) := by
    have h := (summable_nat_add_iff 1).mpr (summable_logTerm 1 hσ₁1)
    refine h.congr fun n => ?_
    simp [etaLogTerm]
  have hbound : ∀ n y, y ∈ Ioi σ₁ → ‖g' n y‖ ≤ etaLogTerm σ₁ n := by
    intro n y hy
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [hg', norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_of_nonneg (etaLogTerm_nonneg y n)]
    unfold etaLogTerm logTerm
    have := Real.log_nonneg h1
    gcongr
    exact (mem_Ioi.mp hy).le
  have hsum0 : Summable (fun n => g n s) := by
    refine Summable.of_norm_bounded (summable_etaTerm hs) fun n => ?_
    rw [hg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_of_nonneg (etaTerm_nonneg s n)]
  have hD := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi isPreconnected_Ioi hgd hbound
    (mem_Ioi.mpr hσ₁s) hsum0 (mem_Ioi.mpr hσ₁s)
  have hval : ∑' n, g' n s = etaDeriv s := by
    have hsum' : Summable (fun n => g' n s) :=
      Summable.of_norm_bounded hu fun n => hbound n s (mem_Ioi.mpr hσ₁s)
    exact tendsto_nhds_unique hsum'.tendsto_sum_tsum_nat (tendsto_etaDerivPartial (by linarith))
  rw [hval] at hD
  refine hD.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds (mem_Ioi.mpr hs)] with x hx
  exact eta_eq_tsum hx

/-! ## 5. The `B₂` Euler–Maclaurin term and the start from a grain -/

/-- [proved-standard; formal-checked] **The `B₂` trapezoid** for `f⁗ ≥ 0` lies within `[−Δf‴/384, 0]` of `∫ f`. -/
theorem trapezoid_B2 {F f f₁ f₂ f₃ f₄ : ℝ → ℝ} {a : ℝ}
    (hF : ∀ x ∈ Icc a (a + 1), HasDerivAt F (f x) x)
    (hf : ∀ x ∈ Icc a (a + 1), HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x ∈ Icc a (a + 1), HasDerivAt f₁ (f₂ x) x)
    (hf₂ : ∀ x ∈ Icc a (a + 1), HasDerivAt f₂ (f₃ x) x)
    (hf₃ : ∀ x ∈ Icc a (a + 1), HasDerivAt f₃ (f₄ x) x)
    (h₄ : ∀ x ∈ Icc a (a + 1), 0 ≤ f₄ x) :
    -(f₃ (a + 1) - f₃ a) / 384 ≤
        (f a + f (a + 1)) / 2 - (f₁ (a + 1) - f₁ a) / 12 - (F (a + 1) - F a) ∧
      (f a + f (a + 1)) / 2 - (f₁ (a + 1) - f₁ a) / 12 - (F (a + 1) - F a) ≤ 0 := by
  -- the Peano kernel `t²(1 − t)²/24` of the rule and its derivatives, at `t = x − a`
  have ht : ∀ x : ℝ, HasDerivAt (fun x : ℝ => x - a) 1 x := fun x => (hasDerivAt_id x).sub_const a
  have hp0 : ∀ x : ℝ, HasDerivAt (fun x : ℝ => ((x - a) ^ 2 - 2 * (x - a) ^ 3 + (x - a) ^ 4) / 24)
      (((x - a) - 3 * (x - a) ^ 2 + 2 * (x - a) ^ 3) / 12) x := fun x => by
    refine ((((ht x).fun_pow 2).sub (((ht x).fun_pow 3).const_mul 2)).add
      ((ht x).fun_pow 4) |>.div_const 24).congr_deriv ?_
    norm_num
    ring
  have hp1 : ∀ x : ℝ, HasDerivAt (fun x : ℝ => ((x - a) - 3 * (x - a) ^ 2 + 2 * (x - a) ^ 3) / 12)
      ((1 - 6 * (x - a) + 6 * (x - a) ^ 2) / 12) x := fun x => by
    refine ((((ht x).sub (((ht x).fun_pow 2).const_mul 3)).add
      (((ht x).fun_pow 3).const_mul 2)).div_const 12).congr_deriv ?_
    norm_num
    ring
  have hp2 : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (1 - 6 * (x - a) + 6 * (x - a) ^ 2) / 12)
      ((x - a) - 1 / 2) x := fun x => by
    refine (((((ht x).const_mul 6).const_sub 1).add (((ht x).fun_pow 2).const_mul 6)).div_const
      12).congr_deriv ?_
    norm_num
    ring
  have hp3 : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (x - a) - 1 / 2) 1 x := fun x =>
    (ht x).sub_const _
  set G₀ : ℝ → ℝ := fun x =>
    ((x - a) ^ 2 - 2 * (x - a) ^ 3 + (x - a) ^ 4) / 24 * f₃ x -
      ((x - a) - 3 * (x - a) ^ 2 + 2 * (x - a) ^ 3) / 12 * f₂ x +
      (1 - 6 * (x - a) + 6 * (x - a) ^ 2) / 12 * f₁ x - ((x - a) - 1 / 2) * f x + F x with hG₀
  have hG₀d : ∀ x ∈ Icc a (a + 1),
      HasDerivAt G₀ (((x - a) ^ 2 - 2 * (x - a) ^ 3 + (x - a) ^ 4) / 24 * f₄ x) x := by
    intro x hx
    refine (((((hp0 x).fun_mul (hf₃ x hx)).sub ((hp1 x).fun_mul (hf₂ x hx))).add
      ((hp2 x).fun_mul (hf₁ x hx))).sub ((hp3 x).fun_mul (hf x hx))).add (hF x hx) |>.congr_deriv ?_
    ring
  have hkernel : ∀ x ∈ Icc a (a + 1), ((x - a) ^ 2 - 2 * (x - a) ^ 3 + (x - a) ^ 4) / 24 ≤ 1 / 384 ∧
      0 ≤ ((x - a) ^ 2 - 2 * (x - a) ^ 3 + (x - a) ^ 4) / 24 := by
    intro x hx
    have h0 : 0 ≤ x - a := by linarith [hx.1]
    have h1 : 0 ≤ 1 - (x - a) := by linarith [hx.2]
    have e : (x - a) ^ 2 - 2 * (x - a) ^ 3 + (x - a) ^ 4 = ((x - a) * (1 - (x - a))) ^ 2 := by ring
    have hq : 0 ≤ (x - a) * (1 - (x - a)) := mul_nonneg h0 h1
    have hq' : (x - a) * (1 - (x - a)) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - a - 1 / 2)]
    rw [e]
    constructor <;> nlinarith
  have hab : a ≤ a + 1 := by linarith
  have hmem0 : a ∈ Icc a (a + 1) := ⟨le_rfl, hab⟩
  have hmem1 : a + 1 ∈ Icc a (a + 1) := ⟨hab, le_rfl⟩
  have hint : interior (Icc a (a + 1)) ⊆ Icc a (a + 1) := interior_subset
  have mono₀ : MonotoneOn G₀ (Icc a (a + 1)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a (a + 1))
      (fun x hx => (hG₀d x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hG₀d x (hint hx)).hasDerivWithinAt)
      (fun x hx => mul_nonneg (hkernel x (hint hx)).2 (h₄ x (hint hx)))
  have hG₁d : ∀ x ∈ Icc a (a + 1), HasDerivAt (fun x => f₃ x / 384 - G₀ x)
      ((1 / 384 - ((x - a) ^ 2 - 2 * (x - a) ^ 3 + (x - a) ^ 4) / 24) * f₄ x) x := by
    intro x hx
    refine (((hf₃ x hx).div_const 384).sub (hG₀d x hx)).congr_deriv ?_
    ring
  have mono₁ : MonotoneOn (fun x => f₃ x / 384 - G₀ x) (Icc a (a + 1)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a (a + 1))
      (fun x hx => (hG₁d x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hG₁d x (hint hx)).hasDerivWithinAt)
      (fun x hx => mul_nonneg (by linarith [(hkernel x (hint hx)).1]) (h₄ x (hint hx)))
  have l0 := mono₀ hmem0 hmem1 hab
  have l1 := mono₁ hmem0 hmem1 hab
  simp only [hG₀, sub_self, add_sub_cancel_left] at l0 l1
  norm_num at l0 l1
  constructor <;> linarith

/-- [proved-standard; formal-checked] The `B₂` trapezoids telescoped over `K` unit steps from `x₀`. -/
theorem trapezoid_B2_telescope {f F f₁ f₃ : ℝ → ℝ} {x₀ : ℝ}
    (hstep : ∀ i : ℕ,
      -(f₃ (x₀ + i + 1) - f₃ (x₀ + i)) / 384 ≤
          (f (x₀ + i) + f (x₀ + i + 1)) / 2 - (f₁ (x₀ + i + 1) - f₁ (x₀ + i)) / 12 -
            (F (x₀ + i + 1) - F (x₀ + i)) ∧
        (f (x₀ + i) + f (x₀ + i + 1)) / 2 - (f₁ (x₀ + i + 1) - f₁ (x₀ + i)) / 12 -
            (F (x₀ + i + 1) - F (x₀ + i)) ≤ 0) (K : ℕ) :
    -(f₃ (x₀ + K) - f₃ x₀) / 384 ≤
        ∑ i ∈ range K, f (x₀ + i) - f x₀ / 2 + f (x₀ + K) / 2 - (f₁ (x₀ + K) - f₁ x₀) / 12 -
          (F (x₀ + K) - F x₀) ∧
      ∑ i ∈ range K, f (x₀ + i) - f x₀ / 2 + f (x₀ + K) / 2 - (f₁ (x₀ + K) - f₁ x₀) / 12 -
          (F (x₀ + K) - F x₀) ≤ 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
    have e : x₀ + ((K + 1 : ℕ) : ℝ) = x₀ + K + 1 := by push_cast; ring
    rw [sum_range_succ, e]
    obtain ⟨h1, h2⟩ := hstep K
    obtain ⟨i1, i2⟩ := ih
    constructor <;> linarith

/-- [proved-standard; formal-checked] The rate of `c y^p` is `c p y^(p−1)` for `y > 0`. -/
theorem hasDerivAt_const_mul_rpow (c p : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => c * y ^ p) (c * p * x ^ (p - 1)) x := by
  refine ((Real.hasDerivAt_rpow_const (p := p) (Or.inl hx.ne')).const_mul c).congr_deriv ?_
  ring

/-- [proved-standard; formal-checked] One `B₂` trapezoid of `x^(−s)` on `[x, x + 1]`, for `s > 1`. -/
theorem rpow_trapezoid_B2_step {s x : ℝ} (hs : 1 < s) (hx : 0 < x) :
    -((-(s * (s + 1) * (s + 2))) * (x + 1) ^ (-s - 3) - (-(s * (s + 1) * (s + 2))) * x ^ (-s - 3)) / 384 ≤
        (1 * x ^ (-s) + 1 * (x + 1) ^ (-s)) / 2 - (-s * (x + 1) ^ (-s - 1) - -s * x ^ (-s - 1)) / 12 -
          (1 / (1 - s) * (x + 1) ^ (1 - s) - 1 / (1 - s) * x ^ (1 - s)) ∧
      (1 * x ^ (-s) + 1 * (x + 1) ^ (-s)) / 2 - (-s * (x + 1) ^ (-s - 1) - -s * x ^ (-s - 1)) / 12 -
          (1 / (1 - s) * (x + 1) ^ (1 - s) - 1 / (1 - s) * x ^ (1 - s)) ≤ 0 := by
  have hs1 : (1 : ℝ) - s ≠ 0 := by linarith
  have hpos : ∀ t ∈ Icc x (x + 1), 0 < t := fun t ht => hx.trans_le ht.1
  refine trapezoid_B2 (F := fun t => 1 / (1 - s) * t ^ (1 - s)) (f := fun t => 1 * t ^ (-s))
    (f₁ := fun t => -s * t ^ (-s - 1)) (f₂ := fun t => s * (s + 1) * t ^ (-s - 2))
    (f₃ := fun t => -(s * (s + 1) * (s + 2)) * t ^ (-s - 3))
    (f₄ := fun t => s * (s + 1) * (s + 2) * (s + 3) * t ^ (-s - 4)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht
    refine (hasDerivAt_const_mul_rpow _ _ (hpos t ht)).congr_deriv ?_
    rw [show 1 - s - 1 = -s by ring]
    field_simp
  · intro t ht
    refine (hasDerivAt_const_mul_rpow _ _ (hpos t ht)).congr_deriv ?_
    ring
  · intro t ht
    refine (hasDerivAt_const_mul_rpow _ _ (hpos t ht)).congr_deriv ?_
    rw [show -s - 1 - 1 = -s - 2 by ring]
    ring
  · intro t ht
    refine (hasDerivAt_const_mul_rpow _ _ (hpos t ht)).congr_deriv ?_
    rw [show -s - 2 - 1 = -s - 3 by ring]
    ring
  · intro t ht
    refine (hasDerivAt_const_mul_rpow _ _ (hpos t ht)).congr_deriv ?_
    rw [show -s - 3 - 1 = -s - 4 by ring]
    ring
  · intro t ht
    have := hpos t ht
    have : 0 < s := by linarith
    positivity

/-- [definition] ζ's tail to the `B₂` term: `N^(1−s)/(s − 1) + N^(−s)/2 + s N^(−s−1)/12`. -/
noncomputable def emTwo (s : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ (1 - s) / (s - 1) + (N : ℝ) ^ (-s) / 2 + s * (N : ℝ) ^ (-s - 1) / 12

/-- [definition] The `B₂` remainder bound: `s(s + 1)(s + 2) N^(−s−3)/384`. -/
noncomputable def emTwoRem (s : ℝ) (N : ℕ) : ℝ := s * (s + 1) * (s + 2) * (N : ℝ) ^ (-s - 3) / 384

/-- [proved-standard; formal-checked] **ζ's `B₂` remainder** after `N ≥ 1` terms: in `[−s(s+1)(s+2)N^(−s−3)/384, 0]`. -/
theorem zetaTail_euler_maclaurin_two {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 1 ≤ N) :
    -emTwoRem s N ≤ zetaTail s N - emTwo s N ∧ zetaTail s N - emTwo s N ≤ 0 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hstep := fun i : ℕ => rpow_trapezoid_B2_step hs (x := (N : ℝ) + i) (by positivity)
  have htel := trapezoid_B2_telescope (f := fun t => 1 * t ^ (-s))
    (F := fun t => 1 / (1 - s) * t ^ (1 - s)) (f₁ := fun t => -s * t ^ (-s - 1))
    (f₃ := fun t => -(s * (s + 1) * (s + 2)) * t ^ (-s - 3)) (x₀ := N) hstep
  have hgo : Tendsto (fun K : ℕ => (N : ℝ) + K) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hpow : ∀ r : ℝ, 0 < r → Tendsto (fun K : ℕ => ((N : ℝ) + K) ^ (-r)) atTop (𝓝 0) :=
    fun r hr => (tendsto_rpow_neg_atTop hr).comp hgo
  have hf0 : Tendsto (fun K : ℕ => 1 * ((N : ℝ) + K) ^ (-s)) atTop (𝓝 0) := by
    simpa using hpow s (by linarith)
  have hf₁0 : Tendsto (fun K : ℕ => -s * ((N : ℝ) + K) ^ (-s - 1)) atTop (𝓝 0) := by
    have h := (hpow (s + 1) (by linarith)).const_mul (-s)
    rw [mul_zero] at h
    simpa only [neg_add'] using h
  have hf₃0 : Tendsto (fun K : ℕ => -(s * (s + 1) * (s + 2)) * ((N : ℝ) + K) ^ (-s - 3)) atTop
      (𝓝 0) := by
    have h := (hpow (s + 3) (by linarith)).const_mul (-(s * (s + 1) * (s + 2)))
    rw [mul_zero] at h
    simpa only [neg_add'] using h
  have hF0 : Tendsto (fun K : ℕ => 1 / (1 - s) * ((N : ℝ) + K) ^ (1 - s)) atTop (𝓝 0) := by
    have h := (hpow (s - 1) (by linarith)).const_mul (1 / (1 - s))
    rw [mul_zero] at h
    simpa only [neg_sub] using h
  have hsum : Tendsto (fun K : ℕ => ∑ i ∈ range K, 1 * ((N : ℝ) + i) ^ (-s)) atTop
      (𝓝 (zetaTail s N)) := by
    have h := (summable_zetaTail hs N).tendsto_sum_tsum_nat
    refine h.congr fun K => sum_congr rfl fun i _ => ?_
    rw [Nat.cast_add, add_comm, one_mul]
  have hD := ((((hsum.sub_const (1 * (N : ℝ) ^ (-s) / 2)).add (hf0.div_const 2)).sub
    ((hf₁0.sub_const (-s * (N : ℝ) ^ (-s - 1))).div_const 12)).sub
    (hF0.sub_const (1 / (1 - s) * (N : ℝ) ^ (1 - s))))
  have hB := ((hf₃0.sub_const (-(s * (s + 1) * (s + 2)) * (N : ℝ) ^ (-s - 3))).neg).div_const 384
  have l1 := le_of_tendsto_of_tendsto' hB hD fun K => (htel K).1
  have l2 := le_of_tendsto' hD fun K => (htel K).2
  have hs1 : (1 : ℝ) - s ≠ 0 := by linarith
  have hFN : 1 / (1 - s) * (N : ℝ) ^ (1 - s) = -((N : ℝ) ^ (1 - s) / (s - 1)) := by
    rw [one_div_mul_eq_div, ← div_neg, neg_sub]
  simp only [hFN, zero_div, add_zero, zero_sub, one_mul, neg_neg] at l1 l2
  unfold emTwo emTwoRem
  constructor <;> linarith

/-- [proved-standard; formal-checked] **ζ's `B₂` enclosure** at real `s > 1` from a head of `N ≥ 1` terms. -/
theorem zeta_mem_enclosure_two {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 1 ≤ N) :
    zetaHead s N + emTwo s N - emTwoRem s N ≤ (riemannZeta s).re ∧
      (riemannZeta s).re ≤ zetaHead s N + emTwo s N := by
  rw [riemannZeta_ofReal hs, Complex.ofReal_re, zetaR_eq_head_add_tail hs N]
  obtain ⟨h1, h2⟩ := zetaTail_euler_maclaurin_two hs hN
  constructor <;> linarith

/-- [proved-standard; formal-checked] A start `N` with `2^k s(s+1)(s+2) ≤ 384 N⁴` meets the tolerance `2^(−k)`. -/
theorem emTwoRem_le_of_pow {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 1 ≤ N) {k : ℕ}
    (hNk : 2 ^ k * (s * (s + 1) * (s + 2)) ≤ 384 * (N : ℝ) ^ 4) : emTwoRem s N ≤ 1 / 2 ^ k := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hc : 0 < s * (s + 1) * (s + 2) := by
    have : 0 < s := by linarith
    positivity
  have hp : (N : ℝ) ^ (-s - 3) ≤ ((N : ℝ) ^ 4)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hN0.le]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  unfold emTwoRem
  calc s * (s + 1) * (s + 2) * (N : ℝ) ^ (-s - 3) / 384
      ≤ s * (s + 1) * (s + 2) * ((N : ℝ) ^ 4)⁻¹ / 384 := by gcongr
    _ ≤ 1 / 2 ^ k := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity), ← div_eq_mul_inv,
          div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        linarith

/-- [definition] The start read from a declared grain `2^(−k)`: `⌈(2^k s(s+1)(s+2)/384)^(1/4)⌉ + 1`. -/
noncomputable def emStart (k : ℕ) (s : ℝ) : ℕ :=
  ⌈(2 ^ k * (s * (s + 1) * (s + 2)) / 384) ^ ((4 : ℝ)⁻¹)⌉₊ + 1

/-- [proved-derived; formal-checked] **The start from a grain**: from `emStart k s` terms the remainder is `≤ 2^(−k)` -/
theorem emStart_spec {s : ℝ} (hs : 1 < s) (k : ℕ) :
    1 ≤ emStart k s ∧ |zetaTail s (emStart k s) - emTwo s (emStart k s)| ≤ 1 / 2 ^ k := by
  have hc : 0 ≤ 2 ^ k * (s * (s + 1) * (s + 2)) / 384 := by
    have : 0 < s := by linarith
    positivity
  have hN : 1 ≤ emStart k s := by simp [emStart]
  refine ⟨hN, ?_⟩
  have hge : (2 ^ k * (s * (s + 1) * (s + 2)) / 384) ^ ((4 : ℝ)⁻¹) ≤ (emStart k s : ℝ) := by
    unfold emStart
    push_cast
    linarith [Nat.le_ceil ((2 ^ k * (s * (s + 1) * (s + 2)) / 384) ^ ((4 : ℝ)⁻¹))]
  have h4 := pow_le_pow_left₀ (Real.rpow_nonneg hc _) hge 4
  have hroot := Real.rpow_inv_natCast_pow (n := 4) hc (by norm_num)
  push_cast at hroot
  rw [hroot] at h4
  have hrem := emTwoRem_le_of_pow hs hN (k := k) (by linarith)
  obtain ⟨h1, h2⟩ := zetaTail_euler_maclaurin_two hs hN
  rw [abs_le]
  constructor <;> linarith

/-! ## 6. Witnesses -/

/-- [proved-standard; formal-checked] `x^(−m) = (x^m)⁻¹` for `x ≥ 0` and a natural `m`. -/
theorem rpow_neg_natCast {x : ℝ} (hx : 0 ≤ x) (m : ℕ) : x ^ (-(m : ℝ)) = (x ^ m)⁻¹ := by
  rw [Real.rpow_neg hx, Real.rpow_natCast]

/-- [proved-standard; formal-checked] **ζ(2 + i) from four terms**: within `9/128` of head plus `4^(1−s)/(s − 1)`. -/
theorem zeta_two_add_I_disc :
    ‖riemannZeta (2 + Complex.I) - (1 + 2 ^ (-(2 + Complex.I)) + 3 ^ (-(2 + Complex.I)) +
      4 ^ (1 - (2 + Complex.I)) / (1 + Complex.I))‖ ≤ 9 / 128 := by
  have hs : 1 < (2 + Complex.I).re := by simp
  have h := riemannZeta_mem_disc hs (N := 4) (by norm_num)
  have hne : -(2 + Complex.I) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    norm_num at this
  have hhead : zetaHeadC (2 + Complex.I) 4 = 1 + 2 ^ (-(2 + Complex.I)) + 3 ^ (-(2 + Complex.I)) := by
    simp only [zetaHeadC, sum_range_succ, range_zero, sum_empty, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat]
    rw [Complex.zero_cpow hne, Complex.one_cpow]
    ring
  have hden : (2 + Complex.I) - 1 = 1 + Complex.I := by ring
  have hnorm : ‖(2 : ℂ) + Complex.I‖ ≤ 9 / 4 := by
    have h5 : ‖(2 : ℂ) + Complex.I‖ ^ 2 = 5 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      norm_num
    nlinarith [norm_nonneg ((2 : ℂ) + Complex.I)]
  have hre : (2 + Complex.I).re = 2 := by simp
  have h4 : ((4 : ℕ) : ℝ) ^ (-(2 : ℝ)) = 1 / 16 := by
    rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, rpow_neg_natCast (by norm_num)]
    norm_num
  rw [hhead, hden, hre, h4] at h
  push_cast at h
  refine h.trans ?_
  nlinarith

/-- [proved-standard; formal-checked] At real `σ` the jet terms are the real log-power magnitudes. -/
theorem jetTerm_ofReal (k : ℕ) (σ : ℝ) (n : ℕ) : jetTerm k (σ : ℂ) n = ((logTerm k σ n : ℝ) : ℂ) := by
  rw [jetTerm, logTerm, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, Complex.ofReal_neg]

/-- [proved-standard; formal-checked] At real `σ > 1`, `ζ′(σ) = −Σ log n · n^(−σ)`, a real value. -/
theorem deriv_riemannZeta_ofReal {σ : ℝ} (hσ : 1 < σ) :
    deriv riemannZeta σ = -((∑' n : ℕ, logTerm 1 σ n : ℝ) : ℂ) := by
  rw [deriv_riemannZeta_eq (by simpa using hσ), Complex.ofReal_tsum]
  simp only [jetTerm_ofReal]

/-- [proved-standard; formal-checked] **ζ′(2) from four terms** and its tail bracket: an interval of width `log 2/8`. -/
theorem deriv_riemannZeta_two_mem :
    (deriv riemannZeta 2).im = 0 ∧
      -(7 * Real.log 2 / 8 + Real.log 3 / 9 + 1 / 4) ≤ (deriv riemannZeta 2).re ∧
      (deriv riemannZeta 2).re ≤ -(3 * Real.log 2 / 4 + Real.log 3 / 9 + 1 / 4) := by
  have h2 : (1 : ℝ) < 2 := by norm_num
  have hd := deriv_riemannZeta_ofReal h2
  rw [show ((2 : ℝ) : ℂ) = 2 by norm_num] at hd
  have hl2 := Real.log_two_gt_d9
  have hlog4 : Real.log ((4 : ℕ) : ℝ) = 2 * Real.log 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hk : ((1 : ℕ) : ℝ) ≤ 2 * Real.log ((4 : ℕ) : ℝ) := by
    rw [hlog4]
    push_cast
    linarith
  obtain ⟨-, hlo, hup⟩ := logTail_bracket 1 h2 (N := 4) (by norm_num) hk
  have hsplit := ((summable_logTerm 1 h2).sum_add_tsum_nat_add 4).symm
  have e2 : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
    rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, rpow_neg_natCast (by norm_num)]
    norm_num
  have e3 : (3 : ℝ) ^ (-(2 : ℝ)) = 1 / 9 := by
    rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, rpow_neg_natCast (by norm_num)]
    norm_num
  have e4 : (4 : ℝ) ^ (-(2 : ℝ)) = 1 / 16 := by
    rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, rpow_neg_natCast (by norm_num)]
    norm_num
  have e4' : (4 : ℝ) ^ (1 - (2 : ℝ)) = 1 / 4 := by
    rw [show (1 - (2 : ℝ)) = -((1 : ℕ) : ℝ) by norm_num, rpow_neg_natCast (by norm_num)]
    norm_num
  have hhead : ∑ n ∈ range 4, logTerm 1 2 (n : ℝ) = Real.log 2 / 4 + Real.log 3 / 9 := by
    simp only [sum_range_succ, range_zero, sum_empty, logTerm, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, Real.log_zero, Real.log_one, pow_one, zero_mul, e2, e3]
    ring
  have hT : logTerm 1 2 ((4 : ℕ) : ℝ) = Real.log 2 / 8 := by
    rw [logTerm, hlog4]
    norm_num [e4]
    ring
  have hP : logPrim 1 2 ((4 : ℕ) : ℝ) = Real.log 2 / 2 + 1 / 4 := by
    simp only [logPrim, zero_add, pow_one, Nat.cast_zero]
    rw [hlog4]
    norm_num [e4']
    ring
  rw [hT, hP] at hup
  rw [hP] at hlo
  rw [hhead] at hsplit
  rw [hd, hsplit]
  simp only [Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.neg_re, Complex.ofReal_re,
    true_and]
  constructor <;> linarith

/-- [proved-standard; formal-checked] The Basel head of ten terms: `Σ_(n<10) n^(−2) = 9778141/6350400`. -/
theorem zetaHead_two_ten : zetaHead 2 10 = 9778141 / 6350400 := by
  have e : ∀ n : ℕ, (n : ℝ) ^ (-(2 : ℝ)) = ((n : ℝ) ^ 2)⁻¹ := fun n => by
    rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, rpow_neg_natCast (Nat.cast_nonneg n)]
  simp only [zetaHead, e, sum_range_succ, range_zero, sum_empty]
  norm_num

/-- [proved-standard; formal-checked] **ζ(2) by its `B₂` head of ten terms**: `π²/6` within `10⁻⁶` of a rational. -/
theorem zeta_two_enclosure_ten :
    (52229957 / 31752000 : ℝ) - 1 / 1600000 ≤ Real.pi ^ 2 / 6 ∧
      Real.pi ^ 2 / 6 ≤ 52229957 / 31752000 ∧
      |Real.pi ^ 2 / 6 - 52229957 / 31752000| ≤ 1 / 10 ^ 6 := by
  have hz : zetaR 2 = Real.pi ^ 2 / 6 := by
    rw [zetaR, ← hasSum_zeta_two.tsum_eq]
    congr 1
    funext n
    rw [Real.rpow_neg (Nat.cast_nonneg n), Real.rpow_two, one_div]
  have h := zetaTail_euler_maclaurin_two (s := 2) (by norm_num) (N := 10) (by norm_num)
  have hsplit := zetaR_eq_head_add_tail (s := 2) (by norm_num) 10
  rw [hz, zetaHead_two_ten] at hsplit
  have e1 : (10 : ℝ) ^ (1 - (2 : ℝ)) = 1 / 10 := by
    rw [show (1 - (2 : ℝ)) = -((1 : ℕ) : ℝ) by norm_num, rpow_neg_natCast (by norm_num)]
    norm_num
  have e2 : (10 : ℝ) ^ (-(2 : ℝ)) = 1 / 100 := by
    rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, rpow_neg_natCast (by norm_num)]
    norm_num
  have e3 : (10 : ℝ) ^ (-(2 : ℝ) - 1) = 1 / 1000 := by
    rw [show (-(2 : ℝ) - 1) = -((3 : ℕ) : ℝ) by norm_num, rpow_neg_natCast (by norm_num)]
    norm_num
  have e5 : (10 : ℝ) ^ (-(2 : ℝ) - 3) = 1 / 100000 := by
    rw [show (-(2 : ℝ) - 3) = -((5 : ℕ) : ℝ) by norm_num, rpow_neg_natCast (by norm_num)]
    norm_num
  simp only [emTwo, emTwoRem, Nat.cast_ofNat, e1, e2, e3, e5] at h
  norm_num at h
  refine ⟨by linarith [h.1], by linarith [h.2], ?_⟩
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

end Holonics.Mathematics.ZetaJets

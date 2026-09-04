# DB3: the average contracts the strip of every member, and N² averages put the zeros of ξ on the seam

**Date:** 2026-09-03  
**Truth status:** `proved-derived`  
**Evidence:** `formal-checked`, `source-inspected`  
**Campaign:** DB3 under
[`THE_SEAM_HAS_A_FIRST_TIME_BY_DE_BRUIJN_AND_THE_THRESHOLD_IS_RH_WITH_NO_PORT.md`](../../archive/plans/THE_SEAM_HAS_A_FIRST_TIME_BY_DE_BRUIJN_AND_THE_THRESHOLD_IS_RH_WITH_NO_PORT.md).  
**Owners:** `RH/KernelAverage.lean`, `RH/LineApproximation.lean` (generalized in place),
`RH/ConjIndex.lean`, `RH/StripAverage.lean`, `RH/DeBruijnIterate.lean` under
`soma/formal/elementary-holonics/ElementaryHolonics/`, registered in the root umbrella; DB1 in
`RH/XiStrip.lean` and DB2 in `RH/TranslationAverage.lean` are its inputs.  
**Scope:** schedules nothing beyond the directed order; the engine frontier is unchanged.

## The return

[definition] `avg μ f (s) = ½ (f(s+μ) + f(s−μ))`; `coshMul κ μ` the kernel `cosh(μu) K(u)`,
`coshPow κ μ k` its `k`-fold form; `NoRealZero f`: every zero has `Im ≠ 0`; `ConjSymm f`:
`f(z̄) = conj f(z)`; `σ'` the involution `u ↦ 1 − ū` on the upper repeated index; `xc z = −i(z − ½)`
the seam coordinate; `xiIter μ k = (avg μ)^[k] ξ`.

[proved-derived; formal-checked]

- **DB1** (`XiStrip`): `re_mem_Ioo_of_riemannXi_eq_zero`, every zero of `ξ` has `0 < Re s < 1`,
  from Mathlib's `riemannZeta_ne_zero_of_one_le_re`, the factorization, and the reflection;
  `riemannXi_ofReal_pos`: `ξ(σ) > 0` on the real axis by the positive kernel; hence
  `im_ne_zero_of_riemannXi_eq_zero`.
- **DB2** (`TranslationAverage`): `pair_norm_lt` (Lemma 1 in coordinates), the product over the
  conjugation-invariant root multiset, `norm_eval_lt`, and **`im_sq_le_of_avg_eq_zero`**
  (Theorem 3 in strip form for real polynomials).
- `KernelAverage`: **`T_coshMul`**: `T_{cosh(μu)K} = avg μ T_K`; `T_coshPow`; `T_ofReal_pos`,
  `T_conj`, `T_one_sub`: a positive real even kernel gives a transform positive on the real axis,
  conjugation-symmetric, and reflection-symmetric.
- `LineApproximation` (generalized): `NoRealZero`, `OnSeam.noRealZero`, and the primed chain
  `mirror_mem_upper_iff'`, `upperEquivCompl'`, `hasProd_lower'`, `P_eq_Qplus_sq'`,
  `eq_centre_mul_Qplus'`, `tendsto_approx'`, with the seam forms kept as wrappers; the FT
  owners downstream build unchanged.
- `ConjIndex`: `analyticOrderAt_conj`, **`mult_conj`** (multiplicities are conjugation-invariant
  for a `ConjSymm` member, by transporting the local factorization through `conj ∘ g ∘ conj`);
  `refl`, `σ'`, `σ'_σ'`, `a_σ'` (`a (σ' i) z = conj (a i z̄)`); `sym`, `tendsto_sym`,
  `σ'_mem_sym_iff`, `prod_sym_σ'`.
- `StripAverage`: `norm_one_add_a` and `norm_pair_eq` (a factor pair is two Lemma-1 pairs in
  `xc`), **`pair_lt`** and `pair_le` (one paired factor contracts left of the seam),
  `sq_prod_eq` and **`prod_le_margin`** (the square of a symmetric finite product is the product
  of the paired factors, so the product contracts with the margin of one fixed pair),
  `sub_ne_zero_of_left`, **`norm_translate_lt`** (`‖f(ζ+μ)‖ < ‖f(ζ−μ)‖` for `Re ζ < ½` outside
  the shrunken strip, by the margin surviving the limit along `sym`), and
  **`re_sq_le_of_avg_eq_zero`**: for a member with `ConjSymm` and `NoRealZero` whose zeros lie in
  `|Re − ½| ≤ Δ`, every zero of `avg μ f` has `(Re − ½)² ≤ max(Δ² − μ², 0)`. This is de Bruijn's
  Theorem 8 in the tree's coordinate.
- `DeBruijnIterate`: `hasGrowth_avg` and `fosterClass_avg` (the class is closed under the
  average given a nonzero centre); `xiIter_eq_T`, `xiIter_conjSymm`, `xiIter_noRealZero`,
  `xiIter_centre_ne_zero`, `fosterClass_xiIter` (the iterates of `ξ` are class members with
  positive even kernels `cosh(μu)^k Φ`); **`strip_xiIter`**: every zero of `xiIter μ k` has
  `(Re − ½)² ≤ max(¼ − kμ², 0)`; **`onSeam_xiIter`**: for `N ≥ 1`, `OnSeam (xiIter (1/(2N)) N²)`.

`#print axioms` on `im_sq_le_of_avg_eq_zero`, `re_sq_le_of_avg_eq_zero`, and `onSeam_xiIter`
returns `propext`, `Classical.choice`, `Quot.sound`. The owners build alone (`DeBruijnIterate`
at 8,797 jobs) and inside the root umbrella.

## The scope, corrected in place

[definition] The contract's DB3 named a strip form of Hurwitz (`StripHurwitz`) and a strip
form of the polynomial approximants. Neither was needed: the entire transport is done on the
infinite product itself, through its finite symmetric sections, with the margin of one fixed pair
carried through the limit by `le_of_tendsto_of_tendsto`; the polynomial theorem of DB2 is the
model, not an input. The class closure needed a nonzero centre, which the general member does not
guarantee and the iterates of `ξ` have by kernel positivity, exactly as the contract's §3 named.
The owner list is corrected accordingly.

## Pass DB3

`OnSeam (xiIter (1/(2N)) N²)` for every `N ≥ 1`, formal-checked. **DB3 passes** at the corrected
scope. Falsifier: an `N ≥ 1` and a zero of the iterate off the seam.

## Boundaries

- No claim on `Λ_DN`; `DeBruijnBound` remains a port until DB5.
- The Gaussian limit `xiIter (1/(2N)) N² → heatE (−1/8) ξ` is DB4's.

## Reproduction

```bash
cd soma/formal/elementary-holonics
timeout 180s lake build ElementaryHolonics.RH.XiStrip
timeout 180s lake build ElementaryHolonics.RH.TranslationAverage
timeout 180s lake build ElementaryHolonics.RH.DeBruijnIterate
timeout 180s lake build ElementaryHolonics
```

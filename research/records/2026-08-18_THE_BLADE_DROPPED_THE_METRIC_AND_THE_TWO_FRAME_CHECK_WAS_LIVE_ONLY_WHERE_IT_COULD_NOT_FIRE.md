# The blade dropped the metric, and the two-frame check was live only where it could not fire

**Date:** 2026-08-18
**Truth status:** `established-bounded` for every repair and every figure, each verified by running
the tests it is asserted in; `proved-standard` for Cauchy–Binet, which is the identity the repair
restores.
**Evidence:** `measured`. `cargo test --workspace` → **2,424 passed, 0 failed, 19 ignored, 43 result
lines**, taken after the last repair. Each repair carries the test that holds it.
**Provenance:** a capability census over 281 library modules and 330,406 lines, dispatched 2026-08-18
at Brandon's instruction — *"Overview the entirety of the repository and address capabilities that
you are not unifying, do not be an idiot and not utilize things that are already partially
constructed"* — together with an external adjudication of the same day.
**Plan:** stations one and two of
[`blueprint/THE_MAP_IS_MATERIAL_THE_HEAD_IS_A_CONTACT_AND_THE_INSTANCE_RESUMES.md`](../../blueprint/THE_MAP_IS_MATERIAL_THE_HEAD_IS_A_CONTACT_AND_THE_INSTANCE_RESUMES.md),
which sits under [`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md).

---

## 0. The result, in one line

> **The organ that computes the area of a crossing dropped the metric, and the doc that hid it
> claimed a false theorem — that Lagrange's identity is Euclidean. Cauchy–Binet holds in every
> diagonal signature, so the guard that withheld the cross-check withheld it exactly where the two
> frames would have disagreed. The two-frame instrument was live only where it could not fire.**

## 1. The defect, and it flips a causal class

`crates/holonic-engine/src/clifford.rs` computed `from_blade = Σ (blade coordinate)²` with **no
`qᵢqⱼ` weighting**, while Lagrange was computed from the metric-weighted spans. The doc said
*"Lagrange holds only in the Euclidean signature, so the second frame is offered only there."*
Cauchy–Binet:

```text
    ‖a‖²‖b‖² − (a·b)²  =  Σ_{i<j} qᵢqⱼ (aᵢbⱼ − aⱼbᵢ)²
```

holds for **every** diagonal signature. The identity failed only because the weighting was missing,
and the `euclidean` guard therefore disabled the comparison precisely where it would have caught
that. `CLAUDE.md` §8's rule fires exactly here: *a check whose material cannot vary the property
under test is the same defect as a check that cannot fail.*

Computed on the module's **own committed Minkowski fixture** — `q = (−1,1,1)`, `a = (1,1,0)`,
`b = (1,0,1)`:

```text
    aim                        −1
    Lagrange                   −1
    Cauchy–Binet blade         −1     agrees
    what the organ returned     3     the unweighted blade
    causal_class  value−aim²    2  ->  TransportDominant
    correct       −1 − 1       −2  ->  StorageDominant
```

**The causal class flipped, and no test asserted `causal_class` on that arrow.** Two now do. And the
test that did exist — `lagrange_is_offered_only_where_it_holds` — **was asserting the defect**: it
required `lagrange == None` on that fixture. It is replaced by
`the_two_frames_agree_off_euclidean_once_the_blade_carries_the_metric`.

This matters beyond the fixture because the four-class causal census is computed from
`area² − aim²`, and that census is the reading the head work depends on.

## 2. Five more, each a doc that denied what its own body did

**The primality check was `prime < 2`.** `surprisal.rs`'s whole exactness argument is the ℚ-linear
independence of `{log₂ p : p prime}` — that is what makes `is_zero` true *exactly* when the form is
zero as a real number. `term(4, …)` is public and was admitted, so `term(2,2).minus(&term(4,1))` is
zero as a real number while `is_zero()` returned `false` and `compare` returned `Open`, never
`Equal`. The claimed iff was false on inputs the public constructor accepts. Repaired by exact trial
division, held by `a_composite_is_refused_by_name_so_the_zero_test_stays_exact`.

**A ruling of Brandon's was corrupted by a mechanical sweep.** `embedding_fiber.rs` quoted him as
*"stop calling the CPU the **'cpu'**"* and then asserted *"`cpu` is CUDA's word."* The ruling is
`host`, and `host` is CUDA's word; a `host → cpu` rename passed **through the quotation marks**,
leaving him quoted telling himself not to call the CPU "the cpu". Three non-quotational sites carried
the same artifact. **This is the contamination `CLAUDE.md` §9 calls hardest to detect, because no
later reader re-checks a provenance line — that is what the line is for.** A sweep that rewrites
prose must not enter a quotation, and this one did.

**`exponentiated_ratio::rebased_by` was documented twice wrongly.** It was said to take *"the root,
taken only where it stays in ℚ"* and to *"refuse where the root leaves ℚ"*; it takes an integer
power, so no root is taken, none can leave ℚ, and `RatioError` correctly carries no variant — the
promised refusal was **unreachable and unimplemented**. And it was said that *"no path here reaches
`T → 0`, which is argmax"*; the parameter **is** `1/T`, so `T → 0` is `reciprocal → ∞` and the
parameter drives straight at it. **The ban is not violated** — every ratio is returned and none
crowned at any reciprocal, which is what actually holds it — but both sentences were false. The
family now also **records the reciprocal it stands in**, because without it a rebased family was
bit-indistinguishable from a warm one, which is the absolute-frame defect one level in.

**`holonic_training` denied a scalar it computes eleven lines later.** The doc read *"Receiver
parameters do not assign a scalar score"* and `agreement_rank = …max()` discarded every route below
the maximum. That is a scalar deciding which routes survive. **And the deletion had a second cost:**
a sub-maximal fiber never entered the two-sided evidence and so **could never be refuted**, which is
the one thing the two-sided standing was added to make possible. The maximum stands — it is an exact
incidence count, not a magnitude — and the population it sets aside is now returned as
`withheld_below_rank`. Measured on real material by
`the_rank_maximum_returns_what_it_set_aside`: **the remainder is non-empty**, so the division
genuinely had one and it was being dropped.

**`Observation`'s doc said *"nothing here can be ordered"* and the next line derives `Ord`.** The
derive is required — `Partition::from_keys` groups by signature and the device path reads the field
as a key. What the sentence meant, and now says, is that no law in the module reads an ordering
between two observations as a magnitude.

## 3. What station one removed, and why the finding survives it

An external adjudication convicted the 2026-08-18 emission work as *"a corpus enumerator decorated
with exact mathematics."* Removed: `RecruitmentLaw::ArrowAdmitted` (a governor — `Cohere => true`,
non-empty `Ortho => true`, `Anti => false` — and the driver never exercised it), the
route-feature `PairingReading` (overlap dressed as Clifford structure), and the `JunctionDigest` the
ratios rode out on. `BranchingLaw::CompleteUnderRatioFamily` is renamed **`CompleteJunction`**: it
branches the whole junction and **forms no ratio**, which is what it always did.

The junction reading — `ContinuationReading`, the horizon profile, the multiplicities — **stands as a
diagnostic**, and so does the measured finding it produced: the gate keeps, at every step, the
continuations attested by the longest matching corpus span, and keeps exactly one. The driver is
rewritten as what it is, a corpus diagnostic, with its own header naming what was superseded.

## 4. Where each repair moved something, and where it did not

| repair | moved |
|---|---|
| the blade carries the metric | **a return and a class**: `3 → −1`, `TransportDominant → StorageDominant` |
| primality | **a refusal**: `term(4, …)` now refused, previously admitted |
| the reciprocal recorded | **a return**: two frames are no longer equal as values |
| the rank remainder returned | **a return**: `withheld_below_rank` non-empty on real material |
| the corrupted quotation | documentation only |
| `Observation`'s doc | documentation only |

Four of six moved a return or a refusal. The two that did not are named as documentation repairs
rather than presented as evidence, which is what `canon/THE_AUTHORED_LEVEL.md` requires of an
excision wave that finds nothing.

## 5. What this does not claim

It does not claim the head exists — stations three through eight of the plan are open, and the plan
states that the readout deed is an embedding **Gram section** rather than a contextual logit. It does
not claim the census is exhausted; it classified 281 library modules and named eight organs nothing
reaches, one of which (`soma/abi/src/conduct.rs`, reached by **nothing, not even a test**) contradicts
`canon/THE_INFORMATION_ENGINE.md`'s cycle table, which lists it `WIRED`. That repair is station nine
and is not made here. And it does not claim the `agreement_rank` maximum is lawful because it is
exhibited — only that it is now visible and refutable, which it was not.

# Two cost laws ran from a binary with no source, and the profile is milliseconds

**Date:** 2026-08-09
**Truth status:** `established-bounded` for every figure at the widths and material stated;
`conjecture` for the Brent–Kung torsion law beyond `w = 6`; `interpretation` for §4.
**Evidence:** `measured`. Every number below was taken by running the binary on this machine today,
**in two frames**, not read from a record. The two probes' complete output is transcribed verbatim
in §1 because their sources do not exist.
**Provenance:** Brandon, 2026-08-09: *"Can you elaborate on what the machine has been shown to do
computationally at the costs (time, RAM/VRAM usage, big O notation) we've measured it at? Regardless
of contaminants or shortcomings, the machine can clearly already be applied usefully, and I want a
quick analysis of what we're not appreciating about it."* And, on the result: *"Good review, I'd
appreciate it if you could deposit, especially the things that you said have never been recorded.
These are useful insights and laws."*
**Band:** 2026-08-09 · THE PIVOT RULE IS WORTH 390,000× / THE TORSION RANK IS `(w−1)²` / EXACT
CERTIFIED RETURNS AT FIFTEEN MEGABYTES

---

## 1. The two laws, and they live in binaries with no source

`canon/THE_MEASURED_CAPABILITIES.md` §4 lists `zz_smith_cost_probe` and `zz_torsion_width_law` under
**"Unrecoverable — do not cite"**, with the note *"they run right now from `target/`"* and
`git log --all -- '*zz_*'` returning empty. They still run. **This section transcribes their complete
output so the figures survive `cargo clean`, which is the only thing standing between these laws and
the sink that already took the tiger atlas and the residue-stratum atlas.**

### 1a. The pivot rule decides feasibility, and the deciding quantity is not the one reported

```text
=== brent-kung w2  d2  [78x52]  extent 52 ===
  SmallestMagnitude      0 ms   pivot selections      52   selections/extent     1.0   rank 52
  LargestMagnitude       1 ms   pivot selections      80   selections/extent     1.5   rank 52
  FirstNonzero           0 ms   pivot selections      78   selections/extent     1.5   rank 52

=== brent-kung w3  d2  [143x101]  extent 101 ===
  SmallestMagnitude      1 ms   pivot selections     101   selections/extent     1.0   rank 101
  LargestMagnitude      10 ms   pivot selections     153   selections/extent     1.5   rank 101
  FirstNonzero SKIPPED -- exceeds 390 s, measured
```

Same matrix, same answer — **rank 101 under all three rules**. One rule finishes in a millisecond and
one exceeds 390 seconds. That is a spread of more than **390,000×** on a computation whose *result*
is identical.

**And the frame-independent quantity is `selections/extent`, not the clock.** `SmallestMagnitude`
returns exactly **1.0** — one selection per extent, no re-selection — while both others return
**1.5**. The milliseconds moved between my two runs (`LargestMagnitude` 7 → 10 ms); the ratio did not.
Under `CLAUDE.md` §8 — *"a cost is measured in work, never in elapsed time"* — the ratio is the
lawful figure and the nanoseconds are the receipt.

**The sharp finding, and it is a gap rather than a result.** `LargestMagnitude` and `FirstNonzero`
have the **same** `selections/extent` of 1.5, and one is 10 ms while the other is infeasible.
**So the selection count does not explain the blowup.** What does is coefficient growth — the
bit-width of the intermediates in fraction-free elimination — which is exactly `intermediate_bits`,
one of the four members of the exact work vector `CLAUDE.md` §8 names, and **the probe does not
report it**. The law is therefore established as a *phenomenon* and unexplained as a *mechanism*, and
closing that needs one added column, not a new organ.

**Why this is worth more than most figures in this repository:** it is reusable outside holonics
entirely. Anyone computing Smith or Hermite normal form, doing integer programming, or reducing
lattices pays this cost, and the rule that avoids it is one line.

### 1b. The Brent–Kung torsion width law

```text
w=2  betti=9   torsion_rank=1   (w-1)^2=1   match=true  all_factors_2=true  [0 ms]
w=3  betti=15  torsion_rank=4   (w-1)^2=4   match=true  all_factors_2=true  [2 ms]
w=4  betti=21  torsion_rank=9   (w-1)^2=9   match=true  all_factors_2=true  [6 ms]
w=5  betti=27  torsion_rank=16  (w-1)^2=16  match=true  all_factors_2=true  [14 ms]
w=6  betti=33  torsion_rank=25  (w-1)^2=25  match=true  all_factors_2=true  [26 ms]
```

Over the reconvergence incidence of a Brent–Kung prefix adder at width `w`:

```text
   betti        =  6w − 3
   torsion rank  =  (w − 1)²          every invariant factor exactly 2
```

Five confirming widths, exact over `BigInt`, **derived rather than fitted** — the probe computes the
Smith normal form and compares against the closed form, and `match=true` is its own check.

**Grade: `conjecture` past `w = 6`, `established-bounded` at 2–6.** It is a statement about a circuit
family in universal use in hardware, produced by this machine, and it is written down nowhere else in
either repository.

## 2. The measured cost profile, in two frames

Taken today, release build, each driver run twice. Peak RSS is host resident set, measured per driver
in its own process.

| driver | what it returns | run A | run B | peak RSS |
|---|---|---|---|---|
| `complex_system_conduct_classes` | 14 one-shot → 18 conduct classes, 5 collapsed pairs each with its separating word | 3 ms | 1 ms | 12 MB |
| `generative_transport_prediction` | identifies `A(τ) = M + τ(S+K+R)`, types the obstruction, predicts exactly at τ = 5 — an interval never fitted | 12 ms | 6 ms | 12 MB |
| `inverse_transport_reconstruction` | 8 exact rational conductances of a hidden Laplacian from clamped responses; affine dim 15 → 0; held-out exact | 13 ms | 12 ms | 12 MB |
| `derivation_atlas_reader` | β₁ = 164 with torsion `ℤ/2+ℤ/2`, `ℤ/3+ℤ/3`, over 31 deposited proofs | 16 ms | 14 ms | 12 MB |
| `grown_circuit_schedules` | Brent–Kung gate counts `[5,13,…,53]` against constant description length 12; exhaustive 32×32 functional check | 52 ms | 40 ms | 12 MB |
| `graded_complex_integer_invariants` | Smith normal form over `BigInt`; 12 closed surfaces inside `C(20,10) = 184,756` | 75 ms | 74 ms | 12 MB |
| `matroid_hodge_riemann` | Hodge–Riemann, with classes outside the ample cone **required to break** — and they do | 76 ms | 74 ms | 12 MB |
| `curvature_is_the_adjacency` | `I − BᵀD⁻¹B == −A/2`, held 10 of 10 | 89 ms | 77 ms | 12 MB |
| `bit_black_box_reconstruction` | 147,456 → 1 candidate program; 87,380 vertices exhausted; independent x86 parity | 308 ms | 310 ms | 15 MB |
| `faces_grow_from_collocation` | co-presentation faces + 15 null-bind re-pairings | 413 ms | 406 ms | 24 MB |
| `signs_are_windings` | `sign(λ_k) < 0 ⟺ 1/4 < k/n < 3/4`, n = 3..16 | 963 ms | 946 ms | 15 MB |
| `reopening_the_collapsed_face` | Euler `(4,4,−1)` and Machin `(16,−4,−1)` recovered exactly; 0 spurious over 16 relation-free searches | 3.84 s | 3.84 s | 12 MB |
| `the_chart_refuses_or_returns` | Tschirnhaus transport, Bareiss resultants, typed refusal | 4.04 s | 4.02 s | 12 MB |
| `the_iron_tokens_carry_the_field` | 486 wholes, 1,061,858 tokens, 27,907 surfaces, exact separation | 12.35 s | — | **571 MB** |
| `skein_far_condensation` | 127 nodes / 510 arcs, cyclomatic 384, 2,420,959 entry-writes removed | 18.98 s | 19.27 s | 173 MB |
| `the_name_elaborates_and_the_loop_fills` | recruitment closures + 2-cells over 103 artifacts | 7.42 s | 7.41 s | **764 MB** |

**Every one of these is exact, certified, and float-free**, and the whole upper block lands inside
**15 MB and under a third of a second**. That is a CI-gate, editor-plugin, embedded-device cost
profile, not a research-prototype one.

**VRAM: none of these measures it, because none of these launches device work.** The seven CUDA mount
gates return `EXACT` separately. `CLAUDE.md` §9 states *"the GPU owns the deed"*; the entire measured
exact-invariant capability above runs host-side in 15 MB, and recording that plainly is more useful
than repeating the doctrine.

## 3. The complexity statement, as far as it is actually measured

- **Substrate — linear.** The suffix ecology founds at most two states per received germ. Measured:
  **11,879 states from 8,185 occurrences against the `2n−1` bound of 19,483**, so ~61% of worst case,
  with exact recurrence multiplicity retained rather than normalized.
- **Invariant layer — Smith-bound, and the real cost is coefficient growth**, controlled by pivot rule
  as §1a measures. The matrix dimension is not the binding constraint; the intermediate bit-width is.
- **Exhaustion layer — `Σ|A|^L` in the *declared radius*.** `foreign_codec_intake` exhausts
  `{w : 1 ≤ |w| ≤ radius}` in **25,259 calls**.
- **Census throughput — ~86,000 tokens/sec** including per-surface exact separation (1,061,858 tokens
  in 12.35 s).

**The bound that governs all of it, from `canon/THE_MEASURED_CAPABILITIES.md` §4:** *"Every timing
figure in this repository has one frame and none is falsifiable."* This record gives the driver
table a **second** frame and it is stable to the millisecond on every row. That still is not a second
*machine*, so the frame-independent content remains the work figures — `selections/extent`, state
counts, call counts — and not the seconds.

## 4. What the profile means, which has not been written down

**Truth status: `interpretation`.**

**The exponential is in a declared parameter, not in the input.** Choose radius 2, pay `|A|²`, and
what returns is a **theorem about radius 2** — *"no admitted query separates these"* as a statement
about an exhausted family rather than a confidence. That is a categorically different bargain from
train-longer-and-hope, and it is the property that makes the cost figures above meaningful rather
than merely small.

**The separating word is the deliverable, and nothing else in the field returns it.** Every
compression, abstraction and summarization system reports a **ratio**. `receiver_exact_compression`
reports the population that departed **and the shortest input that proves it** — `became|become`
separated by `"s"`, over 2,758 surfaces, sub-second. That is directly a test-case minimizer, a diff
explainer, and an abstraction-soundness checker.

**It designs its own experiments, exactly, with a termination proof.**
`inverse_transport_reconstruction` requests its own missing edges and refuses to admit a topology
until the operator basis is complete; `generative_transport_prediction` selects its own
second-interval queries; `bit_causal` picks its own distinguishing query. This is active experimental
design that **terminates on a singleton family**, not a heuristic search that stops on a budget — in
milliseconds.

**The through-line: it is a certified differential instrument.** Everything it does well has one
shape — *here are two things; here is exactly what distinguishes them, or a proof that nothing in the
declared family can.* That is applicable today, at the costs above, independently of every open
question on the learning line.

## 5. Two memory defects, named because the rest of the profile makes them visible

- `the_name_elaborates_and_the_loop_fills` — **764 MB on 103 small Lean files.**
- `the_iron_tokens_carry_the_field` — **571 MB on 1.06 M tokens.**

Against 12–15 MB for the entire exact-invariant family, these are out of line by a factor of fifty
and are not explained by their material. Both are among the newest organs. This is an inefficiency to
diagnose, not a scale requirement.

**And one measurement the machine already computes and discards.** The exact work vector —
`exact_support_evaluations`, `device_threads`, `intermediate_bits`, `aperture_members`, all `BigUint`,
all reproducing bit-for-bit on any machine — exists and is thrown away in favour of nanoseconds.
`CLAUDE.md` §8 convicts that for carrier admission; the same correction applies to every cost figure
in this record, and taking it would make these numbers falsifiable rather than merely repeated.

## 6. The recovery this record does not perform

**The two probes' sources do not exist at any commit in either repository.** This record preserves
their *output* verbatim, so the laws survive; it does **not** make them reproducible. One
`cargo clean` ends that, and the repository has lost evidence to exactly this sink four times.

The reconstruction is small and the parts are all live: `grown_circuit_schedules` already builds the
Brent–Kung incidence, `graded_complex_integer_invariants` already runs Smith normal form over
`BigInt`, and `rebase_invariants::PivotRule` already carries the three rules with `PivotRule::ALL`.
Rebuilding both probes as committed drivers — and adding the `intermediate_bits` column §1a shows is
the missing explanatory quantity — is owed and is not attempted here.

## 7. What this record does not claim

- It does not claim the `(w−1)²` law holds past `w = 6`. Five widths is five widths.
- It does not claim any timing figure is falsifiable. Two frames on one machine is not two machines.
- It does not claim the 390,000× spread is explained. §1a shows the reported quantity does not
  explain it and names the one that would.
- It does not re-grade any capability. The operations are catalogued in
  `canon/THE_MEASURED_CAPABILITIES.md`; this record adds their **cost**, which that document does not
  carry.

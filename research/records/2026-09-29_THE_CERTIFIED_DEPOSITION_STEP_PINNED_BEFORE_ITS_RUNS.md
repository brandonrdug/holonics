# The certified deposition step, pinned before its runs

**Date.** September 29. **Issues.** #73, #63 (THE_REBUILD U6). **Grade.** [definition;
agent-inferred] for the pins; [measured] for the development reads (§3), which used development
seeds, the text's choosing role and the standing cut's first 128 windows only.

**Occasion.** The [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md)
names three failures this loop answers:
- failure 5: deposition's gain was never certified (`γ_U = 1` on a covector that sums every station
  and re-entry, and the source port's entries went 1, 6, 26, 316 at `K = 4`);
- failure 8: the prox step's reach cap (the copy stopped at 234 of 256);
- failure 9: a refusal answered with a larger limit.

Its lesson 6 is the law: "A deposition step is certified. It reads a bound on the covector
reaching its locus, over every station and re-entry, and sets its step from it; the energy bound is
enforced at the commit, not only recorded."

## 1. What is built

- `2dcbd5e2` retires the native text path's seams: the count-priced founding, first-arrival
  placement, the founded `E_0` and the keyed latent's pseudo-random signs.
- `0ab398af` builds the certified step.
  - **The step.** Each linear locus (`E_g`, `R`, `W_c`) prepares its unit step
    `D = Σ_t w g_t (X̂ f_t)ᵀ` through its solved chart (`NormalLaw::prepare`). It reads the
    alignment `a = Σ_t w⟨g_t, D f_t⟩` (checked; `a < 0` is refused), the feature moves
    `b = Σ_t w|D f_t|²` and the covector scale `c = max_t |w g_t|_∞`.
  - **The curvature.** The constitution reads each locus's curvature `C = B·½·κ²·b`. The gain `κ²`
    runs from the locus's output to the station logits over the deposit's reach (stations,
    re-entries, phases), the receiving map's Schur bound, the admittances and the contrast ports'
    per-tick growth `(1 + ω)²`.
  - **The certificate.** The step is the largest dyadic `η = 2^k` with `ηC ≤ a` and `ηc ≤ 1`. It is
    halved until every locus's certificate holds with the gains read at the end of every ray
    (`holon::deposition::CertifiedStep`).
  - **The energy bound.** The storage a deposit changes is certified `Q_(k+1) ⪯ (1 + ε_k) Q_k` by
    inertia before publication, or the deposit is refused (`UncertifiedStorage`). A linear step
    through a pumped resonator is refused (`UncertifiedGain`). A refinement's committed energy bound
    is read at its commit (`RefinementBalance::energy_bound`).
  - **Lean.** `Holon/Deposition` §6 and `HNN/Normal` §7.
- This commit adds a readout only: the exposure's constitution curve carries each deposit's
  certified steps and storage growth.

**No part of the step reads a codec.** It reads `a`, `C`, `c`, the reach (stations, re-entries,
phases), the admittances, the Schur norms of the receiving map and the contrast ports, and the
element lattice's grain. None is an alphabet, a chart, a terrain or a byte, so the same
`Constitution::deposited` runs on the moiré, the copy and text. The computational object is the
helical pair interaction:
- the unit step is carried through the pair contacts' transit and the rings' elements (the pair);
- the station readout is faces and placement;
- the words' re-entries and stations are the tube.

The helix (the receiving ring's clock), the cell holonomy and the tower thread (the carry chain)
stay attached through the field's complex.

## 2. The pins

**The field and refinement** are the native generation pins'
([record](2026-09-29_NATIVE_GENERATION_PINNED_BEFORE_ITS_RUNS.md) §2):
- three rings of `d = 32` in a chain, ring 0 the source and receiver;
- `K = 2` words of `w = 1` tick unless stated, with `m = 8` stations on the terrains and 32 on text;
- a batch of 16.

The constitution is `Constitution::initial` at the factor step `η_x = ½`; every normal-law step is
certified. Nothing is authored for a terrain.

**Acceptance 1: the moiré at `K = 4` and `K = 8`.** The runs are `hnn_prediction -- moire 4` and
`-- moire 8`: the pinned moiré (`Draw::new(2_026_092_903)`), 512 training windows at offsets from
`Draw::new(2_026_092_901)`, evaluated on its 6 distinct windows. Those windows are its training
windows, so the evaluation is a stability reading, not transfer. It **passes** at each `K` when all
of the following hold:
- the balances, pairings and commits each close on every refinement, and every unreached locus is
  unchanged at every deposit;
- the committed energy bound holds at every refinement's commit;
- every learned map's largest absolute entry over the run (`E`, `R`, each `W_c`, and the factor
  families `c`, `b`, `F`, `f`, the slices and `q`) is at most `8 = 2³`;
- training ends within its 540,000 ms deadline and 20 GB cap.

[agent-inferred] The bound `2³` is three binary orders above the founding's unit scale. Every
development read in §3 stayed below `2`, and the divergence it guards against passed 316. The exact
sections, the stations, the certified steps by locus and the storage growth are reported beside.
`hnn_prediction -- divergence`, the development configuration that diverged under `γ_U = 1`
(`d = 16`, `K = 4`, batch 8, 128 windows, development seeds), is read again and reported beside.

**Acceptance 2: the copy and the reach cap.** The run is `hnn_prediction -- copy` at the native
pins: `K = 2`, 1,536 training requests from `Draw::new(2_026_092_901)` and 256 evaluated from
`Draw::new(2_026_092_902)`. The checks are those of acceptance 1. The exact sections are reported
against the `γ_U = 1` run's 234 of 256. The reach cap counts as removed only when all 256 sections
are exact. Otherwise its cause is named by measurement: each locus's certified steps against the
retired `γ_U = 1 = 2⁰`. The step is not tuned around the cap.

**Acceptance 3: the standing cut's exposure.** The run is `hnn_exposure -- cut-file
.local/cuts/u6-encoding-probe.bin cells all`:
- the declared residue chart on the host, over the whole cut of 6,148 cells (sha256
  `39621d52…7fbc`);
- held out 4,096..6,148 from the manifest.

**Parity** is the held-out code at the field's face in the grain cell `5459 + 13/16`, the residue
chart's attribution run at `γ_U = 1`
([record](2026-09-29_THE_PASSAGES_OWN_TRANSPORTS_THE_MOIRE_FOUNDS_ITS_RANKS_WITH_NO_TRANSPORT_DECLARED_AND_TEXT_CODES_BELOW_THE_CELL_CHART.md)
§3). Otherwise the named change is reported: the difference in grain cells, with the certified
steps by locus and the storage growth. The exposure's own checks (tick and word balances) are
reported too. The cut is private, so the report gives counts, bits and hashes only.

**Acceptance 4: one step on every field.** The same deposit path runs unchanged on text:
`hnn_prediction -- develop text .local/cuts/curated-u6-passage-cut.bin 385` (sha256
`c6e51a35…0816`), one pass over the choosing role's 385 pairs. It trains only: no generation and no
validation read. It **passes** when the checks and the entry bound of acceptance 1 hold within the
deadline. No text is generated in this loop and no consumer is added.

**Time and memory.** Each harness stops training at 540,000 ms and at a resident set of 20 GB, and
each process is bounded externally at 600,000 ms. A run that reaches a bound is reported
incomplete and is **not rerun with a larger bound**. The projections, from §3:

| Run | Development read | Projection |
|---|---|---|
| `moire 4` | 64 windows, 18,920 ms | 512 windows: about 152,000 ms; evaluation below 1,000 ms |
| `moire 8` | 64 windows, 34,433 ms | about 276,000 ms |
| `copy` | 128 requests, 30,167 ms; 32 evaluations, 1,870 ms | about 362,000 ms and 15,000 ms |
| `develop text` | 32 pairs, 8,902 ms | 385 pairs: about 107,000 ms |
| exposure | 128 windows, 8,173 ms | 3,074 windows: 196,000–430,000 ms (the founded chart's run took 427,589 ms) |
| `divergence` | 128 windows, 17,276 ms | the same |

Every peak resident set is projected below 1,000,000,000 bytes (the development peaks are 94,457,856
to 478,285,824 bytes). The GPU suite runs after the host runs, alone on an idle card under
`flock .local/gpu.lock`.

## 3. The development reads (before the pins)

Each read closed every balance, pairing and commit, kept every unreached locus unchanged, and held
the committed energy bound at every refinement's commit. `k` is the certified step's exponent (the
step `2^k`); `∏` is the certified storage growth's product since the founding.

| Read | Training | Exact | `k` at `E` / `R` / elements | Largest entry | `ε_k` / `∏` |
|---|---|---|---|---|---|
| divergence (`d = 16`, `K = 4`, batch 8) | 128 | 6 of 6 | −15..−14 / −1..0 / −12..−9 | `R` 2071/1024 | 0..64 / 31928901468750 |
| moiré, `d = 32`, `K = 4` | 64 | 4 of 6 | −16..−15 / −1..0 / −12..−11 | `R` 2547/2048 | 0..4 / 45 = 3²·5 |
| moiré, `d = 32`, `K = 8` | 64 | 6 of 6 | −17..−16 / −2..0 / −13..−10 | `c₀` 1123/1024 | 0..8 / 81 = 3⁴ |
| copy, `d = 32`, `K = 2` | 128 | 22 of 32 | −14 / 0 / −11..−10 | `R` 3769/2048 | 0..2 / 432 = 2⁴·3³ |
| text, choosing pairs | 32 | (no evaluation) | −15 / 0 / −10 | `c₀` 2709/2048 | 0..128 / 129 = 3·43 |
| exposure, the cut's first 128 windows | 128 | (no held-out) | not read | not read | not read |

The storage product on the divergence configuration factors as
`31928901468750 = 2·3¹⁰·5⁶·11³·13`. A contact's `C = c cᵀ` is rank-deficient, and the factor
families' declared step `η_x` grows it relatively in its weak directions, so single deposits reach
`ε_k = 64` and `128`. The bound holds but is loose. The factor families' step is not certified
here (owed in #62).

The certified step never exceeded `2⁰` at the receiving map: the covector scale `c` bounds it
there. That is why acceptance 2 asks whether the reach cap moves.

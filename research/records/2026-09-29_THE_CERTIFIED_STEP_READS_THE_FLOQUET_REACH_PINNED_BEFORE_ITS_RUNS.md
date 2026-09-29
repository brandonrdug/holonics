# The certified step reads the Floquet reach, pinned before its runs

**Date.** September 29. **Issues.** #73, #63 (THE_REBUILD U6). **Grade.** [definition;
agent-inferred] for the law and the pins; [measured] for the development reads (§3), which read
development seeds only.

**Occasion.** The [parametron's re-derivation](2026-09-29_THE_PARAMETRON_RE_DERIVED_THE_PUMP_READS_RELATIVE_PHASE_AND_THE_FLOQUET_CERTIFICATE_DECIDES_THE_LOCK.md)
§1.8 stated the consumer equation for the constitution's certified step and left the step through
a pumped resonator refused (`UncertifiedGain`) until `hnn::constitution` read
`FloquetBound::reach`. This loop builds that reading in its owner.

The [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md)
names what this loop could repeat:
- **Failure 5, an uncertified step.** A step through a pumped ring is certified only by a bound
  read from its own monodromy by inertia, composed into every gain by proved statements (§1); the
  ring's own gains, whose ray moves the monodromy, are held, not stepped on a certificate read at
  the ray's start; the storage certificate stays enforced at every commit. The one composition not
  certified here (the driven ring's loop within a span) is named in the owner's scope and in #62.
- **Failure 9, a refusal answered with a larger limit.** No limit moves: not `ηc ≤ 1`, the storage
  search, the entry bound `8`, the joint term or any run's bound. The refusal is replaced by a law
  (the reach), and it stays where that law has no certificate. Each pinned run runs once.
- **Lesson 3, a located cause repaired in its owner.** The refusal stood in `hnn::constitution`
  and is repaired there, with the composition in `holon::deposition` and the Lean in
  `HNN/Floquet` and `Holon/Deposition` §10. The same law repairs a second located gap in the same
  owner: an unpumped resonator with a signed stiffness was read as passive; it is now read by its
  reach like a pumped one.
- **Failure 7, bits read as progress; failure 6, seen as unseen.** No code length is this loop's
  acceptance; the pumped runs' evaluations are a reading beside the certificate, on copy requests
  at a seed no training read.

## 1. The law (`7c3e9393`)

`hnn::constitution`'s module header states it whole ("The pumped medium's reach").
- **Certified passive** is an unpumped resonator with `K ⪰ 0` by inertia (`C, D ⪰ 0` by
  declaration). Any other is read by its Floquet monodromy on the exact law, decided at its
  resonator lattice's grain `2^(−g)` (`Floquet::decide`) and bounded (`Floquet::bound`,
  `FloquetBound::reach`): `reach_r(s) = (γ_hi/γ_lo) max_o ρ^(2m_o) (max_t σ_t²)^(s − T m_o)`.
- **The metric is attained by any means**: a ladder of growths `ρ₀(1 + 2^k)`, `|k| ≤ g`, above
  the decided `ρ₀`, each attained by the exact Stein solve and certified, climbed from `k = 0`
  toward the least reach at the longest span; each span's reach is the least of the certified
  bounds'. [measured, development] The decided growth's own metric is ill-conditioned: on the
  chain fixture's edge rings `γ_hi/γ_lo = 26869760/247`, between `2^16` and `2^17`, and three such
  rings gave a span factor at six ticks of `1926487452681573810688`, between `2^70` and `2^71`; the
  ladder gives `12753186460568346013/1099511627776`, between `2^23` and `2^24`.
- **The span factor** `F(s) = ∏_r max_(s′ ≤ s) reach_r(s′)` (`holon::deposition::span_factors`)
  multiplies every tick term of every gain but the readout's, and each station's squared re-entry
  sum at its longest span. With every resonator certified passive there is no factor and every
  gain is read exactly as before.
- **Held**: a reach-read ring's own gain families (always for a pumped ring; for a signed stiffness
  unless the readout is zero along the joint ray), named in `DepositReading::pumped`.
- **Refused** (`UncertifiedGain`, with its reason) only where the decided certificate is.

**Lean** (`#print axioms`: propext, Classical.choice, Quot.sound only):
`HNN/Floquet.{partial_period_le_pow, floquet_span_reach}`; `Holon/Deposition` §10:
`span_transport_compose`, `station_tick_gain`, `entry_span_gain`, `runningMax`, `le_runningMax`,
`runningMax_mono`, `pumped_span_factor`.

The computational object is the helical pair interaction. Of the winding guide's six objects:
- **the helix**: the pump's clock, its period `T` and the phase a span starts at;
- **the cell holonomy**: the monodromy of one pump period and its certified growth;
- **faces and placement**: the readout's gain, where the reach enters every station's term.

The pair (the contacts' channels, whose gains read the same factor), the tube (the span of ticks
between an output and a station) and the tower thread (the dyadic grains of the decision and the
ladder) stay attached. Nothing reads a codec, an alphabet or a terrain.

## 2. The pins

Every run below runs once, on the host, in release, sequentially, at the build `7c3e9393`. A run
starts only when no other measured run holds the host's cores (no other `hnn_*` example process);
the host is shared with another worker's runs.

**Acceptance 1: every check on every run.** The balances, pairings and commits close on every
refinement; every unreached locus is unchanged at every deposit; the committed energy bound holds
at every refinement's commit (on the pumped runs read with the span factor at the refinement's
span, `F(K·w)`); every learned map's largest entry stays at most `8` on the prediction fields; the
fold's lobes hold (no class changes but by a proposal the lock takes); on the standing cut the tick
and word balances close.

**Acceptance 2: the pumped receiving ring.** `hnn_prediction -- pumped below` and `-- pumped past`:
the terrains' refinement (`K = 2`, `w = 1`, `|A| = 5`, batch 16) on rings of period `d = 4` with
`m = 4` stations, the receiving ring's resonator `C = I`, `K = I`, `D = 0` under a standing pump
at `p = 1/4` (`below`) and `p = 1` (`past`) its bifurcation `p = ½`; 256 copy requests trained
(`TRAIN_SEED`), 64 evaluated (`EVALUATE_SEED`). It passes when:
- the ring is decided passive below and growing past, by its Floquet monodromy;
- every deposit is certified and taken through the pumped ring: `DepositReading::pumped` read at
  every deposit, every step holding its certificate, no deposit refused (at the parent build
  `874e4c67` every such deposit was refused, `UncertifiedGain`, by source and by its tests);
- every learned map stays within the entry bound `8`.

It reports the steps (their exponents by locus and family), the families held and the reach
readings (each ring's decision, its bounds and its reach over the spans, the span factor).

**Acceptance 3: the copy, the moiré and text.** `hnn_prediction -- copy`, `-- moire 4`,
`-- moire 8`, `-- develop text .local/cuts/curated-u6-passage-cut.bin 385`. No resonator is declared
on these fields, so the law reads no factor and each is expected to read exactly as the standing's
fold's receipt: the copy 256 of 256, the moiré 6 of 6 at both `K`, text 4 of 7 families moving and
the lock's flips (22 of 24 proposals). A difference is named.

**Acceptance 4: the standing cut.** `hnn_exposure -- cut-file .local/cuts/u6-encoding-probe.bin
cells all`, against `5470 + 1/16 + ε`, in counts, bits and hashes only.

**Acceptance 5: projections.** Each process is bounded externally at its projection's upper end
(`timeout`); each harness keeps its own guards. A run that reaches its bound is reported incomplete
with its partial evidence and is not rerun with a larger bound.

| Run | Read (§3, or the fold's receipt) | Projection | Bound |
|---|---|---|---|
| `pumped below` | 32 requests, 4,710 ms training | 30,000–120,000 ms | 120,000 ms |
| `pumped past` | 32 requests, 6,908 ms training | 45,000–180,000 ms | 180,000 ms |
| `copy` | the fold's 315,787 ms | 280,000–420,000 ms | 420,000 ms |
| `moire 4` | the fold's 152,458 ms | 130,000–220,000 ms | 220,000 ms |
| `moire 8` | the fold's 233,186 ms | 200,000–420,000 ms | 420,000 ms |
| `develop text … 385` | the fold's 201,372 ms | 180,000–360,000 ms | 360,000 ms |
| exposure | the fold's 430,521 ms | 400,000–780,000 ms | 780,000 ms |

[agent-inferred] The pumped runs scale the development read's training by the deposits (16 against
2), and allow the host's other worker at the upper end. Every peak resident set is projected below
1,500,000,000 bytes (the pumped development peaks are 23,203,840 and 24,211,456 bytes; the fold's
largest 813,137,920). The gates ran at the build (its commit message); the GPU suite, alone on the
card under the lock, took 135,580 ms beside another worker's host run (the fold's receipt read
43 s idle).

## 3. The development reads (before the pins)

Development seeds 11 and 12, 32 requests trained and 8 evaluated, `d = 4`, `m = 4`:

| Read | Decision | Reach at spans 0, 1, 2 | Certified steps `2^k` | Held (2 deposits) | Time, peak |
|---|---|---|---|---|---|
| `p = 1/4` | passive, `ρ₀ = 1`; 10 bounds read | `5097126651946060315/2^62`, `10143835344963361041/2^62`, `10223238841239700827/2^62` | `R` 0; `W_c,0` −5; `E` −9; the factor families −12 to −6 | 3 | 4,710 ms, 23,203,840 bytes |
| `p = 1` | growing, spectral radius in `[583/256, 73/32]`; 5 bounds read | `9/8`, `6053908215999139187/2^58`, `13199522076780695409/2^56` | `R` 0; `W_c,0` −10; `E` −15; the factor families −17 to −11 | 3 | 6,908 ms, 22,618,112 bytes |

Both reads closed every balance, pairing and commit (32 of 32), kept every unreached locus
unchanged, held the committed energy bound read with the span factor at 32 of 32 commits, and took
both deposits through the pumped ring. Past the bifurcation the reach at the refinement's span is
larger by more than `2^6` and less than `2^7`, and every certified step but the receiving map's
(whose gain is one) is smaller by `2^5` to `2^6`. The `p = 1/4` read ran before the harness read the
reach once a deposit (it read it twice), so its time is the longer of the two readings' cost.

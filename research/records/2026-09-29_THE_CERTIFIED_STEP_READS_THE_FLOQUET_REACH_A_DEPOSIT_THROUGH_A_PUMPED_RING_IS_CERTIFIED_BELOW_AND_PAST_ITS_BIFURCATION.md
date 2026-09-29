# The certified step reads the Floquet reach: a deposit through a pumped ring is certified below and past its bifurcation

**Date.** September 29. **Issues.** #73, #63 (THE_REBUILD U6). **Grade.** [measured] for the runs
(§3), each run once under the [pins](2026-09-29_THE_CERTIFIED_STEP_READS_THE_FLOQUET_REACH_PINNED_BEFORE_ITS_RUNS.md)
(`d343c817`) at the build `7c3e9393`; [proved-derived; formal-checked] for the Lean statements (§2);
[agent-inferred] for the choices named as such.

## 1. The lessons it answers

The [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **Failure 5, an uncertified step.** Every step through the pumped ring read a bound decided by
  inertia on the ring's own monodromy, composed into its gain by proved statements; the ring's own
  gain families, whose ray moves the monodromy, were held wherever they reached a deposit (45 family
  steps on each pumped run), never stepped on a certificate read at the ray's start; the storage
  certificate held at every commit (product 1 on every prediction run, every growth certified on
  the exposure). The composition this loop does not certify, the
  driven ring's loop within a span, is named in the owner's scope and in #62 (§6).
- **Failure 9, a larger limit.** No limit moved: not `ηc ≤ 1`, the storage search, the entry bound
  `8`, the joint term or any run's bound. Each pinned run ran once within its bound; the exposure
  waited for another worker's run to leave the host, as the pins declared, and was not rerun.
- **Lesson 3, a located cause repaired in its owner.** The refusal stood in `hnn::constitution` and
  is replaced there by the law; a second gap in the same owner (an unpumped resonator with a signed
  stiffness read as passive) is closed by the same law.
- **Failures 6 and 7.** The pumped runs' evaluations read copy requests at a seed no training read,
  and are reported beside the certificate, not as its acceptance; no code length is an acceptance.

## 2. The law and its Lean

The pins' §1 and the owner's module header ("The pumped medium's reach") state it. In short: a
resonator not certified passive is read by its Floquet monodromy, decided and bounded at its
lattice's grain on a ladder of certified growths; the medium's span factor
`F(s) = ∏_r max_(s′ ≤ s) reach_r(s′)` multiplies every tick term of every gain but the readout's and
each station's squared re-entry sum at its longest span; the ring's own gain families are held.

**The composition law.** The consumer equation reads the span's energy transport as the ring's
reach composed with the medium's ticks. Lean, `#print axioms` propext, Classical.choice and
Quot.sound only:
- `HNN/Floquet.floquet_span_reach`: a span from any pump phase, partial period, `m` periods and
  partial period, `E_Q(Post Mᵐ Pre x) ≤ (γ_hi/γ_lo) σ_post ρ^(2m) σ_pre E_Q(x)`;
  `partial_period_le_pow`: a partial period's product at most the largest tick's power;
- `Holon/Deposition` §10: `span_transport_compose` (`‖Ψ(Λv)‖² ≤ b a ‖v‖²`), `station_tick_gain`
  (`Σ_j ‖Σ_τ Φ_(jτ) δ_τ‖² ≤ (Σ_j Σ_τ G_(jτ)) Σ_τ ‖δ_τ‖²`, the gain `κ²` as the sum of the span gains
  by Cauchy–Schwarz over the ticks), `entry_span_gain` (one injection's re-entries at the longest
  span's factor), `runningMax`, `le_runningMax`, `runningMax_mono`, `pumped_span_factor`.

`station_tick_gain` also states the composition over a word's stations and re-entries that the
tightened certificate's #62 item 3 left open, given each span's gain.

## 3. The runs

Each process ran once, on the host, in release, sequentially, within its bound, each started when
no other measured run held the host. The cuts' sha256 are the fold's (`c6e51a35…0816`,
`39621d52…7fbc`).

**Acceptance 1 held on every run.** Every balance, pairing and commit closed; every unreached locus
was unchanged at every deposit; the committed energy bound held at every refinement's commit (on
the pumped runs read with `F(2)`); every learned map's largest entry stayed at most `8` (the
largest, the copy's `R`, `7977/1024`); the fold's lobe law ran at every deposit (its readings in
the tables); on the standing cut 9,222 tick balances and 3,074 word balances closed.

**Acceptance 2: the pumped receiving ring — passes.** The receiving ring's resonator `C = I`,
`K = I`, `D = 0` under a standing pump; `d = 4`, `m = 4`, `K = 2`, `w = 1`, 256 copy requests
trained in 16 deposits, 64 evaluated. At the parent build `874e4c67` every one of these deposits was
refused (`UncertifiedGain`: the certified step refused whenever any resonator was pumped; by source
and by its tests).

| Reading | `p = 1/4` (below) | `p = 1` (past) |
|---|---|---|
| Floquet decision | passive, `ρ₀ = 1` | growing, spectral radius in `[583/256, 73/32]` |
| bounds read on the ladder | 10 | 5 |
| the bound the longest span read: `ρ`, `σ²`, `γ_lo`, `γ_hi` | `257/256`, `401/512`, `263/128`, `287/64` | `365/128`, `333/64`, `257/256`, `89/32` |
| reach at spans 0, 1, 2 | `5097126651946060315/2^62`, `10143835344963361041/2^62`, `10223238841239700827/2^62` | `9/8`, `6053908215999139187/2^58`, `13199522076780695409/2^56` |
| deposits certified through the ring and taken | **16 of 16** (144 steps) | **16 of 16** (151 steps) |
| own gain families held | 45 | 45 |
| certified steps `2^k`: `R` / `W_c,0` / `E` | `0` / `−7..−5` / `−10..−9` | `0` / `−13..−11` / `−16..−15` |
| factor families: `f₀` / slices₀ / `q₀` / `q₁` / channel `c`, `b`, `F` | `−7..−6` / `−10..−9` / `−11..−7` / `−16..−9` / `−13..−12`, `−10..−9`, `−10..−9` | `−13..−12` / `−15..−14` / `−12` / `−18..−15` / `−19..−17`, `−15..−14`, `−15..−14` |
| families whose entries moved | `E₀` 15, `R₀` 16, `W_c,0` 15, `f₀` 13 of 16 | `E₀` 15, `R₀` 16 of 16 |
| largest `R`, `W_c,0`, `E` | `771/128`, `11/256`, `1069479/2097152` | `397/64`, `0`, `524439/1048576` |
| the fold | crossings at 11 of 16 deposits (53 slices); 15 halved, 7 dropped; 11 proposals (15 half-turns), 0 taken | nothing offered |
| training code, 1,024 stations | `1950 + 14/16 + ε` | `1972 + 5/16 + ε` |
| evaluation, 64 held-out requests | 43 exact, 209 of 256 stations, 59 released at width zero | 39 exact, 188 of 256 stations, 53 released |
| the marginals on the same stations | static 63, per-station 54 of 256 | the same |
| wall, peak resident | 13,779 ms, 22,863,872 bytes | 23,868 ms, 22,745,088 bytes |

- The ring is decided passive below and growing past, as pinned.
- The reach at the refinement's span past the bifurcation is larger than below by more than `2^6`
  and less than `2^7`, and every certified step but the receiving map's (whose gain is one) is
  smaller by `2^5` to `2^6`.
- Past the bifurcation the step still moved `E` and `R` at 15 and 16 of 16 deposits; no factor
  family's entries moved a lattice unit.
- Both runs finished below their projections' lower ends (30,000 and 45,000 ms): the development
  reads' deposits cost more than the pinned ones'.

**Acceptance 3: the copy, the moiré and text — unchanged.** No resonator is declared on these
fields, and each read exactly as the standing's fold's receipt:

| Run | Exact | The fold | Moved | Largest `R`, `W_c` | Wall, peak |
|---|---|---|---|---|---|
| copy | **256 of 256** (2,048 of 2,048 stations) | offered at 95 of 96 (1,359 slices); 88 halved, 102 dropped; 95 proposals (409 half-turns), 0 taken | `f₀` 93 of 96 | `7977/1024`, `35/512` | 319,525 ms, 403,505,152 bytes |
| moiré `K = 4` | **6 of 6** (48 of 48) | offered at 31 of 32 (1,313 slices); 18 halved, 70 dropped; 31 proposals (414 half-turns), 0 taken | `f₀` 23, `f₁` 19 of 32 | `6815/2048`, `25/2048` | 154,763 ms, 487,514,112 bytes |
| moiré `K = 8` | **6 of 6** (48 of 48) | offered at 25 of 32 (25 slices); 9 halved, 16 dropped; no proposal | none | `2113/1024`, `9/1024` | 236,636 ms, 557,223,936 bytes |
| text, 385 choosing pairs | (training only) | offered at 24 of 25 (1,115 slices); 45 halved, 3 dropped; **24 proposals (808 half-turns), 22 taken (770)** | **4 of 7**: `f₀` 23, slices₀ 6, `q₀` 22, `q₁` 22 of 25 | `2759/4096`; `q₀` `5/2048`, `q₁` `15/4096` | 207,958 ms, 789,491,712 bytes |

Text's training code is `47115 + 12/16 + ε`, the fold's. Every run finished inside its projection.

**Acceptance 4: the standing cut — unchanged.** The residue chart on the host, 3,074 windows,
complete; campaign 1's field declares no resonator:
- held out, the field's face: **`5470 + 1/16 + ε`**, the fold's; the tree alone `5476 + 3/16 + ε`;
  the field's part `−7 + 14/16 + ε`;
- development, the field's face `13068 + 5/16 + ε`; `Kt` `19993 + 6/16 + ε`;
- 6 aeon boundaries and 4 key locations; the storage growth `ε_k` from 0 to `1/4`, every growth
  certified at its commit.

Every reading of the exposure's output is identical to the fold's run but its times.

## 4. Time and memory

| Run | Measured | Projection | Peak resident bytes |
|---|---|---|---|
| `pumped below` | 13,779 ms | 30,000–120,000 ms | 22,863,872 |
| `pumped past` | 23,868 ms | 45,000–180,000 ms | 22,745,088 |
| `copy` | 319,525 ms | 280,000–420,000 ms | 403,505,152 |
| `moire 4` | 154,763 ms | 130,000–220,000 ms | 487,514,112 |
| `moire 8` | 236,636 ms | 200,000–420,000 ms | 557,223,936 |
| `develop text … 385` | 207,958 ms | 180,000–360,000 ms | 789,491,712 |
| exposure | 451,130 ms | 400,000–780,000 ms | 359,862,272 |

No run reached its bound. Every run is complete.

## 5. What the measurement located [agent-inferred]

- **The reach costs the step what the ring's growth costs.** Below the bifurcation the reach at the
  refinement's two ticks lies between 2 and 3, read at the ladder's lowest rung (`ρ = 257/256`,
  `k = −8`); past it the ring's multiplier is between 2 and 3 a tick (its bound read at
  `ρ = 365/128`, `k = −2`), the reach at two ticks lies between `2^7` and `2^8`, and the steps
  shrink by `2^5` to `2^6`. Over a longer span it compounds as `ρ^(2s)`: a ring past its
  bifurcation shrinks every step through it geometrically in the refinement's span. That is the
  certificate reading the growth it must bound.
- **The decided growth's metric is the wrong exterior attainment for the consumer.** The Stein
  metric at the decided growth is ill-conditioned wherever a multiplier lies on or near its circle
  (the chain fixture's edge rings: `γ_hi/γ_lo` between `2^16` and `2^17`, and their best rung
  `k = 0`). The certificate trusts any metric, so the choice is free; the ladder makes it from the
  consumer's own reading at the longest span.
- **The pump's own gains cannot learn yet.** Every deposit held the ring's own families (45 of 45).
  Their learning needs the reach along their ray (§6).

## 6. Owed in #62

"The certified step reads the Floquet reach" (September 29):
1. **The driven ring's loop.** The consumer equation factors a span's transport through the pumped
   ring's undriven ticks (its port terminated) and the medium's passive and contrast ticks. The
   supply-rate certificate of the driven ring, `E_G(x′) ≤ σ_t² E_G(x) + supply(e, s′)` through its
   loaded port, which would discharge that factorization through the field's return into the ring
   within a span, is owed (Lean beside `HNN/Floquet` and `Holon/Deposition` §10).
2. **The reach along a ring's own gain ray.** A certificate over the tube of monodromies
   `M_T(η)`, `η ∈ [0, η_step]` (one metric certified along the ray by an enclosure of the ticks'
   solves), and the pumped storage's growth at the commit (its pumped stiffness is indefinite), so
   that a pumped ring's own gains can step instead of being held.
3. **The per-tick growth of the executed ticks.** `station_tick_gain` composes the span gains into
   `κ²`; the statement that each span's gain through the executed word is `(1 + ω)^(2(s − 1))` of the
   medium times the rings' reach is the word-level composition, still owed.
4. **A modulated pump.** A schedule modulated by the crossing cells (`PumpSchedule::modulated`)
   makes the monodromy the passage's; its reach per passage is owed where a consumer reads it (the
   receiving bank's superposed passage).
5. **The executed chart's monodromy.** The reach reads the exact law's ticks; the lattice word's
   deviation from it is the carried passage's owed bound (the parametron's record §7).

## 7. Verdict

- **Every check holds on every run** (acceptance 1).
- **A deposit through a pumped receiving ring is certified and taken, below and past its
  bifurcation** (acceptance 2 passes): 16 of 16 deposits on each run, where the parent build
  refused every one; the ring decided passive below and growing past; every learned map within the
  entry bound (the largest `R`, `397/64`); the steps shrink past the bifurcation as its reach grows
  (`2^5` to `2^6` at two ticks), and the ring's own gains are held.
- **The copy (256 of 256), the moiré (6 of 6 at `K = 4` and `K = 8`) and text (4 of 7 families, 22
  of 24 proposals taken) read exactly as the fold's receipt** (acceptance 3), and the standing cut's
  held-out code is `5470 + 1/16 + ε`, every reading identical (acceptance 4): with no resonator
  declared the law reads no factor.
- **The composition is proved in Lean** given the consumer equation's factorization; the driven
  ring's loop that would discharge the factorization is owed (§6, item 1).

## 8. Gates

At the build `7c3e9393`:
- `cargo check --workspace --all-targets` is clean;
- `cargo test -p holonics --lib`: 943 passed, among them the laws' tests:
  `the_span_factor_is_the_product_of_running_maxima`, `the_gains_read_the_span_factor_term_by_term`,
  `a_deposit_through_a_pumped_receiving_ring_is_certified_below_and_past_its_bifurcation`,
  `a_pumped_rings_own_gain_is_held_and_named`, and the refinement's balance through every ring
  pumped (`the_refinement_balance_closes_with_the_injection_the_pump_and_the_commit`, now certified
  and taken, the energy bound read with the span factor);
- the GPU suite, alone on the card under the lock: 32 passed (135,580 ms beside another worker's
  host run);
- `bash tools/lean_check.sh Holonics HolonicsResearch`: 10,248 jobs built, no `sorry`.

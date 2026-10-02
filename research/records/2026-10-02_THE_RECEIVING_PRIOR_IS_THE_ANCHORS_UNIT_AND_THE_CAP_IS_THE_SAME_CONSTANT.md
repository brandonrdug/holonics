# The receiving prior is the anchors' unit, and the cap is the same constant

October 2. Refs #73, #62, #63. Lean `HNN/ReceivingPrior`; the exterior replay
`research/notebook/hnn_design/receiver_prior_scale.py`;
[receipts](2026-10-02_THE_RECEIVING_PRIOR_receipts/).

The receiving map's normal law opens at `R₀ = 0` with the prior Gram `H₀ = I`
([the opening record](2026-10-02_THE_RECEIVING_MAP_OPENS_AT_ZERO_AND_THE_SOURCE_MAP_REACHES_THE_CONTACT_ONLY_AS_MOTION.md)
§1 left `H₀` declared). This record asks whether `H₀ = I` is derived or can be released. The
answer has three parts: its shape is derived, its scale is the anchors' amplitude unit, and on
the first 2,192 readings of campaign 1 the readings' own code puts that scale at `I` within two
binary orders above and penalizes every scale below it.

## 1. Where `H₀` acts

`NormalLaw::with_prior` opens `H = H₀ = I`, and each deposit adds `Σ w f fᵀ`
(`NormalLaw::prepare`). The prior enters three places:

- **The Gram's margin.** `H ⪰ (1 − 1/(2L_R)) I` since the founding (`carried_gram_posDef_rule`),
  because the carried Gram is within `n·u ≤ 1/(2L_R)` of `H₀ + Σ w f fᵀ ⪰ H₀`. A prior `s I` keeps
  the margin `s − 1/(2L_R)`. The lattice rule and the chart's release read
  (`ChartRule::read`, divisor `c = 1 − 1/(2L_R)`) are written at `s = 1`. A smaller `s` would owe the
  chart target about `⌈log₂(1/s)⌉` more bits. This bounds `s` from below; it does not fix it.
- **The step's metric.** The unit step is `D = Σ w g (X̂ f)ᵀ` with `X̂ ≈ (s I + F)⁻¹`, where
  `F = Σ w f fᵀ` is the readings' Gram. `B` is not carried, so `W` is the prox iterate. The prior
  never pulls `W` back toward `R₀`; it is only the metric's opening part.
- **The certified step.** On the receiving map, `η` is the largest power of two with `η C ≤ a`
  and `η · max(osc, 1) ≤ 1` (`Constitution::deposited`, the class-metric step of the contact loop
  record §19).

## 2. The shape is derived

Before any reading reaches the locus, the only quadratic form the receiving ring carries on its
anchors is its storage form. That form is `(h/4)Y_R|v|²`: `Y_R` is the junction's one admittance
and `h` the field's step, so the form is a scalar times the identity (`hnn::propagation`, the
storage's split term; module header of `hnn::constitution`, `|v_R|² ≤ (4/h)P/Y_R`). A prior that
the locus holds before it has read anything must therefore be a multiple of `I`. [agent-inferred:
the prior is a form the locus already holds] This also excludes an anisotropic prior built from
the anchors themselves, because none has arrived yet.

## 3. The scale is the anchors' unit, and the cap is the same constant

Lean `HNN/ReceivingPrior`:

```text
unit        H = s I + Σ w f fᵀ ,  f = c f′ ,  x = c x′ ,  s = c²   ⇒   ⟨H⁻¹ f, x⟩ = ⟨H′⁻¹ f′, x′⟩     (unit_step_read_prior_scale)
opening     (s I + z zᵀ)⁻¹ z = z/(s + |z|²) ;   1/2 ≤ s/(s + |z|²) ⇔ |z|² ≤ s                (first_reach, opening_outweighs_iff)
one cap     a, osc ∝ 1/s ,  C ∝ 1/s²   ⇒   min(a/C, 1/max(osc, 1)) · D₁/s = D₁ min(a₁/C₁, 1/max(osc₁, s))  (cap_and_prior_one_constant)
```

- **Unit.** At the prior `c² I`, every read of the unit step on features `c f` equals the read of
  the unit-prior step on features `f`. The alignment, the moves, the Fisher curvature and the
  oscillation are all such reads, so the certified step is the same. A prior `s I` is the unit
  prior with the anchors measured in units of `√s`. Only the anchors' amplitude unit can fix `s`,
  and that unit comes from the medium's declared amplitudes (`E₀ = ±½`, `Y`, `h`), not from the
  receiving map.
- **Opening.** One reading `z` on the prior `s I` corrects its own logits by the fraction
  `|z|²/(s + |z|²)` of the full Newton correction. The opening keeps at least half exactly when
  `|z|² ≤ s`.
- **One constant.** Where the readings' Gram is negligible against the prior, the unit step and
  every read along it scale as `1/s`. The certified move is then `D₁ min(a₁/C₁, 1/max(osc₁, s))`.
  `s` enters only as the floor of the oscillation cap, the same place as the cap's own `1`. Below
  `osc₁` the move is the one-bit oscillation trust region on the deposit's own window, which is the
  regime §18 of the contact loop record measured to overfit. Above it the move falls as `1/s`.

The opening `R₀ = 0` is not a reading ([the opening record](2026-10-02_THE_RECEIVING_MAP_OPENS_AT_ZERO_AND_THE_SOURCE_MAP_REACHES_THE_CONTACT_ONLY_AS_MOTION.md)
§1), so it carries no Fisher information about `R`. The information-theoretic prior is `s = 0`,
which is the trust-region regime with no margin. The opening cannot derive `s`.

## 4. Campaign 1's first 2,192 readings: the readings' Gram never outweighs the prior

The anchors and the landmark tree's exponents were read on the host reference (`hnn_exposure
ablation 1700 samples`, main at `193fc9b6`, cloud, four cores). The run was stopped by a container
restart after the second aeon's close, at 2,192 of 3,400 readings; it is incomplete, and the read
below uses those 2,192 readings
([run](2026-10-02_THE_RECEIVING_PRIOR_receipts/samples_run.txt): launched at 21:40 UTC, second close
written at 21:57 UTC; its peak resident set was lost with the container).

| Reading (2,192 readings, `n = 22` anchor coordinates) | Value |
|---|---|
| largest anchor energy `|z|²` | `68693/2^24` (below `2^(−7)`) |
| mean anchor energy | `10608674/2^35` |
| accumulated `tr F = Σ |z|²` | `726694169/2^30` (below `1`) |

Over these readings every reading is more than `2^7` below the prior, and the accumulated Gram's
trace stays below the prior's single eigenvalue. The opening keeps more than `128/129` of each
single reading's correction (`first_read_share` at `|z|² < 2^(−7) s`). Every eigenvalue of `F` is
at most `tr F < 1 = s`, so along every direction the prior keeps more than
`2^30/(2^30 + 726694169) = 1073741824/1800435993 > 1/2` of the step (`opening_outweighs_iff` read
on each eigenvalue): the readings' Gram shapes the metric but never outweighs the prior. `R`
steps the class-metric gradient `κ G` through `(I + F)⁻¹`, within that share of the prior's
`1/s` along each direction, with `η = 1`: the step median is `1` in the run's log.

The trace below `1` is a reading at 2,192 readings, not of the campaign. At the measured mean the
trace reaches `1` at 3,239 readings (`3239 · 10608674/2^35 ≥ 1 > 3238 · 10608674/2^35`), before
the campaign's 3,400, so over the whole campaign the accumulated Gram may outweigh the prior along
its leading direction. The third aeon is not read here.

[The whole campaign is read](2026-10-02_THE_READINGS_LOCATE_THE_RECEIVING_PRIOR_BY_THE_PREQUENTIAL_CERTIFICATE.md)
§1–§2: the trace reaches `1` at reading 3,109, every eigenvalue stays below it, and the best
member over the integer scales is `2 I`.

## 5. The readings' code locates the scale

`receiver_prior_scale.py` replays the receiving map's executed law on the combined face (tree
plus wave), prequentially: each reading is scored before its window's deposit. The replay uses
the window's class metric, the Fisher curvature and oscillation caps, and the dyadic `η`, at
`H₀ = 2^k I`. It also replays the unit-information prior, `s` equal to the readings' mean energy
per coordinate so far. The anchors are held as the machine produced them; the medium's other loci
are not replayed. This is an exterior yardstick in floating point. Each value is its float's exact
dyadic, given as a carry plus `k/16` plus `ε`
([output](2026-10-02_THE_RECEIVING_PRIOR_receipts/prior_scale.txt)).

| Prior `H₀` | prequential code − tree alone, 2,192 readings (bits) | median `η` |
|---|---|---|
| unit information (`s` about `2^(−16)`) | `179 + 12/16 + ε` | `2^(−3)` |
| `2^(−14) I` | `176 + 8/16 + ε` | `2^(−3)` |
| `2^(−10) I` | `153 + 6/16 + ε` | `2^(−3)` |
| `2^(−6) I` | `134 + 12/16 + ε` | `2^(−1)` |
| `2^(−4) I` | `110 + 5/16 + ε` | `1` |
| `2^(−2) I` | `33 + 9/16 + ε` | `1` |
| `I` | `−4 + 9/16 + ε` | `1` |
| `2^2 I` | `−6 + 2/16 + ε` | `1` |
| `2^4 I` | `−3 + 13/16 + ε` | `1` |

The full table (every even `k` from `−14` to `4`) is in the output. The prequential code is the
readings' description length under the law, which is the evidence for the prior. It is strictly
worse at every scale below `I`: worse than `I` by `37919/1024` bits (`2^(−2) I`) to `11727/64`
bits (the unit-information prior), and worse than the tree alone. The unit-information prior,
the statistical candidate for a derived scale, is the worst member.

The family is eleven priors, the ten scales `2^k I` and the unit-information prior. Naming one of
them charges `log₂ 11` bits, in `(3 + 7/16, 3 + 8/16)`; the ten scales alone charge `log₂ 10`, in
`(3 + 5/16, 3 + 6/16)`. From the output's totals (`I` `8708421/2^10`, `2^2 I` `8705917/2^10`,
`2^4 I` `8709717/2^10` bits), the best member is `2^2 I`. `I` codes `313/128` bits above it,
inside either charge (`2^313 < 10^128`). `2^4 I` codes `475/128` bits above it, outside both
(`2^475 > 11^128`). At 2,192 readings the code is flat over `I` and `2^2 I` and already rises at
`2^4 I`; the odd scales were not replayed.

## 6. Decision

[Superseded on the scale](2026-10-02_THE_READINGS_LOCATE_THE_RECEIVING_PRIOR_BY_THE_PREQUENTIAL_CERTIFICATE.md)
§2 and §6: the family's charge `log₂ |family|` belongs to the grid replayed, not to the readings;
over the whole campaign the readings select `2 I` among the powers of two, and `I` is released.
The code opens at `I` until the change to `2 I` is measured. The shape and the unit theorem below
stand.

[agent-inferred] `H₀ = I` stays. Its status changes from declared to derived in shape and located
in scale:

- the shape `I` is the receiving ring's storage form (§2);
- the scale is the anchors' unit (§3, proved). Releasing it toward the opening's own information,
  `s → 0`, is measured worse on campaign 1, and so is the unit-information prior (§5);
- the readings' code puts `I` within the family's charge of its best member `2^2 I`, and every
  scale below `I` more than `37` bits outside it, so `I` is the least prior the code does not
  penalize: the most plastic one. It is also the scale at which the prior's floor and
  the cap's `1` coincide (§3), so the law carries one constant there, not two.

The plateau is a property of campaign 1's anchors. By §3, a medium whose anchors are `c` times
larger moves it by `c²`, so a field with other amplitudes must locate it again. The derivation
that would carry it per field, the prior that maximizes the readings' evidence read from the
stored statistics (the effective count `n − s tr X̂` against `|W|²` in the class metric) without
a tape, is owed in #62. No code changes in this record.

# The classical loss is the perceived difference, and the deposition remainder is a representation residual

**Date:** 2026-09-25. **Occasion:** HNN campaign 1 (#73). On the declared field the exactly carried
deposition remainders passed the bit budget `B_Θ` inside the first aeon. The primary then asked
Brandon to choose between "release per epoch", "shorter aeons" and "release only at aeons". Brandon
answered:
- "why is 'first aeon' = ~600 … this is a mathematics question";
- "Aeons and Holarchies, Epochs and interacting Holons, they have associated energy flux and entropy
  diffusion, the conservation of faces is what you'd need for any of this … it just isn't only
  about time";
- "What is the speed of light analogue conservation law of motion in general here? The classical
  loss function is real and important, it is the conscious difference gradient that would be
  perceived, part of the autograd and cross-entropy; it's why that works with LLMs."

This record answers those questions from the objects and the pre-rebuild research. The release law
it derives is the step 4 design's Decision 22 ([THE_REBUILD](../../docs/plans/THE_REBUILD.md)).

**Truth discipline:**
- Classical results are `[proved-standard]`.
- Identities checked in exact arithmetic are `[proved-derived]`; the deposition law's are now
  formal-checked in `HNN/LatticeDeposit`.
- Correspondences into the objects are `[interpretation]`.
- The HNN law is `[definition; agent-inferred]`.

## 1. Why the first aeon was "about 600"

`[proved-derived]` The number followed from two declared clocks and said nothing about the remainder.
- **The aeon.** In campaign 1 the aeon boundary is ring 3's carry-out, where the rings have periods
  `(5, 7, 11, 13)`.
  - Rings 0–2 step on a byte `b ≡ 0 (mod d_g)`.
  - Ring 3 steps only by carry.
  - With `n = (52, 37, 24)` bytes fitting the three locks, the long-run carry-out rate on uniform
    bytes is `(n₀ + d₀n₁ + d₀d₁n₂)/(256·d₀d₁d₂d₃) = 1,077/1,281,280` per cell.
  - So the mean aeon is `1,281,280/1,077` cells, printed as a decimal ≈ 1,189.7. The measured mean
    was 1,189.
- **The deposit.** One compare and deposit comes every `A = 2` cells, which gives ≈ 595 deposits per
  aeon.
- **No upper bound.** On text the length depends on how often bytes hit 0 mod 5, 7 or 11. A stream
  with no such byte (for example `a`, which is 97 ≡ 2, 6, 9) never closes an aeon. The aeon is a
  first passage of the joint clock, so any law keyed to its length bounds nothing.

## 2. The speed of light, the face's bits, and what does not follow

This section was corrected the same day by Sol (GPT-6), Claude's derivation partner; the first
version called the identity below a conserved budget.

- **The laboratory's derivation** (Brandon's laboratory notes of June 14 and 18, the speed-of-light
  walk and the theory tablet §0 and §8.4, with Opus 4.8): `c =
  bits/tick` as the boundary's budget per tick, spent between propagation and proper time,
  `(v/c)² + (dτ/dt)² = 1`. The laboratory graded its physical identification a HUNCH, and it stays
  `[interpretation]`: `(εμ)^(−½)` has units of length per time, not bits per tick, and a bit rate
  needs a declared source, channel, receiver and clock.
- **The medium's side** (null-cone record §3). In a homogeneous, isotropic, linear, nondispersive
  medium, Maxwell's principal symbol gives the wavefront speed `(εμ)^(−½)`, the same law as the
  parametron's `ω = (LC)^(−½)`. A general local linear constitution gives a quartic Fresnel
  surface; a single metric cone needs further conditions (no birefringence), and dispersive media
  separate phase and group speed (Hehl, Itin and Obukhov 2006). `[proved-standard]`
- **At the HNN's receiving face** the per-cell identity is exact algebra: `[proved-derived]`

  ```text
  log₂|A|  =  ℓ_k  +  g_k ,     ℓ_k = −log₂ p̂_k(t_k) ,   g_k = log₂(|A| p̂_k(t_k))
  ```

  It is not a conserved budget of two nonnegative parts: `g_k < 0` whenever `p̂_k(t_k) < 1/|A|`
  (a binary face with `p̂ = 1/16` reads `1 = 4 + (−3)`), and `ℓ_k` is unbounded as `p̂ → 0`. Summed
  over an aeon it compares the model's code with the literal; it does not make "every Holon spends
  exactly `c`" or the Minkowski split true. The August 14 record's grading of "compression is
  exactly like relativity" (an interpretation with five breaks; Levin's `Kt` is the honest object)
  stands.

## 3. The classical loss is the perceived difference

- **The news.** `ℓ_k` is the cross-entropy read at the receiver's face at its grain. The laboratory
  names what it measures (§4.4): `κ = S ⊖ E`. The prediction (reafference) cancels, the news
  (exafference) remains, and "learning lives on the foil — and ONLY the foil". `[interpretation]`
- **Its gradient.** `p − q` is the real, grain-level part of `R⁻¹dR`, and the adjoint pulls it back
  (`Objects/Ratio.{hasDerivAt_targetSurprisal_coordinate, lossCovector_eq_expected_logDerivative}`,
  `[proved-derived; formal-checked]`). The phase part completes it.
- **Why it trains language models.** Minimizing expected cross-entropy is minimizing expected
  description length exactly (Kraft–McMillan and Shannon: `E_p[ℓ_q] − E_p[ℓ_p] = D(p‖q)`). `[proved-standard]`
- **As flux.** Cross-entropy is physical: along a passage its change splits into exchange and
  deposition (aeon A7), and its arrow is `σ = D(P_γ‖P_{Rγ})` (A6).

CLAUDE.md and AGENTS.md now state the classical loss this way.

## 4. Faces at the aeon boundary, and where the remainder goes

- **The collapse conserves faces exactly.** It releases only exact complements. Every admitted
  reading is identical, exactly, over every admitted future (the design's collapse, guard 15;
  `release.py`: 72 of 156 entries released with identical readings). This is the conservation the
  aeon needs. The first-law ledger closes on it as well: exchange plus deposition equals the change
  of code length.
- **A carried remainder is not an exact complement.** The word reads only lattice values, so
  releasing a remainder changes no reading now. But it can move a later lattice value by one unit,
  and so a later admitted reading. A release at the collapse therefore breaks the face
  conservation. On the chain control one aeon's release moved the admitted logits by 0.72 of a
  grain, a printed reading of an exact interval.
- **The remainder is the lattice representation's residual.** The exact-representation law governs
  it ("rebased, factored or re-represented with its decoder and residual"): the represented Holon
  must stay within a bounded distance of its exact law on every aeon since its founding, or the representation changes
  the law. Releasing at every aeon lets that distance grow by up to a unit per aeon.
- **Forgetting.** It belongs to the relevance collapse (null-cone record §6) and to the law's
  declared dissipation, not to arithmetic. The light a Holon emits is the change it releases at
  each word's end and its contact dissipation. Brandon's egg reading holds: the interior diffuses
  what does not follow the structure, and the body keeps its exterior face.

## 5. The law: the remainder's precision refines with the locus's own count

`[definition; agent-inferred]` Decision 22, for each locus `ℓ` with unit `u = 2^(−L_ℓ)`.
- **The count.** `m` counts the epochs at the locus's own section: the deposits that reached it
  with a nonzero update. It starts at the locus's founding occurrence (the field's mount, or a
  founding in campaign 3), is not reset at the Holarchy's aeon boundaries, and ends when the
  collapse releases the locus whole. "Since the locus's founding" below means every aeon that
  begins at that occurrence, read in these epochs: a count of flux crossings, not a duration.
- **The split.** With `k_m = 2⌊log₂ m⌋ + 1`:

  ```text
  Δ + r_prev = y_f + e        at the nearest point of 2^(−L−k_m)ℤ
  y_f        = q·u + r        at the nearest point of uℤ, ties upward
  apply q·u;  carry r;  release e, reported in the deposit's receipt
  ```

`[proved-derived]` What follows:
- **Accounting.** applied + carried + released = the exact sum of the updates, always.
- **Kraft.** `|e_m| ≤ u·2^(−k_m−1)` and `Σ_(m≥1) 2^(−(2⌊log₂ m⌋+1)) = Σ_i 2^i·2^(−2i−1) = 1`,
  with every finite partial sum `< 1`. So the released total stays below `u/2` over every aeon since
  the locus's founding, and `|value − exact| < u`.
- **The Gram.** Entrywise deviation below `u` gives an operator-norm deviation below `n·u ≤ 1/(2L_R)`
  (`‖E‖₂ ≤ n·max|E_ij|`, `X_ℓ ≥ n`). The exact Gram is `⪰ I` (the unit prior plus positive
  semidefinite updates), a margin of 1, so the carried Gram stays `⪰ (1 − 1/(2L_R)) I`.
- **Bits.** `r·2^(L+k_m)` is an integer of magnitude at most `2^(k_m−1)`, so a remainder takes at
  most `L + 2k_m + 1 = L + 4⌊log₂ m⌋ + 3` bits (`remainder_rat_bits_bounded`), however long the aeon
  runs.
- **What forces the schedule (corrected by Sol).** Against every sequence of tails, the released
  total stays below `u/2` exactly when `Σ 2^(−k_m) ≤ 1`: this is a worst-case statement, since a
  particular signed sequence can cancel under a non-summable schedule. A constant `k` fails it, and
  an exact remainder (`k = ∞`) has unbounded bits. Summability admits many schedules and no
  pointwise least one; the gamma lengths are chosen because they are the field's own natural code
  and complete (`Σ = 1` in the limit), which is agent-inferred, not forced. Elias delta would save
  about `log₂ m − 2 log₂ log₂ m` bits per entry.
- **What it does not certify.** Releasing a nonzero tail is not an exact-complement release: a
  bound on coefficients does not prove that every admitted future face is unchanged. That needs the
  word's sensitivity from each locus to the faces (#62, below), exactly as the unread carried
  remainder already does.

**Precedent.**
- History's native commits rebased to a dyadic centre at every commit and dropped the radius
  (`13f8c734`, `IncidentRebaseResidual`). They recorded the sum of dropped radii as "not a
  trajectory bound".
- `Objects/CommitRebase.commit_chain_residual` bounds the counterfactual distance by
  `Σ K^(n−1−i) r_i` once the word has a Lipschitz `K`.
- Carrying the remainder bounds the sum of dropped radii. The `K` part stays owed.

## 6. How the floats were used

Every decimal quoted in this work is the printed face of an exact quantity:
- ≈ 595 deposits is `1,281,280/1,077` cells over `A = 2`;
- "250 Mbit" is an exact bit count;
- "0.72 of a grain" is an exact interval printed.

They showed that an exact remainder overran the budget. The replacement law comes from the retention
and exact-representation laws and uses only integers and dyadic rationals.

## 7. bits/tick, abstractly (Brandon's follow-up)

Brandon: "bits/tick makes sense … but what is that in an abstract mathematics sense? … it's just a
statement about change per permeability and permittivity of the partition I think."

- **A bit** is the additive chart of a ratio: `ℓ = log₂ R`, `R` a ratio of two measures of one
  partition; one bit is one halving. To second order the loss between nearby faces is the quadrance
  of their difference in the face's metric, `D(p+Δ‖p) = ⟨Δ, MΔ⟩/(2 ln 2) + O(Δ³)` with
  `M = diag(1/p)` (the Fisher metric): the "delta of products, normalized". `[proved-standard]`
- **A tick** is a crossing of a receiver's section, an epoch boundary; its rate is the flux of the
  motion through the section (aeon record).
- **bits/tick** is a coarse-grained information rate. Under an invariant measure, Kac and Abramov
  relate grains exactly: the mean return to a section `A` is `1/μ(A)` fine ticks, and the induced
  entropy is `h(T)/μ(A)` per coarse tick (`Aeon/Production/Kac`). A rate needs that law, its
  section and its receiver; a pathwise supremum of surprisal per tick can be infinite, so
  "capacity" needs a declared channel class (corrected by Sol). At the HNN's face, `ℓ_k` per cell is
  the classical loss read per tick of the receiving section.
- **Permittivity and permeability.** A constitution's storage form `C` and restoring form `K` give
  modes `Kv = ω²Cv`, so `ω²` is a ratio of two quadratic forms of differences, and the long-wave slope
  is `c = (εμ)^(−½)`. `[proved-standard]` On the face the analogous objects are the difference `Δ`, the
  Fisher metric `M`, the tangent reading `d(log p_i)(Δ) = Δ_i/p_i` and the second-order loss
  `½⟨Δ, MΔ⟩/ln 2`, with the normal law's compliance `ΔW = γ G H'⁻¹` as the flow side.
  `[interpretation]`: the Fisher metric is a statistical face metric, and identifying it with a
  permittivity needs a source map equating measured power or energy forms, which is not given.
  (The first version wrote `R⁻¹dR = d log p = MΔ` as an equality; it holds only as the first-order
  tangent reading.)
- **Correction (Brandon, same day).** This is not a learning law. It is a statement about
  differences relative to each other under coarse graining: when one thing is read as two, when
  the music is not noise. `c` is not a speed limit on how much causality occurs (a star's cascade
  of emissions is not throttled by it). It is the translation barrier between grains of space and
  time: each partition is a local medium or lens with its own constitutive cone, and what crosses
  between partitions conserves a face (the tangential phase and frequency at an interface; the
  Killing energy, read by each receiver through its own lapse, in gravitational redshift). An
  emission spectrum is a chord: its frequency ratios are invariant under the redshift group. One
  unidentified line carries no invariant; one securely identified line with a known rest frequency
  already gives the shift, and several lines identify the source and test that the shift is common.
  The local causal cone is not repealed by this reading: no signal outruns its local null cone,
  while the amount of concurrent causation is not limited by it. The derivations continue in the
  [natural-grain record](2026-09-25_THE_NATURAL_GRAIN_IS_THE_FUTURE_QUOTIENT_AND_REFLECTION_INTEGRATES_A_FRACTAL_PACKING.md).

## Obligations

- **#73, campaign 1: discharged.** Lean `HNN/LatticeDeposit` (`carry_accounting`,
  `lattice_deposit_accounting`, `gamma_kraft_lt_one`, `release_bounded`,
  `release_bounded_since_founding`, `within_one_unit_since_founding`, `remainder_numerator_bounded`,
  `remainder_rat_bits_bounded`, `carried_gram_posDef`, `carried_gram_posDef_rule`,
  `lattice_deposit_descends`) and Rust `hnn::constitution`.
- **#62, step 4:**
  - the word-level certificate of the lattice rule, `Σ_ℓ K_ℓ 2^(−L_ℓ) < 1/(2L_R)`, with `K_ℓ` the
    word's sensitivity from locus `ℓ` to the logits. Passivity gives `‖dCay‖ ≤ ‖dK‖` when the
    element's symmetric part is `⪯ 0`; the active contrast port needs its own bound. It joins
    `Objects/CommitRebase`.
- **The per-cell budget split** as a reading of the exposure: `Σ ℓ + Σ g = n log₂|A|`, per aeon, beside
  the first-law split.

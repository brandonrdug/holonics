# Campaign 1's located failure: the face can read the marginal, the deposition keeps its prior, and the source carries its table without its index

**Date:** 2026-09-25. **Status:** recorded (#73, campaign 1; reviewed by the primary). **Occasion:**
campaign 1's exposure on the standing real cut does not beat the online order-0 held-out bits
(#73's receipt: 7.578 bits a byte against order-0 KT's 4.762). The step 4 design's standing real
cut (review E1, [THE_REBUILD](../../docs/plans/THE_REBUILD.md#d-the-five-campaigns-in-order-reordered-keys-lead))
admits the next campaign only after the failure is recorded with its located cause: source,
relation, encoding or decoder. This record locates it. It changes no law and proposes no fix; it
names the missing term in each owner.

**The measurement.** [`hnn_diagnose.rs`](../notebook/hnn_design/hnn_diagnose.rs), a `holonics`
example run once in release on the host, from the repository root:

```sh
cargo run --release -p holonics --example hnn_diagnose -- cut-file .local/cuts/standing-real-cut-campaign-1.bin
```

It runs campaign 1's exposure protocol (design (d)) step for step through the host reference's
`ExecutionPort` and reads between the port's methods: the compare's staged deposit (the receiving
map's samples), the published constitution's read face, the deposit's reading and the moment. It
adds no accessor. It reproduces the receipt exactly: held-out 7.577520 against order-0 KT 4.762009
bits a cell (1,190 cells), training 7.241416 against 4.949181 (4,958 cells); 3,074 windows, 2,479
deposits, 5 aeon boundaries, 4 key locations, no key published; 614 s for the exposure, about 11
minutes in all (exterior wall time). The cut is private and is reported by scope and counts only.

**Truth discipline.**
- Measured values are `[established-bounded; measured]`: this cut, campaign 1's declared field, one
  run. They are exact rationals or enclosures with exact endpoints, printed as decimals.
- Identities of the laws, checked against their Lean owners, are `[proved-derived]`; classical
  results are `[proved-standard]`.
- A cause is graded `[established-bounded; measured]` where a measurement separates it from the
  others, and `[conditional]` where it rests on a further hypothesis.
- The missing terms named in §6 are `[definition; agent-inferred]`.

## 1. The gap, decomposed

`[established-bounded; measured]` Held-out bits a cell over the 1,190 held-out cells, each face
read at the receiver's grain `L_R = 16` through the machine's own `Face`:

| Face | Bits a cell |
|---|---|
| the declared prior's reading `R_0 z` alone (the held-out reads all use the final map) | 10.6125 |
| the machine's `p̂` | 7.5775 |
| the learned part `(R − R_0) z` alone | 6.7210 |
| the machine's own mean logit vector over the training reads, as one static face | 6.4653 |
| the oracle `R = y wᵀ` on the machine's own read features (`w` fitted on the training reads) | 5.0248 |
| the same, `w` fitted in-sample on the held-out reads | 4.9771 |
| the static order-0 face (the training cells' KT log-frequencies `y`) | 4.7745 |
| online order-0 KT | 4.7620 |
| online order-1 KT | 4.3402 |
| PPM of order 2 (#73's receipt) | 3.297 |

The 2.815 bits between the machine and online order-0 split into three parts:
- 2.553 bits lie between the machine and a face its own features express (the deposition, §3);
- 0.250 bits lie between that face and the static marginal (the face's missing constant, §2);
- 0.012 bits lie between the static and the online marginal.

Orders above 0 (order-1 KT, PPM) lie in the index the source does not carry (§5).

## 2. The decoder can express the marginal

`[proved-derived]` The receiving face is `f_j = R z_j`, `z_j = P_R^(τ_R) v_R(e_j) ∈ ℚ^22` the rotated
anchor (the receiving map's own sample feature), with no constant term. The face reads `Re f` up to
a common shift (atlas `norm.shift-fibre`). So the order-0 marginal `y` is expressible on every read
exactly when some `w` reads `wᵀ z_j = 1` on every read; and the least-squares fit of `R` to `y` on
every read is `R = y wᵀ` with `w` the least-squares solution of `wᵀ z_j = 1`, since each row `c`
fits the constant target `y_c`. The read is then `f_j = s_j y` with the scale `s_j = wᵀ z_j`.

`[established-bounded; measured]`
- The training features have full rank 22 (4 of 4,958 are zero, in the first windows).
- **The constant's reach** `bᵀw/N` (one minus the least-squares residual per read) is 0.805 from all
  22 coordinates. From the receiving ring's **dormant mode** alone, the rotation-invariant sums of
  its nodes' real and imaginary coordinates (the kernel of its unit-weight cycle Laplacian), it is
  0.802. On the held-out reads in-sample it is 0.903. The dormant component holds 63% of the
  features' energy, with stability `|Σu|²/(N Σ|u|²)` = 0.72.
- **The oracle's scales** on the held-out reads are all positive: median 1.29, from 0.147 to 2.69,
  1,051 of 1,190 within `[1/2, 2]`. On shielded-path reads the median is 0.80, on open-path reads
  1.41: the scale follows the path's attenuation and the features' growth.
- **The oracle scores** 5.0248 bits a cell (4.9771 in-sample), 0.25 bits above the static order-0
  face at the same grain.

**Reading.** `[established-bounded; measured]` The face can carry the marginal, to within 0.25 bits
of the static order-0 face, and it carries it on the receiving ring's dormant mode. "Cannot express"
is not the cause of the gap. The missing constant costs the 0.25 bits: the marginal rides the
change, whose scale the path's attenuation and the moment's growth set, so it arrives tempered
(`p^(s_j)`) rather than at unit scale.

## 3. Learning: the deposition does not reach the marginal

**The logits are large and are not the marginal.** `[established-bounded; measured]`
- A held-out read's own spread `max_c Re f_c − min_c Re f_c` has median 15.85 bits (largest 32.0),
  against the marginal's 10.63.
- The mean spread grows by aeon: 8.4, 11.9, 9.9, 13.3, 14.3 bits over the training aeons, 14.9 and
  18.7 over the held-out ones.
- Their mean over the reads holds half their class-centred energy (0.50 on training, 0.54 on
  held-out) and scores 6.47 alone: the machine's own face pays 1.11 bits a cell for the variable
  half.
- **Almost all of it is the declared prior's reading.** Every held-out read uses the final map, so
  `f = R_0 z + (R − R_0) z` splits each held-out read. Class-centred:
  - The prior's reading `R_0 z` holds 91.1% of the logits' energy and the learned part 12.9%. Their
    cross term is −3.9%, so the learning cancels almost none of the prior.
  - The prior's reading alone codes the held-out targets in 10.61 bits a cell, worse than uniform.
    The learned part alone codes them in 6.72, and the sum in 7.578 (the machine's own 7.5775; the
    centring moves the grain cells by less than `1/L_R`).
  - Projected on the centred marginal `ȳ` (`Σ⟨part, ȳ⟩` over `N |ȳ|²`), the learned part carries
    0.265 of it and the prior 0.049. The oracle's scale is about 1.

**The features grow.** Mean `|z|²` by aeon: 11.7, 20.3, 13.1, 23.4, 30.2 over the training aeons,
45.8 over the last held-out aeon. The source moment accumulates counts, so the change the word
opens grows with the population.

**The step shrinks.** `[proved-derived]` The prox step moves each read's logits by `γ g h` with the
leverage `h = zᵀ X̂' z` under the successor's solved chart (Lean `HNN/Normal.normal_prox_step`,
`W' = W + γ G X̂`). `log det` is concave, so at every deposit
`log det H' − log det H ≥ tr(H'⁻¹ ΔH) = Σ_j f_jᵀ H'⁻¹ f_j`, and over a run `Σ h ≤ ln det H_T` with
`H_0 = I` (up to the chart's certified residual). `[established-bounded; measured]`
- The leverage has median 0.0136 over the run; by aeon (median) 0.052, 0.018, 0.0099, 0.0089,
  0.0076.
- The read logits' executed move per deposit, `max_c |(R' − R) z|`, has median 0.019 bits (0.081
  in the first aeon, 0.011 in the fifth), largest 0.70.
- Over the run `Σ h` = 141.80 against `ln det H_T ∈ [153.51, 153.53]` (`log₂ det H_T` = 221.48 for
  `R`'s carried Gram at the end). The bound nearly binds: the step spent almost all the reach the
  Gram's growth allows.

**The curve is flat.** `[established-bounded; measured]` Training bits a cell by block of 512 cells:
7.35, 6.97, 7.25, 7.73, 7.17, 7.11, 7.20, 7.23, 6.98, 7.49, against online order-0 KT's 5.26, 4.55,
4.51, 5.48, 4.86, 5.06, 5.33, 4.97, 4.74, 4.63. By aeon: 7.12, 7.50, 7.16, 7.12, 7.50; the held-out
aeons 7.40 and 7.92. Nothing descends after the first block, and the held-out part worsens as the
features grow.

**Not the lattice.** `[established-bounded; measured]` Decision 22's carry neither starves nor
releases the learning.
- `R`'s exact update per deposit, `(W' − W) + (r' − r) + e` by the carry's accounting
  (`HNN/LatticeDeposit.lattice_deposit_accounting`), has its largest entry at median 5.8 lattice
  units of `2^(−10)` (44 in the first aeon, 2.4 in the fifth).
- 99.96% of its ℓ1 is applied on the lattice, and the released tails are 0.064% (`E_0`: about
  `10⁻⁶`).
- `E_0`'s largest exact entry has median 918 units of `2^(−18)`, and 699 of its 2,560 entries move
  per deposit.

**The covector's phase part does not swamp it.** `[established-bounded; measured]` Over the
training reads, the phase part (`Im f`) holds 18.1% of the covector's energy at the face. Pulled
back through `Rᵀ` to the receiving anchor, where every other locus's covector starts (`E_0`'s
included), it holds 16.4%. The magnitude part leads the learning.

**The mechanism.** `[proved-derived]` In `HNN/Normal.normal_prox_step` the proxy target of a sample
is `y = W f + γ g`, and `B' = B + w(W f + γ g) fᵀ`: the map's own reading plus one covector step.
The comparison enters the normal statistic only as its covector. So the prox iterate is
`W_T = R_0 + Σ_t γ g_t (X̂_t f_t)ᵀ`: the declared prior `R_0` (the sign generator times ½) is never
divided by the Gram that grows under it, its reading `R_0 z` grows with `|z|`, and the increments
shrink with `h`. The measurements above are this mechanism's signature:
- the prior's reading is 91% of the held-out logits and grows with `|z|`, and the logit spread grows
  with the feature energy by aeon;
- the learned part is 13% and carries a quarter of the marginal;
- `Σ h` nearly meets `ln det H_T`.

**Reading.** `[established-bounded; measured]` The decoder does not learn. Neither its
expressivity (§2) nor the deposition's lattice is the failure. The deposition's prox step keeps the
declared prior's reading at full weight while the features grow, and its own reach is bounded by
`ln det H_T`. The prior is what the held-out face reads: removing its reading alone takes the
face from 7.58 to 6.72 bits.

## 4. The relation: the keys are located correctly, and text has none

**Synthetic cribs.** `[established-bounded; measured]` Each crib is generated by one declared ring,
with a true key and a true plugboard drawn by SplitMix64 and the earlier rings at phase 0:
`S(port(x_(k+1))) = W_(key + steps(k)) S(port(x_k))`, each next cell a byte of the forced port class.
There are 16 trials per ring, at the declared crib of 64 cells and at 512 cells.
- The truth is in the fibre in 128 of 128 trials, and no fibre is empty. The injective partial
  closure (below) satisfies every edge in 128 of 128.
- The fibre is one gauge orbit, so a key is published:

  | Crib | Ring 0 | Ring 1 | Ring 2 | Ring 3 |
  |---|---|---|---|---|
  | 64 cells | 7 | 4 | 2 | 1 |
  | 512 cells | 6 | 16 | 16 | 6 |

  (of 16 trials each). Otherwise the fibre is plural: up to 4, 5, 10 and 12 orbits at 64 cells.
  At `δ = 1` a ring whose stage does not change alternates between two ports. Ring 0 steps only
  on its own notch; ring 3 steps only on ring 2's carry.
- Every published key is the truth's gauge-fixed member, and `locate_closing` carries it correctly
  to the boundary. It equals the truth's own key only when the plugboard's image of the least menu
  port is 0 (R3 K2's convention).

**The standing cut.** `[established-bounded; measured]`
- All 16 ring fibres at the 4 key locations are empty, and each ring fell back to phase 0.
- **The best injective partial closure.** The best plugboard satisfies 13–30 of each crib's 63
  edges (exhaustive for `d ≤ 7`, where the local search found the same best in 8 of 8; a
  48-start local search for `d = 11, 13`). That closes 2–21 of the 51–59 independent loops, against
  the fibre's requirement of all of them.
- **Against the crib's own shuffles** (32 orders, its port histogram kept): at 15 of the 16
  ring-locations the crib's best lies within its shuffles' range, at or below the shuffles' best in
  5 to 32 of the 32 orders. At one (the second location, ring 2) it exceeds all 32 shuffles: 30
  edges against at most 23. It is still 33 edges short of a fibre.

**Reading.** `[established-bounded; measured]`
- The inference is not broken: it holds the truth on every synthetic crib.
- The `δ = 1` menu under-determines the key on its own chain: plural fibres even on true machines.
  It is not what failed on the cut, whose fibres are empty.
- Real text at `δ = 1` admits no exact key of the declared machine. Its best injective partial
  closure sits within its own shuffles at 15 of 16 ring-locations. The relation (a reflector machine
  per ring on the residue port chart) is absent from the data, up to one local excess.
- It is not the cause of the order-0 gap. Keys move only the rings' phase classes, which carry no
  information about the next cell (§5).

## 5. The source and encoding: the table without its index

`[established-bounded; measured]`
- **Capacity is not the limit.** The cut is exactly `n* = 6,148`, so the moment is lossless by
  counting at every window of the exposure. `⌈log₂N(n)⌉/8n` is 1.29 at `n` = 2,048, 1.054 at
  4,958 and 1.00002 at 6,147, and it is lossy only at the last cell. Its dense code is 660,380 bits,
  13.4 per source bit.
- **The path is open** at 2,711 of 3,074 windows. On the held-out cells the open reads score 7.67
  and the shielded reads 7.11 (order-0 KT on the same cells: 4.77 and 4.72). Shielding helps, as §3
  predicts: less change reaching the receiver means less of the prior's reading.
- **The per-window context separates nothing.** The word reads 1,410 distinct class configurations
  over 3,074 windows (of 5,005), and the targets are 106 distinct bytes. Online KT on the held-out
  cells, given the source ring's phase `τ_0 mod 5`: 4.881; given the receiving ring's `τ_2 mod 11`:
  5.017; given the whole configuration: 7.768. Order-0 is 4.762 and order-1, given the previous
  cell, 4.340. The phase classes only dilute the counts.
- **The source ring's bins do not separate the bytes they hold.** Coding each cell within the bin
  it lands in costs 5.188 bits a cell over the 6,148 cells, against 4.913 pooled: the five bins are
  five copies of the marginal.
- **Recency is diluted.** The cells since the source ring last moved (median 4), the only recent
  cells in its current bin, make up a median 0.76% (mean 2.8%) of that bin (median 615 counts).

**Reading.** `[established-bounded; measured]` The source reaches the word as the cumulative
phase-binned moment. It carries the source's statistics (a table: counts by phase, and by offset in
`C_g(δ)`) without the index that selects the next cell's row, which is the previous cell. The window
`win_g` holds that cell, and the open never reads it except through the cumulative offset counts
(design (a): "no tick reads it"). So the ideal reading of this encoding is the static marginal
(4.77–4.98 through the face), level with online order-0 at best and never below it. No learning on
this encoding beats order-0 by more than its online adaptation.

## 6. The located causes, graded, and what they imply for campaign 2

1. **The decoder's deposition, the primary cause:** 2.55 of the 2.82 bits.
   `[established-bounded; measured]`
   - The machine reads 7.58 where its own features admit 5.02. The declared prior's reading is 91%
     of its held-out logits, and removing it alone gives 6.72.
   - The missing term is in `NormalLaw` (Lean `HNN/Normal.normal_prox_step`, Rust
     `hnn::constitution::NormalLaw::deposited`). The normal statistic's target side
     `B = Σ w y fᵀ` has no exogenous target: its proxy `y = W f + γ g` is the map's own reading
     plus the comparison's covector. So `R_0`'s reading is kept at full weight, and the reach is
     `ln det H_T`. The comparison's own target face, `q_j` read in the face's chart, never enters
     `B`.
   - Campaign 2 changes the rings' storage, pumps, locks and site kinds, not this law. Its exposure
     on the standing cut inherits the cause unless a campaign amends the deposition's target term.
2. **The decoder's expressivity, a secondary cause:** 0.25 bits. `[established-bounded; measured]`
   The missing term is in `ReceivingPhases::read` (`f = R · P_R^(τ_R) Π_R` on the anchor). The
   receiver reads only the change, never a standing, so the marginal, which is standing, rides the
   change's scale. In the objects, the receiving face has no port on the medium's bound part. The
   dormant mode that already carries the marginal (§2) is the parametron's harmonic mode, which
   campaign 2 gives storage (`C_g`, `ker C_g`). That storage is the object in which a standing read
   would live.
3. **The source and encoding bound the ideal at the marginal.** `[established-bounded; measured]`
   The missing term is in `SourceMoment`'s open (`s_g(0) = P_g^(τ_g) m̃_g`): the window `win_g`,
   the index into the moment's table, enters only through cumulative counts. Beating online order-0
   on this cut needs the recent cells at the receiver as a separable term. Every order above 0
   (order-1 KT 4.34, PPM-2 3.30) lives in that index. The moment's counts also enter unnormalized
   by the population, so the open's scale grows over the cut (§3's `|z|`), and with it the prior's
   reading. Campaign 2 does not touch the open. Campaign 5 (Holonic Encoding and context) is the
   campaign whose laws do.
4. **The relation is not a cause of the order-0 gap.** `[established-bounded; measured]` Key
   location is correct on synthetic machines (128 of 128), and text holds no key of the declared
   machine. The ports are the codec's residues, a codec-dependent exterior chart (guard 9's stated
   exception).
   Campaign 2's locks and lock addresses (`q v_a = p v_b`, Farey addresses) are the next relation
   the keys read. This record says nothing about whether text holds those.

`[conditional]` The ordering assumes the least-squares oracle's 5.02 bits is reachable by the
deposition in principle. The oracle is one `R` over these features (a least-squares fit, not the
cross-entropy minimizer), so its 5.02 bits bound the best static `R`'s code length from above. The
features themselves were formed by the learned `E_0`, which the same deposition moves, so a
better-learned `R` also meets different features.

## 7. Scope

- One cut (the standing real cut, 6,148 cells, 1,190 held out), campaign 1's declared field, one
  run on the host. The device realization returns the same values (#73), so it needs no separate
  diagnosis.
- The key diagnostics use the crib the port uses (64 cells at `δ = 1`). The injective partial
  closure is exhaustive for `d ≤ 7`; for `d = 11, 13` it is a local search's best (48 starts), and
  its shuffles use the same search.
- xz and zstd baselines stay owed to the application (design (f)).

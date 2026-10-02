# The step's candidate states are the cuts of the carried path, and their count is a Weyl law

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1), #62. **Grade.**
[proved-derived; formal-checked] for the laws in `HNN/CarriedCuts`; [derived] where marked, with
the standard argument named; [agent-inferred] for the step law in §5, which is a design not yet
built. No run: the crossing points along `m6`'s and `m7`'s directions are the main line's
measurement (§7).

## 0. The question

Brandon, on the step sizes from `1/16` down to `1/2048`: "that is a `2^(−7)` factor scale and a
scalar difference of denominators as 2032 … you need to pay attention to the *gaps*, this is a
spectral thing, RH work is relevant." The coordinator's reading, checked here: along one move's
direction the decisions change only at a discrete set of step sizes, that set is a spectrum on the
step-size axis, and halving samples it only at powers of two. The main line reports that `m6`
adopted at `1/2048` and flipped at `1/1024`, which halving cannot resolve further.

The derivation below finds that set exactly, counts it, names the gaps that matter, states the
step law that follows, and says what the RH work contributes and where its parallels do not fit.

## 1. The carried path is constant between cuts

The step sizes the own release tries are `η₀ 2^(−j)`, each half the last, from `η₀`
(`ladder_start`) down at most `LADDER_DEPTH` halvings. At none of them is `W + ηD` itself read. Each
reads the successor the budgeted carry builds (`hnn::constitution::carried_entry`). Each entry `i` moves by `q_i u`, `u = 2^(−L)` the locus's
lattice unit. The fine point `P` is `η d_i` plus the entry's carried remainder `r_i`, rounded to
the fine lattice `2^(−L−k)` (nearest, ties upward). The coarse coordinate `q_i` is `P` rounded to
`uℤ` the same way. The two roundings compose to

```text
q_i(η) = ⌊(r_i + η d_i)/u + c⌋,   c = 1/2 + 2^(−k−1)
```

[derived: `⌊(⌊y⌋ + m)/N⌋ = ⌊(y + m)/N⌋` for integers `m` and `N > 0`]. This needs `k ≥ 1`, which
holds because `k = gamma_length(m) ≥ 1`. At `k = 0`, `div_rem_coordinate` skips the coarse rounding
and `c` would be `1/2`. The transport modulus is
carried onto the same lattice, nearest, and contributes one more such coordinate.

So **every coordinate is a step function of `η`**. It changes exactly where `(r_i + η d_i)/u + c`
passes an integer (`coordinate_changes_iff`): at the **cuts** of entry `i`, an arithmetic
progression of spacing `u/|d_i|` whose offset is set by the carried remainder. Every reading,
commitment and code length the comparison reads is a function of the carried state. Between two
consecutive cuts of the union over entries, the successor is the same constitution and
**nothing changes**. The candidate successors along a direction are indexed by their cuts, not by
`η`.

Two consequences:
- "Continuous along the move" holds for the uncarried path `W + ηD` that the first-order
  certificate speaks to. The comparison read at the successor is piecewise constant, with jumps
  only at cuts. The successor reads the entry `W + q_i u`. It differs from `W + η d_i` by the
  carried remainder (at most `u/2` per entry, held for the next deposit) and by the carry's released
  residual (at most half a fine cell). Half a fine cell bounds only the entry plus its remainder
  against `W + η d_i`. Both are bounds on states: the code lengths differ by that state difference
  read through the comparison, which nothing here bounds.
- The halving's own stopping rule, `η · max|d| · 2 < u`, places the first cut near `u/(2 max|d|)`
  when the remainders are zero (just below it, by the fine half-cell in `c`). With nonzero
  remainders the first cut can lie much lower.

## 2. The count is a Weyl law, and its fluctuation is an explicit formula

Let `N(η)` be the number of coordinates the carried path moves between `0` and `η`, its count of
single-entry unit moves. Then

```text
η‖d‖₁/u − n  <  N(η)  <  η‖d‖₁/u + n,      ‖d‖₁ = Σ_i |d_i|,  n the number of entries
```

(`moves_sum_gt`, `moves_sum_lt`; per entry `coordinate_moves_gt`, `coordinate_moves_lt`). The
count grows linearly in `η` with density `‖d‖₁/u`, and its fluctuation is less than the number of
entries at every `η`.

[derived; the sawtooth's Fourier series] The fluctuation is a sum of sawtooth functions
`ψ(x) = x − ⌊x⌋ − 1/2`, one per entry (written for `d_i ≥ 0`; a negative entry reflects):

```text
N(η) = η‖d‖₁/u − Σ_i [ψ(x_i(η)) − ψ(x_i(0))],   x_i(η) = (r_i + η|d_i|)/u + c
ψ(x) = −Σ_(m≥1) sin(2πmx)/(πm)
```

This is the shape of an explicit formula: a smooth count plus an oscillating sum over a spectrum.
Here the spectrum is the frequencies `m|d_i|/u` along `η`, all real and known from the direction.
Each sawtooth is bounded by one half, so the fluctuation stays below `n` without any further
condition. That bound is the analogue of the Riemann hypothesis for this counting function, and it
holds trivially because every cut set is a lattice progression.

## 3. Brandon's numbers on the cut set

- **The multiplicative view.** The step sizes `1/16, 1/32, …, 1/2048` lie on the orbit of `2^ℤ`.
  Eight of them span the factor `2^(−7)`.
- **The additive view.** The carried states in that span number
  `(1/16 − 1/2048)‖d‖₁/u ± n = (127/2048)‖d‖₁/u ± n`. The difference of
  denominators is `2048 − 16 = 2032 = 2⁴·127`, and `1/16 − 1/2048 = 2032/(16·2048) = 127/2^11`.
- **Each octave holds half the states of the one above it.** The octave `[η/2, η]` holds
  `(η/2)‖d‖₁/u ± n` carried states. Halving reads one of them per octave. The coarsest octave
  `(1/32, 1/16]` holds `2^7 = 128` times the states of the finest, `(1/4096, 1/2048]`.
- **Between `m6`'s adoption and its flip** lie `(1/2048)‖d‖₁/u ± n` carried states. Halving
  cannot place the wall among them. Their number for `m6`'s direction needs only `‖d‖₁/u` and the
  remainders (§7).

So halving spends its reads evenly per octave, while the states are spread evenly in `η`. Near the
step that matters, halving resolves the wall to a factor of two, among
`η‖d‖₁/(2u)` states.

## 4. The gaps

Two kinds of gap are spectral here, and the second is the one that sets the step.

1. **The gaps of the cut set.** The cut set is a union of `n` progressions with spacings `u/|d_i|`.
   - For two entries, the gaps between consecutive cuts take few values, set by the continued
     fraction of `|d_1|/|d_2|`: the three-distance law (atlas `rotation.three-distance`; its Lean is
     owed).
   - With every rate an integer `n_i = |d_i|/u` (after rescaling `η`) and every offset zero, the
     cells between cuts are exactly the helix's Farey cells: `N` readings `⌊n η⌋, n ≤ N` agree on an
     interval iff no `k/n` lies in it (`Foundation/Unicity.readings_agree_iff`). The carried
     remainders shift each progression, so a general direction's cells are shifted Farey cells.
   - These gaps decide where a state can change. They do not decide whether a decision changes.
2. **The stations' margins.** A decision changes at a cut only where some station's margin
   reaches zero. In #207's lock rule the margin of a ring's commitment is its certified gap
   against the stations the readings must lock with it. If each coordinate moved changes a margin
   `μ` by at most `κ`, then `μ` stays positive at every step size with

   ```text
   κ (η‖d‖₁/u + n) ≤ μ₀            (margin_survives_moves)
   ```

   So the flip-free stretch of the direction is set by **the smallest margin over its rate per
   coordinate**: `η_safe ≥ (μ_min/κ − n) u/‖d‖₁`. `m7`'s flip is one request whose lock order
   swaps. Its smallest margin at the incumbent is not a sub-resolution tie: it is about 140 cell
   widths, and the replay finds the pair's gaps cross within the step (§4b).
   The bound charges every entry its rounding (the `n`). A station's readings depend on only some
   entries, and charging only those tightens it.
3. **The rate per coordinate.** At first order, `κ` is the reading's covector times `u`
   (`hnn.executed-growth-covector`). Over a stretch, the rate is bounded only where the read
   multiplier stays a simple root (the flip record's §3b names this missing owner).
   [derived; a simple root's perturbation] Near a pair of multipliers of one monodromy that nearly
   coalesce (a zero of the discriminant of `det(μ − M(η))` at complex distance `δ` from the real
   `η` axis), the rate grows like `δ^(−1/2)`. That is an exceptional point of a non-self-adjoint
   family: its eigenvalues meet in a square-root branch instead of crossing.

## 4b. The prediction for `m7`'s pair

The main line's first read of #207 at `m7` (coordinator's relay, 17:45): in every refinement of all
8 requests, no other eligible station's reach meets the largest certain gap. The closest pair is in
request 3, at the second freeze: station 2's certain gap `187540480/2^24` against station 5's reach
`187166208/2^24`. The pair's margin at the incumbent is

```text
μ₀ = g₂ − ρ₅ = 374272/2^24 = 17·43/2^15
```

[proved-derived; formal-checked] Let `w_i ≥ 0` bound how much `μ` changes when entry `i` moves one
coordinate. Then `μ` stays positive at every carried state with

```text
η/u · Σ_i w_i|d_i| + Σ_i w_i < μ₀            (margin_survives_weighted)
```

An entry the pair's readings do not depend on has `w_i = 0` and charges nothing. At first order
`w_i = u|∂μ/∂E_i|`, the covector of `g₂ − ρ₅` (`hnn.executed-growth-covector`) times the unit, so
the condition reads `η Σ_i|∂μ/∂E_i||d_i| + u Σ_i|∂μ/∂E_i| < μ₀`. That is the pair's directional rate
plus one rounding for each entry it reads.

The cut list gives a sharper prediction than the bound in `η`. At each cut `j` the main line knows
which entries moved and by how much, so it can sum the weighted moves exactly:

```text
M_w(j) = Σ_i w_i |q_i(η_j) − q_i(0)|,     j* = the first cut with M_w(j*) ≥ μ₀
```

The pair keeps its certified order at every cut before `j*` (`margin_survives_weighted`'s
hypothesis `|μ(η) − μ₀| ≤ M_w` holds whenever the `w_i` bound the rate). The margin covers the whole
`1/2048` step when `Σ_i w_i|d_i|/(2048u) + Σ_i w_i < μ₀`.

The margin reaching zero means the pair becomes **unranked** at the successor (the reach meets the
certain gap). It does not mean the true gaps cross. That needs more.

Reading the actual flip's cut index `j_f` against `j*`:
- **`j_f ≥ j*`.** Consistent: the pair's margin can be consumed by then. The replay tells whether
  the pair became unranked or its true gaps crossed.
- **`j_f < j*`.** The flip happens where the margin cannot yet be consumed at the first-order rate.
  Reading the pair's actual margin at cuts `j_f − 1` and `j_f` separates two findings:
  - if `μ` reaches zero there, the first-order rates do not bound the margin over the stretch (the
    rate is bounded only while the read multiplier stays a simple root, §4.3);
  - if `μ` stays positive there, the flip is not this pair's reordering: another station or
    another commitment switched.

**The replay** [measured, by the main line, cited; values over `2^24`]. The pair crosses, certain
at both ends. At the successor at `η = 1/2048` station 5 locks second by `55808` (about 20 cell
widths), so the margin moved from `+374272` to `−55808`: a change of `430080 = 2^12·3·5·7`, more
than `μ₀` over the step. Station 2's gap fell `203264` and station 5's rose `231936`. Under linear
motion the crossing lies at `731/840` of the step. No station is unranked at either state (0 of 64
refinements in each request). So `m7`'s flip is a crossing by the readings' first-order motion,
and `j_f ≥ j*` is consistent: a first-order rate large enough to move the margin by `430080` over
the step consumes `μ₀` before the step's end. The cut index `j_f` and the weighted count `M_w`
remain the main line's read.

## 5. The step law that follows

[agent-inferred; derived from `own_telescopes` (a jump only where a commitment switches), §1 (the
candidates are the carried states) and `margin_survives_moves`] Replace halving in `η` by stepping
on the cut index:

1. **Count the candidates.** List the cuts of the carried path up to the starting step size `η₀`: the
   progressions `((j − c)u − r_i)/d_i`. There are `N(η_start)` of them, about `η_start‖d‖₁/u`.
2. **Predict the wall.** Read the smallest certified margin and its first-order rate per coordinate,
   and take the cut index where it would be consumed. Read the carried state there, in one read.
3. **Locate the wall exactly.** If the commitments changed there, bisect on the cut index between
   the incumbent and that cut. This takes `log₂ N` reads and ends at two adjacent carried states:
   - the last before the wall, where the released and held code lengths agree (no jump), so strict
     descent is certified there by the existing first-order law;
   - the first after the wall, where the jump is read exactly.

   No state lies between them.
4. **Cross the wall as its own step.** Whether to cross is then the endpoint comparison of the
   release record: the jump is repaid or not by later steps.

Bisecting on the cut index resolves a wall to one coordinate move. Halving resolves it to a factor
of two in `η`. The reads number `log₂ N(η_start) ≤ log₂(η_start‖d‖₁/u + n)`, so the fixed number
of halvings and its `2^(−7)` range are no longer needed. Nothing here is built. The main line's
measurement (§7) decides whether the wall lies where the margins predict.

## 6. What the RH work contributes, and what does not fit

**What fits.**
- **The explicit formula's shape (§2).** A counting function equals a smooth term plus an
  oscillating sum over a spectrum. Here the spectrum is real and known, so the fluctuation bound
  needs no hypothesis. The zeta case is the hard one; ours is the trivial one. Nothing operational
  transfers back, but the reading is exact.
- **Farey cells (§4.1).** With integer rates and zero offsets, the carried path's cells are the
  helix's Farey cells. The RH criterion of Franel and Landau (atlas `rh.farey-unicity-fairness`,
  Lean owed) is about how evenly *all* fractions with denominators up to `N` are spaced. A
  direction's rates are a finite, arbitrary set and its offsets are not zero, so that equivalence
  does not transfer. The three-distance law is the part that applies.
- **Roots moving with a parameter (§4.3).** The multipliers of one monodromy move along `η` as
  roots of `det(μ − M(η))`. A double root is where a pair meets and separates, which is
  `rh.dbn-last-caustic`'s event for the zeros under the de Bruijn–Newman flow. The discriminant is
  the shared object.

**What does not fit.**
- **Level repulsion and GUE spacing.** Repulsion between eigenvalues comes from one self-adjoint
  operator (or, for zeta, from the heat flow's pair term, `rh.pair-inertia-rate`). A station is a
  tick of the receiving ring's clock, and a candidate is a class placed there. Each candidate's
  reading is the bank's growth with that class placed, so different candidates are read by
  *different* monodromies, independent matrices, none of them self-adjoint. Nothing makes the stations' margins avoid zero. Near-ties occur with positive
  density `p₀` at zero, and [derived; independent margins assumed] the smallest margin over `S`
  stations shrinks like `1/(S p₀)`. Repulsion with spacing density `∝ s²` would give `S^(−1/3)`
  instead; nothing here supplies it.
- **The laboratory's reading** "the zeros' GUE spacing is spectral precession" (`FORMULA.md`
  §XXVII) is graded recognition there and states no step or grain law. It is not used.
- **Choosing a step between crossing points.** The gap-selection lemma (`Zeta/ZeroGap.exists_gap`)
  finds a point away from a finite set. It is not needed: between cuts the state is constant, so
  any step in a cell is the same step.

## 7. What the main line measures

Along `m6`'s and `m7`'s directions:
- `‖d‖₁/u`, `n`, and the cut list in `(1/2048, 1/1024]` (for `m6`) and `(0, 1/2048]` (for `m7`);
- the commitments at each cut, which locates the wall by cut index;
- at the incumbent, the smallest station margin and its first-order rate per coordinate, to test
  `margin_survives_moves`'s prediction against the wall;
- for `m7`, request 3's pair (station 2 against station 5): the first-order rates `w_i`, the weighted
  move count `M_w(j)` at each cut, `j*`, and the flip's cut index `j_f` (§4b);
- the margins' distribution near zero over the requests' stations, which tests §6's prediction that
  near-ties are not repelled.

## 8. Owners

- Lean `HNN/CarriedCuts`: `floor_ne_iff`, `coordinate_changes_iff`, `coordinate_moves_lt`,
  `coordinate_moves_gt`, `moves_sum_lt`, `moves_sum_gt`, `margin_survives_moves`,
  `weighted_moves_le`, `margin_survives_weighted`.
- Rust (unchanged): `hnn::constitution::carried_entry` (the carried coordinate), `hnn::executed`'s
  `ladder_start` and `LADDER_DEPTH` (the halving law §5 would replace).
- Owed to #62:
  - the rounding composition as a Lean statement;
  - the three-distance law;
  - a segment bound on a read multiplier's rate away from a coalescence (the flip record's §3b).

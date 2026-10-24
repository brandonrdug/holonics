# The contacts are a sheaf, weight tying represents the words, and the square law is the scattering read

October 23. Refs #410, #73.

Brandon offered three papers and a list of disciplines to seed intuition:
- categorical deep learning as monad algebras on parametric maps (Gavranović et al., arXiv
  2402.15332);
- sheaf-theoretic multimodal alignment (Ghalkha et al., arXiv 2510.20540);
- homotopy invariants of learning dynamics (Tamim, arXiv 2510.04376);
- a list ranging from cellular sheaves and Fisher geometry to Mallat's scattering transform.

This record derives the lens and joins it to the owners it touches. It changes no plan item's law
or acceptance. Only the abstracts were read. Grades follow
[the epistemic grades](../../docs/canon/EPISTEMIC_GRADES.md).

## 1. The contacts are a cellular sheaf

[derived] The cellular sheaf is assembled from objects that already exist:

| sheaf | Holonics |
|---|---|
| stalks on the vertices | the participating Holons' states |
| stalk on an edge | a contact's comparison space |
| restriction maps | the contact charts (`v₋ = v₊ ∘ σ` in the helical code) |
| coboundary `δ` | the slip, `(δx)_e = F_(u⊴e) x_u − F_(v⊴e) x_v` |
| sheaf Laplacian `δᵀ W δ` | the contact material `M_contact = Σ w J*DJ`, summed over the contacts |
| Dirichlet energy | `Σ_e w_e Q_e`, the summed quadrance of the slips |

The cohomology reads as follows:
- `H⁰ = ker δ` holds the global sections: the states on which every contact agrees, which is
  where the contacts lock.
- `H¹ = coker δ` holds what cannot glue. The tower's three returns (unique, plural, obstructed;
  `Foundation/ContinuingTower`, `Foundation/GluingPassage`) are a section that is unique, a
  section with a nontrivial kernel, and a nonzero obstruction class.
- With invertible restriction maps (a connection sheaf), a global section exists exactly when
  the holonomy around each cycle fixes it. That is the Bombe's loop closure, and its gauge
  freedom is `cell_flux_is_gauge_free` (`Transport/CellHolonomy`).

Mutual loss is this Dirichlet energy. Its gradient moves both ends of every contact
(`DQ = 2J*Δ`). When the contacts carry declared offsets `b` (lock addresses), the energy is
`‖δx − b‖²_W`. Its minimum leaves the residual `b − δx*`, the projection of `b` off the image of
`δ`, which represents an `H¹` class: what each side keeps unresolved. SheafAlign's case against one shared embedding space, with a comparison space for
each pair instead, is the framework's refusal of a global frame or a global gradient.

## 2. Weight tying represents the words

[derived] A field whose cell `t` applies the move chosen by its symbol is an action of the free
monoid of words `Σ*` on its state. The encoding law `E T_a = U_a E` is a morphism of such actions:
equivariance, which is the paper's monad-algebra morphism. A field can read only what the image of
`Σ*` under its linear part keeps:

| linear part | image of the words | what a readout sees | owner |
|---|---|---|---|
| one `M` for every symbol | the length, `ℕ` | (symbol, lag residue) counts | `laggedRun_lag_residue` |
| commuting, chosen by the symbol | the symbol counts, `ℕ^Σ` | each entry transported by the counts of what followed it | owed (§5) |
| reflections in one plane | the dihedral group | parity and a signed phase sum | `plane_turns_commute` |
| non-commuting | the free monoid | order | the minimal realization, `E T_a = U_a E` |

The paper's "tensor product state preparation" is a matrix product state: the selected matrices
`A_(s_1) ⋯ A_(s_n)`, whose bond dimension is the Hankel rank of the amplitude. The repository
already owns that object read through `|·|²`: the Born face (`HNN/BornFace`), whose density is the
future-sufficient retained quotient (`born_state_future_sufficient`).

The Born face was measured negative on September 26
([record](2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) §2):
- its best register coded 4 + 3/16 bits a cell, against the tree's 3 + 10/16;
- its operators were deposited one cell at a time, by `G = 2(δ/T − 1/Z) A ρ` at the state as it
  stood.

[inferred] That covector does not locate an operator through what it did to the state over the
passage. The forward jet does, but for `χ × χ` operators it costs `χ⁴` per cell, against `K|Σ|`
for `K` scalar modes. Selective state-space models keep their transports diagonal for this reason
and take conjunction from a nonlinear read between levels. In the objects, that read is the tower
with a face between its levels (§4).

## 3. The homotopy of a learning path

[derived] The usable content is already a law. The loss `log R` keeps its winding branch, and the
winding of the ratio around zero is a homotopy invariant of the learning path. Two runs whose
ratios wind differently are not deformable into one another through ratios that do not vanish.
Persistence of minima reads as `tower.filtration-persistence`. The paper is single-author with
large empirical claims, so it is read as a lens only.

## 4. The square law is the scattering read

[derived] Each scalar mode `z' = λ_s z + β_s`, with `λ = r e^(iθ)`, is a causal damped resonator: a
complex wavelet at frequency `θ` and scale `1/(1 − r)`. A bank of such modes is a bank of
parametron rings.

- Reading a mode's face `|z|²` demodulates it, and passing the face on to a slower bank is Mallat's
  scattering cascade.
- The modulus is non-expansive and keeps the energy while moving it toward low frequency. The
  phase it drops is carried into the receiver's kernel, not annihilated (the dissolution account,
  record 2026-10-22 §5).
- A quadratic face reads `z_j z̄_k`, the relative phase between modes, and so pairs of past
  symbols.
- The elementary objects already place this read at the pump. No linear reading followed by a
  threshold reads a relative phase (`no_linear_threshold_reads_relative_phase`). The pump's
  monodromy carries it at second order (`reflection_mul_reflection`), and a bank of receiving
  parametrons at declared pump phases reads its class by its lock pattern (the square law,
  [objects](../../docs/ELEMENTARY_OBJECTS.md)).

[measured] The read is the design's diagonal modes (`K = 8`, turns chosen by the symbol, forward
jets, complex deposit) on the 2,027,360 base-four digits of the repository's own English (record
2026-10-22 §6.6), with η = 0.02 and ρ = 0.95. It is an exterior float read, and the quadratic face
is `a_c += zᴴ H_c z` with `H_c` Hermitian. "Alone" means online over the first 80% and held out
frozen; "with the tree" is prequential.

| face | alone, online | alone, held-out | with the depth-6 tree |
|---|---|---|---|
| none (tree alone) | | | 0.9286 |
| linear, K = 8 | 1.2710 | 1.3878 | 0.9221 |
| linear, K = 16 (record 2026-10-22) | 1.245 | 1.378 | 0.9205 |
| quadratic, K = 8 | 1.2163 | 1.3444 | 0.9196 |

What the table says:
- The square law on eight modes reads more than a linear read of sixteen.
- Joined with the tree it adds 0.009 bits a digit, against 0.0065 for the linear read.
- The tree still holds nearly all the conjunctions within six digits, and the field's reach
  beyond them is small at this width.
- The linear arm reproduces the earlier harness exactly (1.271 and 1.388), which checks the new
  harness.

## 5. The tree's second spectral placement: the passage tree

The design thread measured that diagonal modes add nothing once the receiving tree reaches depth 16
(0.614 against 0.613 bits a cell, GSM8K). It asked what a mode bank should carry that the tree
cannot.

**The bound.** Beyond a tree of depth `D` with context `C_t`, any read adds at most
`I(u_t ; u_(<t−D) | C_t)`. A mode splits as `z_t = N_t + λ^D z_(t−D)` with `N_t` a function of
`C_t`, so only the damped far part can add anything, and a shared read sees it mixed with `N_t`.
At `|λ| = 0.95` a cell the far share of a mode's energy is `|λ|^(2D)`: 0.19 at `D = 16` and 0.085 at
`D = 24`. The bank's memory, `1/(1 − |λ|) = 20` cells, sits inside the tree's horizon.

**The address.** In text, what the far past says given `C_t` is mostly the passage's own
statistics: this problem's names, numbers and units recur, and global counts dilute them. That is
a function of (context, next symbol), which a bank addressed only by the current symbol cannot
hold. A KT count `n(c, a)` is the `λ = 1` mode of the indicator `[context c, next a]`. The passage
term is the same indicator's mode at `λ = 1 − 2^(−m)`, a decayed count `l(c, a)` at every node.
This makes a two-by-two table:

| address | `λ = 1` | `|λ| = 1 − 2^(−m)` |
|---|---|---|
| the current symbol only | unigram counts | the design's diagonal bank |
| tree context | the tree | the passage tree |

In exact arithmetic the decay is a dyadic release with the residue carried
(`CarriedRelease.residueRun_conserves`); the plain floor silences counts below `2^m`
(`plainTransported_silences`). No routine looks up an earlier occurrence. Copying is what the
counts read when the passage repeats itself.

**Measurement.** The read is an exterior float read on the first 1,000 GSM8K training problems,
2,084,620 quarter-character cells, scored before each cell is counted. The tree is context-tree
weighting over depths `0..D`, one tree per frame phase, with each node's estimator
`q(a) = (c_a + ½)/(C + 2)`. The plain tree has `c = n`, and the passage tree has `c = n + w·l`. The
control uses a horizon of `2^24` cells, longer than the passage, so `c ≈ (1 + w) n`: the same
sharpening of the estimator with no locality.

| arm | `D = 16` | `D = 24` |
|---|---|---|
| plain tree | 0.5700 | 0.5553 |
| control, `w = 4` (the best control) | 0.5487 | 0.5288 |
| passage tree, horizon `2^13`, `w = 16` | 0.5139 | 0.5003 |
| passage tree, horizon `2^13`, `w = 64` | | 0.4922 |

- Over the best control, the passage tree gains 0.035 bits a cell at `D = 16` (`w = 16`) and
  0.037 at `D = 24` (`w = 64`), 6 to 7%.
- The gain holds through the passage: in the last quarter, 0.4543 against 0.4921 at `D = 24`.
- A horizon of `2^13` cells (about 2,000 characters, four problems) beats `2^11` (0.5019) and
  `2^15` (0.5068) at `D = 24`.
- The weight is not bracketed: 16, 32 and 64 give 0.5003, 0.4937 and 0.4922.
- The horizon and weight were chosen over 17 arms on the same online run. In the machine they are
  located by deposition, not taken from this grid.
- This tree is weaker than the design's own (0.533 and 0.507 at `D = 16` and `24` on the design's
  rendering of the same 1,000 problems). How much of the gain survives on that tree is not
  measured.

## 6. The tower driven by the face's news, and where the code goes

The design built the passage tree natively and measured 0.507 to 0.469 bits a cell at depth 24
(their record of October 23 on GSM8K). It then asked for the move law of a level driven by the
face's news.

**The drive.** A level above the face `p` receives the face's cokernel, never its own read. Two
drives are covectors of the face:
- the news `e_t = [u_t] − p_t`, the covector of the face's logits;
- the centred surprise `c_t = −ln p_t(u_t) − H(p_t)`, the covector of the face's temperature: for
  `p_τ ∝ p^τ`, `d/dτ (−ln p_τ(u))` at `τ = 1` is `c_t`, and the second derivative is
  `Var_p(ln p)`.

When `p` is the true conditional of the whole past, both are martingale differences: their
conditional mean is zero, so no read of them can lower the expected code. Whatever a level driven
by them reads is the face's error against the full past, never a second copy of the tree.

**The move.** `z_k' = λ_k z_k + e_t` and `y_k' = μ_k y_k + c_t`. The drive does not depend on the
pole, so the proved forward jet `J' = λJ + z` (§2c of `Geometry/ScrewTorsion`) is exact. A drive
taken from the level's own joined face would depend on the pole and lose that, which is the
reafference the design already met in generation.

**The placement.** At a zero read, the code's gradient for a mode at pole `λ` is
`g(λ) = Σ_(j≥0) λ^j R(j + 1)`, with `R(τ)` the covariance of the drive with itself `τ` cells later.
The first-order gain is `½ g(λ)ᵀ H⁻¹ g(λ)`, with `H` the Fisher term (`Var_p` for logits,
`Var_p(ln p)` for temperature). So the poles go where the drive's lagged covariance is large, and
`R` is measured before a bank is built.

**Measurement.** These are exterior reads over the passage tree of §5 (depth 24, horizon `2^13`,
`w = 64`), on the same 1,000 problems. The reads use six real poles at horizons `2^2` to `2^12`.
The weights are the Newton point of the quadratic model at the face over the past, solved before
each cell is scored.

| lag (cells) | 1 | 4 | 16 | 64 | 256 | 1024 | 4096 |
|---|---|---|---|---|---|---|---|
| news correlation | −0.003 | −0.006 | 0.005 | 0.003 | 0.005 | 0.001 | 0.001 |
| surprise correlation | 0.022 | 0.020 | 0.013 | 0.006 | 0.007 | 0.004 | 0.003 |

- The face's news is white at every lag up to 4,096. A bank on the news, read into the logits,
  gives 0.4918 against the face's 0.4922.
- Surprises cluster weakly. A bank on the surprise, read as temperature, gives 0.4909, and both
  together give 0.4906: 0.3% overall and 0.7% in the last quarter (0.4512 against 0.4543).
- The bound holds: past the tree and passage tree, moments of the face's cokernel carry almost
  nothing on this text.

**Where the code goes.** Each byte's code length (the sum of its four cells) is grouped by the
byte's role in the problem's own markup:

| role | bytes | plain tree, bits a byte | passage tree, bits a byte | share of the passage tree's code |
|---|---|---|---|---|
| question prose | 229,587 | 2.284 | 2.148 | 48.1% |
| answer prose | 212,594 | 2.012 | 1.595 | 33.0% |
| digits in answer prose | 17,304 | 3.683 | 3.379 | 5.7% |
| calculator markup (`<<`, operators, `=`, `>>`) | 19,869 | 1.686 | 1.669 | 3.2% |
| calculator operand digits | 12,611 | 2.909 | 2.446 | 3.0% |
| question digits | 5,667 | 4.291 | 4.381 | 2.4% |
| calculator result digits | 7,122 | 3.130 | 3.205 | 2.2% |
| digits repeating the result after `>>` | 7,122 | 1.612 | 1.423 | 1.0% |
| final answer digits | 2,279 | 3.344 | 2.990 | 0.7% |

- The passage tree's gain is mostly in the answer's prose and operands, which reuse the question's
  words and numbers.
- A result digit costs 3.2 bits, near `log₂ 10 = 3.32`: the tree does not compute the arithmetic.
- A digit repeating the result after `>>` still costs 1.4 bits, where a copy would cost almost
  nothing. The tree copies a number only when it has met that exact number in that context.

So past the tree, the code that can still fall is in relations between cells, not in moments of
the past: an equality between a cell and a located earlier cell (the repeat, the operands, the
answer's restated numbers), and the arithmetic of the results. A moment bank cannot hold them. By
the lag-residue factorization, a bank reads lagged counts, and recovering one particular earlier
value from them takes a register as long as the lag. A located equality is a pair contact whose
offset is a key located by loop closure.

## 7. The receiving tree's width is set by its tolerance once its ratio is released

The design thread reported that the receiving tree's exact width rule refuses past `2^21` cells:
a population of `2^22` to `2^24` asks for operands of 129 to 133 bits at every depth, so the first
1,000 problems are its ceiling and the full GSM8K partition cannot be carried.

**Where the widths come from.** The rule in `compression::landmark::context` certifies that the
executed tree stays within a quarter grain a cell of the *unreleased* ideal mixture. A node's
drift from that ideal is summed over its arrivals (`weight_log_lipschitz`), so the carrier and the
face lattice must hold `n* P²` rounding units: `2^W ≥ 12 B L_R (2n* + 1) P²` and
`2^(M_p) ≥ 3 B L_R K (n* P² + 2P + 1)`. The passage length `n*` enters every width. The ideal ratio
itself grows with the passage: in the exterior read below, `|log₂ β|` reaches 67,164 bits on 100
problems and 720,805 bits on 1,000. Its exact carrier would be as wide as the passage's code.

**The telescope.** [derived] At a node with its own face `e`, its children's face `k` and the
ratio `β`, the conditional is `q(u) = (β e(u) + k(u))/(β + 1)` and the step is
`β' = β e(u)/k(u)`. Then `1 + β' = (1 + β) q(u)/k(u)` and `1 + 1/β' = (1 + 1/β) q(u)/e(u)`, so for
any release `β_(t+1) = R(β'_t)`:

```text
Σ_t −ln q_t = Σ_t −ln k_t + ln(1 + β_0) − ln(1 + β_n) + Σ_t [ln(1 + β_(t+1)) − ln(1 + β'_t)]
Σ_t −ln q_t = Σ_t −ln e_t + ln(1 + 1/β_0) − ln(1 + 1/β_n) + Σ_t [ln(1 + 1/β_(t+1)) − ln(1 + 1/β'_t)]
```

It holds for the executed faces and the executed ratio, with no ideal to track. (In
`compression::landmark::context` the node's own KT face is named `k` and the child's face `x`, so
`q = (βk + x)/(1 + β)` and `β' = βk/x`: this section's `e` is the code's `k`, and this section's `k`
the code's `x`.) Release the
ratio into `[2^(−K), 2^K]` on a mantissa of `w` bits:
- a release at the upper bound costs at most `log₂(1 + 2^(−K))` bits against `e`, the face the ratio
  favours, and nothing against `k`; the lower bound mirrors it; a rounding costs at most
  `2^(−w) log₂ e` against either;
- so at every node, `code_q ≤ min(code_e, code_k) + 1 + Σ_t (log₂(1 + 2^(−K)) + 2^(−w) log₂ e)`;
- over any stretch of the passage the boundary terms are at most `log₂(1 + 2^K) ≤ K + 1` bits, so
  the released node tracks the better of its two faces stretch by stretch, paying at most `K + 1`
  bits a switch, which the unreleased node cannot (its ratio must first unwind what it gathered).

Each term is one cell's. Along a cell's path of `P` nodes and `B` digits, the excess over the
released law is at most `B P (log₂(1 + 2^(−K)) + 2^(−w) log₂ e)` plus the face lattice's own
rounding, a cell at a time. So `K` and `w` are set by the grain alone, `2^K, 2^w ≈ 12 B L_R P`, and
the face lattice needs `log₂ K_kt` bits for the KT floor `1/(2n* + 2)` plus the same grain term:
the passage enters once, through the count, never through `n* P²`. [agent-inferred] At `B = 2`,
`L_R = 16` and `P = 24`, `12 B L_R P = 9,216 < 2^14`; with `n* = 2^24` the β step's product is near
`2·14 + 25 + 38 + 1 = 92` bits, under `u128` with no carrier rebase.

The release is the carried-release law at a node's ratio: the part of `ln β` past `K ln 2` is
released at the declared tolerance, its cost accounted cell by cell in the telescope. Nothing a
cell can still distinguish at the receiver's grain is lost: past `2^K`, the weaker face's share of
`q` is below `2^(−K)`.

**Measurement.** The exterior read of §5 rewritten in the ratio form (`ctw_beta.rs`), one tree per
frame phase, on the same 1,000 problems:

| ratio released at | `D = 24`, plain | `D = 24`, passage (`2^13`, `w = 64`) |
|---|---|---|
| never | 0.5553 | 0.4922 |
| `2^32` | 0.5553 | |
| `2^16` | 0.5544 | 0.4902 |
| `2^12` | 0.5538 | |
| `2^8` | 0.5624 | |

- Unreleased, the ratio form reproduces the joint form exactly (0.6903 against 0.690 on 100
  problems, 0.5553 on 1,000).
- Released at `2^12` to `2^16` it codes slightly better than unreleased, the tracking above; at
  `2^8` the release begins to cost.
- At `D = 16`, released at `2^16`: 0.5691 against 0.5700.

**The whole training partition.** The design asked what more data buys before the owner changes.
The partition's 6,726 training problems in index order, each as question, newline, answer and a
blank line (the design's rendering: 2,078,532 cells for the first 1,000 problems, 14,112,672 for
all), at `D = 24`:

| problems | cumulative, released at `2^12` | the block's own code, released | cumulative, unreleased |
|---|---|---|---|
| 100 | 0.6888 | 0.6888 | 0.6907 |
| 1,000 | 0.5529 | 0.5371 | 0.5544 |
| 2,000 | 0.5191 | 0.4856 | 0.5205 |
| 3,000 | 0.5039 | 0.4725 | 0.5053 |
| 4,000 | 0.4921 | 0.4584 | 0.4934 |
| 5,000 | 0.4840 | 0.4516 | 0.4852 |
| 6,000 | 0.4780 | 0.4483 | 0.4792 |
| 6,726 | 0.4742 | 0.4430 | 0.4754 |

- More data keeps paying: the whole partition codes 14% below the first 1,000 problems, and its
  last 726 problems code 0.4430, 18% below the 1,000-problem block.
- The release holds its small gain at every scale (0.0012 bits a cell at 6,726 problems), while
  the unreleased ratio reaches `|log₂ β| = 5,169,736` bits.
- The tree has 11,945,309 nodes at the end, and the run's peak was 1,020 MiB.

So the receiving tree can carry the whole partition at fixed widths, if its certificate is the
released law's per-cell telescope instead of the tracking of the unreleased ideal. The
receiving tree's owner decides; this read changes no crate.

## 8. The located equality: a copy is a pair contact whose offset is a key

§6 left the code in relations between cells. The design asked for the first of them as an exact
law at the receiver's face: how a located offset's prediction joins the face, and its certified
step.

**The contact.** [derived] A located equality is a pair contact between the present cell `t` and an
earlier cell `r = t − δ` of the same passage. Its slip is `[u_t ≠ u_r]`, and it holds while the two
agree. The offset `δ` is its key. A run of `ℓ` held contacts at one offset closes `ℓ` squares: the
passage step from `r` to `r + 1`, the step from `t` to `t + 1`, and the two contacts between them.
So a held offset is a loop-closure constraint, and it is located from the menu of contacts, never
supplied.

**Locating the key.** The passage tree already keeps, at each node, the time of its last visit
(its lazy decay's `tl`). The deepest node on the present cell's path with an earlier visit names
the longest context that has recurred, and its last visit `r` gives `δ = t − r`. Nothing new is
needed to locate it.

**Two placements of the same contact.**
- *Node lock.* The prediction `ĉ` is the cell that followed the deepest node's last visit. This is
  the node's indicator at `λ = 0`, the last occurrence, beside `λ = 1` (the tree's counts) and
  `λ = 1 − 2^(−13)` (the passage): one more spectral placement of the node's own past, two bits a
  node, with nothing of the passage kept.
- *Held lock.* `δ` is held while its contact holds, and `ĉ = u_(t−δ)`. At a slip the offset is
  released and located again. It follows one occurrence past the tree's depth, so it reads the
  cell `δ` back. By the lag-residue factorization (§6) no moment bank recovers that cell: it needs
  the passage's own cells within the lock's reach, which is the strand the retention law refuses.

**The join at the face.** [derived] With the face `q(c)·2^(w(c))` that the passage weight already
uses, the lock adds one exponent:

```text
F(c) ∝ q(c) · 2^(w(c) + α_b [c = ĉ])
```

`α_b` is held per bin `b`: the octave of the lock's run (the count of closed squares) and the
locating depth by fours. In octaves:

```text
∂/∂α_b (−log₂ F(u)) = F(ĉ) − [u = ĉ]
∂²/∂α_b² (−log₂ F(u)) = ln 2 · F(ĉ)(1 − F(ĉ)) ≤ (ln 2)/4
```

The first is the news of the declared comparison on the contact's own feature, the same covector
as the face's (§6). The step is the passage weight's Newton step on the cumulative curvature, with a
prior of 1 [agent-inferred]:

```text
H_b ← H_b + F(ĉ)(1 − F(ĉ))
α_b ← α_b − (F(ĉ) − [u = ĉ]) / (ln 2 · (1 + H_b))
```

**The certificate.** [derived] The cell's code is convex in `α_b` with curvature at most
`L = (ln 2)/4` everywhere, so a step `s g` along its covector `g` gives
`ℓ(α − s g) ≤ ℓ(α) − s g² (1 − L s/2)`. The step length is `s = 1/(ln 2 (1 + H_b)) ≤ 1/ln 2`, so
`L s/2 ≤ 1/8` and the stepped weight codes the cell that produced the covector at least
`(7/8) g²/(ln 2 (1 + H_b))` bits better, strictly unless `g = 0`. Stepped jointly with the passage
weights, the curvature is the block Fisher matrix `Cov_F` of the features, which is positive
semidefinite, so the joint Newton direction descends.

The contact names no modality. Wherever a passage repeats at a fixed relative phase, a recurred
context locates the offset: a translation in an image, a period in sound, a repeated screw word in
motion.

**Measurement.** The exterior read of §7 (`D = 24`, ratio released at `2^12`, passage `2^13` with
`w = 64`) as the base, each lock joined beside it (`lock.rs`), online, bits a cell:

| | base | node lock | held lock | node lock, depth bins only | held lock, depth bins only |
|---|---|---|---|---|---|
| first 1,000 problems | 0.4886 | 0.4692 | 0.4640 | 0.4722 | 0.4713 |
| whole partition, 6,726 problems | 0.4274 | 0.4147 | 0.4070 | 0.4174 | 0.4134 |

- A lock predicts at every cell after the first, and its prediction is right at 85% to 87% of
  cells.
- On the whole partition the node lock codes 3.0% below the base, and the held lock 4.8%.
- On the whole partition the run, the count of closed squares, carries 0.0027 bits a cell of the
  node lock's 0.0127 and 0.0064 of the held lock's 0.0204. The rest is the locating depth.
- The held lock's extra over the node lock is 0.0077 bits a cell on the whole partition. That is
  what a lawful realization of a held offset would have to earn.

By role, on the first 1,000 problems, bits a byte:

| role | bytes | base | node lock | held lock |
|---|---|---|---|---|
| question prose | 226,988 | 2.139 | 2.083 | 2.065 |
| answer prose | 212,664 | 1.580 | 1.466 | 1.447 |
| digits in answer prose | 17,379 | 3.365 | 3.366 | 3.362 |
| calculator markup | 19,800 | 1.675 | 1.585 | 1.549 |
| calculator operand digits | 12,625 | 2.431 | 2.451 | 2.407 |
| question digits | 5,658 | 4.338 | 4.540 | 4.521 |
| calculator result digits | 7,118 | 3.199 | 2.976 | 2.903 |
| digits repeating the result after `>>` | 7,118 | 1.398 | 1.162 | 1.100 |
| final answer digits | 2,283 | 2.964 | 3.113 | 2.996 |
| separators | 3,000 | 1.754 | 1.625 | 1.584 |
| `####` marker | 5,000 | 0.485 | 0.549 | 0.542 |
| all | 519,633 | 1.954 | 1.877 | 1.856 |

- Most of the gain is in prose: the answer restating the question's words.
- The repeat after `>>` falls from 1.40 to 1.10 bits, still far from a copy's near-zero cost. Its
  first digit costs 0.94 and the following digits 1.23. The deepest recurred context there is the
  markup of an older calculation, so the located offset points at an older result. The repeat's
  true offset is the result's own length plus two, a relation of the markup that context
  recurrence does not locate.
- New numbers in the question cost more under a lock (4.34 to 4.52 bits). There a confident copy
  is wrong, and the bins cannot see that a number is new.

So the node lock is the contact to build now: it is a placement of the passage tree's own node, it
needs no strand, and it carries most of the gain. The receiving tree's owner decides; this read
changes no crate.

## 9. Owed (#410)

- The summed contact material is the sheaf Laplacian: `Σ_e w_e J_e*DJ_e = δᵀ W δ`, its kernel the
  global sections, and the tower's obstruction the cokernel of `δ`, at the contact and tower
  owners.
- Commuting selected moves see only symbol counts: with linear parts that commute, each entry
  `β(u_t)` reaches the state transported by `∏_a λ_a^(n_a)`, with `n_a` the count of `a` after
  `t` (`Finset.prod_comp`).
- The face's two covectors: for `p_τ ∝ p^τ`, `d/dτ (−ln p_τ(u)) = −ln p(u) − H(p)` at `τ = 1`, with
  second derivative `Var_p(ln p)`; and under the true conditional, the news and the centred
  surprise are martingale differences, so no read of them lowers the expected code (Gibbs).

- The released ratio's telescope: for a mixture `q = (β e + k)/(β + 1)` with step `β' = β e/k` and
  any release `β_(t+1) = R(β'_t)`, `Σ −ln q = Σ −ln k + ln(1 + β_0) − ln(1 + β_n) +
  Σ [ln(1 + β_(t+1)) − ln(1 + β'_t)]` and its mirror in `e`; with `R` the clamp to `[2^(−K), 2^K]`,
  each release costs at most `ln(1 + 2^(−K))` on one line and nothing on the other.
- The located equality's certified step: for `F(c) ∝ q(c) 2^(w(c) + α[c = ĉ])` the cell's code
  `−log₂ F(u)` has derivative `F(ĉ) − [u = ĉ]` and second derivative `ln 2 · F(ĉ)(1 − F(ĉ)) ≤ (ln 2)/4`
  in `α`, so a step of length `s ≤ 1/ln 2` along that covector lowers the cell's code by at least
  `(7/8) s g²`.

## Receipts

- [`quad_field.py`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/quad_field.py),
  output [`quad_field.txt`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/quad_field.txt).
- A development read on 200,000 cells measured at most 114.38 µs a cell (the quadratic face with
  the tree, three runs together). The projection was 232 s and the deadline 240 s.
- The three full runs went together, one thread each: 110.9 s, 176.2 s and 228.3 s, all at 48 to
  49 MiB peak. The ratio of measured to projected for the slowest run is 0.98.
- [`passage_ctw.rs`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/passage_ctw.rs)
  (built with `rustc -O`), the rendering
  [`render_gsm8k.py`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/render_gsm8k.py),
  and every arm's output in
  [`passage_ctw.txt`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/passage_ctw.txt).
  The rendering is `question\nanswer\n` a problem, 153 bytes longer over 100 problems than the
  design's.
- A development read on 100 problems measured at most 12.74 µs a cell, at `D = 24`. Allowing twice
  that for the larger table, the projection was at most 53 s a run, and the deadline was 60 s a run.
  Runs went four together, one thread each. The slowest took 28.0 s (ratio 0.53), with a peak of
  489 MiB.
- [`tower.rs`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/tower.rs), output [`tower.txt`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/tower.txt). A development read on 100
  problems measured at most 22.29 µs a cell. With the measured table growth of 1.054 the projection
  was 49 s and the deadline 60 s; the run took 45.6 s (ratio 0.93) at 489 MiB.
- [`passage_bytes.rs`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/passage_bytes.rs) writes each byte's code length;
  [`classify.py`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/classify.py) groups it by role, output [`classes.txt`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/classes.txt). The
  two runs went together (projection 28 s, deadline 60 s; 25.1 s and 27.8 s at 490 MiB).
- [`ctw_beta.rs`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/ctw_beta.rs) (built with `rustc -O`), output
  [`ctw_beta.txt`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/ctw_beta.txt). Development reads on 100 problems took at most 5.20 µs a
  cell. The projection used the larger 13.34 µs measured for `passage_ctw` on 1,000 problems, with a
  tenth for growth: 31 s a run, deadline 60 s a run, four together on four cores. The runs took
  8.8 s to 13.5 s (ratio 0.44 for the slowest) at 433 MiB.
- [`render_partition.py`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/render_partition.py) renders the partition that
  `tools/gsm8k/partition.py` writes from the public `train.jsonl`;
  [`ctw_beta_full.sh`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/ctw_beta_full.sh), output
  [`ctw_beta_full.txt`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/ctw_beta_full.txt). The projection was 5.38 µs a cell (the
  largest plain read on 1,000 problems) to half as much again for the larger table: 76 s to 114 s a
  run, deadline 120 s, two together. Both took 64 s (ratio 0.56 to the upper end) at 1,020 MiB,
  against about 4.5 GB projected for 29 million nodes; the partition has 11.9 million.
- [`lock.rs`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/lock.rs) (built with `rustc -O`), outputs
  [`lock_1000.txt`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/lock_1000.txt) and [`lock_full.txt`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/lock_full.txt), each with its
  `LOCK_NO_RUN=1` control. In the program's output the held lock is named the ring lock. The
  1,000-problem reads took 9.3 s and 9.2 s at 437 MiB, at most 4.50 µs a cell; they set the
  whole-partition projection.
- [`lock_full.sh`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/lock_full.sh) ran the whole partition: projection 64 s to 95 s a run (4.50 µs
  a cell to half as much again for the larger table), deadline 120 s, about 1.1 GB a run, two
  together. They took 66.6 s and 62.8 s (ratio 0.70 to the upper end) at 1,020 MiB.
- [`classify_partition.py`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/classify_partition.py) and
  [`repeat_split.py`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/repeat_split.py) group each byte's code by role, from the per-byte code
  `lock.rs` writes with its sixth argument; output
  [`lock_roles_1000.txt`](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ_receipts/lock_roles_1000.txt).
- No Rust or Lean in the crates or the Lean package changed.

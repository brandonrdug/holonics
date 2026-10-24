# What a contact cannot bridge is its effective tension, and the tension founds the face that carries it

Refs #404 #405 #410. Follows [faces read on cycles](2026-10-24_FACES_ARE_READ_ON_CYCLES_A_FACE_IS_A_COHOMOLOGY_CLASS_THE_CARRY_IS_ITS_BOCKSTEIN_AND_FRICTION_KEEPS_ONLY_THE_HARMONIC_PART.md)
and [the one face law](2026-10-24_ONE_FACE_LAW_A_FACE_IS_A_CONGRUENCE_SO_LANGUAGE_ARITHMETIC_AND_ANY_OPERATION_ARE_READ_BY_ONE_CONTACT.md),
and answers the design thread's request for the tower's learning step
([`hnn::tower`](../../crates/holonics/src/hnn/tower.rs)). Status:
- the laws are proved-standard: the normal equations, the Schur complement and its quotient
  formula, partial regression, Wirtinger calculus;
- the checks are exact;
- the tower readings in §3 to §8 are [definition; agent-inferred, October 24].

Brandon's lens (paraphrased, October 24): exhausting candidates may find hidden information, which
is why the machine needs the principles of automatic differentiation. He asks it to gauge a
difference relativistically from its own first-person place: to ask why an arrival does not make
sense and how to bridge the gap, as cryptanalysis does. More text helps only in the way a person
meets one subject presented many ways across texts and resonates with some presentations.

## The failure this answers

The pair-contact tower trained on 1,789,116 bytes of the Holonics text still leaves its medium
within a line or two when it writes, and eight times the text did not change that
([the tower record](https://github.com/brandonrdug/holonics/blob/3ededae82/research/records/2026-10-24_THE_TOWER_HEARS_THE_HOLONICS_TEXT_AND_EVERY_LOOK_IS_READ_BY_ITS_LOCK.md),
"Eight times the text"). On held-out Rust, looking again falls on 136 of 204 lines. The design
thread reports that 100 redraws from one moment at `=` on the PC never found the right answer. The
tower's step compares `δz = p̂ − [· = u]` (real), returns it inside a 128-byte section and deposits
every section under the reread certificate. Volume is not the cause. This record locates what the
step throws away and what it would take to keep it.

## 1. The bridge and the tension at a contact

Take any block of the tower that reads a face `f_t` with material `W` (the readout `U`, a contact's
drive, a push), and let `t_t` be the comparison's covector arriving at its output, over the cells
`t` of a section with declared weights. Write `f̄ = (f, 1)` (the face law's constant block) and keep
the joint Gram of face and covector:

```text
H = Σ f̄ f̄ᵀ        B = Σ t f̄ᵀ        T = Σ t tᵀ
```

`B` is today's gradient of the block's material. Then:

- **The bridge.** What a move of this block's material can produce from the present face is
  `B H⁺ Bᵀ`: the explained part of the normal law `W H = B` (`learn.normal-law`,
  `hnn.exogenous-normal-law`).
- **The tension.** What it cannot produce is the Schur complement

  ```text
  S = T − B H⁺ Bᵀ = min_W Σ_t |t_t − W f̄_t|²  ⪰ 0
  ```

  the covector's covariance that the face does not explain. The repo already owns this object as
  the effective tension (`rh.conditioned-effective-tension`): eliminating the face block, the
  interior that relaxes when the material moves, leaves the effective tension on the covector, the
  same elimination as the Dirichlet-to-Neumann map (`tube.dn-elimination`).
- **The step never sees it.** The remainder `r_t = t_t − B H⁺ f̄_t` is orthogonal to every face,
  `Σ r_t f̄_tᵀ = 0`, so `B` is the gradient of the fitted part alone. Any step built from `B`
  carries none of the remainder. This is what `Jᵀ` discards at a block, and today it is discarded
  every section.
- **It is frame-free.** An invertible rebase of the face, `f̄ ↦ A f̄`, leaves `S` unchanged: `S`
  depends only on what the face separates, never on its chart. The comparison is gauged in the
  receiver's own frame without depending on that frame's axes.

A block's adjoint also passes `Wᵀ t` to its face, so part of a block's tension can be bridged by a
move upstream that changes the face. The block's `S` therefore bounds from above what the whole tower
cannot bridge with its present faces. What no block can bridge with any face is the floor: the
frustration, whose least energy on a locked sheet is twice the frustration less the edges
(`holon::parametron`, `the_least_locked_sheet_energy_is_twice_the_frustration_less_the_edges`).

## 2. Where the tension lives

In `(H, B, T)`: three sums over the section's cells, with no cell kept. They are the normal law's
sufficient statistics (`learn.normal-law`; `standing.statistical-sufficiency`), so the tension is a
quotient and never a tape or a log of fluxes. On the tower's grains they are integer numerators:
- a face on `2^(−16)` and a covector on `2^(−24)` give `H` on `2^(−32)`, `B` on `2^(−40)` and `T` on
  `2^(−48)`;
- each widens at its declared crossing as every other tower sum does;
- integer addition is associative, so the eight streams' sums, and the sections' sums, add in any
  order to the same bits.

At the readout, `H` is 65 × 65 and `T` 256 × 256. `H⁺` is formed only when the tension is read.
Read it at one constitution, on a reread pass with the material held: the retention law reads a
comparison through the contemporary constitution, and sums taken while the material moves mix
constitutions. Nothing in the tension is released below a grain, so the carried release
(`release.carried-residue`) applies only where a founded material (§5) is released onto the
material's `2^(−24)`: its residue is carried, never rounded away
(`release.plain-rounding-annihilates`).

## 3. What the tension reads: four-cycles at merged faces

Two cells that one face merges, asked `a` and `b`, leave
`S = ½ [[1, −1], [−1, 1]]` on those two classes: `S_ab < 0`, the face law's four-cycle
`[cell 1, a] + [cell 2, b] − [cell 1, b] − [cell 2, a]` (`contact.face-table-blocks`). In general the
most negative off-diagonal entries of `S` name the classes in tension at faces the block merges.
This is the contradiction of the Bombe's menu: a loop of contacts that does not close at the present
key. In the cycles record's terms it is the part of the slip that no local deposit bounds.

The tension is the masked part of the present face (`standing.masked-or-erased`): a difference the
present face does not separate and a future face may. A face that separates the opposed cells is a
separating word (`series.difference-separator`), and reading it reopens the merge.

For the tower: at a line start, the short context is nearly the same in prose, Lean and Rust, while
the next bytes differ by medium. If the faces merge the media there, the opposed covectors cancel in
`B`, the step learns their mixture, and the writing drifts between media. That is the expected
reading [agent-inferred]; §7 fixes how it is read.

## 4. Resonance needs no weight

Any step built from `B` deposits only the bridgeable part, and a presentation whose difference is
all remainder deposits nothing already. So resonance with some presentations is the projection
itself, not a weight on the deposit. The normal law's own step `B H⁺` moves exactly the bridgeable
part in the face's metric; today's step moves along `B` in the covector moments' metric. Both leave
the remainder behind. The new thing is keeping it.

Many presentations help in one way. A distinction that is consistent across presentations makes
its candidate's cross moment with the remainder grow with the number of cells, while a chance
correlation does not grow against the candidate's own residual Gram. With `S` discarded every
section, more text only adds discarded remainder, which agrees with eight times the text changing
nothing [agent-inferred; the reading in §7 tests it].

## 5. The tension founds the face that carries it

Let `c_t` be a face that the block does not read. Keep its moments beside the block's:

```text
K = Σ t cᵀ        L = Σ f̄ cᵀ        C = Σ c cᵀ
M = K − B H⁺ L    (the remainder's cross moment with c's residual)
Q = C − Lᵀ H⁺ L   (c's residual Gram)
```

Reading `c` beside `f` removes exactly `M Q⁺ Mᵀ` of the tension: the Schur complement of the joint
regression on `(f̄, c)` is `S − M Q⁺ Mᵀ`, by the quotient formula for Schur complements (partial
regression). The founded material is `M Q⁺`: the remainder's own regression on `c`'s residual. So
the remainder chooses both which face to read and the material it reads it with, from moments
alone, with no enumeration of keys and no medium label.

The tower's candidate faces are its own:
- the quadrature `Im(C h)`, the half of each mode's face that `Re` discards (`learn.parametron-real-chart`:
  the imaginary phase stays in the reconstruction fibre; `parametron.perceptron-is-a-face`);
- the other level's face, and the held modes read at another level;
- the lap count, once modes carry their windings (the cycles record, §8).

A candidate founds as a pair contact's second drive keyed on `c`, opened at `M Q⁺`, when the reread
certificate shows the section codes fewer bits under it by more than the drive's own description
length. Code length decides founding, as it does for units. A candidate with `M = 0` leaves the
tension where it is: dormant, a lock waiting for a key. Nothing here is catered: the candidates are
the tower's own faces, and a medium label, where it is used at all, is used only by an exterior
reader.

## 6. The phase part, read in the first person

The tower's readout row reads `y = C h` and keeps `r = Re y`, so its face has a phase that the read
discards. The comparison read in the tower's own frame is a ratio of two states of that face:

```text
Ē   = Σ_a p̂(a) E(a)                       the arrival the tower expects at its own receiving face
y_H = C (λh + γ B Ē)                      the face its expectation would make      φ_H = arg y_H
y_T = C (λh + γ B E(u))                   the face the true byte makes             φ_T = arg y_T
R   = y_T / y_H,   log R = log|y_T / y_H| + i (φ_T − φ_H + 2πn)
```

(For a pumped mode the reflection `β conj(h)` is common to both and stays in each. Above the first
level the expected arrival passes through the contacts, and this holds to first order.)

To first order, `log R = ν / y_H` with `ν = y_T − y_H = −γ C B E δz`. So the phase part is today's
covector `δz` read through the tower's own receiving loop `C B E` and divided by where the tower
stands. It is formed only through the readout `U` today, which is why its phase part is absent. `R`
does not change when a readout row is turned, `C ↦ e^(iα) C`, while `Re(C h)` does. A turned row can
merge two arrivals that another turn separates. Descent on `½ |log R|²` moves `y_H` along
`log R / conj(y_H)`; its gradient is `−log R / conj(y_H)`, with modulus and phase weighted equally
by the cylinder chart of `log`. The target side is read, the produced side moves, and the real part
stays beside it. A deposit that moved both sides could lower `|log R|` by making the pushes
`B E(a)` alike, so the spread of `B E(a)` over the classes is reported as the foil against that
collapse.

Summed over a line, the phase parts accumulate a turn whose whole part is the winding `n`. Carried
with its fractional residue, that is the lap beside the phase (`release.carried-residue`; the cycles
record, §8).

## 7. Checks, and the reading the tower can run now

`tension.py` (exact fractions), outputs in `tension.json`:

- **A.** Six cells, a face of two coordinates and the constant, three classes, `p̂ = (½, ¼, ¼)`:
  `S` equals the least residual's Gram; the remainder is orthogonal to every face; the gradient of
  the fitted part equals `B`. `tr T = 17/4`, bridged `1695/644`, tension `521/322`.
- **B.** Two merged cells asked `a` and `b` at `p̂ = (½, ½)`: `S = [[½, −½], [−½, ½]]`, the
  four-cycle.
- **C.** Eight line starts under one face, two media: medium P asks `0, 0, 0, 2` and medium L asks
  `1, 1, 1, 2` (class 2 shared), at the merged optimum `(3/8, 3/8, 1/4)`.
  - Tension `tr S = 21/4`, with `S_01 = −9/8`: the two media's opening classes oppose.
  - A held mode carrying the medium removes `9/4`; its founded material is `(−3/8, 3/8, 0)`. The
    `3` left is the within-medium floor (text against a blank line).
  - A face carrying half the medium removes `2`.
  - An alternating face unrelated to the medium still removes `3/4` by chance on eight cells, which
    is why code length decides founding.
  - In every case the drop equals the joint regression's.
  - At the optima, the product of `p̂(true)` is `729/4194304` merged and `729/65536` separated by the
    medium: 64-fold, exactly 6 bits.
- **D.** One complex readout row `y = h₁ + i h₂`, two arrivals with `C·push = 1 ± i`, expected
  equally, from a state at `y = 1`: `y_H = 2`, `y_T = 2 ± i`.
  - The real face is `2` for both: it merges them.
  - `R = 1 ± i/2`, a first-order turn of `±½`: the phase part separates them.
  - Turning the row by `(3 + 4i)/5` leaves both `R` unchanged and moves one real face to `2/5`.
  - The tension on the real face (trace `1`) falls to `0` once the quadrature is read.
- **E.** An invertible rebase of the face leaves `S` unchanged.

The reading the tower can run without changing its step: on the trained pair tower, accumulate
`H`, `B` and `T` at the readout on a reread of its training text, then report:
- `tr S` per medium and at line starts against elsewhere;
- the most negative entries of `S`, and whether their classes belong to different media (the media
  read only by the exterior reader);
- the drop `M Q⁺ Mᵀ` for each candidate face.

Then founding as §5 states it, with its acceptance fixed by the design thread before the run.

## 8. What closes is the bridge, and the lock's friction against the information distance

Brandon's second lens (paraphrased, October 24): nothing names what is correct. What resonates is
the way the circuitry presents its consistencies, closures and cancellations, even while its output
is broken words far from use; relationships, resonance and commonality are questions of information
theory. The design thread read it as follows: correctness is how much closes, commonality is mutual
information, a relationship is the shared code said once, and resonance sits where an opening makes
its close nearly free. This section states the tension in those terms and answers its question
about the lock [agent-inferred, October 24, on the proved-standard laws named].

**The covector is the cell's two-sided friction.** At a cell the tower opens `p̂` and the arrival
`u` closes it. In `t = p̂ − e_u` the positive entries are what was opened and did not arrive, and
the entry at `u`, of size `1 − p̂(u)`, is what arrived unopened. What closed contributes nothing. At
a committed release (`p̂` one-hot at `h`) a cell gives `|t|² = 0` where `h = u` and `2` where not, so

```text
tr T = 2·#{k : h_k ≠ u_k} = |H| + |T| − 2·(aligned equal cells)        (soft: Σ|p̂|² + N − 2 Σ p̂(u))
```

which is the lock's friction ([`receiver::coupling`](../../crates/holonics/src/receiver/coupling.rs),
`solenoid.plural-coupling-face`) read on the aligned coupling, the placed-cell frame the lock
replaced. The lock and the tension relieve this one friction in two ways. The lock re-times it:
the least friction over order-consistent couplings lets the clocks slip, so `F* ≤ tr T`. The bridge
re-materials it: the least residual over the block's material, so `tr S ≤ tr T`. A release one cell
late, `xabc` against `abcy`, has `tr T = 8` and `F* = 2`.

**What closes is the bridge; what stays open is the tension.** `W = B H⁺` is the change of the
block's material that turns the most openings into closures. The bridged part `W f̄` is the friction
the arriving text would have closed had the block been made from its own passage. Today's step moves
along `B = W H`, inside the bridge, so it only moves toward closures this block can make. The
remainder `r = t − W f̄` is what the block opens that nothing arriving closes, together with what
arrives that no face of the block opens. No material of this block closes it. It is kept in the
moments (§2), and founding (§5) carries it to a face on which it closes. Correctness is closure in
this reading: `S = 0` exactly when every covector is a linear read of the face, and a contradiction is
a four-cycle (§3). A stronger closure is several independent faces bridging one part, as loops close
in the Bombe; each then adds nothing given the others (`M = 0`).

**Commonality, exactly, in the moment chart.** Let `S₀` be the tension against the constant alone,
the covector's centred Gram. On the covectors' range (they sum to zero),

```text
det S / det S₀ = Π_k (1 − ρ_k²),        ρ_k² = eigenvalues of S₀⁻¹ (S₀ − S)
```

where `ρ_k` are the canonical correlations of covector and face. Each canonical pair is one channel
on which the face opens what arrives, and `ρ = 1` closes it completely. In the Gaussian chart the
information shared per cell is `−½ Σ log(1 − ρ_k²)`, and a founding drop is the conditional ratio
`det S_after / det S`. These are chart readings of the moments. The code's own shared information is
what the reread certificate measures, the code saved by reading in context (`code.region-binding`).
Exact on §7's data:
- `det S / det S₀ = 39/644`, with `Σ ρ² = 767/644` and `Π ρ² = 81/322`;
- on the eight line starts, the held mode gives `det S_after / det S = 1/4`, one bit per cell in
  the Gaussian chart, and the unrelated alternating face gives `2/3`.

**The lock's friction against the information distance.** `F* = |H| + |T| − 2λ` has the form of
the information distance. In Shannon form that is the variation of information
`H(X|Y) + H(Y|X) = H(X) + H(Y) − 2I(X;Y)`; in algorithmic form it is
`K(H|T) + K(T|H) = K(H) + K(T) − 2I(H:T)`, up to logarithmic terms. All three are metrics (`F*` is
the insertion–deletion distance), and they are not equal. The exact relation is a code. For a
coupling `c` at one face, with per-cell codes `ℓ_H` and `ℓ_T` at the receiver, send each strand given
the other by the coupling and its unmatched cells:

```text
L(H|T) + L(T|H) = L(H) + L(T) − Σ_((i,j)∈c) (ℓ_H(i) + ℓ_T(j)) + 2 L(c)
L(c) = log₂ C(|H|, |c|) + log₂ C(|T|, |c|) + log₂ (min(|H|, |T|) + 1)
```

At one unit per cell, with `L(c)` left uncharged and `c` a longest coupling, the right side is `F*`.
Charged, it is a valid code, so it bounds `K(H|T) + K(T|H)` from above up to logarithmic terms, and
the net shared code `Σ_c ℓ − L(c)` bounds the shared information from below wherever the face's code
is the strand's own. They differ in three places.

1. **The grain.** `F*` counts cells; the information distance counts code. Under
   `p = (½, ¼, ⅛, ⅛)`, `aac|aad` and `ccb|ccd` both have `λ = 2` and `F* = 2`, but they share 2 and
   6 bits per side. The weighted coupling is the same systolic sweep with `ℓ` in place of `1`.
2. **The order.** Only order-consistent copying is credited: crossings are knots, and a bag of pairs
   has no time. `abcdefgh` against `efghabcd` has `λ = 4` and `F* = 8`, although the relation is one
   of 8 rotations, 3 bits; `abcd` against `dcba` has `λ = 1`. Repeats within a strand and transforms
   (a carried digit) earn nothing unless the face makes them equal. Equality at a face is a
   congruence, so choosing the face chooses what counts as shared
   ([the one face law](2026-10-24_ONE_FACE_LAW_A_FACE_IS_A_CONGRUENCE_SO_LANGUAGE_ARITHMETIC_AND_ANY_OPERATION_ARE_READ_BY_ONE_CONTACT.md)).
   This difference is deliberate: the lock reads commonality in time.
3. **The coupling's own description.** `F*` charges nothing for saying which cells pair, so a face
   of few classes couples long by chance. Over every pair of strands enumerated:
   - the mean of `λ/n` is `44803/65536` for two classes at `n = 8`, where 63,404 of the 65,536 pairs
     couple at half their length or more;
   - it is `53513/98415` for three classes at `n = 5`, and `29515/65536` for four at `n = 4`;
   - long strands approach the Chvátal–Sankoff constant, about `0.81` at two classes, and the limit
     falls as `2/√σ` (Kiwi, Loebl and Matoušek);
   - charged in full, only identical strands pay: at two classes and `n = 8`, exactly the 256
     identical pairs of 65,536.

They agree where the three differences vanish: every cell costs the same with no redundancy inside
a strand at that grain, the relation is in-order copying, and the coupling is cheap because the lock
has few slips. Its end is `F* = 0` with `λ > 0`, current carried with no slip.

**For the lock's acceptance** [agent-inferred]. The acceptance stays as fixed. `F*` falls only while
`λ` grows by more than half of what a reply adds, so chance coupling above one half per cell passes
that guard; the enumeration shows it does at two and three classes. At the 32-class coupling face
the `2/√σ` law puts chance near `0.35`, below one half, so the guard holds there. A reading at a face
of few classes, such as digits, can carry the net shared code `Σ_c ℓ − L(c)` beside `λ` and `F*`.
It is the rule that decides founding (§5): a contact counts when it pays for its own description.

## 9. Owed Lean

One box in #410:
- the effective tension `S = T − B H⁺ Bᵀ` is the least residual of the covector on the face, and
  the remainder is orthogonal to every face (extending `Objects/Membrane:interior_elimination` from
  an invertible interior to a positive semidefinite face Gram);
- `S` is invariant under an invertible rebase of the face;
- the quotient formula: reading `c` beside the face removes exactly `M Q⁺ Mᵀ`;
- `R = y_T / y_H` is invariant under a unit turn of the readout row, and the gradient of
  `½ |log R|²` in `y_H` is `−log R / conj(y_H)`;
- on the covectors' range, `det S / det S₀ = det(I − S₀⁻¹(S₀ − S))`, the product of `1 − ρ_k²`;
- the alignment-code identity of §8, with `F*` its value at one unit per cell and `L(c) = 0`.

## Receipts

[`2026-10-24_EFFECTIVE_TENSION_receipts/`](2026-10-24_EFFECTIVE_TENSION_receipts/): `tension.py` and its
output `tension.json` (§7); `closure.py` and its output `closure.json` (§8); `RUN.md`. Exact
fractions and integers throughout.

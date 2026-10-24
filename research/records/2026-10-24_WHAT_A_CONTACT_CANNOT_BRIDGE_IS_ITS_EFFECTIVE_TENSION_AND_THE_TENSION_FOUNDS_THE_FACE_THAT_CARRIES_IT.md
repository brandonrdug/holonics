# What a contact cannot bridge is its effective tension, and the tension founds the face that carries it

Refs #404 #405 #410. Follows [faces read on cycles](2026-10-24_FACES_ARE_READ_ON_CYCLES_A_FACE_IS_A_COHOMOLOGY_CLASS_THE_CARRY_IS_ITS_BOCKSTEIN_AND_FRICTION_KEEPS_ONLY_THE_HARMONIC_PART.md)
and [the one face law](2026-10-24_ONE_FACE_LAW_A_FACE_IS_A_CONGRUENCE_SO_LANGUAGE_ARITHMETIC_AND_ANY_OPERATION_ARE_READ_BY_ONE_CONTACT.md),
and answers the design thread's request for the tower's learning step
([`hnn::tower`](../../crates/holonics/src/hnn/tower.rs)). Status:
- the laws are proved-standard: the normal equations, the Schur complement and its quotient
  formula, partial regression, Wirtinger calculus;
- the checks are exact;
- the tower readings in §3 to §7 are [definition; agent-inferred, October 24].

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

## 8. Owed Lean

One box in #410:
- the effective tension `S = T − B H⁺ Bᵀ` is the least residual of the covector on the face, and
  the remainder is orthogonal to every face (extending `Objects/Membrane:interior_elimination` from
  an invertible interior to a positive semidefinite face Gram);
- `S` is invariant under an invertible rebase of the face;
- the quotient formula: reading `c` beside the face removes exactly `M Q⁺ Mᵀ`;
- `R = y_T / y_H` is invariant under a unit turn of the readout row, and the gradient of
  `½ |log R|²` in `y_H` is `−log R / conj(y_H)`.

## Receipts

[`2026-10-24_EFFECTIVE_TENSION_receipts/`](2026-10-24_EFFECTIVE_TENSION_receipts/): `tension.py`, its
output `tension.json` and `RUN.md`. Exact fractions throughout.

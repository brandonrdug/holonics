# Information diffuses in the potential, travels in the turn, and a key is read from diffusion only to its square root

October 26. Refs #404, #405, #410. **Grade.** Each claim carries its grade: [owned] an existing owner
states it; [proved-standard] established outside the repository, cited; [conditional] proved outside
the repository on the Unique Games Conjecture; [measured] read on a receipt or a design record;
[agent-inferred] a join made here, owed its construction; [interpretation] a reading of a classical
result in the objects. The exact receipt is `diffusion_keys.py` in
[`…_receipts/`](2026-10-26_INFORMATION_DIFFUSES_IN_THE_POTENTIAL_TRAVELS_IN_THE_TURN_AND_A_KEY_IS_READ_FROM_DIFFUSION_ONLY_TO_ITS_SQUARE_ROOT_receipts/RUN.md).

**The lens.** Brandon, October 26, asking whether more passes are now the remaining key, so that what
is left is time, scale and compute, which he would welcome as ordinary programming. He asked for a
critical appraisal for planning, and for the place of game theory (the Unique Games Conjecture), of P
versus NP and of the rest of the mathematics in his messages, derived as far as needed to hold how
information diffuses in the theory as a whole.

**What it gathers.** The lenses this joins, each already given and derived once:
- October 17: a game is a compressed instantiation of a dynamics, one law for every kind of game;
  computation is information diffusion through definite channels, the vorticity of information
  propagation, with Boltzmann and P versus NP named beside it.
- October 18: sparse binding and resonance; foveation and coarse-graining; friction and glue.
- October 22: information dissolves into a receiver's kernel, never annihilated.
- October 23: frustration, what repeated looking cannot place, as measurable tension.
- October 25 and 26: laps over one paragraph, and the binding bank.

The October 17 play and computation records and the October 18 reach record were written during the
power outage and kept in the project files; they are not in this repository. Everything this record
uses from them is restated here with its grade, so it stands alone.

## 0. The law in ten statements

1. **What moves is a difference on contacts.** The news `q − p̃` reaches the complex as a 1-cochain
   `c` on its contacts, each contact transporting by its connection
   ([owned] `complex.connection-incidence`).
2. **It has one split.** `c = dφ ⊕ δβ ⊕ h`: the exact part (potential, boost), the coexact part (local
   turn, curl round a face) and the harmonic part (global turn, dormant)
   ([owned] `constitution.hodge-split`). A game is such a cochain on states and moves; its potential is
   `φ`, and its frustration is the least weight of its class. Unique, cooperative and strategic games
   are this one law ([agent-inferred, October 17]; Monderer and Shapley 1996, Candogan, Menache,
   Ozdaglar and Parrilo 2011).
3. **Diffusion drains the potential and keeps the turn.** Relaxing the potential,
   `c ← c − τ d₀d₀ᵀc`, is a gauge move: an exact cochain integrates to zero round every cycle
   (Stokes), so it keeps every circulation and every holonomy and can never lower a frustration,
   which belongs to the class ([owned] `key.gauge-orbit`; Lean `Holon/Complex.exact_closed_iff_flat`).
   Friction on the faces (the Hodge heat flow) drains the local turn as well and leaves `h` exactly
   in place ([owned] `fluid.friction-keeps-harmonic`). Alignment through contacts decays at the
   spectral gap ([owned] `contact.alignment-spectral-gap`).
4. **A pass reaches one hop, and the gap sets how far it carries.** `t` passes are a polynomial of
   degree `t` in the constitution, so they reach `t` hops (the cone, a discrete Lieb–Robinson bound),
   and the exact response itself falls per hop by `q = (√κ − 1)/(√κ + 1)`, `κ` the constitution's
   condition number ([proved-standard] Demko, Moss and Smith 1984).
5. **The turn is what travels.** Relaxation by the potential alone contracts per pass by
   `(κ − 1)/(κ + 1)`; relaxation that carries a rate (momentum, a held oscillation: the telegraph form
   of heat, [owned] `heat.telegraph-relaxation`) contracts by the same `q` as statement 4 when tuned
   to critical damping ([proved-standard] Polyak 1964; Chebyshev semi-iteration; no method of `t`
   passes does better on the class, Nemirovski and Yudin 1983; reading the telegraph form as the
   swing's carried rate is agent-inferred). On a chain of length `ℓ`, `κ ~ ℓ²`, so
   potential-only passes cost `~ℓ²` and carried-turn passes `~ℓ`: diffusion spreads as the square root
   of its passes, a carried turn as their number. One constant governs the reach in space and the
   passes in time ([measured] receipt B: 28, 77, 246, 908 plain passes against 12, 20, 37, 73 at
   `κ ≤ 9, 25, 81, 289`).
6. **A key is a gauge, and exact keys are found by loop closure in linear time.** The labelling of a
   unique game is a section of a flat connection; loop closure (the Bombe) propagates one hypothesis
   along a tree and checks one holonomy per independent cycle, `|E| − |V| + 1` of them
   ([owned] `key.menu-loop-closure`, `key.consistent-fibre`). A few corrupted contacts are located by
   their cycle syndrome when the menu's least edge cut exceeds twice their number
   ([owned] `attribution.syndrome-localization`). [measured] Receipt C: on the Petersen graph over
   `S₃` the key is the only labelling closing all 15 contacts and loop closure finds it with 3 × 15
   reads; with one contact corrupted loop closure returns nothing, dropping each contact in turn
   locates the corrupted one alone (Petersen is 3-edge-connected), and the key returns.
7. **Diffusion reads a key only to its square root.** For a connection Laplacian with least
   eigenvalue `λ₁` and frustration Cheeger constant `h₁`, `½λ₁ ≤ h₁ ≤ C√λ₁`
   ([proved-standard] Lange, Liu, Peyerimhoff and Post 2015, `C = 2√(2d_μ)` for `ℤ_k`, `(3/2)√(2d_μ)`
   for `U(1)`; Bandeira, Singer and Spielman 2013 for `O(d)`, `λ₁ ≤ η ≤ √(10λ₁)`). The twisted cycle
   is the extreme case. [measured] Receipt A: on the `n`-cycle with one contact turned by `c/k`, every
   eigenvector is `ζ_N^(a x)` with `a ≡ −c (mod k)`, exactly in `ℚ(ζ_N)`; a labelling must break one
   contact in `n`, while the diffusion's least energy is `λ₁ = |1 − ζ_N^c|²`, about `(2πc/k)²/n²`.
   By `|1 − z^n|² = |1 − z|² |1 + z + … + z^(n−1)|²`, a labelling's Rayleigh quotient is the
   diffusion's times the Fejér factor `|1 + z + … + z^(n−1)|²/n`, which grows like `n`: 1.71, 3.28,
   6.51, 12.98 at `n = 2, 4, 8, 16`. A violated fraction `ε = 1/n` shows in the
   spectrum as `ε²`, and diffusion needs `~n²` passes to feel the turn.
8. **That square root is the frontier of every polynomial reading.** From a `(1 − ε)`-satisfiable
   unique game on `k` labels a polynomial algorithm satisfies `1 − O(√(ε log k))`
   ([proved-standard] Charikar, Makarychev and Makarychev 2006); doing better is NP-hard
   ([conditional] Khot, Kindler, Mossel and O'Donnell 2007); under the conjecture the basic
   semidefinite relaxation, a diffusion-type vector reading, is the best polynomial algorithm for
   every constraint problem ([conditional] Raghavendra 2008). Unconditionally, telling value
   `≥ 1/2 − ε` from `≤ ε` is NP-hard ([proved-standard] Khot, Minzer and Safra 2018, the 2-to-2
   theorem). At value exactly 1 the same game is solved by statement 6 in linear time.
   [interpretation] **This is why exactness is a computational law, not an aesthetic one**: exact
   transports keep the machine's own constraints at value 1, where keys are found by propagation;
   noise of `ε` moves them into the `√ε` regime, where no polynomial procedure is known to do better.
9. **The exponential lives only in the slow modes.** Unique games on expanders are easy
   ([proved-standard] Arora, Khot, Kolla, Steurer, Tulsiani and Vishnoi 2008); in general they run in
   time exponential only in the number of eigenvalues near 1, the threshold rank
   ([proved-standard] Arora, Barak and Steurer 2010); planted structure above the Kesten–Stigum
   threshold is located by non-backtracking spectra (Bordenave, Lelarge and Massoulié 2018). Exact
   counting on a surface of genus `g` costs `4^g` Pfaffians, `4^g = |H¹(Σ; ℤ₂)|`, the number of turn
   classes ([proved-standard] Galluccio and Loebl 1999; Cimasoni and Reshetikhin 2007; the October 17
   reading). [agent-inferred] **Location is polynomial in what diffuses and exponential only in the
   slow modes no landmark has pinned.** [measured] Receipt D: two flat blocks joined by two
   conflicting contacts have exactly two slow modes (`λ₂ ≤ 1` by the block sign, `λ₃ ≥ 4` by
   interlacing): the global shift, which is gauge, and the blocks' relative shift, which nothing
   decides; the optimum keeps 6 labellings, 2 once the gauge is fixed, 1 after one landmark.
10. **Only foundings, re-keying and landmarks move what diffusion leaves.** Passes at one
    constitution never take the tension below `tr S`, `S = T − BH⁺Bᵀ` ([owned]
    `contact.effective-tension`); a founded face lowers it by exactly `M Q⁺ Mᵀ` ([owned]
    `contact.tension-founds-face`); a landmark pins one slow mode's gauge, `log₂ k` bits. [agent-inferred] A founding
    that bounds a frustrated cycle turns its holonomy into a face's curvature the face can carry; a
    founding that adds a reach edge (a keyed contact, the bank) raises the gap. [interpretation]
    This is the laboratory's "growing P = NP" made exact: each founding or landmark turns a slow mode
    into a fast or pinned one, so later location there is propagation. The worst-case classes do not
    change, and nothing here bears on the open equality, which `HolonicsResearch/Computation/PVersusNP`
    states.

**Games in motion** [owned, with receipt E]. A comparison between two Holons that both change is a
game; its motion splits against the receiver's metric into a turn and a boost
([owned] `motion.turn-boost-split`; Balduzzi et al. 2018 for games). The boost settles like diffusion.
The turn circulates: simultaneous steps on a pure turn multiply `|ξ|²` by `1 + η²` (5/4 at `η = 1/2`),
alternating steps conserve a quadratic (recurrence), and only friction settles it (13/16 per step at
friction 1/2, 1/4 at friction 2). A mutual comparison needs both parts: the turn to carry the
difference across, and friction to deposit it.

**How it dissolves** [owned, October 22]. Nothing above destroys a distinction. A part that diffuses
below a receiver's grain is carried into its kernel; only a merge of what an admitted future would
separate pays. The harmonic part is the memory no relaxation reaches; the tension is the part no
present face carries.

## 1. Is more passes the remaining key?

**At one constitution, passes are relaxation toward a fixed point** [agent-inferred, from statements
3, 5 and 10; the lap law, [owned] `contact.lap-founds-reachable`]. Their code decrements fall
geometrically at the rate of the gap, and their limit is computable in one exact solve rather than
extrapolated:
- in Brier terms, `read-tower-tension` on a held text tower prints per medium the share of `tr T` the
  exact readout bridges (`bridged_by_readout_permille`) and the tension it leaves;
- in bits, the readout founded by exact Newton rounds with every other family held (the
  readouts-only lap of the lap record, which coded the ring tower's held-out text at 2.512 against
  3.033 for the full pass).

[measured] The Holonics-text pair tower's seven passes coded held out at 2.791, 2.645, 2.585, 2.543,
2.511, 2.497 and 2.469 bits a byte, founding nothing, and the tension stayed at 98.5 to 99.2% of
`tr T` in every medium: the passes finished the bridge and left the tension where it was.

**A founding moves the ceiling, by more than a lap** [measured, the bank records]. One pass with the
bank joined, a reach edge that reads any distance in one hop:
- the GSM8K units tower: 1.607 against 1.822 for the bankless pass;
- the Holonics text: 3.042 on prose against 3.083, every medium lower, and zeroing the join returned
  each medium to within 0.015 bits of the foil.

**The subject question is not a passes question as it stands** [agent-inferred; the falsifier is the
read below]. The bank's MQAR success (15,999 of 16,000) is recall by content: the query carries the
key's own token. The subject question asks recall by role: the answer must reach "the name the
question opened on" without carrying the name. A key read from content cannot serve a role query. A
key read from the face can, only if the face where the name was bound and the face where the answer
asks for it fall on one key cell. That alignment is a unique game over the bank's cells, and passes
learn it by descent only if a lower step exists: the read at the answer's opening must already
return the name in some share of the training problems. Of the 4,647 training problems whose
question opens on a name, 2,653 answers name it, so the relation is in what the tower heard; whether
the bank's read reaches it is not yet measured.

The read that decides it, from the trace law of the spec record (bank read weights): on those 4,647
problems, after each pass, the share whose read at the answer's opening puts its largest weight on
the binding written at the question's name.
- If the share is near zero and does not rise, more passes will not bring John: the step is
  dormant, and it needs a founding (a key face that is the product of the two faces) or a landmark
  (the role arriving as received material, natural communication).
- If the share rises pass by pass, passes are the key here, at the rate the rise shows.

**When it becomes compute** [agent-inferred, statement 10 and receipt F]. Once the lap loop founds by
itself (pool from the present faces, exact charge, exact bridge), compute and data scale it:
- the charge `(S/(S − drop))^N > N|P|²` certifies smaller foundings as the evidence grows; the least
  certifiable share of the tension is 1/48, 1/433 and 1/3941 at `N = 10³, 10⁴, 10⁵` with `|P| = 2¹⁰`,
  about `(ln N + 2 ln|P|)/N`;
- compute buys larger pools, at `log₂|P|` bits of charge each, and more laps;
- a carried rate turns `ℓ²` passes into `ℓ` (statement 5).

Until laps found, a further pass at one constitution only finishes the bridge, and asking for more
of them is a larger limit, the recorded failure.

## 2. What the machine can found by its own search, and the floors

[agent-inferred, from statements 6 to 10] Two floors bound a learner's own search:
- **The staircase floor.** A face with no correlate of lower order is invisible to every pool of
  lower order: the drop of `a`, of `b` and of `(a, b)` against `a·b` is zero, while the drop of `a·b`
  is the whole tension ([owned] `contact.pool-founding`). Laps climb one order per founding (Abbe et
  al. 2022, the merged staircase); a target of order `r` with no staircase needs a pool of order `r`,
  `|F|^r` candidates, and gradient methods meet the same wall ([proved-standard] the statistical-query
  bounds for parities, Blum et al. 1994; Kearns 1998).
- **The frustration floor.** For near-consistent keys the best polynomial reading leaves `√ε` where
  `ε` was owed (statements 7 and 8).

The pools the machine can search cheaply:
- exactly flat systems, its own clocks and exact landmarks, located by propagation (statement 6);
- expanding contact graphs, read by their spectrum (statement 9);
- low threshold rank, by enumerating the few slow modes;
- staircases, by laps;
- coprime rings: a cyclic key mod `M = ∏ p_i^(a_i)` is its residues (Chinese remainder theorem),
  so each ring is founded from a pool of `p_i^(a_i)` and the whole from their sum, not their product.

Beyond both floors only received material helps: a landmark supplies the missing lower step or pins
the slow mode's gauge.

## 3. The stopping rule for laps, with no agent choosing the foundings

[owned, the lap law; one addition agent-inferred] A lap:
1. rereads through the present constitution;
2. founds from `P_k = {f·g : f, g ∈ F_k} ∖ span F_k` by the drop `M Q⁺ Mᵀ`, rank by rank, while the
   charge is paid;
3. refounds the bridge exactly to its precision.

The laps stop at the first lap that founds nothing. **The addition:** at the stop, the remaining
tension reports how many of its eigendirections carry a share of `tr S` that would pass the charge
if a face carried it whole. Each such direction is one that no pool of present order reaches. The
count is exact without an eigenvalue: it is the inertia of `S − θI` (Sylvester), `θ` the least
certifiable drop, read by one fraction-free `LDLᵀ`. It is the number of landmarks, or of pool orders,
the remainder needs. That turns "the bar is not met" into a measured
count of what must be supplied.

## 4. Where it enters

- **Design (Athena):**
  - make the ceiling read of §1 the first deliverable on the units tower and on the Holonics text
    tower, beside one more ordinary pass;
  - add the subject-role read of §1 to every pass of the planned run;
  - the deposit is first order in the passes. A carried rate tuned from the measured gap
    (`α = 4/(√λ_max + √λ_min)²`, `β = q²`) is the momentum form. Its consumer equation is the per-pass
    contraction `q` on the bridge's quadratic, and it is owed with its owner.
- **Lean, owed to #410:**
  - the twisted cycle's eigenvectors and the Fejér identity `|1 − z^n|² = |1 − z|²|Σ_(j<n) z^j|²`;
  - frustration's gauge invariance as a class function;
  - the critically tuned two-step contraction on a quadratic;
  - the charge threshold's monotone fall in `N`.

## 5. The recorded failures these choices could repeat

- **Bits read as progress.** The subject question's bar is behaviour, and its decisive read (§1) is a
  share of recalls, not a code.
- **A refusal answered with a larger limit.** More passes at a fixed constitution is such a limit
  once the bridge is finished; §1 makes the ceiling a read so the limit is not raised blind.
- **An authored routine standing in for learning.** Landmarks are received material, never a parser
  computing an answer, and foundings come from the machine's own pool under an exact charge.
- **Arrays and windows.** Reach is stated in hops, gaps and slow modes, never in offsets.
- **Text as the exception.** Every statement is on contacts and cycles, so it holds for text, image,
  acoustic and motor input alike.

## Receipts

`diffusion_keys.py`: exact Fractions, integers and `ℚ(ζ_N) = ℚ[x]/(x^(N/2) + 1)`; decimal figures are
printed only as readings beside exact values. Parts A to F as cited above; `all 394 checks hold`.
Projection, deadline, wall time and peak resident set are in
[`RUN.md`](2026-10-26_INFORMATION_DIFFUSES_IN_THE_POTENTIAL_TRAVELS_IN_THE_TURN_AND_A_KEY_IS_READ_FROM_DIFFUSION_ONLY_TO_ITS_SQUARE_ROOT_receipts/RUN.md).

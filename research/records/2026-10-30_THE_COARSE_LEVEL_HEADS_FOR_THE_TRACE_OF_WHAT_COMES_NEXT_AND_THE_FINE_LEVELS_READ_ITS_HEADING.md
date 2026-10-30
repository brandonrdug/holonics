# The coarse level heads for the trace of what comes next, and the fine levels read its heading

Refs #404 #406. Status: [the lens and the located cause; the law and its acceptance fixed before the
build; agent-inferred, October 30]. Claude (opus), design lead. Read beside
[the packet record](2026-10-30_A_CLOCKED_LEVEL_HEARS_THE_PACKET_ITS_CLOCK_CLOSED_NOT_THE_STATE_ITS_OWN_MODES_ALREADY_HOLD.md)
(whose clocked levels and packets are the race's base declaration, C′),
[the Galois-gap record §12–13](2026-10-26_A_GALOIS_GAP_IS_A_MODES_MOMENTUM_AN_ORBITS_GAPS_MULTIPLY_TO_ITS_PRIME_AND_A_TIME_BOUNDARY_IS_THE_PUMPED_MODE.md#12-colourless-is-compressible-the-trace-the-tower-of-colours-and-the-quasicrystal)
(colourless is the trace),
[the scope record §4 and seed 11](2026-10-26_NEUTRAL_IS_A_RATIO_OF_ONE_AGAINST_WHERE_THE_RECEIVER_STANDS_AND_THE_SCOPE_DECIDES_WHAT_A_COLOUR_READS.md#4-the-scope-decides-what-a-colour-reads)
(a coarser scope is a relative trace of the same field) and
[the diffusion law, statements 6, 9 and 10](2026-10-26_INFORMATION_DIFFUSES_IN_THE_POTENTIAL_TRAVELS_IN_THE_TURN_AND_A_KEY_IS_READ_FROM_DIFFUSION_ONLY_TO_ITS_SQUARE_ROOT.md#0-the-law-in-ten-statements)
(keys by loop closure; the exponential lives in the slow modes). Owners it joins: `Tower::step` (the
residual stream's opening and a clocked level's tick), `Tower::reverse_joined`, the section's
certificate (`TowerLearner::section_inner`), the state's text, the card (`kernels/tower.cu`,
`TowerCard`).

**Computational object.** The helical pair interaction, read as a pair contact between a coarse
level's heading and the trace of the arrivals its next tick closes, over the menu of the passage's
spans. Of the winding guide's six objects it touches:
- the tower thread: the coarse level's scope over the fine field, and the read back down;
- the pair: the heading against the trace, with the other spans as the menu;
- faces and placement: the trace is the colourless face of a span.

The helix, cell holonomy and the tube stay as the packet record has them.

## 1. The lens

Brandon, October 30 (paraphrased; his words stay outside the repository).
- Passes and laps are only discrete iterations, and code length read globally is not the measure.
- The machine recombines fragments of words and grammar validly and keeps cycling through relevant
  modes, but it scrambles: it does not aggregate local continuations into a larger, coarse-grained
  motive, and it shows no organized attention. The local game is being played without integrating
  into fields that act like lenses (unique games; the coloured and the colourless; the classes of
  energy distribution that associate compressible cycles).
- Bring it back to fluid dynamics: an auto-gradient with the terrain it learns from, an NPC
  navigating a map. Compression is intelligence is navigation.
- The coloured and colourless are the Galois colours of the October 26 records.
- Short loops: three-to-fifteen-minute races first, extended to an hour only when they separate. He
  expects the right algorithm to show things snapping into place within minutes.

## 2. What the races measured

[measured, RTX 4080 SUPER]
- **The local game converges early and then crawls.** On the four arrival levels (October 27), 66%
  of the held-out gain of 45 laps came by lap 3, 76% by lap 5 and 87% by lap 10. The largest single
  gain was lap 0 to lap 1 on the same bytes (2.356 to 2.139).
- **The levels collapse onto short memories.** The four arrival levels' mean decay was about 0.996
  at lap 0 (a memory of some 270 arrivals) and 0.984, 0.957, 0.990 and 0.991 at lap 40 (about 60,
  23, 100 and 110).
- **The clocked levels hold long and add little.** On the news clock the top level's modes held
  near 0.998 of their own ticks while it gathered and steered nothing; packets made the two clocked
  levels of C′ worth 0.010 to 0.036 bit a byte over laps 25 to 45 (the packet record §7).
- **The founded split does not change this.** Its free copies read with their dormant control
  within the lap-to-lap swing (the pair record §7).
- **The writing** is markdown and GSM8K shapes with invented words and wrong arithmetic at every
  mark: phrases locally valid, never composed into a sentence that goes somewhere.

## 3. What is owned, and what is missing

[owned] **The packet already takes the trace.** A clocked level hears the packet its clock closed,
the fine level's motion from rest since the level's last tick (the packet record §3). Over the
span it is the sum of the span's pushes carried by the fine moves: a relative trace of the fine
field over the coarse level's scope, in the sense of the scope record's seed 11.

[owned, without a tower caller] **Loop closure** (`compression::keys::edges::Menu::propagate`,
`hnn::keys::locate_closing`, `holon::contact::menu::menu_loop_closure`; Lean `Compression/Core/Keys`)
runs only in the pre-tower resident machine and its terrain tests. **Landmarks**
(`compression::landmark`) and the **whole-section release** (`hnn::prediction`) likewise have no
tower caller. The **duplex** (`hnn::tower::duplex`) refines both strands to a fixed point but holds
no coarse mode and has no caller in the races.

[agent-inferred] **The located cause.** The tower's forward is strictly upward: `x^(ℓ+1) = x^ℓ + W₂v`,
the readout on the top. A clocked level is asked nothing at its own grain: its only covector is the
arrivals' code reaching it through the residual stream, where it returns a constant between ticks.
And nothing it holds reaches the fine levels' moves. So it holds a long memory (measured) and no
motive: it is never compared with where the passage goes next, and the fine levels never read where
it is going.

## 4. The law

[definition; agent-inferred, October 30] **A clocked level carries a heading.** On a tower with
packets whose news clock begins at level `F`, each level `l ≥ F` reads its modes through its own
heading material `C^→_l` (complex, `w × n`, beside its read):

```text
ĥ_l(t) = r̂(Re(C^→_l h_l(t−1)))          the heading, read from the modes before arrival t
```

Between its ticks a coarse level's modes do not move, so its heading is held, and the heading at a
tick is the one it held since its last tick.

**The trace of a span.** Each clocked level carries the open trace of the arrivals since its last
tick, the sum of their encoded faces:

```text
o_l ← o_l + E(u_t)                        at every arrival
τ_l(j) = r̂(o_l),  then o_l ← 0            at tick j of level l
```

The span is the packet's span, closed by the same tick. Order inside it is what the coarse scope
does not tell apart; the trace is the span's colourless face (the Galois-gap record's §12, the trace
over the span's translations). `o_l` is the present span, released at the tick, not a store.

**The heading meets the trace through a pair contact over the passage's menu.** The menu of a tick
is the traces of the same stream at the same level in the learner's section, `M_l`. With the pairing
read on the bits' grain,

```text
z_ji = 2^(−s) ⟨ĥ_l(t_j), τ_l(i)⟩ / 2^(2·16),   s = ⌈½ ⌈log₂ w⌉⌉     (bits; i ∈ M_l)
e_ji = 2^(z_ji − max_i z_ji),   ℓ_j = −log₂ (e_jj / Σ_i e_ji)       the closure's code at tick j
```

The loop closes when the heading the level held picks out the trace of the span its own tick
closed, against every other span of the passage: the Bombe's menu test, read as a Gibbs face. `s`
is the scale at which a heading and a trace with independent directions pair with unit spread
(each `r̂` has `|r̂|² = w` on the face's `2^(−16)`), so the face opens neither flat nor sharp
(`s = 3` at the race's `w = 64`).

**Both sides change.** The closure's covector is the classical descent covector of its declared
comparison, `g_ji = e_ji/Σ_i e_ji − [i = j]` (in bits), reaching
- the heading, `Σ_i g_ji τ_l(i)`, and through `r̂`'s adjoint `C^→_l` and the modes `h_l(t_j − 1)`
  (whose covector the level's own reverse then carries into its moves, its push and its packets);
- each trace, `Σ_j g_ji ĥ_l(t_j)`, and through `r̂`'s adjoint every arrival's encoding row in that
  span.

The target is the arrivals' trace, encoded through the same `E` as the source (the loss law), never
a packet the fine levels formed: a packet is moved by the fine levels, which read the heading, so a
heading compared with a packet could close its loop on its own echo.

**The fine levels read the heading.** The residual stream opens on the encoding plus each clocked
level's heading through its descent material `D_l` (real, `w × w`, opening at zero):

```text
x⁰_t = E(u_t) + Σ_(l ≥ F) D_l ĥ_l(t)
```

so every level's push, gate, turn and contacts read where the coarse levels are heading, and the
tower opens on C′ face for face. During release the same read steers the fine levels toward the
trace the coarse level heads for: the release descends through the field the coarse level holds.

[agent-inferred] **The heading is located by its closure alone.** The fine levels' covector stops at
`D_l`: `G_D += δx⁰_t ĥ_l(t)ᵀ`, and the heading is a given input to the fine levels' reverse.
Carrying that covector into the heading would need one reverse across the levels in time (the fine
scan at `t` would reach the coarse modes at their last tick, whose packet read the fine level before
`t`), and the question this loop asks is whether a heading located by closure steers. Under the
news clock the section's opening is already a constant; a heading read from the opening modes
reaches only `C^→_l` and its trace.

**The certificate reads the whole code.** A section's code is the arrivals' code plus every tick's
closure code, the faces `(e_jj, Σ_i e_ji)` joining the arrivals' faces in the exact comparison of
products, so the deposit is certified on the comparison it descends.

## 5. Acceptance, fixed before the build

1. **Unchanged without the heading.** Every tower test passes unchanged; a state's text carries
   `traces -` without it.
2. **It opens on C′.** With `D` at zero the forward is C′'s face for face, at the race's declaration
   with the heading joined.
3. **Refusals.** The heading is refused without packets, beside participation, and on a learner after
   its first section.
4. **The covector.** It matches the code difference (arrivals plus closure) on three levels clocked
   from level 2 with packets, with and without the passage, at steps of `2^(−9)` units.
5. **The state.** The state's text carries the open traces and restores whole; a passage read in
   carried sections is the passage read whole.
6. **The card.** Parity at the race's declaration with the heading, host against card: every face,
   every closure face and every covector entry equal.
7. **The smoke** (three minutes on the card from C′'s founding, the race's passage and keys):
   - *The heading locates.* At each clocked level the closure's code a tick, read by window, ends the
     smoke at least one bit below `log₂` of its menu (the heading at least halves where the passage
     could be going), and the reading is printed each window so the minute it moves is seen.
   - *It costs the arrivals nothing.* The arrivals' training code by window is no worse than C′'s
     at the same sections.
   - *The writing* at the smoke's end is shown whole, beside C′'s lap-0 writing.

   Short of the first claim the heading did not locate, and the next loop's subject is why (the
   trace, the menu or the scale). With both, the same declaration runs fifteen minutes beside C′ at
   the same sections, and an hour only on a separation beyond the lap-to-lap swing.

## 6. The recorded failures these choices could repeat

From [the lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md),
[the prototypes' lessons](2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md) and
[the recurrences](2026-10-09_LESSONS_THE_FAILURES_THAT_RECURRED_FROM_SEPTEMBER_30_TO_OCTOBER_9.md):
- *A copier standing in for learning*: a closure compared with a packet the heading itself steered
  would close on its echo; the target is the arrivals' trace.
- *An index of contexts counted as generation*: the menu is the section's present spans, recomputed
  in every section; nothing is written to be looked up.
- *A design thought in the programming language*: the span is the clock's packet in information time
  and the menu is the learner's section, stated as traces, headings and modes, not offsets.
- *Text as the exception*: the trace is of the arrivals' encoded faces; nothing reads a class, a
  letter or a modality.
- *Bits read as progress*: the closure's code is a reading of whether the heading is located; the
  claim on the arrivals is only that they pay nothing, and the writing is shown.
- *An uncertified deposition step*: the certificate reads the code the step descends.
- *A located cause carried unrepaired into a new consumer*: participation stays refused beside
  packets, and the duplex is not joined until the heading is measured.
- *A refusal answered with a larger limit*: the smoke's three minutes are its deadline.

## 7. What is not derived

- The fine levels' covector into the heading (one reverse across the levels in time) is not carried.
- The release is still a class at a time, steered by the heading; a joint-field release (the duplex
  refined under the heading) is the next step if the heading locates.
- The menu's horizon is the learner's section, so the coarsest heading sees at most a section of
  spans; reach beyond it is participation's or the carried modes'.
- No orbit of colours is classified by its energy (the Galois-gap record's §5), no landmark pins a
  slow mode, and no potential is located from the tower's own contacts (the diffusion law's
  statement 6 at the tower).

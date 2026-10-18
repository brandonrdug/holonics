# The receiver reads in the passage frame: an absolute lift released one class

Refs #73 #63 #62. October 16, 2026.

The objective is to replace one-class release with learned, input-dependent decisions, without
forced diversity or arbitrary gain.

## 1. The finding

On the placed MNIST chart (200 train, 50 development images, host, one continuing listener), the
trained commit released class 1 on all 50. Four causes were located, each switched off alone by a
diagnostic switch that was never committed; with all four off the commit read 26 of the 50 right over
eight classes (0, 1, 2, 3, 4, 6, 7, 9), against 9 for class 1 everywhere. Every one of the four is
necessary on this run: with any one restored the commit returns to class 1 on all 50, or (the carry)
falls to 14 of 50.

| Cause | What it does | Measured |
|---|---|---|
| **The frame** | `R` read `P_R^(τ_R) v_R`, with `τ_R` the receiving ring's absolute lift, which advances once per arrival; on a ring of period `d_R` the feature turned one node per image | a ridge read of the deposited feature gives 8 to 11 of 100 turned, 34 to 37 of 100 in the passage frame |
| The carry copy | the carried interior is a `-(1/2, 1]` copy of the previous arrival | the previous label is released on 60 of 200 train images with the carry kept, 19 at rest |
| The prior's climb | the located receiving prior moves up on most deposits once the carrier carries the digit | up on 167 of 200 deposits; class 1 on all 50 |
| The prior's scale | the prior founds at `2^1` against features near `2^(−6)` | the founding ridge reads the feature at 12 of 100, the marginal; below `2^(−8)` it reads 36 to 39 |

The 50 images were read by every diagnostic case, so they are development images, not held out.
Per-case raw diagnostics and dataset inputs are not included in this repository.

This record lands the frame. The carry copy is read together with the arrival in the paired
arrival/context read (F2), and the prior's move and scale in the receiving prior's law (F3), both in
their owners.

## 2. The law

[definition; agent-inferred, October 16] **The receiver reads in the passage frame.**

```text
f_j = k(a_j)/L_R + R · v_R(e_j)          the read, v_R the anchor as the word left it
P_R^(τ_R − τ_R^open) = I                 the frame transport inside one reception
g ↦ Rᵀ g_j                               its transpose, no rotor
φ^T_j = (τ_R(j) − λ_R)/d_R,  w = ⌊λ_R/d_R⌋    the target phase from the anchor's own lift; the branch
```

- **Why this is the frame.** The source enters as phase-carried moments
  `m_g = Σ_k Ĝ_g(τ_g(k))⁻¹ E_g(u_k)`, so the stream's clock is already carried into storage on the
  source rings, and the word adds each injection to the carried storage without rotating it
  (`Word::continuing`): the arrival and the carried context stand in the material's frame. A
  receiver's receipt is read in its own frame and clock, and there is no privileged clock. The
  receiving ring's clock advances by the passage between the reception's opening and its read; the
  current does not advance inside a reception, so that transport is the identity. U6's smallest
  native form already reads its stations this way, `y_j = ρ_R(P_R^(1+j) v_R)`, unwound from the
  request's last tick (HNN_FORMULA, the smallest native form).
- **What the absolute lift did.** `P_R^(τ_R)` turned every feature by the count of arrivals. A fixed
  `R` that must read the same feature at every residue reads only the part that the turn fixes, the
  cyclic average: on the period-11 placed chart, 2 of the 22 realified coordinates. The digit was in
  the other 20. This is a design thought in a counter, not in the passage: an arrival count is a
  program's counter, not the receiver's epoch.
- **Every modality.** Text, image, acoustic and motor streams all enter through the source rings'
  `P_g^(τ_g)` and through the carried context, which is unchanged. Only the receiver's extra turn by
  its own lift goes, which on a text stream turned the read by the stream position in the same way.
- **The target.** Its phase is measured from the frame the read is in, the anchor's own lift; the
  cut's winding stays the log's branch and is never descended on. Measured from `λ_R` the phase lies
  in `[0, 2(j+1)/d_R]`, at most a step and a carry a cell. The move of a common origin is gauge for the
  ratio (Lean `HNN/Ratio.receivingPhase_ratio`).
- **What stays.** The source rotations `s_g = P_g^(τ_g) m̃_g` (the moment, `BankPlacement`), the mode
  explorer's intrinsic turn, the junctions' half-turns and the executed oriented slip are unchanged.

**The consumer equation.** An identical arrival at two receiving clocks reads identically:
`f(λ) = f(λ′)`, equal target phases, branches `⌊λ/d_R⌋ ≠ ⌊λ′/d_R⌋`, and one covector; and the
return stays the exact adjoint of the tangent map.

## 3. The owners changed

- `hnn/receiving.rs`: `ReceivingPhases::read`, `read_observer`, `read_carrier` (`R` applied to the
  anchor), `section_bits` (the anchor decomposed directly), `ObservationPartition::read`,
  `SourceObserverView::{seeds, source_covector}`; the module's read law.
- `hnn/port.rs`: `Word::{pull_back, pull_back_full, pull_back_world}` and the reverse sweep, `Rᵀ g_j`
  at each read with no rotor.
- `hnn/ratio.rs`: `target_phases`, measured from the anchor's own lift.
- `hnn/prediction.rs` and `prediction/charted.rs`: the physical domain and completion reads, the
  source observer, `receiving_feature`.
- `hnn/word/action.rs` (`prospective_feature`, the coupled passage), `word/variation/gain.rs`,
  `word/continuation.rs` (`return_contact`), `hnn/reference.rs` (kept anchors), `hnn/pending.rs`.
- The CUDA mirror, a separate change for the native validation queue: `holonics-cuda/src/hnn/`
  `execute.rs` (the receiving gather is the identity), `readout.rs`, `port.rs`, `lattice.rs`, and the
  kernel comments; the card test reads `R v` with no gather.
- Guides: HNN_FORMULA (the tick table and its note), THE_MACHINE guard 18, ELEMENTARY_OBJECTS (the
  joint); atlas rows `hnn.receiving-phase-pullback`, `hnn.align-cost-turns`, `hnn.physical-repair`,
  `hnn.physical-communication`, `hnn.receiving-producing-operands`, `hnn.source-relative-observer`,
  `hnn.encounter-comparison-credit`. `hnn.section-return` keeps U6's `P_R^(1+j)`.

## 4. Tests and receipts

- New: `hnn::tests::port::an_identical_arrival_reads_identically_at_two_receiving_clocks`. One
  arrival opened at two clocks that differ on the receiving ring by `3 d_R + 1` ticks reads equal,
  nonzero faces; the turned read it replaces differs between them; the target phases are equal; the
  branches are each clock's winding and differ; the covectors are equal.
- Kept and passing: `the_word_return_is_the_exact_adjoint_of_its_tangent_map` (the duality),
  `the_read_adds_the_trees_face_to_the_passage_frame_wave` (renamed; it asserts the wave is
  `R v`), `receiving_section_reads_each_mode_over_its_cycle`.
- The gate and the changed laws' tests: [receipts](receipts/2026-10-16-passage-frame/RECEIPTS.md).
- The CUDA mirror's GPU suite runs in the native validation queue; its receipt goes with that change.

[measured; review-thread host debug reads, October 17] The passage-frame read keeps the receiving
relation `R` in motion on the material-tangent fixtures: on fixture 1 with alternating `u = ±1`,
`receiving_before != receiving_after` at 38 of 40 encounters (all except 1 and 8); with `u = 1`
held, at 23 of 30, including 28 and 29; on fixture 2 with alternating controls, at 24 of 40,
including every `u = −1` encounter from 9 through 39. The replaced absolute-lift read let `R` see
only the feature's cyclic average, so its publications stopped moving `R` by encounter 12 and the
fixed-readout cycle's fixture premise held. Under the passage-frame law that premise fails:
`world_cycle` correctly refuses a run whose receiving publications move `R`. The three cycle tests
report this exact refusal and the moved encounters from their own passage receipts; their existing
closure, credit and comparison claims remain conditional on admission. Neither a larger encounter
count nor a weakened guard repairs the missing hypothesis. Owed (#73, #62) is the cycle with the
receiving publication joined into the orbit's state.

## 5. Owed

- Lean (#62): the passage-frame read as a statement, the frame transport of one reception equal to
  `P^(τ − τ^open)` and the identity when the current does not advance inside it, and the
  identical-arrival invariance `f(λ) = f(λ′)`. The existing ratio, pullback and alignment theorems are
  generic in `τ` and hold at the passage frame unchanged.
- The development read of F1 natively with the other three causes still switched (the parity with the
  diagnostic case), then with F2 and F3 in their owners.

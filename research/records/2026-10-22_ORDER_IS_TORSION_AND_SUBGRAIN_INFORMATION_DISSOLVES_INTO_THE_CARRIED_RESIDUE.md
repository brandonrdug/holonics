# Order is torsion, and information below the grid dissolves into the carried residue

October 22. Refs #410, #73.

This record settles the open items of the October 22 synthesis of Holonics with teleparallel
gravity (the loop intercept: a loop of moves fails to close by a turn, which is curvature, or by a
carry, which is torsion). It states the laws once, names their Lean owners, gives one account of
how information dissolves into geometry, and says what the account gives Athena. Grades follow
[the epistemic grades](../../docs/canon/EPISTEMIC_GRADES.md).

## 1. Order is torsion

[proved-derived; formal-checked] For two turns `z ↦ k_u z + b_u` and `z ↦ k_v z + b_v` with pivots
`(1 − k) O = b`, the two orders differ by

```text
b_u (1 − k_v) − b_v (1 − k_u) = (1 − k_u)(1 − k_v)(O_u − O_v)
```

so two turns commute exactly when they share a pivot, and the carry of their loop is the product of
their departures from free fall times the separation of their pivots. For moves with one linear
part `M` the carry is `(1 − M)(b₁ − b₂)`. Lean: `Geometry/ScrewTorsion`
(`complex_moves_commutator`, `complex_commutator_pivots`, `complex_moves_commute_iff_shared_pivot`,
`move_same_linear_commutator`), on the motion owner's `move` and pivot (`Geometry/Motion`).

Consequence for learning: pairwise loop data (the carries of each pair) fixes the pivots up to one
common shift, which is the Bombe's loop closure read on moves: a key is located up to its gauge.

## 2. The Burgers vector and the base point

[proved-derived; formal-checked] A loop of pure translations closes by the sum of its carries, its Burgers vector
(`flat_loop_carry`). Read from a base point shifted by `t`, a move keeps its turn and its carry
gains `(M − 1) t` (`move_basepoint`), so the carry is free of the base point only when the turn is
trivial (`translation_basepoint`). Teleparallel gravity is the case where every loop closes in turn
and fails only in carry, which is why its torsion is base-point free. The Rust screw
(`geometry/winding.rs`) had tests only; this is its Lean statement.

## 3. The fifth torsion and the redshift loop

[proved-derived; formal-checked] For a teleparallel Kaluza–Klein frame `e⁵ = dy + A`, the exact part never reaches
the coboundary, so `T⁵ = d e⁵ = dA = F` (`fifth_torsion_is_field`); charge is the carry around the
fifth circle, and it is a whole number only because that fibre is compact
(`Complex.exp_eq_one_iff` in Mathlib supplies the quantization).

[proved-derived; formal-checked] For the time coframe `e⁰ = N dt`, the coboundary summed over a grid of cells is
the lapse difference times the clock difference across the grid (`redshift_loop`). A static lapse
difference therefore leaves a carry around every loop that spans it: a static mass is read as a
carry in the time coframe, and the fall toward slower clocks is `a = c² ∇ ln N`.

## 4. The two boosts are one boost

[proved-derived; formal-checked] The det-1 squeeze `diag(λ, λ⁻¹)` of the turn·boost·shear factorization
(`Geometry/Motion`, `iwasawa`) and the ratio dilation `v′ = s v` of `MoveKind::Boost` collided as
names. Read on the undivided pair `(a, b)`, the squeeze multiplies the ratio by `λ²`
(`squeeze_dilates_ratio`), so the two are one boost in two charts. The synthesis's sentence that
"only the dilation makes entropy" is withdrawn: entropy needs a trace term beside the boost (the
`½ xᵀ Ġ x` of a changing receiver metric, or a dissipation `D ⪰ 0`), not the dilation alone.

## 5. How information dissolves

[derived] This is the account, stated once.

1. **Information is a receiver-relative distinction.** Two states differ for a receiver exactly
   when some admitted read separates them. There is no information without a receiver family, and
   no global scalar of it.
2. **Transport conserves the fine distinction.** An exact transport (an invertible move, a
   Hamiltonian flow by Liouville, a unitary) keeps every distinction; what it changes is which
   receiver can still read it.
3. **Dissolving is transport into the receiver's kernel.** A distinction dissolves when the
   transport carries it into modes finer than the receiver's grain, into the environment outside
   the receiver's partition, or into lags that a periodic carrier folds together. The receiver's
   coarse entropy rises by exactly the distinctions that crossed.
4. **Entropy is distributed through geometry.** It is a density with a current and a nonnegative
   production, `∂ₜ s + ∇·J_s = σ ≥ 0`, `σ = Σ_c J_c A_c` (each flux times its affinity), read by a
   receiver over a partition; a single entropy number is one face of that flux.
5. **It dissolves fastest where it is sharpest.** Under heat flow, de Bruijn's identity
   `d/dt H(X + √t Z) = ½ J(X + √t Z)` makes the entropy rate the Fisher information, the
   receiver's sensitivity to a shift.
6. **Running it backward needs the retained fibre.** The backward heat flow (`Zeta/HeatEquationEntire`)
   is well posed only on what the series retains. Exact series keep the fibre; a float rounds every
   term to one width and destroys it. This is the physical reason floats are refused as storage.
7. **Erasure costs only at a merge.** Landauer's `k_B T ln 2` per bit is paid where the retention
   quotient identifies two states the admitted future would separate. Releasing into the kernel,
   what no admitted receiver reads, merges nothing readable.

[proved-derived; formal-checked] The grid case is formal (`Foundation/CarriedRelease`). A stream released onto a
grid with its residue carried conserves exactly (`release_conserves`), keeps the residue inside one
step (`release_residue_bounds`), tracks the stream within one step at every length
(`release_tracks`), and is the winding of its running sum with the residue as its open phase
(`release_is_winding_of_running_sum`, joining `Aeon/Clock/Winding.split_unique`). Its step error is
a coboundary (`release_step_error`), invisible to every closed window. [counterexample; formal-checked] Plain
rounding annihilates a constant reading below half a step at every length
(`plain_rounding_silences`), while the carried release turns it into a rate
(`release_keeps_constant_rate`). A bound owes only its direction and is released outward
(`outward_release`). The HNN deposit's own release keeps its owner, `HNN/LatticeDeposit`
(nearest point, a remainder carried on a refining grain, a Kraft-budgeted release); this module is
the release-free floor chart of the same accounting.

The account replaces four confusions: loss read as annihilation; information conserved by the
reversibility of states (time parity lives on the transport, never on the state); entropy as a
global scalar; and bits read as progress.

## 6. What it gives Athena

Sent to the Athena design thread on October 22 with the derivations.

1. **Where sub-grain information goes.** Into the receiver's kernel, released at the grid with its
   remainder accounted. A certificate owes only its direction, so outward rounding of bounds at a
   fixed width is lawful as it stands. Deposits keep `HNN/LatticeDeposit`. The carried remainder
   is not dissipation: the release conserves exactly, so the remainder stays in the state as its
   open phase. `D ⪰ 0` is a contact's material law on flows and belongs to the dynamics; a grain
   release is the receiver's quotient. Coarse entropy rises only where a release drops a
   remainder, and retention stays sufficient while no admitted probe separates what that drop
   merges.
2. **Why the input barely reaches the receiver.** [proved-derived; formal-checked] If every
   symbol's ring move shares one linear part `M` with `M^N = 1` and the input only adds, the ring
   state is a linear function of its (symbol, lag modulo `N`) counts, and equal counts give equal
   states (`Geometry/ScrewTorsion`: `laggedRun_closed`, `laggedRun_lag_residue`,
   `laggedRun_eq_of_counts`). A readout of it cannot beat context counts because it is context
   counts; the design thread confirmed that the alpha field runs in this case. A lossless ring also shrinks the newest symbol's share like `1/n`.
   Carrying more than counts needs a linear part that depends on the symbol: the input modulating
   the constitution, which is the parametron's pump. The measurements: the carry `δ_uv` of a few
   symbol pairs on the actual moves, the newest contribution's share of the state across cells, and
   whether any linear part depends on the symbol.
3. **Which checks a step owes.** Deposition is the only law that changes the constitution, so a
   certificate that depends only on the constitution is computed once per deposition. Per cell the
   forward owes outward bounds, exact integer carries and residues. A check that cannot flip a
   decision is not owed. With a certified curvature bound `L` (softmax cross-entropy has logit
   Hessian norm at most ½), the descent lemma admits the step `1/L` without a halving search.
4. **The declared clock cannot see the source's own period.** [measured] The alpha field declares
   rings of periods 5, 2 and 3 (`crates/holonics/examples/solenoidal_alpha.rs`), so if each ring
   ticks once a cell its clock closes at 30. The byte codec (`Base4Bytes`) writes four base-four
   digits a byte, so the source's own period is 4, and 4 does not divide 30: the field's phases
   resolve the byte frame only modulo 2. Read on 507 KB of the repository's own English
   (`docs/ELEMENTARY_OBJECTS.md`, `docs/THE_MACHINE.md`, `CONSTRUCTION_STATE.md`,
   `docs/plans/THE_REBUILD.md` at `a37a7e3`), with Krichevsky–Trofimov counts fitted on the first
   80% and scored on the held-out 20%:

   | receiver | bits per digit |
   |---|---|
   | marginal | 1.959 |
   | phase modulo 30 (the declared clock) | 1.765 |
   | phase modulo 4 (the source's frame) | 1.522 |
   | best readout additive in the last six digits, with a frame bias | 1.440 |
   | the same, its lag weights depending on the frame phase | 1.266 |
   | conjunctions of the last six digits (context counts) | 0.971 |
   | the same with the frame | 0.915 |

   The additive rows bound what a field that is linear in its input carries between depositions
   (the paired consumer keeps the linear circuit; the locking pump is refused). The gap from 1.27
   to 0.92 is conjunction, which needs a linear part that depends on the symbol, as item 2 says.
   The period-4 dependence is what the founding law tests (`Field::found`, the founding null of
   #398), so the lawful route is that the passage founds the ring; authoring a period of 4 would
   put the codec's grain into the field. The contacts `(1,2)` read nodes 0 and 1 only, so the
   period-3 receiving ring's node 2 is never driven directly: a defect, but the smaller one. The
   additive fits ran 100 Adam steps, not to convergence.
5. **The modes the field needs are few, and they must be located.** [measured] On the same text,
   the conditional futures (the next one, two and three digits) of the 5,186 six-digit contexts
   with their frame phase, each row weighted by its occurrences, form a matrix of small rank at
   tolerance. Its rank-`r` projection, scored as a predictor of the next digit on the held-out
   20%, gives:

   | rank | weighted energy kept | bits per digit |
   |---|---|---|
   | 1 | 0.297 | 2.054 |
   | 4 | 0.693 | 1.032 |
   | 8 | 0.841 | 0.931 |
   | 16 | 0.932 | 0.922 |
   | 32 | 0.982 | 0.917 |
   | full (84) | 1.000 | 0.915 |

   A readout through 16 located directions loses 0.007 bits a digit against every conjunction of
   the last six digits. A field of 32 modes whose transports depend on the symbol but are drawn at
   random (orthogonal, damped by 9/10), with a fitted softmax readout of the state and the frame
   phase, scores 1.433; the same field with one shared transport scores 1.440, the additive
   ceiling above. Symbol dependence chosen at random buys 0.007 bits a digit, where 16 located
   directions buy 0.52. The pump's transports must be located from the comparison: at a settled
   state the residual `r` the state cannot absorb still pairs with the state as the covector
   `(W r) z*` on the constitution, and that covector is what deposition spends. A 128-mode run of
   both fields gave no reading: its readout fit did not converge in 100 steps (both scored worse
   than the marginal).

6. **Where the source must enter** (October 23, sent to the design thread with its two requests).
   The design asked which lawful entry makes the source ring's linear part depend on the symbol,
   and whether its decided field, `K` complex modes `z' = λ_(k,s) z + β_(k,s)` learned by forward
   jets, is lawful.

   **The move must be chosen by the symbol.** By item 2 and the minimal realization
   (`encoding.minimal-realization`, `E T_a = U_a E`), a source of Hankel rank `r` needs a state of
   dimension `r` moved by a transport that its symbol selects.

   **The three candidates.**
   - [proved-derived; formal-checked] Reflections chosen in one plane collapse: two plane
     reflections compose to a turn and such turns commute (`plane_reflections_compose`,
     `plane_turns_commute`), so a word reads its parity and a signed phase sum. The group is
     dihedral, not free.
   - [derived] Order needs at least two coupled planes whose mirrors do not share a pencil. The
     turns by the norm-5 quaternions `1 + 2i` and `1 + 2j` already generate a free group in SO(3).
     In the elementary objects this is a chain of rings joined by pair contacts, the symbol
     choosing each ring's pump phase.
   - [derived] In the locked regime the sheets move by `σ' = sign(h_s + J_s σ)`. A sign of a sum
     is a threshold gate, so the transitions make conjunctions over up to `2^L` configurations of
     `L` locks: capacity grows with the lock count, at `L²` integer additions a cell. A readout
     linear in the sheets is additive in them, so the conjunctions must be made in the
     transitions.
   - A founded period-4 ring is a clock: it adds the frame only.

   **The design's diagonal modes** have commuting linear parts. Their affine moves still carry
   order through their separate pivots (item 1), but each past entry is transported by
   `Π λ_(u_r)`, which depends only on the counts of the symbols that followed it.

   **The jet.** [proved-derived; formal-checked] The forward jets `J' = λ_(t, u t) J + [u t = a] z`
   and `J' = λ_(t, u t) J + [u t = a]` are the exact derivatives of the stream with respect to one
   shift of the turn or the addition of symbol `a` at every cell, read in dual numbers `ε² = 0`.
   This holds also when deposition changes the moves during the passage (`lamJet_is_derivative`,
   `betaJet_is_derivative`, `betaJet_eq_selectedRun`). The jet is the phase-carried moment, and its
   adjoint needs no tape.

   **The deposit.** [derived] The design's `Re(conj(g) J)` is `∂L/∂(Re λ)` alone. The complete
   step on a complex turn is `Δλ = −η g·conj(J)`, with `g = ∂L/∂Re z + i ∂L/∂Im z`; with the real
   part alone, the turn of each mode stays where it was initialized.

   **The certificate.** [proved-derived; formal-checked] For a scalar mode the per-symbol bound is
   the joint bound. `‖λ‖ ≤ ρ ≤ 1` and `‖β‖ ≤ B` give `‖z‖ (1 − ρ) ≤ B` and `‖J‖ (1 − ρ)² ≤ B`
   (`selectedRun_norm_bound`, `lamJet_norm_bound`). With `ρ = 1 − 2^-m` the state needs `m` guard
   bits and the turn's jet `2m`, and the check `a² + b² ≤ (2^L − 2^(L−m))²` on
   `λ = (a + ib)/2^L` reads the constitution only.

   **The transported residue.** [proved-derived; formal-checked] The design's
   `e' = A e + Δ − q` is `residueRun`: for a linear transport in any module and any release rule,
   lattice part plus residue is the exact orbit (`residueRun_conserves`). Its floor form on a line
   keeps the residue in one step and the lattice part within one step of the orbit for every
   transport (`transportedRelease_conserves`, `_residue`, `_tracks`). [counterexample;
   formal-checked] Plain rounding of a damped state holds a drive below half a step at zero
   forever, while the exact orbit grows toward `x / (1 − ρ)` (`plainTransported_silences`,
   `exactOrbit_damped`).

   [measured] On the same 2,027,360 cells, with ρ = 0.95 and η = 0.02 (the dense field also at
   η = 0.005), these are exterior float reads, not the machine.

   The field alone (online over the first 80%, held out frozen):

   | arm | online | held-out |
   |---|---|---|
   | dense `U_s` per symbol, n = 16, deposition reaching one cell back | 1.363 to 1.384 | 1.457 to 1.467 |
   | dense, one shared `U`, n = 16 | 1.430 to 1.431 | 1.492 to 1.510 |
   | diagonal, one shared turn, K = 8 | 1.410 | 1.494 |
   | diagonal, selected turns, complex deposit, K = 8 | 1.271 | 1.388 |
   | diagonal, selected turns, complex deposit, K = 16 | 1.245 | 1.378 |
   | diagonal, selected turns, real-part deposit, K = 8 | 1.291 | 1.422 |

   Joined with Krichevsky–Trofimov counts on (frame phase, last six digits) as
   `softmax(log q + W [Re z, Im z])`, with every cell scored before it is learned:

   | arm | bits per digit |
   |---|---|
   | counts alone | 0.9286 |
   | with the shared turn, K = 8 | 0.9252 |
   | with selected turns, K = 8 | 0.9221 |
   | with selected turns, K = 16 | 0.9205 |

   What the tables say:
   - Selecting the turn by the symbol doubles what the field adds over the counts, and the gain
     holds in each 500k-cell quarter of the passage.
   - At depth six the counts already hold the conjunctions, so commuting modes add only
     lag-weighted counts there.
   - The rank-16 projection of §6.5 reaches 0.922, while 16 diagonal modes reach 1.245 online.
     [inferred] The gap is in which features commuting linear parts can form, not in how many
     modes there are.

## 7. Owed (#410)

Each is a box in #410 except the neck.

- de Bruijn's identity on the receiver's partition, and the entropy balance `σ ≥ 0` on a complex.
- The neck with no comma: `dr² + κ²r²dτ²` is smooth at `r = 0` exactly when `τ` has period `2π/κ`
  (Gibbons and Hawking). It stays a standard citation until a consumer needs it.

## Receipts

- New Lean: `lean/HolonicsResearch/Geometry/ScrewTorsion.lean` and
  `lean/HolonicsResearch/Foundation/CarriedRelease.lean`, imported from `HolonicsResearch.lean`.
  Written in a cloud container with no Lean toolchain, then checked on the PC at `ce16afb`:
  `bash tools/lean_check.sh HolonicsResearch.Geometry.ScrewTorsion HolonicsResearch.Foundation.CarriedRelease`
  completed (3,454 jobs, exit 0, 16 s wall; Mathlib reused, only `Holonics.Geometry.Motion` and the
  two targets recompiled), with no errors, no warnings and no `sorry` in either module. All
  eighteen theorems are formal-checked; no proof was changed.
- The lag-residue factorization (`laggedRun_closed`, `laggedRun_lag_residue`,
  `laggedRun_eq_of_counts`) was added at `7213b44` and checked on the PC the same way:
  `bash tools/lean_check.sh HolonicsResearch.Geometry.ScrewTorsion` completed (3,396 jobs, exit 0,
  17.2 s wall against a 1,200 s deadline), with no errors, no warnings in the module and no `sorry`.
- §6.6's Lean (`ScrewTorsion` §2c and the transported residue in `CarriedRelease`) was added at
  `7beead7` and checked on the PC: the same command completed (3,454 jobs, exit 0, 12.55 s wall
  against a 1,200 s deadline; only the two targets recompiled), no errors and no `sorry`. One
  linter warning (`[FloorRing R]` unused in `exactOrbit_damped`) was removed with `omit`. The
  first placement, between the doc comment and its theorem, did not parse (`5ba90b2`, exit 1);
  moved above the doc comment at `05a8ed1`, the check completed (3,454 jobs, exit 0, 5.6 s), with
  no errors, no warnings in either module and no `sorry`.
- Atlas rows (formal-checked): `motion.commutator-carry`, `motion.lag-residue-factorization`,
  `screw.burgers-loop-carry`, `motion.squeeze-ratio-dilation`, `gr.teleparallel-fifth-torsion`,
  `gr.redshift-loop`, `release.carried-residue`, `motion.selected-move-forward-jet`,
  `motion.plane-reflections-commute`, `release.transported-residue`, and the counterexamples
  `release.plain-rounding-annihilates` and `release.plain-transport-silences`.
- No Rust changed. The runs are §6.4's and §6.5's measurements, exterior reads with their scripts
  and outputs in [`2026-10-22_ORDER_IS_TORSION_receipts/`](2026-10-22_ORDER_IS_TORSION_receipts/):
  the count read took 9.6 s at 44 MiB peak; the two additive fits took 225.8 s and 222.3 s against
  224 s projected each (peak resident not measured). §6.5's rank read (`context_rank.py`, output `context_rank.txt`) took 1.7 s. The 32-mode fields
  (`pumped_field.py` with float64 states, every training cell and 150 readout steps) took 83.3 s
  and 82.4 s under a 200 s deadline. The 128-mode fields first passed their 240 s deadline and were
  stopped, because float64 readout weights promoted the float32 states at every step; with float32
  weights and every second training cell (the receipt's version of the script) they took 59 s wall
  under a 150 s deadline, at 2.1 GiB peak each (`random_field.txt`).
- §6.6's field reads: `located_field.py` (dense, four runs together, 78.8 to 81.5 s each against a
  200 s deadline, 48 MiB peak, `located_field.txt`); `diagonal_field.py` (four runs together, 104.9
  to 108.0 s against 200 s, 48 MiB, `diagonal_field.txt`); `joined_field.py` (four runs together,
  12.2 s for the counts and 134.6 to 139.3 s for the joined fields against 220 s, 49 MiB,
  `joined_field.txt`). The per-cell times (39 to 69 µs) are a Python loop's and say nothing about
  the machine's cost.

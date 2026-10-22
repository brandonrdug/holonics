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
2. **Why the input barely reaches the receiver.** [hypothesis until measured] If every symbol's
   ring move shares one linear part and the input only adds, the ring state is a linear function
   of (symbol, lag modulo the ring's period) counts, and a readout of it cannot beat context counts
   because it is context counts. A lossless ring also shrinks the newest symbol's share like `1/n`.
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

## 7. Owed (#410)

Each is a box in #410 except the neck.

- The factorization of a one-linear-part stream through its lag-residue counts, stated in Lean.
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
- Atlas rows (formal-checked): `motion.commutator-carry`, `screw.burgers-loop-carry`,
  `motion.squeeze-ratio-dilation`, `gr.teleparallel-fifth-torsion`, `gr.redshift-loop`,
  `release.carried-residue`, and the counterexample `release.plain-rounding-annihilates`.
- No Rust changed. The one run is §6.4's measurement, an exterior read with its scripts and outputs
  in [`2026-10-22_ORDER_IS_TORSION_receipts/`](2026-10-22_ORDER_IS_TORSION_receipts/): the count
  read took 9.6 s at 44 MiB peak; the two additive fits took 225.8 s and 222.3 s against 224 s
  projected each (peak resident not measured).

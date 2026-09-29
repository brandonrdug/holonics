# The factor families' certified step: text holds its entry bound, the copy is exact, and the factor families barely move

**Date.** September 29. **Issues.** #73, #63 (THE_REBUILD U6). **Grade.** [measured] for the runs
(§3), each run once under the [pins](2026-09-29_THE_FACTOR_FAMILIES_CERTIFIED_STEP_PINNED_BEFORE_ITS_RUNS.md)
(`ebcb7f4c`) at the build `231a8939`; [proved-derived; formal-checked] for the Lean statements (§2);
[agent-inferred] for the choices named as such.

## 1. The lessons it answers

The [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **Failure 5, the uncertified deposition gain.** Every family now steps by the certificate: the
  linear loci and every factor family, in one loop and one count `B`. The declared `η_x` is
  retired and no declared step remains in the constitution.
- **Failure 8, the prox step's reach cap.** The copy is 256 of 256 exact (§3), against 237 of 256 in
  the previous loop. The cap was not tuned: nothing in the step reads the copy.
- **Failure 9, a refusal answered with a larger limit.** Every run ran once within its pinned bound.
  No bound was raised after a run.
- **Lesson 3, a located cause repaired in its owner.** The cause stood in `hnn::constitution` and is
  repaired there. The gap found beside it is closed in the same owner: a declared boost's signed
  stiffness breaks the passivity every gain assumes, so every step through it is refused
  (`ActiveContact`), as a pumped resonator's is.

## 2. The certificate

The pins record §1 states the law and the owner's module header states it whole ("The factor
families' certified step"). A factor family's unit step is `D = G_x/h_x′` in its metric `h_x′`, its
alignment `a = |G_x|²/h_x′`, its covector scale `c` at its output. Its curvature is
`C = B·½·κ²·b(η)`:
- `b(η)` is its output's moves along the whole ray, read at the ray's end by the Schur test;
- `κ²` is the gain from that output to the stations:
  - the element's gain for the passive factor, the slices and the standing's lock chart;
  - the source's gain for a pair port;
  - the solve's difference power for a channel and a loaded resonator.

The step is the largest dyadic with `ηC ≤ a` and `ηc ≤ 1`, halved with every other family until each
holds. [agent-inferred] The comparison reads its readings at 64 significant bits (`a` at its floor,
each factor of `C` and `c` at its ceiling), which implies the exact certificate. The exact readings
run to thousands of bits from the pullback.

The Lean statements, with their `#print axioms` in `Framework/HolonObject`, are in `Holon/Deposition`
§8:
- `factor_unit_step_alignment`: `⟨G, h⁻¹G⟩ = h⁻¹|G|² ≥ 0`;
- `square_ray_identity` and `square_ray_move`: a square carrier's output moves along its ray by
  `(t − s)(B(D, x) + B(x, D)) + (t² − s²)B(D, D)`, bounded by `|t − s|‖B‖‖D‖(2‖x‖ + |t + s|‖D‖)`;
- `square_ray_deriv` and `square_ray_deriv_bound`: its Jacobian is at most `2‖B‖‖D‖(‖x‖ + η‖D‖)` on
  `[0, η]`, the move `gauss_newton_curvature` reads;
- `contracting_resolvent`: `m ⪰ 1` gives `|ζ| ≤ |m ζ|`;
- `transit_difference_power`: the transit's difference state carries at most
  `(G/(2h) + ½(G/h)²c + ⅛G²k)|δζ|²`, and the loaded resonator is the case `G = 2Y`.

## 3. The runs

Each process ran once, on the host, in release, alone, within its pinned bound. The GPU was idle.

**Text training (acceptance 1): passes.** One pass over all 385 choosing pairs (sha256
`c6e51a35…0816`), 25 deposits:
- every check held: 385 of 385 balances, pairings and commits; 25 of 25 unreached checks over 175
  loci;
- the committed energy bound held at 385 of 385 commits;
- the largest entries over the run: `R` 1405/1024, `E` 524865/1048576, `W_c` 1/2048, the standings
  `q₀` and `q₁` 1/2048, every other factor family at its founding value (`c` 1, `b` ½, `F` ½, `f` ½,
  the slices 1). All are below 8; the previous loop's `q₁` reached `8 + 517/1024`;
- **the storage growth product is 1**: `ε_k = 0` at every deposit, against a product between
  `2²⁷⁴` and `2²⁷⁵` with the declared factor step;
- the certified steps: `R` `2⁻²..2⁰`, `E` `2⁻¹⁹..2⁻¹⁴`, `W_c` `2⁻¹⁶..2⁻¹¹`, and the factor families
  `2⁻²³..2⁻⁷` (the standing `q₀` the largest);
- the training sections coded `97224 + 1/16 + ε` bits over 12,320 stations, against
  `97342 + 10/16 + ε`;
- 121,975 ms training (projected 150,000–260,000), peak 680,660,992 bytes.

The 8 sections of the pinned text reading were generated into the owner-only file: 2 released and
6 held (a plural section is a typed refusal). They are shown only in the worker's report.

**The moiré (acceptance 2): passes at `K = 4` and `K = 8`.**

| `K` | Checks / unreached | Energy bound | Exact | Largest entry | `k`: `R` / `E` / `W_c` / factor families | `∏(1+ε_k)` | Training, peak |
|---|---|---|---|---|---|---|---|
| 4 | 512 of 512 each / 32 of 32 (64 loci) | 512 of 512 | 6 of 6 (48 of 48) | `R` 2683/1024 | −2..0 / −17 / −13..−12 / −21..−11 | 1 | 101,650 ms, 508,944,384 bytes |
| 8 | 512 of 512 each / 32 of 32 (0 loci) | 512 of 512 | 6 of 6 (48 of 48) | `R` 701/512 | −3..0 / −18..−17 / −13..−11 / −20..−11 | 1 | 209,183 ms, 602,324,992 bytes |

**The copy (acceptance 2): 256 of 256 exact**, 2,048 of 2,048 stations, against 234 under `γ_U = 1`
and 237 under the certified linear step:
- every check held (1,536 of 1,536 each; 96 of 96 unreached checks over 672 loci), and the energy
  bound held 1,536 of 1,536;
- largest entry `R` 13269/2048;
- certified steps: `R` `2⁻²..2⁰`, `E` `2⁻¹⁵..2⁻¹⁴`, `W_c` `2⁻¹³..2⁻¹¹`, the factor families
  `2⁻²¹..2⁻⁹`;
- storage product 1;
- 182,605 ms training and 5,857 ms evaluation, peak 389,165,056 bytes.

The previous record named the cap the Gram's, since `ηc ≤ 1` bounds `R`'s step. Two things changed
on this path: the factor families' declared step is gone (the standing, element and contacts no
longer move under the readout at every deposit), and `B` now counts them, so `R` steps by
`2⁻²..2⁰` against `2⁰..2¹` before. The Gram's `ln det` still bounds the prox step's reach, and the
copy no longer meets it. [agent-inferred] The cap was the factor families' uncertified motion, not
the Gram's retention; the step was not tuned around it.

**The standing cut's held-out code (acceptance 3): longer.** The residue chart on the host, 3,074
windows (sha256 `39621d52…7fbc`), complete, no budget stop:

| Reading | `γ_U = 1` | The certified linear step | Every family certified |
|---|---|---|---|
| held out, the field's face | `5459 + 13/16 + ε` | `5462 + 4/16 + ε` | `5472 + 3/16 + ε` |
| held out, the tree alone | `5476 + 3/16 + ε` | `5476 + 3/16 + ε` | `5476 + 3/16 + ε` |
| held out, the field's part | `−17 + 10/16 + ε` | `−14 + 1/16 + ε` | `−5 + 15/16 + ε` |
| development, the field's face | `13069 + 5/16 + ε` | `13068 + 7/16 + ε` | `13070 + 8/16 + ε` |
| `Kt` | `19992 + 3/16 + ε` | `19991 + 12/16 + ε` | `19997 + 12/16 + ε` |

- The held-out code is longer than the certified linear step's by more than `9 + 14/16` and less than
  10 bits, and longer than the old step's by more than `12 + 5/16` and less than `12 + 7/16` bits. The
  field's share of the held-out code falls from about 14 bits to about 6.
- 9,222 tick balances and 3,074 word balances closed. There were 6 aeon boundaries and 4 key
  locations.
- On campaign 1's field the receiving map stays small, so the gains are small, and the certified
  steps are large:
  - the factor families `2⁻³³..2¹⁰` (the passive factors the largest);
  - `W_c` `2⁻⁷..2⁹`, `E` `2⁻¹¹..2²`, `R` `2⁰..2²`.
- **The storage growth**: `ε_k` from 0 to 1/32 in one deposit; the product over 3,072 deposits lies
  between `2⁸` and `2⁹`, against `2¹⁵⁴..2¹⁵⁵` with the declared factor step.
- 353,824 ms (projected 560,000–700,000, bounded at 720,000), peak 385,925,120 bytes.

**Time.** Every run finished within its bound. The moiré and the copy ran inside their projections.
Text and the exposure ran below their projections' lower ends: the development reads' per-window
growth did not carry to the full runs.

**Gates.**
- `cargo check --workspace --all-targets` is clean.
- `cargo test -p holonics --lib`: 923 passed. The tests the retired declared step levered on now
  read the law:
  - the fixtures at `R = 0`, where the certified step is the covector bound's;
  - the storage refusal read on a rank-one storage at the constitution;
  - the port's refusal through a declared boost;
  - the reached gain return's certified step read through its carry, its move far below the gain's
    lattice unit on its fixture;
  - three new tests: every family steps by its certificate on a generic constitution, a channel step
    through an unbounded conductance is refused, and a storage grown outside its range is refused.
- The GPU suite, alone on the idle card under the lock: 32 passed in 56 s. The resonators' parity
  test no longer carries a boost, since a boost refuses every step; the refusal's parity test reads
  the boost's refusal on both ports.
- `bash tools/lean_check.sh Holonics HolonicsResearch`: built, no `sorry`.

## 4. Verdict

- **Failure 5 is answered for every family.** Text holds the entry bound the declared factor step
  broke: the standing reached `1/2048` against `8 + 517/1024`. Every check and every committed
  energy bound holds on text, the moiré at `K = 4` and `K = 8`, the copy and the standing cut.
- **The storage bound is tight, measured.** The product is 1 on text (against `2²⁷⁴..2²⁷⁵`), 1 on
  the moiré and the copy, and between `2⁸` and `2⁹` on the standing cut (against `2¹⁵⁴..2¹⁵⁵`), with
  no single deposit above `1/32` (against `2²⁸`). On the prediction field it is tight because
  nothing grows: the factor families' certified steps are `2⁻²³..2⁻⁷`, below their lattices' units,
  so the contacts' and the element's factors never move.
- **The factor families barely move on the prediction field.** Only the standings and the contrast
  ports move, by `1/2048` to `5/2048`. The certificate's curvature compounds three upper bounds: the
  readout's Schur bound, the Cauchy–Schwarz count `B` over about 10 families, and the gain over every
  tick and station. Against the families' small alignments it certifies steps far below a lattice
  unit.
- **On campaign 1's field they move**, with steps up to `2¹⁰`. The held-out code is `9 + 15/16` bits
  longer than the certified linear step's, and the field's part of the code shrinks from about 14 bits
  to about 6.
- **The copy is exact (256 of 256)**, and the moiré holds 6 of 6 at both depths.
- **Text's sections are two of 32 spaces and six held.** The readout still sits at the byte marginal
  (the lessons' failure 4, located September 25 and still unrepaired), and the certified step does
  not move it. The blocker, by measurement: the field's released sections read the most frequent
  byte at every station.

## 5. Owed in #62

"The factor families' certified step" (September 29):
1. The factor families' second-order terms along their rays: the square's own `2B(D, D)` paired with
   the station covector, the element's resolvent `(I − ½K)⁻¹` and the transit's `m⁻¹` differentiated
   twice, and the ticks' products. The Gauss–Newton curvature bounds only the logits' first-order
   moves.
2. The Schur test `‖W‖₂² ≤ ‖W‖₁‖W‖_∞` and its composition into each family's moves `b(η)`: the
   square's move is proved over the operator norm (`square_ray_deriv_bound`), the slices' and the
   pair port's by Cauchy–Schwarz in Rust only.
3. The composition of `contracting_resolvent` and `transit_difference_power` into the channel's and
   the loaded resonator's gain `κ²` over a word's ticks and stations, with `active_element_growth`.
4. The standing's fold. Its certificate holds in its lock chart; the element reads only the classes,
   so a class that crosses its fold jumps, and no curvature bounds the jump.
5. A declared boost's growth bound. Its signed stiffness stores indefinite energy, so every step
   through it is refused until the bound exists, as for the pumped resonator's Floquet bound.
6. The conductance bound `G_a = 2^(−β_a Q_a/2) Y_a ≤ Y_a` at `β_a ≥ 0` as a Lean statement, and a
   bound at `β_a < 0`, where a channel family's step is refused.
7. The certificate at its faces: `ηC⁺ ≤ a⁻`, `ηc⁺ ≤ 1` at 64 significant bits implies the exact
   certificate (`holon::deposition::significant`).

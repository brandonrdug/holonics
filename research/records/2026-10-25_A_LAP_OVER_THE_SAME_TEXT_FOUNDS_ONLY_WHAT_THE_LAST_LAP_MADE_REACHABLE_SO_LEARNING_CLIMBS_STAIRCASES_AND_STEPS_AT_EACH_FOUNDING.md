# A lap over the same text founds only what the last lap made reachable, so learning climbs staircases and steps at each founding

**Date:** 2026-10-25. Refs #404 #405 #410. Follows
[the effective-tension record](2026-10-24_WHAT_A_CONTACT_CANNOT_BRIDGE_IS_ITS_EFFECTIVE_TENSION_AND_THE_TENSION_FOUNDS_THE_FACE_THAT_CARRIES_IT.md)
and [a moment is a lap](2026-10-23_A_MOMENT_IS_A_LAP_AROUND_A_SINGULARITY_AND_LOOKING_AGAIN_CLOSES_THE_CHECK_LOOP_ON_ANOTHER_FACE.md).
Status:
- the moment and Schur-complement laws are proved-standard (the effective-tension record);
- the lap law of §§1–5 is [definition; agent-inferred, October 25], and its checks are exact;
- §1's reading that a lap's deposit is the bridge, refounded exactly, is measured on the tower (§1,
  "Measured" and "The bridge is refounded exactly");
- the reach predicted for the tower in §6 is a guess, to be measured by the acceptance in §7.

**Brandon's lens (paraphrased, October 25, on the orientation document).** Language is
combinatorial potential and its usage. Even one paragraph exposes a finite set of constraints on the
consistency of the symbols it encodes, so a reader who knew no English could derive part of the
language from the message alone: that is the cryptanalysis. Plain text such as children's stories
helps only as primitive examples of composition that expose founded pathways to pivot from. The
nuance is that one can recursively pass over the composition of any sample and keep deriving
nuances on each pass; that is why forward and backward passes work. Transformers improve with more
data because they compact enormous amounts of it together; Holonics instead harmonizes information
and transport. Every impulse carried along an axis is a moment of communication, where information
is mediated and agreed upon.

This record states what one more pass over the same text can and cannot add, in the objects that
own it, and fixes the acceptance the design thread builds laps against.

## 1. A reread at one constitution returns the same moments

A lap rereads the passage through the held constitution and accumulates the tension record's
moments, `H = Σ f̄f̄ᵀ`, `B = Σ t f̄ᵀ`, `T = Σ t tᵀ`, so its tension is `S = T − B H⁺ Bᵀ`
(`contact.effective-tension`). These sums are sufficient (`learn.normal-law`): the same text read
through the same constitution gives the same `(H, B, T)` to the bit. So:

- **A lap that founds nothing adds no new evidence.** It can only finish the bridge, moving the
  material along `B` until `B` vanishes at the readout's optimum. The tension it leaves is the
  tension it met.
- **What makes a lap new is the constitution it reads through.** If the last lap founded a face,
  this lap's moments are taken over a different face, and its pool (§2) holds candidates the last
  lap could not form.

**The tower's passes so far are laps that found nothing.** A tower pass is not a strict reread: it
also re-encodes the carried state at the learning rate (the tower record, "The ring's readout is a
pair contact with the top face"). So it moves the material along its covector as well as the
bridge, without founding, and the tension stays where it was. The pair tower on eight times the text
([the tower record](2026-10-24_THE_TOWER_HEARS_THE_HOLONICS_TEXT_AND_EVERY_LOOK_IS_READ_BY_ITS_LOCK.md),
"Eight times the text", "One more pass", "The second pass"), in bits a byte:

| pass | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|
| held out | 2.791 | 2.645 | 2.585 | 2.543 | 2.511 | 2.497 | 2.469 |
| training | 2.767 | 2.396 | 2.299 | 2.220 | 2.171 | 2.134 | 2.114 |

- No pass founds. The held-out gains shrink (0.146, 0.060, 0.042, 0.032, 0.014, 0.028) and the
  gap to the training code widens from 0.024 to 0.355.
- The tension stays where it was: 98.5–99.2% of `tr T` in every medium after five passes (the
  effective-tension record, §7).
- The writing does not change: it still leaves its medium within a line or two.
- The pair forms founded once, beside passes 6 and 7, show the other failure. Their training gain
  grew two and a half times (0.012 to 0.030) while their held-out gain fell (0.007 to 0.005): the
  per-section path fits the training text without generalizing. The same forms solved in closed
  form on the frozen tower took 0.058 bits a byte off the held-out code.

This is the law's prediction for laps without founding [agent-inferred]: they converge on the
bridge, and the remainder and the writing stay put. The re-encoding has a second cost, which the
ring met: a face founded in one frame is read through factors held in that frame, and a pass that
re-encodes the state dephases it (the tower record, same section: 257 of 495 at the held-out units
before one pass, 65 after).

**Measured** (the tower record, "The push's factors learn with the tower, and the deposit under the
ring moves its frame"). The design thread ran one block pass from the founded ring tower with every
family held but the readouts, so the pass deposited only the bridge:
- the founded ring kept its read at the second operand's cell (379 of 495, as founded) and the
  tower's guess at the held-out units held (253 of 495, against 55 for the full pass);
- the held-out text coded 2.512 bits a byte, the lowest of every pass: the full pass coded 3.033 and
  the same pass on the tower without the ring 2.690;
- the training block coded lower as it was read too (2.190 against the full pass's 2.252).

So a lap deposits the bridge and leaves the constitution as it was founded until a founding
changes it; the design thread adopted this as the lap's deposit.

**The bridge is refounded exactly, not stepped** (the tower record, "The readout founded to its
precision, and the lap that undoes it"). The ring's readout founded by exact Newton rounds on the
code, each round paying half a nat for each free parameter it re-states, read 308 of 495 at the
held-out units. One readouts-only lap of section steps on the same block then took it to 247,
while the block's code at its own read fell from 2.186 to 2.167 bits a byte. Once the bridge is
solved to its precision, a step on the text it was solved on moves it only by the passage's noise.
This retires the stepped deposit after an exact founding, not the lap: a lap still rereads, founds
from the pool of §2, and, when it founds, refounds the bridge exactly to its precision. A lap that
founds nothing is the fixed point and deposits nothing.

## 2. A lap's pool comes from the faces the last lap founded

The tension record's first pool rule says the machine's own navigators generate candidates,
symmetrically, including the products of pairs of present faces. Applied lap by lap:

```text
lap k:  F_k = the present faces;   P_k = { f·g : f, g ∈ F_k } ∖ span F_k
        found from P_k by drop M Q⁺ Mᵀ (contact.tension-founds-face), rank by rank, while
        (N/2) log₂(S / (S − drop)) > ½ log₂ N + log₂ |P_k|
        F_(k+1) = F_k ∪ founded;   a lap that founds nothing is the fixed point
```

The charge is the tension record's: about `½ log₂ N` for the founded material column and the
description of the choice among `|P_k|` candidates. The decision is exact as
`(S / (S − drop))^N > N |P_k|²`. No lap count is chosen: the laps stop where nothing passes.

This is Brandon's recursion stated on the objects. Each lap reads the same composition through
what the previous lap founded, so the composition degree the machine can read grows with the laps.
A product of two present faces of degree `d` has degree up to `2d`, so after `k` founding laps from
single-symbol faces the reach is at most `2^k` symbols.

## 3. Laps climb staircases; a conjunction with no lower part stays dormant

A product candidate's drop is `M Q⁺ Mᵀ`, nonzero only when the remainder correlates with the
product's residual. So a lap can found a conjunction only when a lower part of it already carried
tension on the lap before. Compositions whose every part is reachable this way are staircases;
those with no lower part (parities) stay dormant, locks waiting for a key.

Exact checks (`laps_found.py`), every cell of `{±1}⁵` met `r` times, `x1..x4` offered as faces and
`z` withheld (the floor, tension `N`), scalar covector `t`:

| case | target `t` | laps (founded) | tension by lap |
|---|---|---|---|
| A, reread | staircase below | same `(H, B, T)` twice at one constitution | 96, 96 |
| B, staircase | `x1 + x1x2 + x1x2x3 + z` | 1: `x1x2`; 2: `x1x2x3`; 3: none | 96 → 64 → 32 = floor |
| C, parity | `x1x2x3 + z` | 1: none (fixed point) | 64 |
| C, foil | the same, pool of all triples offered at once | 1: `x1x2x3` | 64 → 32 |
| E, doubling | `x1x2 + x3x4 + x1x2x3x4 + z` | 1: `x1x2`, `x3x4`; 2: `x1x2x3x4`; 3: none | 128 → 64 → 32 |

At `N = 32` the savings are 9.36 and 16 bits against charges of 5.09 and 5.31 (staircase), and the
parity's pairs remove exactly nothing. The foil shows that the parity is reachable by a pool that
offers the whole conjunction at once: the reach is set by the pool's composition, not by how much
text was read. The doubling case founds a degree-4 face on the second lap.

## 4. The length of the passage lets a weak first step found; the laps carry it

The saving of a founding grows with `N`, while its charge grows only as `½ log₂ N + log₂ |P|`. So a
weak lower part of a staircase is under its charge on a short passage and over it on a long one.

| case D | target `t` | passage | laps |
|---|---|---|---|
| weak first step | `¼ x1x2 + x1x2x3 + z` | `N = 32` | 1: none (dormant) |
| | | `N = 288` | 1: none |
| | | `N = 320`, the least multiple of 32 that founds | 1: `x1x2` (7.10 bits against 6.75); 2: `x1x2x3` (160 bits against 6.97); 3: none |

So volume and laps do different work [agent-inferred]. More passage lets a weak first step pass its
charge, and laps climb from there. This reconciles "more data helps" with "laps over the same
composition are the lever". Without founding, more passage only adds remainder that no step keeps
(the effective-tension record, §4), which is what eight times the text showed.

## 5. The learning curve steps at foundings, and the laps end

- **Steps.** By §1 the tension changes only where a face founds, by exactly the founding's drop
  (the quotient formula). So the code length falls in steps, one per founding, and between steps
  only the bridge is finished.
- **Each step is predicted before it is taken.** The drop and its saving are read from the lap's
  moments before the deposit, so a lap states in advance what its founding should save. The
  measured fall on held-out text, against that prediction, is the reading that tells law from fit.
- **The laps end.** Each founding saves more than its charge, at least `½ log₂ N` bits, and the code
  is bounded below by the floor. So the number of foundings is at most
  `(L₀ − L_floor) / (½ log₂ N)`, and a lap with nothing to found is reached.

Known results this joins, credited in a line each: stage-like learning in deep linear networks,
where each mode of the input–output correlation is learned as one step in order of its strength
(Saxe, McClelland and Ganguli, 2014, arXiv 1312.6120); and the merged-staircase property, under
which gradient descent learns a sparse function on a two-layer network only when its high-degree
parts are reached through lower-degree ones (Abbe, Boix-Adserà and Misiakiewicz, 2022, arXiv
2202.08658). What the lap law adds [agent-inferred]: the step is a founding decided by code length
on exact moments, it happens only when the charge is paid, and the pool of the next lap is built
from what this lap founded.

## 6. What it predicts for the tower (a guess)

- The pair forms are the first lap's foundings: the last two bytes carry 40.72‰ of the tension at
  most, and four founded ranks carried 3.46‰ (the tower record, "Founding pair faces on the
  tension"). The tower record reads the pair face as spent at that grain.
- The second lap's pool holds the products of those forms with the faces beside them (the byte
  before, the tower's top state). By §2 that reaches three and four bytes, and further where the
  tower's own state carries the passage (the situated pool `top ⊗ x̂`).
- On the training text, the order-3 count prediction, a conjunction of the last three bytes read
  from the Witten–Bell model over contexts up to six bytes, removed 29.93‰ of the tension, against
  7.18‰ for the linear faces of the same three bytes (the effective-tension record, "The floor
  split"). If text's conjunctions are staircases, the second founding lap should reach that
  order-3 horizon, and the forms of each lap should hold on held-out text as the pair forms did.
  The Witten–Bell model's out-of-sample lead on held-out text (its Brier, in the same record) is
  the further horizon a third lap would reach toward.
- If a lap finds nothing to found while the count model still beats the tower, the missing contrast
  is not a staircase from the present faces, and the next subject is the pool's navigators, not
  more passes.

## 7. Acceptance for laps, fixed before the build

For the design thread, which builds laps in the learner.

Each lap rereads the training text at the held constitution, founds from the pool generated by the
present faces (including every face founded on an earlier lap) under the charge of §2, and then
refounds the bridge, the readouts, exactly to its precision, with no section steps, holding the
founded constitution (§1, "Measured" and "The bridge is refounded exactly"). The laps stop at the first lap that founds nothing. Each lap reports:
- every founding, with its face, its degree, and its predicted drop and saving against its charge;
- every earlier founding's drop retested at this lap's constitution, against its charge (a founding
  that falls under its charge has been dephased by the deposit, as the ring was);
- training and held-out bits a byte per medium, and `tr S` per medium;
- the writing at each prompt, whole.

It passes when:
1. held-out bits fall at every lap that founds, against a foil lap with the same deposit and no
   founding;
2. no lap lowers the training code while raising the held-out code (the memorizing foil, already
   met by the pair forms' second pass);
3. a face founded on a lap after the first is a product involving an earlier lap's founding and
   passes its charge (the composition climbs past two bytes);
4. the laps stop on their own, at the fixed point;
5. no earlier founding falls under its charge when it is retested on a later lap.

The recorded failures this could repeat: bits read as progress (the acceptance reads held-out bits
only against a foil lap, and shows the writing beside them); a refusal answered with a larger
limit (the laps stop at the fixed point, never at a raised count); seen material graded as unseen
(the held-out text is read by no founding); an authored routine standing in for learning (the pool
is products of the machine's own faces, and no conjunction is named).

## 8. Owed

Lean (#410, one box, "Laps found by composition (#404)"):
- the tension of a lap that founds nothing is the tension it met (a reread at one constitution is
  the identity on `(H, B, T)`);
- founding `c` lowers the tension by `M Q⁺ Mᵀ ≥ 0`, so the tension is non-increasing over laps;
- a product of two faces whose remainder correlation is zero for every product of present faces
  founds nothing at any later lap unless a face is added;
- the number of foundings is at most `(L₀ − L_floor) / c_min` for a charge bounded below by
  `c_min > 0`.

## Receipts

[`2026-10-25_A_LAP_OVER_THE_SAME_TEXT_receipts/`](2026-10-25_A_LAP_OVER_THE_SAME_TEXT_receipts/):
`laps_found.py` (exact Fractions and integers; the bits are printed readings), its output
`laps_found.json` (every lap's pool size, foundings, drops, tensions, savings and charges, and the
least passage for case D), and `RUN.md`.

# The Holarchy and its aeons are the top; the Decisions dissolve into their owners; learning is prototyped where a Holarchy made the terrain

**Date:** 2026-09-27. **Scope:** a unity audit of the library, and the basis for prototyping
learning. Refs #63, #73, #147. **Grades:** the audit findings are `established-bounded` (read from
source at `289e63af`); the unification and the terrain basis are `agent-inferred`.

## The question

Brandon, September 27:
- The numbered "Decisions" were a habit of the agents, not his instruction.
- He asks for an audit of the unity of Holonics: is everything synthesized and consolidated in the
  library objects?
- On learning: the conversation logs are being used as the material. They may not be packaged for
  the learning the machine needs, and curating data is a separate problem from learning itself. Is
  there a better basis for prototyping learning? How is behavior being gauged on those logs?
- "Don't reinvent the wheel": past experiments, including the laboratory, bear on this.
- "Aeons and Holarchies are at the top."

## 1. The audit

### 1.1 The Decisions log mixes three kinds of text

`THE_REBUILD` has 3504 lines. Its `### Decisions` section, from line 2500 to the end, holds 39
numbered entries. They mix three kinds of text that the operating guide routes to different places
("documentation is the fix"):
- **definitions**, which belong in their object's guide or beside their owner;
- **measurements**, which belong in dated records (most already have one);
- **order**, which alone belongs in `THE_REBUILD`.

Rejected and superseded entries sit beside adopted ones: 33 (the Born face), 34's node-local law,
and 36 (second-arrival founding). The log grew by accretion. It keeps each choice's reason, which
is worth keeping, but it scatters each object's law across entries. For example, the receiving
tree's law is spread over Decisions 28–30, 32 and 34–37 and the module doc of `hnn::landmark`.

### 1.2 The working predictor is outside the object library

`hnn::landmark` is 5570 lines. It is the component that earns the HNN's bits: on the wide cut,
`1 + 15/16 + ε` bits a cell against PPM-2's `3 + 0/16 + ε`. It imports only `Rat`,
`ExactInterval` and `ceil_log` from the library. None of the objects its nouns name are used:
- **its retention** is not a `receiver::standing::StandingLaw`;
- **its node arrivals** are not `aeon::Epochs`, and its capacity carry (Decision 39) is not an
  aeon cycle;
- **its addresses** are not navigator words;
- **its "landmark"** is not `compression::landmark`. That is a different owner, rebuild step 3's
  landmark discovery (sites, fixed points, identities, primitive cycles), so two unrelated owners
  carry the name.

`hnn::receiving` likewise bypasses `receiver::{face, reception, standing}` for its tree faces.

### 1.3 Ten Lean modules stand apart from the framework

Ten of the 25 `lean/Holonics/HNN` modules import no framework object:
- `LandmarkCompaction`, `LandmarkCapacity`, `ConvergenceFounding`, `LocalWeighing`,
  `LandmarkCarrier`;
- `RegionCounts`, `StandingRead`, `TargetFace`, `Word`, `IndexedOpen`.

Their theorems are correct and checked, but they are not joined to `Foundation/Standing`,
`Aeon/Clock/Epoch`, `Holarchy` or `Compression`.

### 1.4 The machine's top is a field and a harness

The HNN's top is `hnn::field::Field` and the exposure harness `hnn::reference::Reference::expose`.
The Holarchy enters only as `Holarchy::parametric` inside `reference.rs`, and the aeon through
`EnclosedLedger` and the retention collapse.

### 1.5 What is already joined

- `hnn::modes` descends through `compression::FaceMap` and `receiver::standing`.
- `hnn::retention` reads `aeon::{Cycle, Epochs, EnclosedLedger}` and `holarchy::Count`.
- `hnn::field` builds on `holon::{parametron, contact, dirac, element}` and `aeon::ClockLift`.
- `hnn::port` reads `receiver::{face, receipt, reception, release}`.
- `hnn::ratio` reads `aeon::Reading` and the carried power.

## 2. The unification

- **The Holarchy and its aeons are the top** (Brandon; `agent-inferred` as a construction). The HNN
  is a Holarchy: its rings, contacts and receiving tree are Holons joined at ports by
  `interconnect`. Its passage is an aeon:
  - a receiving window is an epoch at the receiver's section;
  - a pump period or a clock closure is a cycle;
  - the aeon boundary is the collapse.

  `Field` and `Reference::expose` become charts of that pair, not the top.
- **The receiving tree is a mixture over retention quotients** (`agent-inferred`; the
  identification is exact). The chain of identities:
  - Each pruned context tree partitions the source's histories into classes that predict alike: a
    candidate standing, a `StandingLaw` on the source navigator's words.
  - Context-tree weighting weighs those candidates by the stop prior, and its dominance bound is
    the code cost of choosing among them (`LandmarkTree.own_kraft_and_dominance`).
  - A node's arrivals are the epochs of its section; the capacity carry acts at the register's
    cycle.
  - A node is a face where source paths converge. It is a landmark of the shift navigator, the
    same object `compression::landmark` finds for other navigators.

  The consolidation expresses the tree through these owners and names it once. Its own name
  becomes the receiver's standing mixture, so the two "landmark" owners no longer collide.

## 3. The basis for prototyping learning

### 3.1 How behavior is gauged now

On the conversation cut behavior is gauged only against baselines: online order-0, order-1 and
PPM-2. There is no ground truth. The cut has no known generator, keys or entropy rate. So a
failure cannot be told apart from absent structure. Campaign 2's letter families "add no bits on
text", and the keys "are located correctly where a machine made the data and are absent from text"
(campaign 1). The data's packaging and the learning law are measured together.

### 3.2 What the past established

The following comes from the laboratory at commits `c91914d5`, `32007c95` and `703b0dab`, and
from history at `13f8c734`:
- **The laboratory's rule.** Its May kickoff wrote: "Stop using whim-selected substrates.
  Construct them." Constructed microscopes are for structure and living substrates for the thesis,
  "never mix them".
- **Sources with a known generator** gauged learning against the truth: the prime stream against
  the coprime rate, Dyck depth against the known depth, clocked reach, the copy floor `log 26`,
  and exact arithmetic answers. Infinite generated arithmetic reached held-out exact-match on
  between 83 and 91 of every 100 queries, where a fixed corpus of 45k reached 14 of every 100.
- **Here, on machine-made cribs,** the HNN located the true key 128 times in 128.
- **What failed on real corpora:**
  - TinyStories and walks confounded depth, entropy and repetition;
  - code worlds enacted nothing;
  - pre-reset conversation exposure produced nothing useful, with replay 18/388;
  - campaign 2's rings found no letter family on text.
- **The golden-mean source's rate** `log₂ φ` is proved in `Foundation/ReceiverCodeCost`, and no
  testbed has used it yet.
- **Brandon's ruling of August 26 still governs the milestone.** The HNN must return "an
  inferred response and not a manually posed outcome", so every campaign's criterion stays on the
  real cut.

### 3.3 The basis

`agent-inferred`. Learning is prototyped on terrain that a Holarchy made:
- A declared Holarchy, run over declared aeons with drawn keys and constitution, generates the
  terrain.
- Its truth is exact: the entropy rate as an exact enclosure, the keys, and the constitution.
- Learning is gauged three ways:
  - **redundancy:** the HNN's code minus the true rate, never only against baselines;
  - **recovery:** the located keys and constitution against the drawn ones;
  - **attribution:** each mechanism's share, by a terrain that holds one kind of structure.
- The keys are drawn, not posed, and the terrain is the same objects the machine is made of. So it
  honours Brandon's August 26 ruling as a prototype.
- The conversation cut stays the living substrate and the milestone. The two are never mixed in one
  claim.

The first family, one terrain per mechanism:

| Terrain | Its truth | The mechanism it isolates |
|---|---|---|
| A tree source with a drawn context tree and drawn leaf faces | the tree and the rate | the receiving tree: does it recover the tree and reach the rate? |
| Rotation words: a rational rotation read at a grain, and the golden-mean shift | the period or the rate `log₂ φ` | the rings: lock, resonance, the helix that never locks |
| Rotor cribs (`hnn/tests/keys.rs::synthetic_crib`) | the key and the plugboard | key location (128/128 already) |
| An aeon-switching source: a mode silent for an aeon, then returning | the switch epochs and the dormant mode | dormancy across aeon boundaries (campaign 3) |

This also separates the two problems Brandon names:
- **Curating the conversation data** is exterior codec work (step 8, #148).
- **The learning law** is tested where the truth is known.

## 4. Order

1. Dissolve the Decisions log:
   - each surviving law goes to its object's guide or owner doc, with its reason;
   - each measurement goes to its dated record;
   - rejected and superseded entries become one-line pointers to their commits;
   - `THE_REBUILD` returns to order.
2. Put the Holarchy and its aeons at the top of `hnn`. Express the receiving tree through
   `receiver::standing`, `aeon::Epochs` and the source navigator's words. Join the ten free Lean
   modules to the framework.
3. Build the terrain owner and the first family above, with each terrain's exact truth receipt.
4. Continue campaign 3 on the aeon-switching terrain, then on the real cut.

## 5. The moiré terrain

Brandon, September 27: "Moire patterns and overlap/intersections -> color theorems. The gaps from
the patterns, it's exactly like polarity in charges and photons, lenses. Layers are like these as
lenses … emanating axes of foundings … The classes are like slit diffraction patterns, imagine
fraying threads through pathways of these as layers. Enigma and Bombe style."

**What the laboratory already had** (commit `3450a0bc`):
- `src/holobrochos/holo/src/found.rs::comb_upto` is "the sieve as moiré". Each founding lays its
  grating (its multiples). The residue no grating covers founds a new grating. The covered part is
  the span (the composites); the complement is the basis (the primes). It "never divides — it only
  lays gratings and reads the residue".
- Its `chance_floor` reads a founding as recurrence that outruns the moiré null `μ`, the coincidence
  rate that independent gratings give.
- `src/pureholonics/05_THE_WEAVE.md` holds the pair reading. Most lineage pairs are
  "moiré-null, phase-orthogonal" and conduct without relating. Only aligned ("bright-moiré") pairs
  weave.
- `03_THE_RELATING.md`: "the threshold is the three-body moiré null, never a stored constant".

**The joins to the objects** (`agent-inferred`; each piece is classical):
- **Layers are rings.** Each ring is a grating, a clock with its period. Their overlap is the joint
  clock torus, the Holarchy's parametric orientation (`Holarchy::parametric`). A fringe is a joint
  phase class, and the beat is the difference of the rates.
  - Bright moiré is a lock: the least-denominator rate in the fibre (the contact's lock address,
    Farey).
  - Moiré-null pairs are the dark, unlocked ones.
- **The coloring is the polarity.** The boundaries of the layers' cells form an arrangement.
  Coloring each face by the parity of the sides it lies on (the sum of the sheet readings, mod 2)
  properly two-colors it. That parity is the polarized side reading of a half-turn, the rings'
  sheets and their Ising lock. General maps need more colors; layered gratings need two.
- **The gaps found.** The uncovered residue of the existing gratings is the cokernel: faces no
  current ring reaches. It founds a new ring at its period. This is campaign 3's "founding by
  interconnect from the cokernel residual". The old sieve is its arithmetic instance, and the
  moiré null is its chance threshold.
- **The classes are diffraction orders.** A path through successive layers composes each layer's
  phase, like threads through lenses. Its class is the winding `m` of the composed phase read at
  the last section, as a grating's order is.
- **The Bombe reads a moiré.** Rotors are gratings stepping with carry. The key is the layers'
  relative phases, and the Bombe locates them by loop closure over the menu.

**The terrain.** The rings' first terrain (§3.3) is a moiré:
- A declared Holarchy of `k` rings with drawn periods and phases.
- Each tick emits the layers' joint class: the parity color, or the tuple of sheets, at a grain.
- The truth is exact: the periods, the phases (the keys) and the lock addresses. The entropy rate
  of the unmixed moiré is zero, so every bit the machine spends above it is the cost of locating
  the keys.
- Its founding variant is the sieve, where gratings are founded at the gaps. That is the
  laboratory's prime-stream microscope, whose truth was known.
- The gauges:
  - the keys located against the drawn ones;
  - the gratings founded at the true gaps;
  - the code length against the exact rate.

## 6. The first receipts on terrain (September 27, commit `ab416919`)

The owner is `holarchy::terrain`. It holds moiré, tree source, rotor cribs and aeon switching, each
drawn by the library's exact `Draw` and returned with its truth. The notebook is `hnn_terrain`.
These are development receipts, and the conversation cut stays the milestone. Each reading is
`+ ε` with `0 ≤ ε < 1/16`.

### 6.1 The receiving tree against a tree source's truth, at `n = 2^16` cells

The receiving tree learns what the source is:

| Source | `n·h` (the exact rate) | Tree code | Code against the source's own code | The ideal weighting bound | Recovered tree |
|---|---|---|---|---|---|
| depth 2, three leaves | `56543 + 13/16` | `56464 + 2/16` | `+27 + 1/16` | `33 + 7/16` | the drawn tree, 16 of 16 addresses |
| depth 4, eight leaves | `47257 + 8/16` | `47134 + 11/16` | `+51 + 4/16` | `79 + 5/16` | the minimal tree, 64 of 64 |

- Both codes lie below `n·h`. That is a sample's own fluctuation: the source's own code is lower
  still.
- At depth 4, two drawn leaves share one face, and the tree merges them. It recovers the coarsest
  tree with the same faces, which is the retention quotient: two histories that predict alike are
  one standing.

### 6.2 The moiré locates two failures

Three gratings, with keys `14/15 @ 5/15`, `4/15 @ 10/15` and `11/16 @ 12/16`, joint period
`240 = 2^4·3·5`, and a key description of 30 bits:
- **The depth rule stops at a plateau.** The harness's depth sweep stops at the first code that
  does not fall, below the determining depth `D*`: `D = 10` against `D* = 14` for the parity
  class, `D = 5` against `D* = 8` for the sheet tuple.
  - At the chosen depths the codes are `2016 + 6/16` (parity) and `5427 + 1/16` (sheets), with
    `17 + 13/16` and `62 + 10/16` bits a period still spent at period 67.
  - At `D*`, read as a control and not a choice, they are `993 + 5/16` and `1549 + 0/16`.
- **The tree memorizes a moiré it could name.** Even at `D*` the zero-rate terrain costs about 30
  times its key description. The tree learns the pattern's contexts, not its gratings. The rings
  exist for exactly this terrain; the gap between those 993 bits and the key's 30 is theirs to
  earn.

### 6.3 What the rings need to be measured on it

- **Parallel gratings.** The field's selective law carries a ring's overflow to the next ring, an
  odometer. Moiré gratings are independent: they need rings with no carry between them.
- **A rate is a plugboard.** Stepping one port a cell carries grating `i` exactly under the key
  `p_i⁻¹c_i`, since `(c + tp) mod q = p((p⁻¹c + t) mod q)`. The sheet letter must read the ports
  with that relabelling declared.
- **The Bombe for a moiré.** `hnn::keys` builds its menu from port-to-port edges, and a moiré cell
  (a parity or a tuple) gives none. Locating the phases needs a menu of parity constraints on the
  joint clock torus: with the rates known, one relation a tick over at most `Π q_i` phase
  configurations.
- **Locks at the winding grain.** Over one joint period the contact letters read the pairs' locks
  coarsely (`19/14` for the true `224/165`). The pair lock is not resolved within a period.

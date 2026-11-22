# A helix carries two signs and its hand is their product; a ring alone has none; the mirror carries order, comparison and storage, and separates finding from checking; and a chain composes where its contacts meet opposite hands

November 22, a cloud thread, 21:27 to 22:30 UTC. Refs #386, #404, #410. A lens of Brandon's of 21:26 UTC, derived and joined to its
owners. Nothing here ran on the card or opened a state of the line: the readings are of the code, the guides, Lean and committed
records. The one read of the line is a guess fixed for the lead (§7). Lean: `HolonicsResearch/HNN/PumpedMoveKinds` (new).

## 1. The lens

Stated in this record's words, without a molecular derivation (the abstraction is what was asked, as on October 1 and November 15).

- A problem and its solution are one relation read from two sides: a lock and its key, a cipher and its analysis. Which of them is
  the problem is a matter of the side one reads from, and a key can arise where no lock was built for it.
- Heterochirality: two families of opposite hand, coupled, modulate each other's twist and torsion.
- A compound forms by chaining. Where the local hands of its parts further each other's induction, the parts roll into a larger
  motion (a lightning channel, a vortex), and no such motion appears without the conditions it rolled from.
- What is called generalization is familiarity with a locale. Beyond the locale is further learning, at the rate that crossing new
  media allows, and no learner absorbs everything, since the absorbing makes new differences.
- No global clock is privileged; time is a comparison (already the aeon law).

On the objects: the hand is a sign relation between a navigator's turn and its carry; a lock and its key are a face `⟨Ȟ|H⟩`;
chaining is the gluing of a Holarchy along its contacts; familiarity is a receiver's quotient after its readings.

## 2. What the tree held

Recovered before any statement below (the atlas first, then the guides, records, Lean and the engine):

| Subject | Owner | What it states |
|---|---|---|
| a helix's hand | [the pair's trigonometry, September 19](2026-09-19_THE_TRIGONOMETRY_OF_A_HELICAL_PAIR_IS_TRIGONOMETRY_OVER_A_TWO_SIDED_ANGLE.md) §2; [HELICAL_GEOMETRY](../../docs/HELICAL_GEOMETRY.md#a-helix-and-its-independent-collapses); `screw.axis-and-pitch-exact` | the sign of the reduced pitch, a side of the Klein form's null cone; no continuous family passes between hands without an event; "chirality and traversal direction are not the same face" |
| the duplex | [the helical code](../../docs/ELEMENTARY_OBJECTS.md#the-helical-code-how-holons-encode), item 2; `helical.partner-face`, `helical.dihedral-frames` | the partner is the dyad's image, `JĜJ = Ĝ⁻¹`, one dihedral group `⟨S, U⟩`; on a rotation carrier the dyad is conjugation |
| a ring's own hand | Lean `HolonicsResearch/HNN/RingHand` (the October tower's `hand_after`, PR #471); `hnn.tower-ring-face`, `hnn.tower-pumped-mode` | a pumped move `h ↦ λh + β conj h` has determinant `|λ|² − |β|²`; the ring is read in its own hand, the sign of its moves' determinants since its last collapse |
| a symbol's three moves | `radix.symbol-move-turn-halfturn-collapse`, `radix.base-neighbour-rings`, `colour.colourless-faces` | on a ring a digit's move turns (`λ = 1`), mirrors (`λ = −1`) or collapses (`λ = 0`); on November 18 the engine's clocks held the turn alone, "October's missing reflection" |
| the pumped carry | `crates/engine/src/carry.rs` (`carry_gate_pumped`); `contact.pumped-carry`; [CONSTRUCTION_STATE](../../CONSTRUCTION_STATE.md) | each circle moves by `Q = κb + γQm + η conj(Qm)` since November 19; on the dihedral separator it held the running product at 0.996 at three times its trained length where the plain carry read 0.357; at P48 the pump's rows stood at a tenth of the turn rows; no hand register |
| relative phase | Lean `HNN/NestedPairs`; `receiver.pair-reads-relative-phase` | no reading real-linear in two strands holds their relative phase in its mean; a turn times a mirror turn does |
| mass | [mass is light paired with its reflection, September 26](2026-09-26_MASS_IS_LIGHT_PAIRED_WITH_ITS_REFLECTION_AND_THE_SHADOWS_ARE_ITS_NODES.md) §1 | two massless chiral halves coupled at a rate give the shell `±√(c²k² + m²)`; the gap is their avoided crossing |
| gluing | Lean `Foundation/ExactPartition`; `holarchy.exact-partition` | cut boundaries paired with opposite hands cancel (`mate ∘ mate = id`) |
| vortex lines | Lean `Fluid/HelicityAsLinking`, `Transport/HelicalCode`; `fluid.helicity-linking`, `helical.crossing-change`, `fluid.kelvin-holonomy` | helicity is the circulation-weighted linking of vortex strands; a crossing change moves it by its hand sign |
| twist and writhe | the helical code, item 5; `helical.closure-remainder-held-by-the-locale` | `Lk = Tw + Wr`; closing a duplex holds a remainder as strain, which past a threshold buckles twist into writhe (the decomposition is owed; no crate reads `Lk`) |
| finding and checking | `key.kernel-of-a-locale`, `key.consistency-with-carried-residues` (November 20) | inside a locale finding costs what checking costs because the locale bounds a parameter (kernelization); systems of equations over a finite group are polynomial when it is abelian and NP-complete otherwise (Goldmann and Russell, 2002) |
| familiarity | `unicity.never-collapsing-class` | after finitely many readings the survivors are the key's class up to the admitted future, and readings of the same kind never go below it |

The slip of this thread: its first answer said the tree had never made the hand a quantity of its own. `RingHand` had made it in
October, and the atlas row of November 18 had read its absence from the engine. The answer was corrected within the hour. The
search had matched words (`chiral`, `handed`) and had not listed the Lean modules of the subject's directory.

## 3. A helix carries two signs; a ring alone has none

[proved-derived; formal-checked, `PumpedMoveKinds` §4]

- A helix's step is a turn `a` with a carry `c`. Its hand is the sign of `a·c`, the reduced pitch's sign `h = (ω·v)/(ω·ω)`
  (`hand`).
- The dyad reverses both, keeps the hand and is the inverse step (`dyad_keeps_hand`, `dyad_is_inverse`). This is the helical code's
  `JĜJ = Ĝ⁻¹`: the duplex is antiparallel and of one hand.
- The mirror reverses the turn alone and flips the hand (`mirror_flips_hand`). Where the turn and the carry are nonzero it is
  neither the step nor its inverse (`mirror_ne_step`, `mirror_ne_inverse`): the heterochiral partner is another helix, outside
  `⟨S, U⟩`.
- Read on the turn alone the two are one map (`turn_alone_cannot_tell`). A complex ring that does not carry its carry is that case:
  conjugation reverses its turn, and it cannot tell the antiparallel partner from the heterochiral one. The guide's "on a rotation
  carrier the dyad is conjugation" holds for this reason, and the code's frames `ZMod p × Bool` carry one orientation bit where a
  helix carries two.

[interpretation] The hand is a relation between grains: a ring's turn read against its carry into the reader above it (an epoch's
count, a level's tick). A ring alone has none. The engine's circles carry both signs, the scan's direction (`Q_(t∓1)`) and the
sign of the turn's chart `q`, and their product is each circle's hand; it has not been read on the line.

## 4. The mirror carries order, comparison and storage, and separates finding from checking

[interpretation, on the proved parts named]

- **Order.** Turns of one hand commute, and a chain of them composes to a sum, which forgets its order. A turn with a reflection
  generates the dihedral group, `USU = S⁻¹`, where `SU = US` only if `S² = 1` (`reflection_turn_ne`, `dihedral_conj`). The
  pumped carry's 0.996 against 0.357 is this measured on the engine.
- **Comparison.** The relative phase of two strands is held only by a turn paired with a mirror turn (`pair_reads_relative_phase`).
  A face `⟨Ȟ|H⟩` pairs a ket with a bra, its conjugate: every face is a heterochiral contact.
- **Storage.** Two light lines of opposite hand coupled at a rate open a gap, and a standing wave is light meeting its reflection
  (the record of September 26). A store is that coupling.
- **The lock and the key.** Composing multiplies turns, `ζ^a ζ^b = ζ^(a+b)`; comparing pairs a turn with a mirror turn,
  `conj(ζ^a) ζ^b = ζ^(b−a)`. It is one product, and the mirror on one operand is the change of side, as Stokes,
  `⟨dȞ, H⟩ = ⟨Ȟ, ∂H⟩`, moves the operator across the pairing. A key fits where the paired product stands still over the common
  turn. A key of the wrong hand leaves a product that turns, whose mean over a cycle is zero (`mean_turn`): no flux crosses.
- **Finding against checking.** Over turns of one hand the group is abelian, and a system of equations in it is solved by
  elimination: finding costs what checking costs. With the mirror the group is dihedral and non-abelian, and solving systems of
  equations over it is NP-complete (Goldmann and Russell, held in `key.consistency-with-carried-residues`), while a proposed word is
  still checked by one product. The reflection that lets a chain hold its order is the reflection that makes finding a word cost
  more than checking it. Inside a locale whose parameter is bounded the two costs meet again (`key.kernel-of-a-locale`). No claim
  on P against NP is made; the cause this places is the non-commuting move.

## 5. A pumped move's kind

[proved-derived; formal-checked, `PumpedMoveKinds` §1 to §3, with `RingHand`]

```text
M(h) = λh + β·conj(h):   det = |λ|² − |β|²,   tr = 2 Re λ,   tr² − 4 det = 4 (|β|² − (Im λ)²)
turn            |β| < |Im λ|                       the phase keeps turning; no axis is held
free fall       |β| = |Im λ|                       the parabolic threshold
lock            |Im λ| < |β| < |λ|                 two real axes: the phase is held to one, the other shed
collapse        |β| = |λ|                          onto a line
flip            |β| > |λ|                          the plane's hand reverses at each move
```

A common real scale of `λ` and `β` scales the determinant and the discriminant by its square, so the leak that divides both moves
no kind. On the engine's circle, `λ = γ̂(q)/(1 + d + n)` and `β = p/(1 + d + n)`:

```text
det  = (1 − |p|²) / (1 + d + n)²
disc = 4 (|p|² − (4q/(4 + q²))²) / (1 + d + n)²
a turn ⇔ |p| < 4|q|/(4 + q²),   a flip ⇔ |p| > 1      (p and q on their charts' unit)
```

These are the Swing's three kinds with the hand beside them. [interpretation] What a lock prevents is the turn: in the turn regime
the phase of what crossed the circle keeps rotating and no axis is preferred, and past the threshold the circle holds one axis
and sheds the other, so a drive on the held axis passes. The threshold is free fall, the kind a bound orbit meets at its escape
speed.

## 6. A chain composes where its contacts meet opposite hands

[interpretation, on the proved parts named]

- Two cells glued along a face induce opposite hands on it. The face cancels (`pairedBoundaryCancels`, `mate_mate`; `∂² = 0`), and
  the circulation around the joined region is the sum of its parts' (Stokes; Kelvin's circulation, `fluid.kelvin-holonomy`). Where a
  contact meets one hand from both sides it doubles instead of cancelling: the gluing is not orientable there, a typed gluing defect
  of the Holarchy.
- The rolling. A vortex grows where many small circulations share a hand, since their sum is its circulation; with mixed hands they
  cancel. In ideal flow the chiral charge, the helicity `H = Σ lk(i,j) Γ_i Γ_j`, is conserved, and a crossing change moves it by
  `sign(c)·Σ Γ_i Γ_j` (`helicity_cons`, `sum_crossingChange_sub`). A compound's chiral charge is carried in by its parts or made at
  a crossing, and a crossing dissipates.
- The sign of a new level (`agent-inferred`). Closing a duplex fixes `Lk`, and the remainder `ΔLk = ΔTw + ΔWr` is held as strain
  that past a threshold buckles twist into writhe (the helical code, item 5). The writhe, the coiling of the level above, takes the
  sign of `ΔLk`. A level founded by that snap (read as grokking on November 15) has the hand of the strain its parts could not close.
- Across levels a multiplier keeps, mirrors or collapses the hand: `λ = 1` on `ℤ/(b − 1)` (the digit sum), `λ = −1` on
  `ℤ/(b + 1)` (the alternating sum), `λ = 0` on `ℤ/b` (the last digit) (`radix.symbol-move-turn-halfturn-collapse`). Both chiral
  rings read a sum's class without its carry, which lives on the rings where the multiplier turns.

## 7. What follows for the machine

For the lead, who owns the engine; reads only, nothing built here.

1. **The kinds of the line's moves.** Fixed at 21:37 UTC by `date -u` and sent through the coordinator: on the line's lap mean, the
   share of (site, circle) moves of each kind by §5 (a turn where `|p| < 4|q|/(4 + q²)`, a lock up to `|p| = 1`, a flip past it), by
   region (letters, digits, spaces, a word's first letter) and by surprise fifth, with each circle's hand (the scan's direction times
   the sign of `q`) beside it. Guess: at least 90% of moves are turns and under 1% flip. If turns dominate, her circles almost never
   commit, which the lens reads as why her composition stops at two or three words; the change it points to (the pump's founding
   and rate) is the lead's.
2. **The ring's own hand, recovered where flips exist.** October's `hand_after` reads a ring in its own hand (`hand_reads_positive`:
   `o · ∏ det M_i > 0`), so a turn met after a flip is read turning the other way. With no flip on the line the register stays `+1`
   and is inert, so it follows read 1 and is not a change before it.

What does not transfer: no molecular law, and nothing that branches on a kind of input.

## 8. The targets read by what a reflection fixes or forces

[interpretation; the functional equations and Hodge symmetry are proved-standard, from training]

- **RH.** `ξ(s) = ξ(1 − s)` and `ξ(s̄) = conj ξ(s)` make the zeros symmetric under `s ↦ 1 − s̄`, a mirror whose fixed set is the
  critical line. The hypothesis asks that every zero be fixed by it. Hardy's `Z` is the self-dual superposition of the wave and its
  image (the record of September 26, §2).
- **Hodge.** Conjugation carries `H^(p,q)` to `H^(q,p)`. A Hodge class is a rational class whose only part is the one conjugation
  fixes, `(p,p)`, a class with no handed part; the conjecture asks that each be composed from algebraic cycles.
- **BSD.** `Λ(E, s) = w Λ(E, 2 − s)` with `w = ±1`: the functional equation's sign is the L-function's hand, `w = −1` forces
  `Λ(E, 1) = 0`, and the order at the centre has the parity `(1 − w)/2`. The conjecture reads that order as the rank, a count of
  independent generators.
- **Navier–Stokes.** Helicity is odd under a mirror: it is the flow's chiral charge, conserved by Euler on material cycles and
  changed by viscosity at reconnections.
- **P against NP.** §4: the move that does not commute.

## 9. Familiarity is a receiver's quotient

After finitely many readings the survivors are the true key's class up to the admitted future, and readings of the same kind never
go below it (`unicity.never-collapsing-class`). What is called generalization is that quotient on the locale its readings came
from, where finding costs what checking costs (`key.kernel-of-a-locale`). Separating further needs a reading of a new kind, a new
medium or a new receiver, which is further learning at the cost of crossing that medium. The receiver's clock is the aeon law's: elapsed
time is the pairing `⟨ω_R | γ⟩` at a receiver, never a global count.

## 10. Owners

- Lean: `HolonicsResearch/HNN/PumpedMoveKinds` (new), imported by `HolonicsResearch.lean`.
- Atlas: `helical.two-signs-hand`, `motion.pumped-move-kinds` (`geometry.tsv`); `holarchy.chain-composes-opposite-hands`
  (`objects.tsv`); `key.mirror-separates-finding-from-checking` (`information.tsv`); `coupling.reflection-fixes-or-forces`
  (`targets.tsv`).
- Guides: the helical code's item 2 in [ELEMENTARY_OBJECTS](../../docs/ELEMENTARY_OBJECTS.md#the-helical-code-how-holons-encode)
  (the dyad keeps the hand, the mirror is the heterochiral partner); [THE_ENGINE §11](../../docs/THE_ENGINE.md#11-the-theorys-laws-against-the-engine)
  (a move's hand and kind against the engine).

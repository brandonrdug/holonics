# A lattice, an aperture and a dilation are one lens: the hexagon is three classes without their common mode, and the characteristic polygon lies on or above the grains' (in Lean)

November 20, 2026, 23:06 to 24:00 UTC. A short addendum to
[the failure-group record](2026-11-20_HODGE_ASKS_THAT_EACH_VARIETYS_FAILURE_GROUP_BE_FINITE_A_CLASS_OF_GRAIN_K_CLOSES_AFTER_K_TURNS_ONE_OBJECT_REFUTES_WHERE_A_CAUSE_COMPLETES_AND_A_CHART_OF_ONE_PERIOD_REACHES_NO_DECAYING_FUNCTION_IN_LEAN.md),
on a lens of the same evening. Refs #410, #404. Nothing ran on a learner or on the card. One Lean module enters
(§5). Each paragraph carries its grade: `tree` (read in this repository), `from training` (a result of the
literature, named, not looked up that day) or `agent-inferred` (this record's join). Every statement of §6 is
`agent-inferred`: a host read with its guess to fix, and no build.

## 1. The lens and how it is taken

Brandon's pointer for Hodge was to polygons and polytopes of the characteristic kind, within the hypergeometry
that his writing of the summer carried more of, and to lenses in nature that concentrate entropy and do work as
lenses: carbon rings, compound eyes with their ommatidia, and siphonophores. A first brief for this pass asked
whether such things are lattice lenses or likenesses of them. He corrected it at once: the lenses are lattices as
they stand, and the task is to model each one in mathematics and in computation until the model carries it, which
is what compressing it means. The correction's receipt is this record's
form: §2 states the one object, §3 reads each of his lenses as that object with its count, and no paragraph weighs
a lens against a standard of its own. Its reason, in the agent's words: a discipline is a chart of the objects
(CLAUDE.md), so the question about a lens is which object and which operation its nouns and verbs are, and a
framing that asks whether it "really" is one keeps the disciplines apart.

What the tree held (`tree`). The canon keeps his August statements that every polynomial has a geometric diagram
as its counterpart and that crystals focus through lattice pathways
([THE_QUOTE_NETWORK](../../docs/canon/THE_QUOTE_NETWORK.md)); the objects' guide keeps the lifts "lattices and
crystals" and "hypergeometry" (a turn that holds a lattice has order 1, 2, 3, 4 or 6; monodromy is a group of
moves, the half-turn, the third-turn and the cusp's shear;
[ELEMENTARY_OBJECTS](../../docs/ELEMENTARY_OBJECTS.md)); the atlas holds `landmark.hypergeometric-residues`
(Beukers and Heckman's interlacing), `lock.riemann-scheme-rigidity`, `egg.period-coefficients` (the egg's period
is `(π/2) ₂F₁(½, ½; 1; λ)`), `globe.closed-mesh-twelve` (a closed hexagonal mesh, a compound eye's, needs twelve
pentagons), `radix.hexagonal-turned-base`, `cell.a2-cone-orientation`, `winding.crystallographic-restriction`,
`linalg.smith-normal-form` and `ratio.temperament-kernel-commas`; and
[the record of July 25](2026-07-25_THE_HEXAGON_CARRIES_TWO_AND_THREE_THE_MESH_BENDS_THE_RECEIVERS.md) reads a cube
down its body diagonal as 8 source corners, 7 received coordinates and 6 silhouette corners, with ommatidial axes
on a triangulated surface. The atlas held no row for a count of lattice points, a Newton polygon, a slope or a
majorization, and no row that reads the hexagon as one object across these charts. Those enter (§7).

## 2. One lens: a lattice, an aperture and a dilation

`from training`, restated on the objects (`agent-inferred` where it says "reads").

- **The lattice** `M ≅ ℤⁿ` is the receiver's carriers: the characters of a torus, each a winding on `n` rings.
- **The aperture** `P` is a polytope with corners in `M`: the carriers the receiver passes.
- **The dilation** `k` is the clock: `kP` is the aperture after `k` ticks of growth.

The count `L_P(k) = #(kP ∩ M)` is a polynomial in `k` of degree `n` (Ehrhart 1962). Its leading coefficient is
the volume of `P`, its next is half the boundary's, and its constant is 1. So the width a part needs at a dilation
is read from its aperture and is neither a doubling nor a choice: the bulk grows as `kⁿ` and the boundary as
`kⁿ⁻¹`. At a negative dilation the same polynomial counts the interior, `L_P(−k) = (−1)ⁿ #(interior of kP ∩ M)`
(Ehrhart and Macdonald's reciprocity): running the clock back reads what the boundary encloses.

The same count is a dimension. `P` defines a toric variety `X_P` and a line bundle whose sections at degree `k`
have the lattice points of `kP` as a basis, so `L_P(k)` is the Riemann–Roch count on `X_P`. Its cohomology is
spanned by the classes of its torus-invariant subvarieties, one for each face of `P` (Jurkiewicz 1980; Danilov
1978): on a toric variety every class is carried by a face of the aperture, the face functor of the day's first
record is full by construction, and the failure group of the day's second record is zero. Read from here
(`agent-inferred`), the Hodge conjecture says that the rational classes a general variety's turn keeps are as
combinatorial as an aperture's faces, although no lattice was handed with the variety.

## 3. The hexagon is three classes without their common mode

The object: `ℤ³` modulo its diagonal `(1, 1, 1)`, the lattice `A₂`, with the aperture the hexagon whose corners
are the six differences `e_i − e_j`. Three classes are read, their common mode is the kernel, and the plane that
remains holds their ratios. Its count is `L(k) = 3k² + 3k + 1 = (k + 1)³ − k³`: 1, 7, 19, 37, each ring adding
`6k`. Each reading below is this object (`from training` for the named results, `tree` where a row or a record is
named, `agent-inferred` for the identification).

- **Sight, the classes.** Three cone classes respond to a light; their sum is its brightness, the tree's loudness, and
  lies on the diagonal, and the plane is hue. The six sextants of hue are the six orders of the three responses by
  size (Smith's hexcone, 1978), so the hexagon's corners are the six orders of three things, and neighbouring corners
  differ by one swap. This is the cone reading of the day's second record (`receiver.classes-compose-in-the-kernel`)
  with its kernel named.
- **Sight, the receivers.** Ommatidia stand on `A₂`: `k` rings about a facet hold `3k² + 3k + 1` facets, and a
  band-limited field is sampled on this lattice with 13.4% fewer receivers than on a square one (Petersen and
  Middleton 1962). The lattice and the aperture are locked by the sampling theorem: a facet of width `D` on an eye
  of radius `R` resolves `λ/D` and neighbours stand `D/R` apart, so `D² = λR/2` (Barlow 1952; Snyder 1977). A
  facet's width is sized from its role and widens where the eye must see more finely. In flies six receptors that
  look one way sit under six neighbouring facets and their axons meet in one cartridge (Kirschfeld 1967;
  Braitenberg 1967): the count is made where six arrivals add, the collision of the second record's §6.1. A
  closed eye needs twelve pentagons (`globe.closed-mesh-twelve`).
- **Sound.** Euler's lattice of tones (1739) is `A₂` with the fifth and the major third as its two axes; a triad
  is a triangle, and a temperament is the lattice's quotient by its commas (`ratio.temperament-kernel-commas`).
- **Matter.** A carbon ring is the hexagon's boundary as a ring of six: its orbitals are the six characters of
  `ℤ/6` at energies `α + 2β cos(2πj/6)`, and a shell closes at `4n + 2` electrons (Hückel 1931). A half-twist
  moves every character by half a step and the shell closes at `4n` (Heilbronner 1964): the ring of grain two of
  the second record (`coupling.grain-is-a-period`). In a sheet the hexagon's corners fall into two classes by an
  alternating colouring, the sign of a swap. A stack of sheets is a word in three positions, and its polytypes are
  its words (`AB`, `ABC`, and the long words of silicon carbide; Ramsdell 1947).
- **The cube down its diagonal** (`tree`, July 25). The 8 corners land on 7 points and 6 of them are the
  silhouette: `7 = L(1)` and `6` is its boundary. A cube of side `k + 1` shows `(k + 1)³ − k³` of its cells, the
  hexagon's count, and the fibre over a point is a run along the diagonal, the common mode.
- **The surface.** The hexagon is the polygon of the del Pezzo surface of degree six, whose sections at degree
  `k` number `3k² + 3k + 1`. It is one of the sixteen polygons with one interior point; its polar is a hexagon
  again, and the boundary points of the two sum to twelve (Poonen and Rodriguez-Villegas 2000), the same twelve as
  the closed mesh's, both an Euler characteristic.

**A strand of the same kind** (`from training`; `agent-inferred` for the reading). A siphonophore is the case
`n = 1`: a stem with a growth zone at one end, zooids budded in a repeating word of kinds (the cormidium: feeding,
swimming, reproduction, defence), one genome read by position, and one gut and one conduction path shared along
the stem (Mackie, Pugh and Purcell 1987; Dunn and Wagner 2006). On the objects it is a strand with a unit cell,
a dilation at one end, a gene as a partial key (`unicity.gene-partial-key`) and a common port; each kind's extent
is sized by its role, and the colony is a holarchy whose constituents are kept and cannot stand alone.

## 4. The polygons of Hodge

`from training`, restated on the objects.

**A hypersurface's forms are the lattice points of its polygon.** Let `f` be a Laurent polynomial with Newton
polytope `Δ`, the hull of its exponents. For a general `f` the holomorphic top forms on its zero set are named by
the interior lattice points of `Δ`: the point `m` gives the residue of `x^m (dx/x)/f` (Baker 1893 for curves, where
the genus is the count of interior points; Khovanskii 1978). The rest of the middle cohomology is named by the
interior points of the dilates `kΔ` modulo the Jacobian ring, and the dilation is the pole's order, which is the
Hodge level (Griffiths 1969; Danilov and Khovanskii 1986; Batyrev 1993). The hexagon has one interior point, so a
curve with that polygon is of genus one. On §2's lens the Hodge filtration is the dilation's clock.

**The pairing with the cycles is hypergeometric.** The forms are counted on the lattice of exponents and the
cycles on the lattice of homology. Their pairing, the periods, satisfies the hypergeometric system of the
exponents' configuration, whose rank is the volume of `Δ` (Gelfand, Kapranov and Zelevinsky 1989; Batyrev 1993).
The egg's period (`egg.period-coefficients`) is its first case, a triangle with one interior point. A Hodge class
is a lock of this pairing: a rational relation among periods that holds on a locus of the coefficients, and that
locus is algebraic (Cattani, Deligne and Kaplan 1995). The same polytope counts the solutions of a system
(Bernstein 1975: the mixed volume) and names the roots of one polynomial as hypergeometric series in its
coefficients, an edge of horizontal length `d` of a subdivision of its Newton segment carrying `d` roots (Mellin
1921; Sturmfels 2000). This is the diagram that is a polynomial's counterpart.

**A hypergeometric family counts its Hodge numbers on a circle.** For upper exponents `α_j` and lower `β_j` on
the circle, walk once around, add one at each `α` and take one at each `β`: the number of `α` met at each height
is a Hodge number (Corti and Golyshev 2011; Fedorov 2018). Where the two sets interlace the height stays at one
level, every class sits in one slot and the monodromy is finite: the row the tree holds
(`landmark.hypergeometric-residues`) is the level case of this count. It is a count made on a ring with a carry,
the reading of the second record's §6.1.

**Over a finite field there are two polygons.** The Hodge polygon has a segment of slope `i` and length `h^i`
for each Hodge number. The Newton polygon has the slopes of Frobenius, the valuations of its eigenvalues. The
Newton polygon lies on or above the Hodge polygon and the two share their ends (Mazur 1972). Where they touch at
a break of the Newton polygon, the crystal splits there into two (Katz 1979). The segment of slope `p` bounds the
rank of the classes of cycles of codimension `p`: on a K3 surface of height `h` the rank is at most `22 − 2h`
(Artin and Mazur 1977). In rank three the Newton point lies in the hexagon whose corners are the six orders of
the Hodge point, and in any rank it lies in the hull of the orders (Rapoport and Richartz 1996; Kottwitz and
Rapoport 2003): the Newton slopes are a mixing of the Hodge slopes, which is the statement that mixing raises
entropy, on slopes.

**The same statement for any matrix.** Over the integers at a prime, the Hodge polygon of a square matrix is
drawn by its grains, the invariant factors `d₁ ∣ d₂ ∣ …` of `linalg.smith-normal-form`, and the Newton polygon by
its characteristic polynomial. Over the reals the grains are the singular values and the rates the moduli of the
eigenvalues, and the products of the `k` largest moduli are at most the products of the `k` largest singular
values, with equal totals (Weyl 1949). Where the two products agree at some `k` and are not zero the matrix
splits there: in a Schur form `[[T₁₁, T₁₂], [0, T₂₂]]` with the `k` largest eigenvalues in `T₁₁`,
`∏ |λ_i| = |det T₁₁| ≤ ∏ σ_i(T₁₁) ≤ ∏ σ_i([T₁₁ T₁₂]) ≤ ∏ σ_i(A)`, and equality through the chain gives
`tr(T₁₂ T₁₂*) = 0` (a hand derivation of this record, not in Lean).

## 5. The integer form in Lean

`lean/HolonicsResearch/Landmarks/CharacteristicPolygon.lean`, namespace
`Holonics.Landmarks.CharacteristicPolygon`, on the tree's `Landmarks/SmithMinors` and Mathlib's expansion of a
characteristic coefficient into principal minors. Twelve statements.

- `dvd_charpoly_coeff_of_dvd_minors`: for a square matrix over a commutative ring, whatever divides every `k × k`
  minor divides the coefficient of `X^(n − k)` of the characteristic polynomial. `pow_dvd_charpoly_coeff` is the
  same at a power `p^a`: the characteristic height at `k` is at least the grains' height.
  `principal_minor_eq` carries Mathlib's principal minors over sets to the tree's minors over maps from `Fin k`.
- `charpoly_coeff_card` and `dvd_charpoly_coeff_zero_iff`: the two polygons share their ends, the leading
  coefficient one and the constant coefficient the determinant up to sign.
- Two specimens with the grains 1 and 2, joined by the swap of their two places (`mixed_eq_swap_mul_sorted`,
  `isUnit_det_swap`, `dvd_minors_mixed_iff_sorted`). `sorted = [[1, 0], [0, 2]]` keeps one place and doubles the
  other at every tick; its characteristic polynomial is `X² − 3X + 2` (`sorted_charpoly`), and its polygon at
  the prime two is the grains', slopes 0 and 1. `mixed = [[0, 2], [1, 0]]` doubles both places every two ticks
  (`mixed_mul_mixed`); its characteristic polynomial is `X² − 2` (`mixed_charpoly`), the middle coefficient is
  zero, and its polygon is the straight line of slope one half. `same_grains_different_rates` states the pair:
  the same divisors of minors and different middle coefficients.

Read at the prime two, where a factor of two is one place of a word: `sorted` holds one coordinate for ever and
moves the other one place a tick, and `mixed` moves both half a place a tick and holds nothing. The grains fix how
many places a tick moves in all, and the tick's mixing decides how that is shared. Up to a sign `mixed` is the
Frobenius of a supersingular elliptic curve and `sorted` of an ordinary one.

Not stated: the polygons, their convexity and the valuation (the module holds the divisibility that orders the
heights); Mazur's and Katz's theorems; Weyl's inequality and the splitting of §4. Two constructions are named for
#410: the grains' polygon itself (for a diagonal whose entries divide in a chain, `d₁ ⋯ d_k` divides every
`k × k` minor, which `Landmarks/SmithMinors.prod_dvd_minor` holds at full rank only), and the splitting where the
two polygons touch.

## 6. What follows for the machine

`agent-inferred`, every item; each is a host read on saved states, and none is built or asked for. The engine's
form is read at its guide ([THE_ENGINE §2](../../docs/THE_ENGINE.md#2-the-one-move)) and the atlas.

**6.1 The built tick is the cusp's shear, and its slopes are all zero.** `tree`: the ticks at a site are a sum,
`x ← x + O y`, and every reader divides the filling out (`tower.field-tick-running-mean`). On November 20 the
engineering thread read the tick on the store line's trained state (the end of lap 71, width 224, twelve ticks
over 240 sites of public text; `receipts/2026-11-20_engineering/tick_residual_L71.txt`): the state's step stands
at 0.957, 0.977, 0.985, 0.990, 0.993, 0.994 and 0.996 of the step before at the receipt's `k = 5` to `11`, and
the chart's step against the chart falls with a ratio that climbs from 0.11 to 0.62, so there is no steady factor
under one. On the polygons (an inference from the form, nothing read): a reader that divides by the norm fixes
the ray, so the tick's linear part has the eigenvalue one along every filled ray, and across it `1 + ν_j/‖x‖`
with `‖x‖` growing as the tick count, where `ν_j` are the rates at which the current answers a change of the
ray. A difference across the ray then falls as `k^ν`, a power and no geometric rate: every slope on the tick's
clock is zero, and the rates `ν` live on the clock `ln k` (the row's logarithmic clock). In the swing's words the
tick is a shear, a move whose two pivots coincide and whose multiplier is one
(`motion.mobius-multiplier-cross-ratio`), and a shear approaches its pivot as a power of `1/k`.

What the polygons add is the condition and the place. The condition: the two polygons share their ends, so the slopes
sum to the logarithm of the determinant, and the built tick's determinant, `∏ (1 + ν_j/‖x‖)`, tends to one as the site
fills. On it a part leaves a width of `w` places only after a count of ticks that grows as `2^(w/|ν|)`, so its tape is
as long as a power of the tolerance asks. A tick whose multiplier stays away from one has slopes: a part at slope `s`
leaves a width of `w` places after `⌈w/s⌉` ticks, and a part at slope zero is never released and is the tick's
retention (the unit-root part). The place: the form the theory already uses along the strand and across a lap, a leak
(`Q_t = κ_t b_t + γ_t Q_(t∓1)` on the carry circles, `1 − 2^(−r)` on a lap's sections), which at a site is the news
written in place of the current, `x ← x + (y − P x)` with `P x` what the site already holds of what arrives. Its
slopes are `−log |1 − μ_j|` over the eigenvalues `μ_j` of `P`: zero on what the reading does not see, which stays
retained, and positive where `0 < μ_j < 2`. The specimens of §5 say what a turn inside such a tick does: with the same
grains, a tick that keeps its places apart holds one and releases the other, and a tick that swaps them releases both
at half the rate.

The read before any build: on the host reference at saved states, the eigenvalues of the tick's reading-then-
writing map by finite differences at a sample of sites, sorted, with their polygon. The guess to fix: on the
built tick, at every site read, one eigenvalue a filled lane stands at one, and the others' distances from one
fall as `1/(k + a)` from tick 4 to tick 16, halving between ticks 7 and 15, with the exponents `ν_j` spread over
more than a factor of four. A leak is a change of law: it is founded at `γ = 1`, where the built tick
is reproduced bit for bit, its value is a deposited state as the carry circle's is, and it runs as an arm beside
a control from one saved state. Resembles: the cooling of November 4 and a rate set by hand. Differs: nothing is
set; the part is founded at the built tick and deposition moves it.

**6.2 A part's registers are the segments of its polygon.** For a part's transport read on saved states, sort the
logarithms of its one-step gains (the grains: singular values, or the invariant factors at a prime where the part is
an integer map) and of its long-run rates. Read at the grain of one place, a factor of two, each polygon's segments
are registers: a segment's slope is its place (the gains in one octave) and its length is its width (their count).
Where the two polygons touch at a break the part splits there (§4), and the two sides can be carried at their own
widths; where the rates' polygon stands above the grains', the tick mixes those places and they share one carrier. The
guess to fix on the store line's face (seven lanes of 32): the counts by octave are unequal by more than a factor of
two between the fullest occupied octave and the emptiest, and no break falls on a multiple of 32. Resembles: a width
turned as a dial (October 31). Differs: the read is a partition of the part's own transport, and no width is chosen by
a code.

**6.3 The six closing orders of three pairs are the hexagon's corners.** The second record's §8.4 found that one
terminal product reads only the parity of the crossings. On §3's object that is the alternating colouring of the
hexagon's corners, the sign of a swap, the one character of the six orders besides the trivial one. The six are
told apart on the plane, where the swaps act as reflections, a dyad each. The read, on the fork ruler's states:
the terminal state of the carry circles on the six closing orders of three opened pairs, with and without the
pump's word (`contact.pumped-carry`). The guess to fix: without the pump the six fall into two clusters by
parity, and with it into six, at the corners of a hexagon in the plane of the two largest principal directions.
Resembles: recitation counted as generation, if the six orders were all in the passage. Differs: the read is at
depths and orders the passages did not hold, and a planted hexagon is recovered on the same shapes first.

## 7. Atlas

Rows that enter: `landmark.lattice-aperture-count`, `cell.hexagon-three-classes-mod-common-mode`,
`hodge.forms-are-lattice-points-of-the-polygon`, `hodge.newton-above-hodge-is-a-mixing`,
`coupling.characteristic-polygon-above-grains`, `holarchy.strand-with-a-unit-cell`. Notes on rows that stand:
`tower.field-tick-running-mean`, `landmark.hypergeometric-residues`, `globe.closed-mesh-twelve`,
`linalg.smith-normal-form`, `parametron.crossed-pair-is-a-commutator`.

## 8. Receipts

Cloud container, 4 cores, Lean 4.33.0 at the Mathlib the package pins, the built cache fetched. Nothing ran on the
card or on a learner.

- `lake build HolonicsResearch.Landmarks.CharacteristicPolygon`: 3,804 jobs, exit 0. The first build ran 36.8 s
  under one deadline of 20 minutes fixed before launch (ratio 0.03) and failed on one goal, `X² + −2 = X² − 2`
  after the simplifier, closed by `ring`; the rebuild (5.2 s) passed with one warning, a section variable
  `principal_minor_eq` did not use, omitted there; the two builds after it (5.2 s and 7.5 s) gave none from the module.
- `#print axioms` on each of the 12 statements, from a scratch file outside the tree: every one stands on
  `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, no `native_decide`, no added axiom.
- The module is imported by the root `HolonicsResearch.lean`; `python3 tools/lean_census.py` reads no module
  outside the targets.
- Text: `python3 tools/link_check.py links`, `python3 tools/link_check.py atlas`, `python3 tools/records_index.py`
  and its control pass (the pull request carries their lines).

**Not checked, and why.** The whole research library (`bash tools/lean_check.sh HolonicsResearch`, about an hour
from cold in this container) was not run. The inference that stands in for it, stated apart as on the day's
earlier pull requests: the module declares one new namespace that no other file opens, no instance, no notation
and no attribute, and is imported by the root alone, so no other module's elaboration reads it. Gate 1's code
half and gates 2 and 3 do not apply: no crate's tokens changed.

## 9. Sources

`from training`, none looked up on the day: Euler 1739; Baker 1893; Mellin 1921; Hückel 1931; Ramsdell 1947; Weyl
1949; Barlow 1952; Horn 1954; Ehrhart 1962; Petersen and Middleton 1962; Heilbronner 1964; Braitenberg 1967;
Kirschfeld 1967; Griffiths 1969; Macdonald 1971; Mazur 1972; Bernstein 1975; Artin and Mazur 1977; Snyder 1977;
Danilov 1978; Khovanskii 1978; Smith 1978; Katz 1979; Jurkiewicz 1980; Danilov and Khovanskii 1986; Mackie, Pugh
and Purcell 1987; Beukers and Heckman 1989; Gelfand, Kapranov and Zelevinsky 1989; Batyrev 1993; Cattani, Deligne
and Kaplan 1995; Rapoport and Richartz 1996; Poonen and Rodriguez-Villegas 2000; Sturmfels 2000; Kottwitz and
Rapoport 2003; Dunn and Wagner 2006; Corti and Golyshev 2011; Fedorov 2018. A date or an attribution here is a
reader's memory and is checked at its source before it is leaned on.

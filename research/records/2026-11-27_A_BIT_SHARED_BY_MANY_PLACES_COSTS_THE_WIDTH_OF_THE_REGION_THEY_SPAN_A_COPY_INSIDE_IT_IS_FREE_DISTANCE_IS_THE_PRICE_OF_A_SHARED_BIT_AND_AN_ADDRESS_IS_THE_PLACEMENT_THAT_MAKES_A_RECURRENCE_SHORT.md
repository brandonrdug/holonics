# A bit shared by many places costs the width of the region they span, a copy inside it is free, distance is the price of a shared bit, and an address is the placement that makes a recurrence short

[interpretation at weight 0.75, on an outside theorem taken as stated; a thread of November 27, on the paper Brandon sent at
16:51 UTC with no comment] Status: what the paper proves, what the tree already held, one law on the objects, its charts with a
weight on each, a host ruler on five planted cases, and the three items sent to the formal thread.

## 1. The paper

OpenAI, *Euclidean geometry in the asymptotic spectrum of tensors*, November 24, 2026, 86 pages
([the preprint](https://github.com/openai/math/blob/main/preprints/Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/paper.pdf)).
Companion papers use it for lower bounds on arithmetic circuits and a bound on sunflower-free families.

- **A spectral point** (Strassen) is a reading `F` of tensors on a fixed set of parties that keeps `0` and `1`, never rises under a
  local linear map at each party (a restriction), multiplies on tensor products and adds on direct sums (two tensors in separate
  blocks at every party). Its **price** is `H = log₂ F`. Matrix rank across one cut of the parties is one such reading.
- **A wire** `e₀⊗e₀ + e₁⊗e₁` with its two ends at two sites is one shared bit. Every spectral point makes `d(a, b) = H(wire)` a
  pseudometric: two wires joined at a common end give a wire between their far ends (the triangle inequality).
- **Theorem 1.1, 5.3.** Over every field there is one system of prices on tensors placed in a real Hilbert space in which a wire
  costs its Euclidean length, and a `q`-valued label shared by a finite set `S` of sites costs `W(S) log₂ q`, where
  `W(S) = √(2π) E max_(s∈S) ⟨g, s⟩` is the mean width of their hull, normalized so a segment has its length. A triangle's is half
  its perimeter. The value is forced: every compatible system that realizes the wire lengths on a whole flat gives it.
- **Proposition 5.2.** Appending a copy of a shared label at `z` raises a tensor's price by at most `(W(S ∪ {z}) − W(S)) log₂ q`,
  so a copy anywhere inside the hull costs nothing, and the price of shared labels is submodular.
- **(2.3).** An ordinary sum of `m` alternatives on `S` costs at most the costliest alternative plus `W(S) log₂ m`.
- **§1.1.** An average of log ranks over cuts recovers a wire's length (each cut between its ends counts once), but such an
  average is no spectral point: on a square split by its midlines a horizontal and a vertical wire each read `√2` and their
  direct sum reads `3`, against `2√2` for a sum.
- **Theorem 4.3.** Every complete geodesic spectral space is CAT(0): the geometry of prices is flat or saddle-shaped, never closed
  like a sphere.
- **Lemma 2.2** (Strassen's duality, the form used). If every spectral point reads `F(X) < F(Y)`, then `K Y^m ≥ X^m` for one
  `K` and every `m`: what a tensor can become over many copies is decided by its spectral points.
- **Theorem 1.2.** Over every field there are Euclidean flats of every finite dimension. The proof is by contradiction: a largest
  dimension would let a universal computation be simulated by a network of amortized size `V/(log V)^A`, and a diagonal argument
  on its external wires refutes that. The geometry has as many directions as computation needs because computation cannot be
  compressed below itself.

## 2. What the tree holds

- `holarchy.pocket-min-cut`: what a pocket shares with the rest is bounded by its smallest cut. A bound on flow across one cut,
  with no price for a label shared among many places.
- `tower.level-unit-is-the-epochs-strand-face` (0.75) and the word record of this morning
  ([the record](2026-11-27_A_WORD_IS_A_STRAND_A_LOCALE_ADOPTED_ITS_ENDS_ARE_WHERE_ITS_READINGS_AGREE_ITS_INSIDE_IS_EVERY_SPLIT_AT_ONCE_A_MOVED_END_TURNS_ITS_FACE_AND_A_ROW_HANDED_DOWN_PAYS_ONLY_BY_NEWS_ITS_READER_LACKS.md) §3, 0.7):
  the news cuts a unit's ends, the count of its parts addresses its inside, and the inside is every split at once. Neither row
  held a cost law for why the ends pay and the inside does not.
- `receiver.merge-segmentation-mass`: the mass over every split codes a source at most as any one parse. It bounds the code, and
  holds no price for keeping every split at once.
- `compression.located-transport` and the level's row: positions are told apart up to the product of the rings' periods. The tree
  held the rings as an address, never as a placement with a distance.
- `store.far-price-stands-at-recurrence` and the formal thread's law of 15:55 UTC (far news only by address, 0.6, PR #1189): far
  news reaches her only where a unit is heard by its address. No row said why address and not reach.
- `globe.relative-completeness` (#410): completeness is relative to a receiver family, the full theorem not yet written.

## 3. The law

**General physics first.** Count the sections a common phase must be carried across. A plane wave of one phase over a region costs
nothing on a section that leaves the whole region on one side, and costs once on every section that cuts it. The measure of the
sections that cut a convex region is its width (Cauchy and Crofton): on a line, the sections strictly between its two ends; in a
plane, half its perimeter (normalized so a segment has its length). A body inside the region adds no section. Separate phases each
pay their own sections.

**On the objects (0.75).** A label that several places hold in agreement (a residue, a key, a word) costs `log q` on every section
of the receiver that separates its holders, which sums to the mean width of their hull.
1. The outermost holders set the price, and a holder inside their hull pays nothing.
2. Separate labels add their prices, and joined labels multiply their readings. A local map at one place never raises a price.
3. The distance between two places is the price of one bit they share. Distance is read from agreement, never laid down under it.
4. An address is a placement. It fixes which sections separate which places, so it fixes what agreement costs. The rings'
   placement makes a recurrence short.

## 4. The charts

**The word and the level's unit (0.75).** The cost clause of the word law and of the strand face is Theorem 5.3 on the line: a
unit's ends pay `(end − start) log q` and every place inside is addressed free (receipt line 2: `W = 8.002` for the ends and for
the ends with seven places inside, on one set of draws). Agreement costs span, never headcount: a word adopted by many readers in
one locale costs what one pair at its edges costs.

**Every split at once (0.7).** Holding `m` splits of a unit as one sum costs at most the costliest split plus `log₂ m` bits for
each place of span (receipt line 5: 8, 12.68, 16 and 24 bits on a span of 8 for 2, 3, 4 and 8 splits). Keeping the plural fibre
is cheap, and committing one split saves at most that.

**An address is a placement (0.7).** Place each place on each ring of period `p` at radius `p/2π`, one place to a unit of arc.
Two places at lag `L` sit at chord distance `d(L) = ((1/k) Σ_p (p/π)² sin²(πL/p))^(1/2)` over `k` rings, and a ring that
divides `L` puts them at one point. On rings of periods 5, 7 and 9 the nearest lags are 315, then 189 and 126 (each divided
by two of the rings, at 0.540), while lag 2 stands at 1.705 (receipt line 4). On the line a recurrence 189 places back costs 189
places of wire, and on the rings it costs less than a recurrence two places back. This is the reason far news travels only by
address: a far recurrence is cheap only in a placement where it is near. Octave periods share their factors and fold every
multiple of the longest period onto the present, where coprime periods fold only at their product; that matters only where a
ring holds longer than its period, and the bank's rings fade at one e-fold a turn (0.4 that it moves any reading of the bank).

**Rings are read by chord, never by arc (0.6).** A ring whose distances are arc lengths is a complete geodesic space with two
geodesics between antipodal places, so it is not CAT(0) and by Theorem 4.3 and Corollary 3.4 it is no spectral space. A ring
read by chord sits in the flat it spans, and that is a spectral placement. Her face already reads each ring on two axes
([the record of November 26](2026-11-26_A_CLASSS_MEAN_WORD_CARRIES_A_TWENTIETH_OF_WHAT_ITS_SITES_HEARD_ONE_BY_ONE_CARRY_ACROSS_A_CUT_AND_HER_FACE_ALREADY_READS_EACH_RING_ON_TWO_AXES.md)),
which is the chord.

**A reading is a price only where it adds over separate parts (0.55).** A mean over cuts of the log rank crossing them is no
price (receipt line 3: `3` against `2√2`). Reach by age read at one cut is a reading of one cut's rank, and a mean of such
readings across cuts is not a reading of the machine's geometry. This is a reason for the report by depth and by part: each
cut, octave and part is read as its own spectral reading, and the mean is kept beside them.

**Strassen's duality is a proved case of relative completeness (0.75).** The receivers are the readings that never rise under a
local map, multiply on joins and add on separate parts. Lemma 2.2: if every such receiver reads `X` below `Y`, then over many
copies `Y` becomes `X`. Completeness relative to that family is a theorem, with the family named by its three laws. Retention as
a quotient sufficient for the admitted receivers has here one family where sufficiency is proved.

**Directions are never bounded by law (0.6).** Flats of every dimension exist because a bounded dimension would compress
universal computation below its size. A reader's count of coprime rings is its count of directions in which recurrences can be
placed near. A fixed set of rings is a ceiling on what it can place near, and nested depth adds directions.

## 5. Sent to the formal thread

1. The width law as the cost behind the word record and the level's unit, with the line case as a finite statement for Lean
   (on a line the shared label's price is `(max − min) log₂ q`, a place inside costs nothing) and the sum bound beside it.
2. A ruler: her code on a word's recurrence against the chord distance of its two places on her rings, at equal lag on the line.
   The prediction is that at one lag her code is lower where the rings place the two near. The guess is fixed after her rings are
   read at their owner, per the rule on guesses on built parts.
3. Strassen's duality as a case for #410, with the receiver family named by its three laws.

## 6. Owners

- Atlas: `receiver.shared-label-mean-width`, `receiver.sum-of-splits-price`, `receiver.spectral-duality-relative-completeness`,
  `key.address-is-a-placement`.
- Receipt: `receipts/2026-11-27_shared_label_width/width_ruler.py` and its lines `width_ruler.txt`, seeded (`python3 -I`).

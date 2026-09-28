# God's algorithm is the geodesic navigator; the chase is retrograde analysis; a tempo is a Möbius loop

**September 28, 2026.** Brandon, on the chase, cornering and moves: compare the intelligence to chess
and to "God's Algorithm" for Rubik's cubes (Cayley graphs), in line with Möbius strips and trefoil
knots as intersecting strings; "God's Algorithm is equivalent to our navigator I think, the aeons and
lengths are related to what would traditionally be the diameter; we respect General Relativity,
spatial and temporal and higher dimensions and derivatives." This record states what is exact, what
is an image, and what it adds to the [unified plan](../../docs/plans/THE_REBUILD.md#the-unified-plan-september-28).
Checked items were verified exactly before writing; the rest are cited.

## 1. God's algorithm and the diameter

- [proved-standard] **God's algorithm** is the optimal policy on a puzzle's move graph: from every
  state, a shortest word of moves to the goal. Its value is the word metric's distance, and **God's
  number** is the move graph's diameter. For Rubik's cube it is 20 when a half-turn of a face counts as
  one move and 26 when only quarter-turns do (Rokicki, Kociemba, Davidson and Dethridge, 2010;
  Rokicki and Davidson, 2014); for the two-by-two cube, 11 and 14.
- [interpretation, on the exact statement] **The diameter depends on which moves are elementary.**
  Counting the half-turn as one move shortens every long word. This is the motion record's point in
  a finite group: what counts as one move is the metric
  ([motion record §3](2026-09-28_THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_A_GRIP_TURNS_A_PUSH_BOOSTS_AND_A_FREE_BODY_FALLS.md#3-the-derivation)).
- **The navigator reading** [definition; agent-inferred]. God's algorithm is the geodesic navigator: a
  navigator whose word from every state is a geodesic of the move metric. The diameter is the longest
  aeon such a navigator needs, counted in its own ticks. A navigator in the objects' sense carries a
  key and a clock; God's algorithm is the special navigator that already knows the whole graph.
- **Intelligence is not the table** [interpretation]. God's algorithm stored as a table is an index:
  a chess endgame tablebase keeps a value for every position (the seven-piece tables run to many
  terabytes). A player compresses it into a few navigators (the box that drives a lone king to the
  edge, the opposition, triangulation) that play near the table's optimum. That is the same
  distinction as F0's standing: a context model is an index, and the machine's task is to find the short
  navigators. The measurable question on a solved game is a navigator's description length against
  its regret to God's algorithm.

## 2. The chase already computes it

- [established-bounded; source-inspected] The chaser's capture basin (`holarchy::terrain::pursuit`)
  is **retrograde analysis**: backward induction from captured states, the construction of endgame
  tablebases. Its truth-only least capture on a seed is the distance to capture under perfect play,
  the chase's distance to mate.
- [interpretation] The runner's viable tube is the complement a defender keeps: the states from which
  capture can still be avoided for `n` ticks. **Cornering** is shrinking it, which is how the lone king
  is mated in king and queen, or king and rook, against king: the attacker cuts a box and shrinks it to
  the edge. The walls are what make that possible, in chess as in the chase. [proved-standard] Those
  endgames are mated in at most 10 and 16 moves.
- [established-bounded; measured, U4's rebase] The chaser's lattice admits only one nonzero speed per
  direction, so it never boosts purely. A move set without boosts is a metric without a generator:
  the chase's capture distances are measured in that metric, and admitting speed changes would change
  them.

## 3. Pieces are motion primitives

- [proved-standard] **Riders fall freely; the knight leaps.** A rook, bishop or queen moves along a
  ray until something grips it (a blocking piece or the edge). The king steps by the units and
  `1 ± i`. [checked] The knight's eight moves are exactly the Gaussian integers of norm 5, the
  associates of the two Gaussian primes over 5, `2 + i` and `2 − i`, and the ratio of its two
  chiralities, `(2 + i)/(2 − i) = (3 + 4i)/5`, is the rational turn that never closes
  ([motion record §5.2](2026-09-28_THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_A_GRIP_TURNS_A_PUSH_BOOSTS_AND_A_FREE_BODY_FALLS.md#52-lattices-and-crystals)).
- [checked] **Conserved faces.** A bishop keeps its square's colour; a knight flips it on every move.

## 4. A tempo is a Möbius loop

- [proved-derived; checked on the 8 × 8 board] **Losing a tempo needs an odd cycle.** Pair each
  square with the parity of the move count. A piece can reach the same square with the opposite
  parity, losing a tempo, exactly when its move graph has an odd cycle: the parity cover over the
  graph is then connected. The king has triangles and can triangulate; the rook can; **the knight
  cannot**, because its graph is bipartite (every move flips the colour).
- [formal-checked, the objects' theorem] This is the objects' orientation theorem: a cycle whose signs
  multiply to `−1` admits no orientation (`Objects/Pairing.no_orientation_of_reversing_cycle`; the
  witnesses `two_face_mobius_band` and `two_face_annulus` in `Objects/Orientation`). The king's triangle
  is a Möbius loop of the tempo bundle; the knight's graph is an annulus. The opposition is the
  tempo's phase class, the aeon's phase modulo two.

## 5. The trefoil's two classes are the cube's first two corners

- [proved-standard] The cube's reachable states are the index-12 subgroup cut out by three conserved
  faces: the edge flips sum to zero modulo 2, the corner twists to zero modulo 3, and the corner and
  edge permutations have equal parity.
- [proved-standard; the reading an interpretation] Thistlethwaite's algorithm corners the cube through
  the nested subgroups `⟨L, R, F, B, U, D⟩ ⊃ ⟨L, R, F, B, U², D²⟩ ⊃ ⟨L, R, F², B², U², D²⟩ ⊃
  ⟨L², R², F², B², U², D²⟩ ⊃ {1}`. Its first phase fixes the edges' flips (the half-turn class, of order
  2) and its second the corners' twists (the third-turn class, of order 3): the half-turn and the
  third-turn that generate the modular group, the trefoil's quotient
  ([egg packing](2026-09-27_EGG_PACKING_THE_MOIRE_OF_TWO_HELICES_IS_A_TORUS_KNOT_AND_THE_TREFOIL_IS_THE_HALF_TURN_WITH_THE_THIRD_TURN.md)).
- [proved-standard] **Where greedy descent is God's algorithm.** The modular group is the free product
  of the half-turn and the third-turn, so every element has one reduced word, and reducing a matrix to
  it is Euclid's algorithm on its entries (the Stern–Brocot descent the ratio object already owns). In a
  group whose Cayley graph is tree-like or hyperbolic, local shortening finds near-geodesics (Dehn's
  algorithm); in a group with many relations (loops, holonomy), such as the cube's, it does not, and
  either search or cornering through subgroups is needed.

## 6. In continuous motion, and in spacetime

- [proved-standard] **Shortest paths are made of the motion primitives at their bounds.** A body at
  constant speed with a least turning radius (the runner's `v²/(μg)`) travels shortest along at most
  three pieces: a maximal turn, a straight free fall, a maximal turn (Dubins, 1957). A body with bounded
  acceleration reaches rest at a point fastest by a full boost then a full brake, switching on the
  parabola `x = −½ v|v|` of free-fall arcs. God's algorithm for such a body is words in turn, boost and
  free fall.
- [proved-standard] **In spacetime the extremum reverses.** Between two events, free fall maximizes
  proper time (the reverse triangle inequality, which follows from the reverse Cauchy–Schwarz
  inequality that `Coupling/LorentzianPerp` owns);
  every turn or boost shortens it, which is the twin paradox (`Physics/Spacetime/Boost.time_dilation`).
  The Lorentzian diameter of a causal diamond is its free fall's proper time. So "the longest aeon
  between two occurrences" is the geodesic's, where a spatial God's algorithm seeks the shortest word.

## 7. What it adds to the plan

- [definition; agent-inferred] **Two known-truth game terrains in U4**, after the chase's next loop
  and before the fluid-cell terrain, because they are exact, small and test the plan's central
  question (a short navigator against an index):
  - the two-by-two cube's Cayley graph (3,674,160 states; diameters 11 and 14), with the metric
    chosen by the admitted moves, and Thistlethwaite-style cornering as the navigator to price;
  - king and queen, and king and rook, against king, by retrograde analysis (the chase's capture
    basin, already built), with the box as the navigator to price.

  Each measures a navigator's description length against its regret to God's algorithm, charged, with
  the table itself as the index control.
- **The chase's metric.** The chase's next loop records its capture distances as a function of the
  admitted move set (the chaser's missing boost), beside its measured failure.
- **Owed.** Lean: the tempo cover's connectivity equals an odd cycle (a graph statement over the
  orientation theorem); the knight's move set as the norm-5 associates; Dubins and the bang-bang
  switching curve are cited, not proved.

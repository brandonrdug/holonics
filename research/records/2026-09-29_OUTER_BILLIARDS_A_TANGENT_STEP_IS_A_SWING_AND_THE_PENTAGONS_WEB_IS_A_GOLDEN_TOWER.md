# Outer billiards: a tangent step is a Swing, and the pentagon's web is a golden tower

**Date.** September 29. **Issues.** #63, #62, #147. **Grade.** Each join is graded below;
[proved-standard] marks a result of the references, [proved-derived] an identity checked exactly
here, [interpretation] a reading the framework does not yet prove.

**Occasion.** Brandon sent five references as "valuable fundamentals and elementary information for
the framework", noting that external references tend to be neglected, and asked that they be fetched
and analysed, with GPT-6 Sol assisting the derivations. All five were fetched and read (the scanned
Tabachnikov paper by OCR), then analysed against the repository by GPT-6 Sol, read-only; every
algebraic identity below was re-checked exactly with sympy.

- L. Edwards-Costa, *Outer length billiards on polygons*, [arXiv 2510.11869](https://arxiv.org/abs/2510.11869) (October 2025).
- L. Costa, [*Mathematical Billiards*](https://structures.uni-heidelberg.de/blog/posts/2024_01_costa/index.php) (Heidelberg STRUCTURES, January 2024).
- S. Tabachnikov, *On the Dual Billiard Problem*, Adv. Math. 115 (1995) 221–249 ([course copy](https://www.math.brown.edu/reschwar/M272/advances.pdf)).
- G. H. Hughes, *Outer Billiards on Regular Polygons*, [arXiv 1311.6763](https://arxiv.org/abs/1311.6763).
- G. H. Hughes, [*Dynamics of Polygons*](https://www.dynamicsofpolygons.org/) (webs, winding numbers, projections, digital filters).

## 1. What the references establish

- **Three distinct maps.** Ordinary outer billiards (the tangent map) reflects a point through the
  support vertex, `τ(x) = 2c − x`. Outer length billiards (Edwards-Costa) uses three support lines
  and an auxiliary circle, a length variational law, and is not an isometry. The digital filter
  (Hughes, Appendix F) is a rotation followed by an overflow carry. Shared pictures do not make them
  one map.
- **Duality.** On the sphere, projective duality turns the direct billiard's length into the dual
  billiard's area through Gauss–Bonnet; the planar dual map is a symplectomorphism with area as its
  generating function; near a smooth strictly convex table and far from it, KAM invariant curves
  bound every orbit (Tabachnikov §I). [proved-standard]
- **Polygons.** A polygon's map is piecewise: on each support-vertex cell it is one half-turn. Its
  singular set (the web) is the pulled-back support rays. For the triangle, square and hexagon every
  nonsingular point is periodic. For the affine regular pentagon the periodic cells are dense, and
  the nonperiodic residual is self-similar with Hausdorff dimension `log 6 / log(2 + √5)`, coded by
  the substitution `0 ↦ 0010100`, `1 ↦ 000` (Tabachnikov §III). Tabachnikov's conjecture that every
  polygonal orbit is bounded was later refuted by Schwartz's kite. [proved-standard]
- **Regular polygons in general.** A regular `N`-gon's real coefficient field
  `Q(2cos(2π/N))` has degree `φ(N)/2`, so `N = 5` is quadratic, `7` cubic and `11` quintic. Hughes
  reduces the dynamics to piecewise rotations on a rhombus, a piecewise affine map on a torus, and
  relates it to the digital filter with twist `ρ = p/q`. His polygon–filter conjugacy in general and
  the `4k+1` prime pattern are proposals and observations, not theorems. [proved-standard for the
  degree; conjecture for the rest]
- **Outer length billiards.** A segment table gives confocal ellipses; every triangle has a
  three-periodic orbit; a distant once-around passage of a polygon stays in an annulus of bounded
  width (Edwards-Costa, Theorems 1–2). Three-periodic orbits for every polygon, a fractal singular
  set and an escaping square orbit are conjectures (§5). [proved-standard; conjecture]
- **A correction.** For ordinary outer billiards about an ellipse, the invariant curves are
  homothetic ellipses (Tabachnikov §I.2), not ellipses sharing the table's foci, as a summary of the
  Heidelberg post stated.

## 2. The joins to Holonics

1. **A tangent step is a Swing.** [proved-derived] On the support-vertex cell `U_i`,
   `τ|_(U_i) = S_(c_i)`, the half-turn about the grip `c_i`, and `S_(c_j) S_(c_i) x = x + 2(c_j − c_i)`
   (Lean `Geometry/AffineSwing`, `Motion.swing_word_linear_part`). An itinerary word is a translation
   when even and a half-turn when odd. A return word equal to the identity on a cell locks every
   point of it; an odd return fixes only the cell's centre, a fixed-point landmark candidate. Changing
   support vertex is a change of branch, of grip.
2. **The web is where paths part.** [proved-derived for the domain; interpretation for the receiver]
   `W_k = ∪_(j ≤ k) τ^(−j)(W_0)` is exactly where a `(k + 1)`-step itinerary fails; a receiver
   joining the two one-sided readings there holds a plural Preimage Fibre. The pulled-back rays have
   dimension one; the dimension `log 6 / log(2 + √5)` belongs to the nonperiodic residual that
   accumulates on them. Equating the two sets would turn a theorem into a false claim.
3. **The pentagon's web is a golden tower.** [proved-derived, checked exactly] The substitution's
   incidence matrix `[[5, 3], [2, 0]]` has characteristic polynomial `(t − 6)(t + 1)`, and the
   geometric contraction is `(2 + √5)⁻¹ = φ⁻³` since `φ³ = 2φ + 1`. So the dimension solves
   `6 · φ^(−3D) = 1`. The address words have lengths 1, 7, 41, 247, 1481 (each `6·ℓ ± 1`), and the
   decagon periods 10, 70, 410, 2470 are exactly ten times them: a period is the address word's
   length times the decagon's own ten. This is the fractal navigator's scale square on a first-return
   passage (word, restriction, golden scale), not a claim that the raw map commutes with dilation.
4. **The dynamics' exact field.** [proved-standard] A regular `N`-gon needs `Q(2cos(2π/N))`, of
   degree `φ(N)/2`: the exact representation law ("algebraic quantities are their constraint
   identities") applies, and the complexity of the web grows with the degree. Lean
   `HolonicsResearch/Geometry/Constructible` proves the full cyclotomic degree `φ(N)`; `ratio::ring`
   does not yet carry arbitrary cyclotomic fields.
5. **The digital filter is a turn on a torus with a carry.** [proved-derived, checked exactly]
   `F_a(x, y) = (y, −x + ay − 2k)` with `a = 2cos θ`: its branch linear part has determinant one and
   trace `a`, the turn kind of the motion record, and preserves `Q_a = x² − axy + y²`; the carry
   changes `Q_a` by `2aky − 4k(−x + ay) + 4k²`, so a branch preserves separation while a carry does
   not preserve a state's `Q_a`. The HNN's lattice split with error feedback
   (`x_t + r_(t+1) = y_t + r_t`, `hnn::chart`, Lean `HNN/LatticeWord`) shares the carry identity but has
   no fixed lossless branch map: the comparison is [interpretation], not a theorem about the HNN's
   error dynamics.
6. **Duality is a typed pairing, and symplectic is not power-neutral.** [proved-standard;
   interpretation] Length–area duality pairs two polygon receivers on the sphere, like a face and its
   coface. A symplectic map's graph is Lagrangian, but a Holon's Dirac structure needs a declared
   flow/effort pairing with zero total port power: the repository's exact hyperbolic symplectic
   matrix is a counterexample to "symplectic implies energy-conserving" (atlas, `arithmetic.tsv`). A
   KAM invariant curve bounds a candidate relatively complete region only once coupling, persistent
   interior motion and a genuine membrane are shown.
7. **Separate constructions.** Outer length billiards' generating function is not the Swing's
   potential (`Geometry/SwingPotential` is a rebase of an admitted future); Tabachnikov's higher
   dimensional dual billiard uses the symplectic quarter-turn `J` and a hypersurface normal, and the
   complex parametron's quarter-turn is a common operand, not the same boundary.

## 3. What the machine takes from it

- **Compression by itineraries.** A polygonal orbit compresses exactly when its support word, return
  translation and receiver distinctions factor through a smaller key; a periodic centre is a
  fixed-point landmark and a web face is where paths part, whose alternatives survive in the fibre.
- **A known-truth terrain for the fractal navigator.** The pentagon's substitution, golden scale and
  periods give an exact scale-and-address test for the tower. It is terrain, not a predictor: the
  machine must locate its keys from passages (the governing law "No catered machinery", lessons 1–2).
- **The carry's branches.** The filter comparison suggests reading the HNN's branch and remainder
  dynamics at each lattice split beside its exact accounting. It licenses no stability claim.
- **Traps named in advance** (the lessons record): a finite web picture read as an infinite-scale
  theorem; a periodic island called a convergence landmark; a polygon routine substituted for
  learned navigation; a symplectic identity read as a power certificate.

## 4. Owed (#62)

`Geometry/OuterBilliard`: `vertexBranch_eq_swing`, `defined_iterate_iff_not_mem_web`,
`even_itinerary_fixed_iff_translation_zero`, `odd_itinerary_square_fixed`. `Geometry/Constructible`:
`realCyclotomic_finrank` (`φ(N)/2` for `N > 2`). `Geometry/PentagonWeb`:
`pentagon_substitution_matrix`, `pentagon_scale` (`φ⁻³`), the period identity `D_n = 10·ℓ_n`, and
`pentagon_residual_dimension`, scoped to the residual. `Geometry/DigitalFilter`:
`filter_branch_quadrance`, `filter_branch_area`, `filter_carry_changes_energy`.
`HolonicsResearch/Geometry/OuterLength`: `outerLength_triangle_three_periodic`.

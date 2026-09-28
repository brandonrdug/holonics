# A loop reads the curvature it encloses: rings, tubes, eggs, and navigation by reweighting

**September 28, 2026.** Brandon asked for a derivation "with the toroidal/helical geometry and egg
shapes with calculus, something like manifolds that integrates all potential flux forces": how egg
packing relates to induction, how the spins of rings relate to the flux of tubes "about a
macroscopic perspective of flux integrating through a tube's calculus", the Enigma and Bombe as rings
aligning and resonating, the egg's symmetry and time parity, and the gradient between egg and tube
(his figures: an egg-shaped tube's cross-section under gravity, and a bank of egg-shaped tubes in a
cross flow; and the locating chromatic number of the pentagonal circular ladder graph). He also
pointed at navigation: brains warp the geometry by landmarks to navigate, "like for GPS", and a fly or
a cell moves through the waves toward what it senses without knowing where it is.

The spine is the winding guide's fourth general object, the face as the holonomy around a cell, read
in its scoped forms. GPT-6 Astra reviewed the first draft; its corrections are in the text, and §9
lists what the draft, and the summary first given to Brandon, got wrong. "Checked" marks a
computation whose script is named; everything else is cited or graded.

## 1. Loops read curvature, in scoped forms

- [proved-standard] **Abelian.** For a `U(1)` connection `A` with curvature `F = dA` and a loop `∂S`
  bounding an oriented surface `S` inside the domain, the holonomy is `exp(i ∬_S F)`: the loop reads
  the curvature flux through the surface, modulo `2π`. A lifted turn needs branch data beyond it.
- [proved-standard] **Nonabelian.** With `F = dA + A ∧ A`, finite holonomy is ordered transport; a
  small loop reads the curvature to leading order, and the transported curvature values generate the
  holonomy Lie algebra, hence the connected restricted holonomy (Ambrose–Singer). Curvature alone does
  not recover all global monodromy.
- [counterexample, and the key instance] **A flat connection can still turn a loop.** `A = α dθ` on an
  annulus has `F = 0` and holonomy `e^(2πiα)` around the hole, a loop that bounds no surface in the
  annulus. This is the Aharonov–Bohm effect: a charge carried around a ring acquires the relative phase
  `qΦ/ħ` (modulo `2π`) of the flux through the hole, where no field touches the ring.
- [formal-checked, for finite complexes] The repository owns the discrete forms: the dual-boundary
  pairing (`Geometry/ExteriorBoundary.stokes_pairing`, algebraic, not analytic Stokes) and the cell
  holonomy's group identities and finite Hodge results (`Transport/CellHolonomy`, which excludes
  continuum connections).

Instances, each with its own hypotheses:
- **Superconducting rings** [proved-standard, under London's assumptions]: the **fluxoid**,
  `Φ + μ₀λ_L² ∮ j_s·dl`, is quantized in `h/2e`, not the magnetic flux alone.
- **Berry's phase** [proved-standard]: the geometric phase of an adiabatically followed nondegenerate
  eigenstate, dynamical phase removed, is the Berry curvature's flux through the loop in parameter
  space. `Transport/CellHolonomy` does not prove it.
- **Two boosts** [formal-checked, perpendicular boosts in `2 + 1` dimensions]: a loop of perpendicular
  boosts returns a rotation equal to its velocity triangle's area defect (`Physics/Spacetime/Wigner`).
- **Foucault's pendulum** [proved-standard, in the ideal spherical adiabatic model]: the plane turns by
  `−2π sin λ` in a sidereal day, equal modulo `2π` to the solid angle `2π(1 − sin λ)` of the cap.
- **A cat in free fall** [proved-standard]: with zero angular momentum and no external torque, the mass
  metric gives a mechanical connection over shape space, `I(r)Ω + J(r)ṙ = 0`; a closed shape path
  returns an `SO(3)` holonomy, the turn (Kane and Scher, 1969; Montgomery, 1993). Its curvature lives in
  shape space and is Lie-algebra valued; a finite turn is ordered holonomy, and a retraced loop returns
  the identity. The body's centre falls freely while the cat spends muscle energy on its shape.
- **A swimmer at low Reynolds number** [proved-standard]: force and torque balance in Stokes flow give
  the connection; a small stroke's displacement reads its curvature, and a finite one is ordered
  `SE(3)` transport (Shapere and Wilczek, 1989). A reciprocal stroke returns the swimmer to where it
  started (Purcell's scallop theorem, for Newtonian fluid and negligible inertia); not retracing is
  necessary, not sufficient. A rotating flagellum is a periodic motor coordinate whose loop need not
  bound a surface.

## 2. Tubes and induction

- [proved-standard] **Flux agrees across a tube's sections.** For a divergence-free field, two
  cross-sections of a tube segment whose side wall carries no flux have equal flux: a spatial balance
  along the tube.
- [proved-standard] **Induction.** For a moving contour,
  `∮ (E + u × B)·dl = −d/dt ∬_(S(t)) B·dS` (Faraday); for a fixed contour the motional term drops. A
  nonzero circulation shows that `E` is not globally exact
  (`Physics/HolonicDiscreteInduction.emf_ne_exactDrop_of_fluxDifference_ne_zero`), not that the whole
  field is coexact: exact and admissible harmonic parts can be added without changing the curl. The
  discrete Faraday history reads flux as the coordinate whose source is the negative circulation,
  under its declared history (`em.faraday-successor`).
- [proved-standard] **A ring's current.** An undriven ring of constant inductance `L` and resistance
  `R` relaxes at the rate `R/L`, friction's boost. With `R = 0` under a changing external flux,
  `LI + Φ_ext` is conserved, not `I`.

## 3. Egg, tube and the harmonic circulations

- [proved-standard; checked] **Surfaces.** `b₁(S²) = 0` and `b₁(T²) = 2`
  (checked on the cube's surface and a three-by-four square torus,
  `research/notebook/motion/loop_curvature_checks.py`). A solid torus and a cylindrical surface have
  `b₁ = 1`; a solid tube has `b₁ = 0`. The repository's transport tube has no prescribed topology.
- [proved-standard] **What `b₁` counts.** On a finite positive weighted complex (objects §2), the
  harmonic one-cochains, silent at the declared node and cell receivers, have dimension `b₁`. That
  counts the harmonic part of the motion on that complex; it is not a persistence theorem, and it does
  not bound every receiver-relative dormant mode. A harmonic circulation decays under resistance; a
  steady rotation on a sphere has circulation and vorticity with `b₁ = 0`, because it is coexact.
- [proved-standard] **An egg reads what it encloses.** The flux of `D` out of any closed surface is the
  free charge it encloses (Gauss), whatever its shape; a torus-shaped closed surface does too.
- [interpretation] **Egg and tube differ by a handle.** Attaching a handle to a sphere-like surface
  raises `b₁` from 0 to 2 (a single puncture leaves it 0; the horn torus between them is singular). No
  change of frame changes the genus, and no theorem turns enclosed charge into circulation across that
  surgery. The gradient Brandon draws between egg and tube is, in this chart, the handle.

## 4. Twist, writhe and helicity

- [proved-standard] **`Lk = Tw + Wr`** for a sufficiently regular, closed, embedded, two-sided framed
  ribbon with disjoint closed edges (Călugăreanu, White, Fuller; Dennis and Hannay). Twist includes the
  framing and is not in general the integrated Frenet torsion; `Tw` carries `1/(2π)` and the Gauss
  integrals for `Lk` and `Wr` carry `1/(4π)`. A Möbius ribbon does not meet the hypotheses. Linking is
  fixed under deformations that keep the edges disjoint; a buckling threshold (a twisted tube coiling
  into a helix) needs a constitutive and stability law beyond the identity.
- [proved-standard] **Helicity of thin framed tubes**:
  `H = Σ_i Φ_i²(Tw_i + Wr_i) + 2 Σ_(i<j) Lk_ij Φ_i Φ_j`, with `H = ∫ A·B dV` for a magnetic field and
  `∫ u·ω dV` for a fluid (vortex flux read as circulation); internal twist and boundary and gauge
  conditions matter (Moffatt; Moffatt and Ricca).
- [proved-standard] **Frozen-in topology.** Smooth ideal frozen-in evolution keeps the field lines'
  topology. Reconnection needs something beyond it, and it is not always friction: collisionless
  electron-inertia models reconnect without resistive or viscous terms. A change of helicity does not
  imply reconnection either: a decaying Beltrami field keeps its line geometry while its helicity
  decays.

## 5. Tori and locks

- [proved-standard] On an integrable torus in straight-field-line coordinates, a reduced rational slope
  `p/q` gives closed orbits, `(p, q)` torus knots (the trefoil at `2/3`,
  [egg packing](2026-09-27_EGG_PACKING_THE_MOIRE_OF_TWO_HELICES_IS_A_TORUS_KNOT_AND_THE_TREFOIL_IS_THE_HALF_TURN_WITH_THE_THIRD_TURN.md)).
  Under a sufficiently small, regular, nondegenerate perturbation, tori with Diophantine rotation
  persist (Kolmogorov–Arnold–Moser); resonant tori can break into island chains, though not under every
  perturbation (one that preserves integrability breaks none).
- [interpretation] The aeon's carry word never recurs at an irrational rate
  (`Aeon/Clock/CarryWord.never_locks_iff_irrational`, carry periodicity only); reading a magnetic
  surface through it needs the actual coding map, and proves no persistence.

## 6. Navigation by reweighting, charts and landmarks

- [proved-standard] **A potential reweights the costs.** A* uses `c′(u, v) = c(u, v) − h(u) + h(v)`.
  With `h` the exact distance to the goal, `c′ ≥ 0` and the edges of shortest paths have `c′ = 0`;
  following zero-reduced-cost edges (with a termination rule against zero-cost cycles) is optimal.
  Choosing the neighbour of least `h` is not: edges `s → t` of cost 9, `s → b` of cost 1 and `b → t` of
  cost 1 defeat it. Reweighting is not a metric: path costs telescope by their endpoints, and physical
  travel is not made free.
- [proved-standard] **Landmarks in routing.** The ALT method (A*, landmarks, the triangle inequality;
  Goldberg and Harrelson, 2005) precomputes distances to a few landmarks and uses their triangle bounds
  as `h`.
- [proved-standard; checked] **Landmarks that locate.** A set of vertices resolves a graph when the
  distances to it identify every vertex. The metric dimensions (Cáceres and others, 2007; checked by
  exhaustive search on small cases, same script): a grid `P_m □ P_n` needs 2; the prism `C_n □ P_2`, a
  ring by a segment, needs 2 for odd `n` and 3 for even `n`; the torus `C_m □ C_n` needs 3 if either
  ring is odd and 4 otherwise. There is no general topological law behind these counts: the paths
  `P₃` and the star `K_(1,3)` are both contractible trees and need 1 and 2. The locating chromatic
  number Brandon cited uses resolving proper colourings, a different count again (for `P₃`: 3, against
  metric dimension 1 and partition dimension 2). GPS locates by clocks and pseudorange equations; a
  resolving set is its graph analogy.
- [proved-standard] **A wind makes going and returning differ.** Zermelo navigation with a Riemannian
  speed norm and a stationary wind `|W| < 1` is a Randers metric whose unit ball is a translated
  ellipsoid, so `F(v) ≠ F(−v)` in general (equality holds across the wind). Reversing both the velocity
  and the wind restores reciprocity, `F_W(v) = F_(−W)(−v)`: a drift's asymmetry, not a thermodynamic
  arrow.
- [proved-standard] **Light** in a stationary isotropic medium follows geodesics of `n² g` (Fermat);
  anisotropic media need more. Caustics are where a ray family converges.
- [proved-standard] **The Smith chart** is the Möbius map `Γ = (z − 1)/(z + 1)` for normalized passive
  impedances; a lossless line section turns `Γ` about the centre, `Γ_in = e^(−2iβl) Γ_L`, and a series
  reactance moves it along a constant-resistance circle (a parabolic Möbius action, not a rotation).
  It is a chart, not a metric warped by data.
- [established-bounded; measured] **A bacterium's taxis.** *E. coli* alternates runs (propelled against
  viscous drag, not free fall) and tumbles (reorientations), and lowers its tumble rate while the
  attractant it senses rises, through temporal sensing with adaptation and memory (Berg and Brown,
  1972; Macnab and Koshland, 1972): no position, a turn rate set by a sensed history. [interpretation]
  A fly steering toward what it senses is the same kind of navigation.

## 7. Egg-shaped bodies in flow (Brandon's figures)

- [proved-standard] **Slow flow.** Stokes flow is linear, dissipative and kinematically reversible:
  for a declared body, reversing both its translation and rotation reverses both force and torque. Shape
  still matters: translation and rotation can couple (a chiral body rotates under a force), so shape and
  orientation are observable at zero Reynolds number. A static egg shape is time-even; its fore-and-aft
  asymmetry is spatial.
- [conditional] **Films and inertia.** A gravity-drained film over a tube (the first figure's
  geometry) depends on the tangential gravity, the film's thickness, pressure, capillarity and the
  boundary conditions; the surface's normal angle alone is no transport law. The figures' mechanisms
  need their source papers before any claim.

## 8. The Enigma, the Bombe and lightning

- [formal-checked] **Loop closure is a fixed point.** A menu loop closes at a port exactly when the
  known stage word fixes the boundary image, `(S⁻¹WS)a = a ⇔ W(Sa) = Sa`
  (`Transport/HelicalPairInteraction.menu_loop_closure`): a fixed point, not an identity transport. The
  transposition `(1 2)` fixes `0` while being no identity, and a wrong key can survive a menu too small
  to refute it.
- [open] Aligned rings opening a path for lightning is not implied: a pure-gauge transport can be
  trivial around every loop while a potential drop drives current, and identity transport can coexist
  with no drive. The correspondence has no maps or falsifier yet.

## 9. What the first draft, and the first summary to Brandon, got wrong

- "A loop's turn is the flux through it" stated as universal: it holds for abelian connections on
  bounding loops, modulo `2π`; nonabelian transport is ordered, and flat connections turn loops around
  holes.
- Superconducting rings quantize the fluxoid, not the flux; the ring's winding does not count magnetic
  flux in general.
- The Bombe's closure was stated as trivial holonomy; it is a fixed point.
- *E. coli*'s runs were called free fall; they are driven against drag, and the tumble control has
  memory.
- "Holes cost landmarks" and "topology sets how many landmarks": false in general.
- "Knots are undone only by friction": collisionless reconnection is a counterexample.
- "An egg holds no dormant circulation; a tube holds two": true only for the harmonic cochains of the
  declared surfaces, and a solid tube has none.
- "The egg's direction does work only where the physics is nonlinear or dissipative": Stokes flow is
  both linear and dissipative, and shape is observable in it.
- "Greedy descent is optimal" under a perfect potential: only along zero-reduced-cost edges.
- The Randers asymmetry was called broken time parity; reversing the wind restores reciprocity.
- The Smith chart's series reactance was called a turn; it is parabolic.

## 10. What it adds, and what is owed

- **For the field** [open]: reading a ring's loop transport, not only its phase class, is a candidate
  for U1's family contract; it needs its map to the ring's actual constitution and a measurement.
- **For the harmonic modes** [definition; agent-inferred]: the harmonic circulations a complex can hold
  number its `b₁`; a receiver meant to hold one needs a complex with a handle, and the persistence is a
  separate dynamical question.
- **For navigation** [definition; agent-inferred]: routing landmarks (a reweighting potential) and
  locating landmarks (a resolving set) are different tasks; neither is yet identified with the
  machine's landmarks.
- **Owed** (#62): the first Betti numbers over `Holon/Complex`; the zero-reduced-cost lemma; the small
  metric-dimension cases as finite checks. Cited, not proved: Aharonov–Bohm and the fluxoid,
  Ambrose–Singer, Berry, Kane–Scher and Montgomery, Shapere–Wilczek and Purcell,
  Călugăreanu–White–Fuller, Moffatt–Ricca, KAM, Zermelo–Randers, Berg–Brown and Macnab–Koshland.

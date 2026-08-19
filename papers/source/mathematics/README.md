# Holonic mathematics library

This directory stores reusable mathematical objects independently of any one paper or
application. A paper may import an object, restate it in a local diagram, or refine it through a
new object; it must not silently copy and alter the claim.

The historical orientation is pinned at
[`MATHEMATICAL_HOLONICS.md`](../../../reference/holobrochos-a07ff376/src/soma/MATHEMATICAL_HOLONICS.md).
The external mechanism atlas is pinned at
[`MATHEMATICAL_RESEARCH_NETWORK.md`](../../../reference/minimum-mechanics-a07ff376/src/soma/MATHEMATICAL_RESEARCH_NETWORK.md).
This directory owns neither document; it supplies the exact reusable objects they route into.

## Object contract

```text
definitions/   declared vocabulary with explicit jurisdiction
lemmas/        local supporting results
theorems/      proved statements under written hypotheses
corollaries/   immediate consequences with dependency routes
proofs/        reusable demonstrations of named objects
catalogue.typ  one importable registry
```

Every object record contains:

- a stable key;
- mathematical kind and title;
- evidence status;
- dependency keys;
- exact claim;
- proof or demonstration when appropriate; and
- the boundary beyond which the object says nothing.

The library separates dependency from publication sequence. Exact, conditional, classical,
computational, and open objects remain typed apart.

## Exterior equation material

The curated machine-readable equation and relation store lives at
[`research/equation-atlas/README.md`](../../../research/equation-atlas/README.md), outside this reusable object
registry. That store contains exterior formulation occurrences, contexts, receiver scopes and
graded research correspondences. It is material for a later codec intake, not a second theorem
library and not the semantic owner of its formulas.

Raw document bytes, page layouts, raster/vector renderings and repeated source occurrences must
remain distinct at intake. They must not be silently normalized into this Typst catalogue or
collapsed because their rendered equations agree. Only a returned formulation-span or other
standing comparison owner may establish the relevant equality, rebase, quotient or obstruction.

## Elementary relational geometry

The foundational definitions are:

- [`situated-occurrence.typ`](definitions/situated-occurrence.typ);
- [`receiver.typ`](definitions/receiver.typ);
- [`holon.typ`](definitions/holon.typ);
- [`comparison-face.typ`](definitions/comparison-face.typ);
- [`phase.typ`](definitions/phase.typ); and
- [`situated-event-correspondence.typ`](definitions/situated-event-correspondence.typ);
- [`holonic-process-double-category.typ`](definitions/holonic-process-double-category.typ)
  separates boundary recharts, open causal constructions, comparison 2-cells, sequential gluing,
  and monoidal juxtaposition, while requiring a declared interaction action for actual
  co-presence;
- [`receiver-indexed-holonic-system.typ`](definitions/receiver-indexed-holonic-system.typ)
  separates evolution shape, interface interaction, parameter enrichment, receiver fibers,
  local observation, and domain realization; it defines a global face only as a boundary-bounded
  gluing of transported local sections;
- [`causal-soul.typ`](definitions/causal-soul.typ) refines soul from a scalar invariant or stored
  provenance into a marked oriented causal diagram;
- [`causal-time-parity.typ`](definitions/causal-time-parity.typ) defines time parity as the
  opposed induced incidence of one shared temporal face under forward event composition, not
  inverse causality;
- [`typed-axis-unit-ratio.typ`](definitions/typed-axis-unit-ratio.typ) separates a typed
  one-dimensional quantity fiber, its orientation, a local unit, its scalar coordinate, and a
  projective rational glyph;
- [`situated-knot-receiver.typ`](definitions/situated-knot-receiver.typ) makes a crossing a
  transverse receiver incidence between two source parameters rather than an intrinsic vertex;
- [`contextual-tangle-compression.typ`](definitions/contextual-tangle-compression.typ) defines
  exact local substitution over every declared exterior context and receiver; and
- [`co-present-receiver-atlas.typ`](definitions/co-present-receiver-atlas.typ) defines the
  non-Cartesian joint image of one event through several independently grained receivers, its
  compatible interior, and receiver-relative tolerance;
- [`receiver-topology-atlas.typ`](definitions/receiver-topology-atlas.typ) separates declared
  source incidence, receiver planarization, apparent crossings, oriented face boundaries, and
  face-dual primitive recurrence; and
- [`joint-decorated-path-carrier.typ`](definitions/joint-decorated-path-carrier.typ) retains
  lawful source darts while co-present receivers jointly refine their exact interval grain
  without turning apparent crossings into source junctions; and
- [`receiver-incidence-census.typ`](definitions/receiver-incidence-census.typ) keeps source
  vertices, distinct received coordinates, fiber multiplicity, silhouette corners, apparent
  crossings, and planarized diagram counts as separate typed populations;
- [`embodied-optical-receiver-atlas.typ`](definitions/embodied-optical-receiver-atlas.typ)
  makes a body's surface, metric, boundary, load, optical axes, propagation, and finite sampling
  one coupled receiver atlas rather than a Cartesian bank of external cameras;
- [`three-frame-counting-correspondence.typ`](definitions/three-frame-counting-correspondence.typ);
- [`radix-residue-character-cell.typ`](definitions/radix-residue-character-cell.typ) separates
  an invertible radix presentation, a residue quotient with complete fibers, and the invertible
  finite-character transform instead of calling all three a basis change.

Their first consequences are:

- [`ordered-composition.typ`](lemmas/ordered-composition.typ);
- [`receiver-nonreconstruction.typ`](lemmas/receiver-nonreconstruction.typ);
- [`soul-sameness-hierarchy.typ`](theorems/soul-sameness-hierarchy.typ), which uses the Yoneda
  criterion to separate occurrence identity, soul isomorphism, doctrinal equivalence,
  observational equivalence, receiver equivalence, equal face, and equal encoding digest;
- [`local-global-holon-assembly.typ`](theorems/local-global-holon-assembly.typ), which proves
  that every lawful global face and invariant over a declared region is assembled by compatible
  local transport, while nontrivial overlap holonomy obstructs the gluing;
- [`three-frame-return-covariance.typ`](theorems/three-frame-return-covariance.typ);
- [`four-member-projective-swing.typ`](theorems/four-member-projective-swing.typ), which proves
  that three marked members establish a projective pivot while the fourth carries the
  cross-ratio, and that overlapping four-member cells grow a covariant receiver atlas;
- [`joint-receiver-grain-refinement.typ`](theorems/joint-receiver-grain-refinement.typ), which
  separates a grain-dark local difference from a difference resolved by the joint family;
- [`source-diagram-loop-separation.typ`](theorems/source-diagram-loop-separation.typ), which
  proves that unweighted source recurrence is receiver-invariant but geometry-blind, while raw
  receiver recurrence is perspective-dependent and may recur across nonidentical source
  geometries;
- [`exact-receiver-turn-return.typ`](theorems/exact-receiver-turn-return.typ), which proves that
  rational local turn quotients telescope around every closed receiver path while their ordered
  metric and crossing interiors remain distinct;
- [`causal-parity-kirchhoff-return.typ`](theorems/causal-parity-kirchhoff-return.typ), which
  derives interval balance, Kirchhoff boundary/coboundary duality, admittance-governed branch
  reflection, standing phase return, wavelength, and positive-real dynamic shorting from one
  oriented causal complex with declared additive and constitutive laws;
- [`hexagonal-receiver-census.typ`](theorems/hexagonal-receiver-census.typ), which proves the
  regular hexagon is the first polygonal cycle carrying both order-two and order-three rotations,
  derives its opposite-edge pentagonal cut, and separates the exact cube and pentagonal-pyramid
  projection censuses;
- [`cm-norm-one-receiver-family.typ`](theorems/cm-norm-one-receiver-family.typ), which proves
  that one CM norm-one constituent lies on a unit circle in every complex embedding while
  conjugate prime valuations carry opposite hand;
- [`comparison-boundary.typ`](theorems/comparison-boundary.typ);
- [`comparison-triangle.typ`](proofs/comparison-triangle.typ); and
- [`point-line-loop.typ`](corollaries/point-line-loop.typ).

The knot-causal extension adds:

- [`knot-presentation-sameness.typ`](theorems/knot-presentation-sameness.typ), a classical
  synthesis which keeps Reidemeister diagram equivalence, Alexander braid closure, Markov braid
  equivalence, and Schubert prime decomposition at their proper levels;
- [`receiver-discriminant-curvature.typ`](theorems/receiver-discriminant-curvature.typ), which
  separates receiver crossings and Reidemeister seams from curvature formed by alternate
  receiver transports; and
- [`contextual-skein-compression.typ`](theorems/contextual-skein-compression.typ), which proves
  contextual equivalence stable under iterated gluing while a skein relation remains a linear
  relation among nonidentical interiors; and
- [`polyhedral-face-word-nonreconstruction.typ`](corollaries/polyhedral-face-word-nonreconstruction.typ),
  which uses the great and small stellated dodecahedra to prove that equal f-vector, abstract
  skeleton, and convex hull do not determine face traversal, winding, or dual interior.

Together they distinguish an occurrence from its presented value, a complete path from its
endpoint, and a returned loop from either. The three-frame correspondence gives independently
ordered lineages an actual incidence object rather than a shared master clock; its triangular
return is covariant under independent recharting. A receiver may be exact at its scope without
reconstructing the complete interior.

The categorical carrier is agnostic rather than indiscriminate. A mathematical or scientific
domain supplies a representation of the open causal category into its own algebraic, analytic,
geometric, logical, physical, or computational objects. A conserved quantity is then an additive
invariant of that representation. Causal time parity supplies the exact cancellation of internal
temporal faces. The represented current, storage, source, and constitutive law determine which
balance, loop, wave, or quantum face that common cancellation assumes.

[`ordered-causal-execution.typ`](definitions/ordered-causal-execution.typ) supplies the analytic
execution layer which that carrier previously left implicit. A receiver boundary is a positive
functional on its available distinction algebra; an event is a completely positive carried
transport plus a Hermitian residual. Residuals compose exactly, and positive residuals form a
composition-closed subcategory stable under arbitrary finite co-presence. Generic Eros events
remain signed or OPEN until the selected domain proves their residual positive.

## Parameterized formulation atlas

The formulation ecology now has an exact reusable carrier:

- [`situated-formulation-family.typ`](definitions/situated-formulation-family.typ) retains a
  parameter base, complete internal state, typed law, discriminants, receiver family, cost face,
  and testimony without making any one receiver the family's identity.
- [`formulation-span-atlas.typ`](definitions/formulation-span-atlas.typ) defines lawful
  comparisons as receiver-decorated spans. Directed limits, quotients, projections, and
  compressions remain available without being misnamed as reversible rechartings.
- [`formulation-span-composition.typ`](lemmas/formulation-span-composition.typ) composes two
  comparisons by pullback over the complete shared middle interior. Receiver exactness composes,
  while discarded directions remain discarded.

Only equivalence correspondences and invertible comparison cells form the exact rechart
bigroupoid; after identifying invertible 2-isomorphic arrows, they give the ordinary rechart
groupoid. The whole formulation atlas is therefore a bicategory, not a groupoid.

Three exact elementary cells validate the carrier:

- [`pi-split-formulation-family.typ`](theorems/pi-split-formulation-family.typ) gives a
  parameterized two-arm arctangent family with constant return \(\pi\), a genuine involutive
  arm swap, and parameter-dependent series interiors.
- [`exponential-split-formulation-family.typ`](theorems/exponential-split-formulation-family.typ)
  gives an entire two-stage family with return \(e\), a midpoint fixed by stage reversal, and a
  stage receiver which multiplication forgets.
- [`euler-factor-formulation-cell.typ`](theorems/euler-factor-formulation-cell.typ) relates one
  rational Euler factor, its geometric series, and its recurrence. The value comparison is exact;
  bare summation on the ambient sequence space is noninvertible, while a retained prime,
  parameter, and recurrence law can regenerate this constrained geometric lineage. The
  convergence boundary is not the same object as the rational pole set.

These cells establish a common comparison grammar without claiming one universal taxonomy of
formulas, a classification of transcendental presentations, or an RH implication.

## Transported calculus and geometry

- [`transported-fundamental-theorem.typ`](theorems/transported-fundamental-theorem.typ) gives the
  classical connection identity along a path.
- [`situated-mean-transport.typ`](lemmas/situated-mean-transport.typ) and
  [`equal-return-tangency.typ`](corollaries/equal-return-tangency.typ) retain parallel transport
  and discrete seams in mean-value reasoning.
- [`covariant-coarea-carrier.typ`](definitions/covariant-coarea-carrier.typ),
  [`covariant-coarea-fundamental-theorem.typ`](theorems/covariant-coarea-fundamental-theorem.typ),
  [`mellin-half-density-chart.typ`](lemmas/mellin-half-density-chart.typ), and
  [`weighted-mellin-basis-rebase.typ`](lemmas/weighted-mellin-basis-rebase.typ) join change of
  variables, half-Jacobians, bundle transport, signed seam terms, and the exact weighted family
  in which the displayed midpoint is \(\beta/2\).
- [`oriented-half-density-crossing.typ`](theorems/oriented-half-density-crossing.typ) factors
  \(-\partial_u^2+1/4\) into oppositely oriented first-order half-density crossings, retains the
  signed endpoint flux, and proves that closing the positive crossing with its adjoint is a
  support-preserving convolution square.
- [`convex-half-overlap-crossing.typ`](theorems/convex-half-overlap-crossing.typ) realizes a
  geometric \(L_+\) as the outward-oriented half-overlap boundary of a convex covariogram. Its
  neighboring level surfaces carry swept interior through coarea; \(1/2\) is the normalized
  overlap at the boundary, not a claim that every raw surface area is \(1/2\).
- [`situated-ray-receiver.typ`](definitions/situated-ray-receiver.typ) records the observer ray as
  part of the geometry rather than an exempt camera.

These objects do not define one universal information metric or connection.

## Prime and archimedean geometry

- [`prime-valuation-atlas.typ`](definitions/prime-valuation-atlas.typ) represents integers on
  finite prime-valuation axes.
- [`radix-residue-phase-decomposition.typ`](theorems/radix-residue-phase-decomposition.typ)
  proves that a radix receiver splits by CRT into finite suffix locality on prime powers shared
  with the radix and periodic winding on the coprime component. It also carries the same integer
  occurrence from radix and residue faces into its valuation/logarithmic/Mellin face.
- [`prime-wheel-euler-transport.typ`](theorems/prime-wheel-euler-transport.typ) proves that
  primorial COPY/CUT/JOIN, arithmetic Möbius exclusion, the finite Euler difference, and the
  prime-power resolvent are exact finite, scalar, and operator faces of one valuation-stratified
  admission event. It also identifies dilation similarity as the projective face of those
  strata, without turning similar triangles into a primality test.
- [`prime-axis-root-closure.typ`](lemmas/prime-axis-root-closure.typ) and
  [`prime-simplex-census.typ`](theorems/prime-simplex-census.typ) give exact finite root and
  population relations.
- [`centered-prime-character-geometry.typ`](theorems/centered-prime-character-geometry.typ)
  separates circular phase, reciprocal hyperbolic normal motion, and the flat one-prime sheet.
- [`prime-power-aperture-incidence.typ`](theorems/prime-power-aperture-incidence.typ) identifies a
  finite-prime current with overlap between a logarithmic aperture and its translate.

These exact local structures do not classify all primes or imply RH.

## RH dependency spine

The RH objects are grouped by mathematical role rather than by the date on which they were added.

### Symmetry, chart, and sign

- [`critical-seam-conjugacy.typ`](lemmas/critical-seam-conjugacy.typ) identifies the fixed seam of
  the completed involution.
- [`parametric-weil-bundle.typ`](definitions/parametric-weil-bundle.typ) states the changing
  receiver family over the actual incidence of arithmetic, archimedean, and receiving lineages.
- [`three-frame-return-covariance.typ`](theorems/three-frame-return-covariance.typ) separates the
  conjugacy class of a closed triangular return from its coordinate matrices and distinguishes a
  genuine new response from a mere rechart.
- [`weil-signature-transport.typ`](theorems/weil-signature-transport.typ) proves that an invertible
  rechart cannot erase a genuine negative direction.
- [`positive-perspective-descent.typ`](theorems/positive-perspective-descent.typ) packages that
  fact as an anchored descent law: compatible local positive forms glue to one positive global
  form, while a change of orientation cannot repair negative inertia.
- [`reciprocal-monodromy-counterexample.typ`](lemmas/reciprocal-monodromy-counterexample.typ)
  disproves “reciprocal monodromy implies unitary.”
- [`positive-covariant-monodromy-seam.typ`](theorems/positive-covariant-monodromy-seam.typ) gives
  the sufficient replacement under an independently positive transported metric.

### Completed response and aperture geometry

- [`mellin-return-seam.typ`](lemmas/mellin-return-seam.typ);
- [`completed-defect-recurrence.typ`](theorems/completed-defect-recurrence.typ);
- [`euler-successor-geometry.typ`](theorems/euler-successor-geometry.typ);
- [`euler-metric-recurrence.typ`](theorems/euler-metric-recurrence.typ);
- [`normalized-euler-resolvent-return.typ`](lemmas/normalized-euler-resolvent-return.typ);
- [`metric-half-jacobian-aperture.typ`](theorems/metric-half-jacobian-aperture.typ); and
- [`archimedean-remainder-amplitude.typ`](theorems/archimedean-remainder-amplitude.typ).
- [`completed-return-flux.typ`](theorems/completed-return-flux.typ) proves that the endpoint,
  Gamma, and finite Euler metrics are local factors of one completed return metric. Its normal
  logarithmic derivative is the full endpoint--archimedean--prime current. It gives exact
  equivalent RH faces as a positive-real half-plane impedance, an inner Cayley scattering
  function, a Stieltjes impedance on the squared axis, the boundary Poisson energy equal to the
  Weil form, and two connected Hankel Gram populations derived recursively from the theta
  coefficients.
- [`completed-scattering-hankel-successor.typ`](theorems/completed-scattering-hankel-successor.typ)
  integrates that infinitesimal normal field into Suzuki's exact two-face scattering ratio
  \(\Theta_\omega\), then exposes its one-sided arithmetic--archimedean Hankel kernel. RH is
  equivalent to every finite source cut being a contraction, or equivalently to both polarities
  \(I\pm\mathsf H_{\omega,a}\) being positive. Nested apertures obey one exact pair of Schur
  successor inequalities. The locally finite decomposition admits the integer \(n\) exactly when
  \(a^2\) crosses \(n\), with coefficient
  \(n^{\omega-1/2}\prod_{p\mid n}(1-p^{-2\omega})\). It also separates unconditional
  unitary boundary scattering from causal source realization, gives the equivalent logarithmic
  tail \(1-J_\omega\in L^2(dx/x)\), identifies the nonintegrable causal mode made by an off-seam
  zero, expresses the accumulated source as a convolution of integer events at times \(\log n\)
  with one exact Gamma response, and proves a strict-contraction interval inside the first
  \(n=1\) cell.
- [`completed-source-event-port-transport.typ`](theorems/completed-source-event-port-transport.typ)
  rebases the finite source cut to logarithmic receiver time. Its kernel is the causal triangle
  \(j_\omega'(\tau-s-t)\); every earlier body is carried by an exact right shift, while an integer
  response is born at the exposed boundary and grows as a source triangle. A Green identity gives
  the inverse-free bipolar port balance. Suzuki's Fredholm responses supply the corresponding
  coupled \(+\)/\(-\) differential connection and determinant Hamiltonian in the established
  regular range. This removes the blank-receiver initialization circle and leaves unconditional
  continuation and simultaneous causal passivity of the two source ports in \(0<\omega<1/2\) as
  the RH-equivalent sign.
- [`completed-source-volterra-frame-defect.typ`](theorems/completed-source-volterra-frame-defect.typ)
  factors that logarithmic Hankel cut as receiver reflection after one causal Volterra
  convolution. Consequently
  \((I-\mathcal H)(I+\mathcal H)=I-\mathcal V^*\mathcal V\), and the shared defect is the
  continuous Gram deficit of the exact arithmetic--Gamma action currents. Boundary-visible and
  port-dark null modes are the same unit-gain saturation of this frame, not separate proof
  obligations. The unresolved statement is the source-native Bessel bound, equivalently the
  Schur continuation of
  \(\widehat\psi_\omega(p)=\Xi(\omega-p)/\Xi(\omega+p)\).
- [`completed-source-common-founding-crossing.typ`](theorems/completed-source-common-founding-crossing.typ)
  expands the causal frame at its actual integer-event grain. The weights are generalized
  Jordan atoms and obey the exact meet--join law
  \(w(m)w(n)=w(\gcd(m,n))w(\operatorname{lcm}(m,n))\). Grouping crossings by their common
  founding exposes a Möbius-signed coprime-arm incidence, so a founding layer is not an
  independent positive energy. It also proves that, for \(0<\omega<1/2\), the separated
  arithmetic and archimedean transfers have a compensating zero and pole at
  \(p=1/2-\omega\); only the completed current is causal. The remaining sign is the exact
  coupled capacitance between archimedean storage and the complete arithmetic load.
- [`completed-source-seam-regularization.typ`](theorems/completed-source-seam-regularization.typ)
  performs the zero--pole rebase at \(p_0=1/2-\omega\). The raw positive Jordan incidence
  there diverges as
  \(X^{2\omega}/(2\omega\zeta(1+2\omega))\), so it cannot converge termwise to the
  analytically continued arithmetic zero. After the completion counterterm is retained, the
  full transfer has the unconditional strict seam capacity
  \((1-4\xi(1-2\omega)^2)/(1-2\omega)>0\). The two regularized constituent capacities
  exchange signs as \(\omega\) varies; only their completed sum has fixed orientation.
- [`completed-theta-phase-current-bridge.typ`](theorems/completed-theta-phase-current-bridge.typ)
  derives the full shifted-\(\Xi\) kernel as a bilateral-Laplace pullback of one exact
  sum/difference-coordinate kernel built only from the Riemann theta source. Its normal derivative
  at the unshifted seam is the theta phase current \(\mathcal P_0\). Positivity of
  \(\mathcal P_0\) on the bilateral-exponential receiver span is equivalent to RH; positivity on
  the whole coordinate space is a stronger sufficient Weyl-kernel theorem. This replaces the
  unnecessarily broad demand for an independently guessed Gram at every finite shift.
- [`theta-positive-execution-lift.typ`](theorems/theta-positive-execution-lift.typ) identifies that
  same equivalence as an exact process statement: RH holds precisely when the infinitesimal theta
  event lifts from signed ordered execution to its positive-residual subcategory. Equivalently,
  one source-derived residual executor factors the complete phase-current form as a squared norm
  on every finite exponential receiver superposition.
- [`theta-crossing-layer-indefiniteness.typ`](lemmas/theta-crossing-layer-indefiniteness.typ)
  proves that every isolated \(y\)-layer of the coordinate kernel is indefinite: an opposed pair
  can be born off-diagonally before either diagonal is active. The phase current therefore cannot
  be factored by declaring its layers independent positive constituents. A successful executor
  must carry those open crossings across the ordered \(y\)-sweep or work after the exponential
  pullback.
- [`theta-parity-execution-reduction.typ`](theorems/theta-parity-execution-reduction.typ) uses the
  exact simultaneous-sign symmetry to split the full coordinate current into its two parity
  receivers \(A+B\) and \(A-B\). Full coordinate positivity is equivalent to one relative law:
  the opposed-hand crossing \(B\) must factor through the same-hand storage \(A\) by a
  self-adjoint contraction. This is a sufficient full-coordinate executor, not an enlargement of
  the RH-equivalent exponential-span obligation.
- [`causal-impedance-rh.typ`](corollaries/causal-impedance-rh.typ) joins these faces through the
  elementary causal-parity/Kirchhoff theorem. A source-derived family of passive dynamic
  incidence bodies whose shorted port responses converge to
  \(\Xi'(z)/\Xi(z)\), with \(\Xi(z)=\xi(1/2+z)\), proves RH. Equivalently, one nonnegative
  theta--Euler--Gamma storage/dissipation identity on the explicit causal source state composes
  across every logarithmic interval and integer admission.
- [`completed-source-causal-storage-reduction.typ`](theorems/completed-source-causal-storage-reduction.typ)
  realizes that statement on the known source coordinates. The carried state obeys a left-shift
  equation with source injection \(\psi_\omega\) and boundary output. A nonnegative storage
  operator satisfying one explicit KYP block inequality proves every finite source cut
  contractive and hence proves RH when constructed source-natively for all
  \(0<\omega<1/2\).
- [`divisor-source-transport-boundary.typ`](theorems/divisor-source-transport-boundary.typ)
  turns the integrated source sign into an exact capacitated divisor graph. Its full Hall cut is
  the original RH-equivalent sign, so abstract max-flow is not a reduction. It proves that every
  fixed old cell requires at least order \(x^{1-2\omega}\) distinct descendants, while prime
  descendants supply ample individual capacity; only simultaneous divisor congestion remains.
  One proportional diffuse flow succeeds exactly when its explicit congestion
  \(\mathcal C_{\omega,x}(m)\) never exceeds one.

These objects construct exact local amplitudes, metrics, recurrence terms, and aperture
incidences. The
[`archimedean-carrier-prime-boundary.typ`](corollaries/archimedean-carrier-prime-boundary.typ)
proves why the established base aperture cannot already contain nontrivial finite-prime overlap.

### Squeeze and conditional RH consequences

- [`nested-aperture-deficit-persistence.typ`](lemmas/nested-aperture-deficit-persistence.typ)
  prevents a negative compact witness from disappearing merely by enlarging compatible support.
- [`geometric-remainder-squeeze.typ`](lemmas/geometric-remainder-squeeze.typ),
  [`positive-remainder-resolution-squeeze.typ`](theorems/positive-remainder-resolution-squeeze.typ),
  and
  [`finite-archimedean-tail-squeeze.typ`](corollaries/finite-archimedean-tail-squeeze.typ)
  distinguish a valid finite squeeze from the unproved semilocal completion.
- [`transported-positive-atlas-rh.typ`](corollaries/transported-positive-atlas-rh.typ),
  [`squeezed-positive-return-rh.typ`](corollaries/squeezed-positive-return-rh.typ),
  [`coarea-carrier-rh.typ`](corollaries/coarea-carrier-rh.typ), and
  [`receiver-domination-rh.typ`](corollaries/receiver-domination-rh.typ) are exact conditional
  consequences, not four independently advanced proof stages.
- [`semilocal-successor-defect-contraction.typ`](theorems/semilocal-successor-defect-contraction.typ)
  normalizes those presentations to one equivalence: the complete successor defect is
  \(\lVert Xf\rVert^2-\lVert Yf\rVert^2\), and an independently constructed contraction from the
  first channel to the second would supply the required sign.
- [`natural-contraction-feasibility.typ`](theorems/natural-contraction-feasibility.typ) requires those local
  fillers to be one natural transformation across prime, support, and receiver arrows. Its exact
  factorization, naturality, and contraction constraints form a convex weak-operator-closed set;
  finite-dimensional restrictions are linear matrix inequalities.
- [`natural-contraction-rh.typ`](corollaries/natural-contraction-rh.typ) states the exact
  conditional consequence: a complete natural contraction of the completed zeta amplitudes
  implies Weil positivity and RH. Nonemptiness of that feasibility set remains the same proof-bearing sign
  obligation, now with its coherence exposed.
- [`positive-skein-carrier-rh.typ`](corollaries/positive-skein-carrier-rh.typ) states the exact
  knot-causal specialization: a complete completed-zeta tangle presentation whose
  star-compatible evaluation constructs the natural contraction would imply RH. Ordinary skein
  recursion does not supply positivity; its signed or complex local coefficients expose the
  missing requirement rather than satisfying it.
- [`dyadic-euler-boundary-polarization.typ`](theorems/dyadic-euler-boundary-polarization.typ)
  resolves the first nontrivial \(R=2\to4\), \(p=2\) Euler contact into two exact positive
  core/shell amplitudes. Their difference, rather than either amplitude alone, is the signed
  prime response; the still-missing arrow couples the departing amplitude to support growth and
  the Sonin/remainder carrier.
- [`dyadic-character-filler-bound.typ`](theorems/dyadic-character-filler-bound.typ) diagonalizes
  that signed response in the exact \(C_2\) character basis. The symmetric core/shell modes are
  precisely its two negative directions, so any anchored support-growth passage must dominate
  \((\log 2)/\sqrt2\) on that subspace and satisfy the resulting Schur-complement constraint.
- [`dyadic-poisson-half-filler.typ`](theorems/dyadic-poisson-half-filler.typ) restricts actual
  \((\log 2)\mathbb Z\)-periodization to the four-cell dyadic section. Its normalized quotient
  has Gram projector \(P_+\), normalized operator area \(1/2\), and—under the independently fixed
  Euler amplitude \((\log 2)/\sqrt2\)—constructs the unique minimum local filler. The isolated
  dyadic cell is therefore positive.
- [`semilocal-sonin-prime-induction.typ`](theorems/semilocal-sonin-prime-induction.typ) proves
  that the published Sonin intertwiners already close the space-level prime/support induction.
  Prime admission \(I-p^{-1/2}U_p\) and the adjoint Euler resolvent are exact dual transports,
  commute with nested apertures, and commute across distinct primes. It also proves that the
  dyadic quotient cannot be a restriction of either transport: the quotient has a rank-two
  kernel while both transports are invertible. Its Gram is instead the lower-metric spectral
  face of the dyadic admission metric.
- [`weil-support-induction-reduction.typ`](theorems/weil-support-induction-reduction.typ) replaces
  the former exhaustive-atlas framing with the exact mathematical induction. The archimedean
  \(n=2\) cell is the base. The step \(P(n)\Rightarrow P(n+1)\) is precisely a positive Gram
  completion of the old body and the new support shell, equivalently positivity of the shell
  after its cross term is shorted through the old carrier. One uniform source-derived successor
  law would prove every \(P(n)\), and compact support would then give the full Weil criterion.
  The first step is \(P(2)\Rightarrow P(3)\), with \(p=2\) overlap \(\log(3/2)\); the symmetric
  \(p=2,R=4\) cell is only a calibration face because \(p=3\) is already present in \(P(4)\).
- [`prime-admission-cross-shell.typ`](theorems/prime-admission-cross-shell.typ) computes the new
  prime's exact position inside that first successor. Translation by \(\log p\) has zero
  old--old and shell--shell blocks from \(P(p)\) to \(P(p+1)\); it exchanges two boundary strips
  of width \(\tfrac12\log((p+1)/p)\). The new prime is therefore a pure cross face, not an
  independently positive or negative constituent.
- [`conditioned-support-quotient-shorting.typ`](theorems/conditioned-support-quotient-shorting.typ)
  corrects the raw support split: every admitted shell direction carries the unique old-region
  compensation preserving the source's Mellin moments. The invariant successor residual is the
  form short after that conditioned cross is carried through the old energy completion.
- [`prime-power-hinge-cell-recurrence.typ`](theorems/prime-power-hinge-cell-recurrence.typ) proves
  the complete symbolic threshold law. A paired signed hinge is born exactly at each prime power;
  conditioning couples all active hinges through one common old-body response. The resulting
  component Gram is a coordinate expansion, not an additional global object.
- [`conditioned-effective-tension.typ`](theorems/conditioned-effective-tension.typ) identifies
  that invariant object as the shell's Dirichlet-to-Neumann effective tension after the old body
  relaxes. Its Schur complement carries exactly every new negative or null direction, and
  sequential shorting is associative.
- [`passive-incidence-kron-composition.typ`](theorems/passive-incidence-kron-composition.typ)
  separates incidence, conservation, and passivity. A nonnegative edge/storage form remains
  nonnegative under port gluing and Kron shorting; a signed cross or \(\partial^2=0\) alone does
  not supply that form.
- [`prime-active-positivity-continuation.typ`](corollaries/prime-active-positivity-continuation.typ)
  combines the published strict \(R=2\) gap with continuity of the localized Weil ground value.
  It proves positivity on some nonquantitative interval \(2<R\le R_*\) with \(R_*>2\), where the
  \(p=2\) crossing is genuinely active.
- [`first-prime-fixed-domain-hinge.typ`](lemmas/first-prime-fixed-domain-hinge.typ) specializes
  the published scaled screw form to the complete first cell. Before \(p=3\) enters, the entire
  finite-place operator is one partial-isometry swap between disjoint boundary strips, with exact
  spectral faces \(-1,0,1\). The remaining wall is a continuum domination by the declared
  archimedean-plus-smooth-kernel form.
- [`first-prime-capacitance-completion.typ`](lemmas/first-prime-capacitance-completion.typ)
  completes that mutual strip coupling to one positive difference branch plus its exact endpoint
  storage debit. Together with Suzuki's nonlocal Dirichlet energy this yields a positive
  source-derived storage form \(\mathcal E_a\), a Hermitian load \(\mathcal D_a\), and the
  equivalent compact unit-gain wall
  \(\lambda_{\max}(\mathcal E_a^{-1/2}\mathcal D_a\mathcal E_a^{-1/2})\le1\).

## Current mathematical boundary

The completed proof object is now identified before choosing a support split. If
\[
\Xi(z)=\xi\!\left(\frac12+z\right),\qquad F(z)=\frac{\Xi'(z)}{\Xi(z)},
\]
then RH is equivalent to \(F\) being positive real on \(\Re z>0\). The Weil form is the boundary
Poisson energy of \(2\Re F\). Under \(w=z^2\), the same statement is that
\[
Z(w)=\frac{d}{dw}\log\frac{\Xi(\sqrt w)}{\Xi(0)}
\]
is Stieltjes. Writing \(Z(w)=\sum_{n\ge0}(-1)^n\mu_nw^n\), the exact source-side obligation is one
uniform factorization of both Hankel families
\[
[\mu_{i+j}]_{i,j=0}^N\ge0,\qquad [\mu_{i+j+1}]_{i,j=0}^N\ge0
\]
for symbolic \(N\). The \(\mu_n\) are connected logarithmic transforms of the positive Riemann
theta moments, so this does not enumerate zeros or support cells.

The same field now has a direct theta-source coordinate. With
\(m=(a+b)/2\), \(d=(a-b)/2\),
\[
\mathcal P_0(a,b)
=\frac{c_\Phi^2}{2}\int_{|m|}^{\infty}
y\,\Phi(y+d)\Phi(y-d)\,dy .
\]
Its bilateral-Laplace pullback is one quarter of
\[
\mathcal M(p,q)
=\frac{\Xi'(p)\overline{\Xi(q)}+\Xi(p)\overline{\Xi'(q)}}
       {p+\overline q}.
\]
RH is equivalent to \(\mathcal M\succeq0\), hence to \(\mathcal P_0\) being nonnegative on the
exponential receiver span. The pointwise positivity of \(\Phi\) does not settle this: the moving
boundary is a sum coordinate while the opposed theta faces use a difference coordinate, so the
individual crossing layers are not rank-one squares. This integrated phase-current sign is the
smallest presently isolated source theorem.

The same proof object now has an exact source-successor chart. For
\[
\Theta_\omega(z)
=\frac{\Xi(\omega+iz)}{\Xi(\omega-iz)},
\]
the infinitesimal normal field is recovered from
\[
\Re F(\omega-iu)
=-\lim_{v\downarrow0}\frac{\log|\Theta_\omega(u+iv)|}{2v}.
\]
Suzuki's explicit inverse-Mellin kernel \(h_\omega\) defines compact finite cuts
\(\mathsf H_{\omega,a}\). RH is equivalent to
\[
I+\varepsilon\mathsf H_{\omega,a}\ge0
\qquad
(\varepsilon=\pm1,\ \omega>0,\ a>0).
\]
If a nested cut is written
\(\mathsf H_{\omega,b}=\begin{psmallmatrix}A&C\\C^*&D\end{psmallmatrix}\), the exact induction
cell is
\[
I+\varepsilon D-C^*(I+\varepsilon A)^{-1}C\ge0
\qquad(\varepsilon=\pm1).
\]
This is the explicit bipolar source inequality formerly hidden by “uniform Gram
factorization.” It starts from \(\mathsf H_{\omega,a}=0\) for \(a\le1\) at every fixed
\(\omega\). Its sign for \(0<\omega<1/2\) remains the complete RH obstruction.

The support induction is a local Dirichlet-to-Neumann chart of that completed field. The first
successor is more complete than the former boundary stated. The source's moment
constraints determine its shell graph; the published strict \(P(2)\) gap carries the complete
old/shell cross; and the conditioned shell block is explicit in the zeta screw-kernel chart.
After internal relaxation, the only invariant sign is
\[
S_{2,3}=D_{2,3}-C_{2,3}^{*}A_2^{-1}C_{2,3}.
\]
The full first-successor form has the same new inertia as this effective tension. “Global Gram
dominance” was only a coordinate description of the energy absorbed by the one old-body
response.

Strict positivity is also known to cross the \(p=2\) seam: continuity of the attained lowest
localized eigenvalue carries the \(R=2\) gap to some \(R_*>2\). What remains in the first cell is
quantitative. One must control the already source-defined family \(S_a\), or an equivalent modulus
for its lowest value, throughout
\[
\left[\frac{\log 2}{2},\frac{\log 3}{2}\right].
\]
Continuity alone does not reach the right endpoint.

The circuit interpretation now has an exact, limited content. If
\[
\delta_aw=P_R(a)w-V_aP_L(a)w,
\]
then
\[
-\alpha_2\langle T_aw,w\rangle
=\alpha_2\|\delta_aw\|^2-\alpha_2\|P_aw\|^2.
\]
The first term is a complete positive branch; the second is the endpoint-storage debit absent
from the raw prime cross. Suzuki's archimedean \(\mathcal L\) already supplies positive nonlocal
pair incidence and boundary storage, but the scalar and smooth-kernel loads remain coupled to it.
Thus the honest first-cell condition is the complete relative-load bound above, not the stronger
and unproved claim that the remaining diagonal is independently positive.

Equivalently, the support presentation requires the same relation uniformly over every successor:
\[
q_{n+1}(x\oplus y)
=\lVert Z_nx+Y_ny\rVert^2+\langle S_ny,y\rangle,
\qquad S_n\ge0.
\]
At prime stages the exact dual Euler admission/return pair enters; at prime-power stages an
existing axis acquires another traversal; at other stages only the support boundary moves.
Associativity of shorting shows how a completed interior may depart while its effective boundary
law becomes the next standing form. This is an inductive theorem, not an infinite computation.

The arithmetic Euler lineage, archimedean Fourier--Poisson--Mellin lineage, and receiving
aperture lineage remain independently ordered and meet through actual incidences. That
three-frame organization governs covariance and composition of the effective-tension law; it
cannot repair its sign by a favorable perspective. Likewise knot modes describe relative
equilibrium but do not calibrate the absolute zero of the Weil response. The current constructive
route is to derive the positive Stieltjes/Lévy measure—or the equivalent inner scattering
contraction—from the Euler--Gamma--theta source. Any support-effective-tension estimate is a
lawful local realization of that same object, not a competing proof programme.

## Publication use

[*Elements of Holonics*](../papers/elements-of-holonics/main.typ) is the first composed reading of
the elementary objects. [*Categorical Holonics*](../papers/categorical-holonics/main.typ) derives
the open-process carrier, soul sameness, domain representations, perspective descent, and natural
contraction feasibility set. [*Knot-Causal Topology*](../papers/knot-causal-topology/main.typ)
derives the receiver crossing field, presentation hierarchy, typed ratios and units, contextual
tangle substitution, and positive-skein RH boundary. [*Riemann Receiver
Geometry*](../papers/riemann-receiver-geometry/main.typ) is the first domain paper to assemble the
RH dependency spine. None owns the reusable objects.

Proof objects remain distinct from theorem claims so one result may acquire algebraic,
geometric, computational, or medium-specific demonstrations without silently changing the
theorem. Each proof names the definitions and result on which it depends.

## Visual proof grammar

[`../lib/elements.typ`](../lib/elements.typ) implements an original Typst proof language inspired
by Oliver Byrne's method. A geometric constituent is defined once and retains the same color and
textual label in the main figure, inline prose, and equations. Color is redundant with labels,
orientation, and position; it never carries identity alone.

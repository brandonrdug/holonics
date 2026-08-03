#import "schema.typ": entry

#let manifold-knot-geometry = (
  entry(
    id: "H.0270",
    kind: "Definition",
    grade: "definition",
    title: [Smooth manifold, tangent space, and differential],
    depends: ("H.0206", "H.0220"),
    statement: [
      A smooth $n$-manifold has compatible charts into $RR^n$. A smooth map
      $f:M arrow.r N$ induces
      $
        dif f_p:T_p M arrow.r T_(f(p)) N,
        quad
        dif(g compose f)_p=dif g_(f(p)) compose dif f_p.
      $
    ],
    transformations: [
      Charts are local receiver faces; the differential is their exact
      first-order transport.
    ],
    boundary: [
      A smooth structure supplies no lengths, angles, preferred coordinates, or
      connection.
    ],
    source: [Standard differential geometry.],
  ),
  entry(
    id: "H.0271",
    kind: "Identity",
    grade: "proved-standard",
    title: [Differential forms and exterior derivative],
    depends: ("H.0203", "H.0270"),
    statement: [
      A differential $k$-form is a section of $Λ^k T^*M$. The exterior
      derivative is the unique graded derivation extending the differential of
      functions and satisfying
      $
        dif^2=0,
        quad
        dif(alpha ∧ beta)=dif alpha ∧ beta
        +(-1)^(deg alpha)alpha ∧ dif beta.
      $
    ],
    transformations: [
      Forms receive oriented $k$-dimensional transport; $dif^2=0$ is the smooth
      counterpart of boundary cancellation.
    ],
    boundary: [
      Closed need not mean exact. The identity does not manufacture an interior
      for every closed form.
    ],
    source: [Exterior-calculus theorem.],
  ),
  entry(
    id: "H.0272",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Stokes theorem],
    depends: ("H.0208", "H.0271"),
    statement: [
      For an oriented compact smooth $n$-manifold $M$ with boundary and a
      smooth $(n-1)$-form $omega$,
      $
        integral_M dif omega = integral_(partial M) omega
      $
      with the induced boundary orientation.
    ],
    transformations: [
      Interior differential and exposed boundary testimony are exact receivers
      of one oriented body.
    ],
    boundary: [
      A conservation statement follows only after the relevant closedness or
      source equation is supplied.
    ],
    source: [Generalized Stokes theorem.],
  ),
  entry(
    id: "H.0273",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Projective space, incidence, and recharting],
    depends: ("H.0201", "H.0202", "H.0270"),
    statement: [
      $PP(V)=(V minus {0})/FF^times$. Standard affine charts are related by
      rational transition maps; $"PGL"(V)$ preserves projective incidence, and
      on a projective line it preserves the Swing of H.0201.
    ],
    transformations: [
      Homogeneous rescaling changes a coordinate presentation while retaining
      the projective occurrence and its incidence.
    ],
    boundary: [
      Projective maps need not preserve Euclidean distance, angle, area, or
      causal path.
    ],
    source: [Classical projective geometry.],
  ),
  entry(
    id: "H.0274",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Riemannian metric and Levi--Civita connection],
    depends: ("H.0210", "H.0270"),
    statement: [
      A Riemannian metric is a smooth positive-definite symmetric form $g_p$ on
      every $T_p M$. There is a unique connection $nabla$ which is
      metric-compatible and torsion-free:
      $
        nabla g=0,
        quad
        nabla_X Y-nabla_Y X=[X,Y].
      $
    ],
    transformations: [
      A local unit law and its path transport are separate structures coupled
      canonically after $g$ is declared.
    ],
    boundary: [
      Positivity is specific to Riemannian geometry. Lorentzian and other
      indefinite metrics have different cone and sign structure.
    ],
    source: [Fundamental theorem of Riemannian geometry.],
  ),
  entry(
    id: "H.0275",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Geodesic and exponential map],
    depends: ("H.0252", "H.0274"),
    statement: [
      For $p in M$ and $v in T_p M$, there is a unique local geodesic with
      $
        nabla_(dot(gamma))dot(gamma)=0,
        quad
        gamma(0)=p,
        quad
        dot(gamma)(0)=v.
      $
      The exponential map is a diffeomorphism from a neighborhood of
      $0 in T_p M$ to a normal neighborhood of $p$.
    ],
    transformations: [
      Local straight continuation is determined by the connection rather than
      an external Cartesian frame.
    ],
    boundary: [
      This is local. Cut loci, conjugate points, incompleteness, and multiple
      global geodesics remain possible.
    ],
    source: [Geodesic existence theorem and normal-neighborhood theorem.],
  ),
  entry(
    id: "H.0276",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Curvature, Jacobi deviation, and holonomy],
    depends: ("H.0210", "H.0274", "H.0275"),
    statement: [
      Curvature is
      $
        R(X,Y) Z=nabla_X (nabla_Y Z)-nabla_Y (nabla_X Z)-nabla_([X,Y]) Z.
      $
      A geodesic variation has Jacobi field
      $
        nabla_t^2 J+R(J,dot(gamma))dot(gamma)=0.
      $
      Ambrose--Singer generates the holonomy Lie algebra from transported
      curvature endomorphisms.
    ],
    transformations: [
      Curvature is the residual between neighboring transports; Jacobi fields
      receive relative continuation; holonomy is a returned finite path face.
    ],
    boundary: [
      One loop or projected crossing does not determine the complete connection
      or curvature tensor.
    ],
    source: [Jacobi equation and Ambrose--Singer theorem.],
  ),
  entry(
    id: "H.0277",
    kind: "Theorem",
    grade: "proved-standard",
    title: [de Rham correspondence],
    depends: ("H.0226", "H.0271"),
    statement: [
      Integration of forms over singular chains induces a natural isomorphism
      $
        H^k_("dR")(M) equiv H^k_("sing")(M;RR).
      $
    ],
    transformations: [
      Local differential transport and global incidence topology are exact
      alternate presentations of one cohomology class.
    ],
    boundary: [
      The theorem identifies classes, not individual forms or path interiors.
      Harmonic representatives require a metric and Hodge theory.
    ],
    source: [de Rham theorem.],
  ),
  entry(
    id: "H.0278",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Gauss--Bonnet curvature total],
    depends: ("H.0226", "H.0272", "H.0274", "H.0276"),
    statement: [
      For a closed oriented Riemannian surface,
      $
        integral_M K dif A = 2 pi chi(M).
      $
    ],
    transformations: [
      Distributed local Gaussian curvature integrates to one topological
      receiver invariant.
    ],
    boundary: [
      This exact formula is two-dimensional. A surface with boundary owes
      geodesic-curvature and corner terms. It does not identify the projective
      Swing with Euler characteristic.
    ],
    source: [Gauss--Bonnet theorem.],
  ),
  entry(
    id: "H.0279",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Ricci flow and metric response],
    depends: ("H.0252", "H.0274", "H.0276"),
    statement: [
      On a closed smooth manifold, an initial metric $g_0$ admits a unique
      short-time solution
      $
        partial_t g=-2 "Ric"(g),
        quad
        g(0)=g_0,
      $
      and its volume form obeys
      $
        partial_t(d mu_g)=-R d mu_g.
      $
    ],
    transformations: [
      The metric receiver itself evolves by contracted curvature instead of
      observing a fixed geometry from outside.
    ],
    boundary: [
      Singular continuation, surgery, convergence, and topology classification
      require additional theorems.
    ],
    source: [Hamilton's short-time Ricci-flow theorem.],
  ),
  entry(
    id: "H.0280",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Three-dimensional Poincaré theorem],
    depends: ("H.0224", "H.0279"),
    statement: [
      Every closed connected simply connected topological $3$-manifold is
      homeomorphic to $S^3$.
    ],
    transformations: [
      Complete global return structure constrains topology, but the proof
      passes through controlled geometric evolution and singularity analysis.
    ],
    boundary: [
      This dimension-specific theorem is not a consequence of the phrase “all
      loops close” or of short-time Ricci flow alone.
    ],
    source: [Perelman's proof through Ricci flow with surgery.],
  ),
  entry(
    id: "H.0281",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Symplectic structure and Darboux chart],
    depends: ("H.0271",),
    statement: [
      A symplectic form is a closed nondegenerate $2$-form $omega$. Locally
      there are coordinates with
      $
        omega=sum_(j=1)^n dif q_j ∧ dif p_j.
      $
    ],
    transformations: [
      Every local symplectic region has the same incidence normal form while
      its global winding and topology may differ.
    ],
    boundary: [
      Symplectic structure supplies no metric, positive energy, or preferred
      global split.
    ],
    source: [Darboux theorem.],
  ),
  entry(
    id: "H.0282",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Hamiltonian flow and Liouville preservation],
    depends: ("H.0281",),
    statement: [
      Define $X_H$ by $iota_(X_H)omega=dif H$. Then
      $
        cal(L)_(X_H)omega=0.
      $
      An autonomous $H$ is constant along its own flow, and the flow preserves
      the symplectic volume $omega^n/n!$.
    ],
    transformations: [
      Hamiltonian current preserves the symplectic relation and its volume
      across time.
    ],
    boundary: [
      A time-dependent Hamiltonian need not be conserved; symplectic
      preservation supplies no dissipation law.
    ],
    source: [Cartan formula and Liouville theorem.],
  ),
  entry(
    id: "H.0283",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Holomorphic local degree and argument principle],
    depends: ("H.0224", "H.0261", "H.0270"),
    statement: [
      A nonconstant holomorphic map between Riemann surfaces has local form
      $
        f(z)-f(p)=a(z-p)^m+O((z-p)^(m+1)),
        quad
        a != 0.
      $
      For meromorphic $f$ with no boundary zero or pole,
      $
        frac(1,2 pi i)integral_(partial D) frac(f',f)dif z
        =N_D(f)-P_D(f)
      $
      with multiplicity.
    ],
    transformations: [
      Local branching has integer degree; boundary winding exactly counts
      interior zero and pole incidence.
    ],
    boundary: [
      Winding counts but does not locate or metrically classify the individual
      singularities.
    ],
    source: [Local mapping theorem and argument principle.],
  ),
  entry(
    id: "H.0284",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Conformal maps and Möbius automorphisms],
    depends: ("H.0202", "H.0283"),
    statement: [
      A holomorphic map with nonzero derivative preserves oriented angles.
      Automorphisms of the Riemann sphere are Möbius maps, and automorphisms of
      the unit disk have the form
      $
        exp(i theta)frac(z-a,1-overline(a)z),
        quad
        abs(a)<1.
      $
    ],
    transformations: [
      The receiver may rechart a face conformally while the cross-ratio and
      complex orientation retain exact projective information.
    ],
    boundary: [
      Conformal maps preserve angles, not general lengths or areas.
    ],
    source: [Classical one-complex-variable automorphism theorems.],
  ),
  entry(
    id: "H.0285",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Hyperbolic metric and law of cosines],
    depends: ("H.0200", "H.0274"),
    statement: [
      In curvature $-1$, a geodesic triangle with side lengths $a,b,c$ and
      angle $gamma$ opposite $c$ obeys
      $
        cosh c=cosh a cosh b-sinh a sinh b cos gamma.
      $
      The disk and upper-half-plane models are related by a Möbius isometry.
    ],
    transformations: [
      A triangle law changes with ambient curvature while projective or
      conformal recharting can preserve its hyperbolic metric relation.
    ],
    boundary: [
      Euclidean, spherical, and hyperbolic cosine laws are not interchangeable.
      Gyrovector notation is one model-specific re-expression.
    ],
    source: [Hyperbolic law of cosines and Cayley transform.],
  ),
  entry(
    id: "H.0286",
    kind: "Definition",
    grade: "definition",
    title: [Conics, quadratic forms, and focal receivers],
    depends: ("H.0122", "H.0126", "H.0273"),
    statement: [
      A projective conic is the zero locus of a nonzero homogeneous quadratic
      form. In an affine Euclidean chart, nondegenerate real conics appear as
      ellipses, hyperbolas, or parabolas according to the restricted form and
      chart; circles are a metric subclass of ellipses.
    ],
    transformations: [
      Foci, axes, tangents, and projective incidence are different receiver
      structures on one quadratic locus. Changing chart may change its affine
      species while retaining projective nonsingularity.
    ],
    boundary: [
      A focal point or visible arc is not an intrinsic projective invariant.
    ],
    source: [Classical projective classification of conics.],
  ),
  entry(
    id: "H.0287",
    kind: "Definition",
    grade: "definition",
    title: [Embedded knot and projected diagram],
    depends: ("H.0220", "H.0270"),
    statement: [
      A knot is a tame embedding $K:S^1 arrow.r M^3$. A generic projection to a
      surface has finitely many transverse double points supplied with over/under
      data.
    ],
    transformations: [
      Knot type belongs to the embedding; crossing data belongs to a declared
      projection receiver.
    ],
    boundary: [
      A projected double point is not a source self-intersection or intrinsic
      knot vertex.
    ],
    source: [Standard knot and regular-diagram definitions.],
  ),
  entry(
    id: "H.0288",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Reidemeister presentation equivalence],
    depends: ("H.0287",),
    statement: [
      Two plane or sphere diagrams represent ambient-isotopic links in
      $RR^3$ or $S^3$ exactly when they are related by planar or spherical
      isotopy and finitely many Reidemeister I, II, and III moves.
    ],
    transformations: [
      The three local moves generate equality of regular projection
      presentations for one link type.
    ],
    boundary: [
      A crossing change is not a Reidemeister move and may alter knot type.
    ],
    source: [Reidemeister theorem.],
  ),
  entry(
    id: "H.0289",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Alexander braid presentation],
    depends: ("H.0287",),
    statement: [
      Every oriented link in $S^3$ is isotopic to the closure of a braid.
    ],
    transformations: [
      A closed return can be re-presented as ordered transport about a selected
      axis.
    ],
    boundary: [
      The braid axis and braid word are presentation data, not intrinsic link
      identity.
    ],
    source: [Alexander's braid theorem.],
  ),
  entry(
    id: "H.0290",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Markov closure equivalence],
    depends: ("H.0289",),
    statement: [
      Two braids have isotopic oriented closures exactly when they are connected
      by braid relations, conjugation, and stabilization or destabilization.
    ],
    transformations: [
      Distinct axis-relative ordered lineages may close to the same standing
      link.
    ],
    boundary: [
      Markov equivalence need not preserve braid index, word length, crossing
      count, or construction path.
    ],
    source: [Markov theorem.],
  ),
  entry(
    id: "H.0291",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Prime-knot decomposition],
    depends: ("H.0287",),
    statement: [
      Every nontrivial knot in $S^3$ is a finite connected sum of prime knots,
      uniquely up to order and isotopy.
    ],
    transformations: [
      Irreducibility is typed by the connected-sum composition law.
    ],
    boundary: [
      Prime-knot factorization does not imply additive crossing number,
      unknotting number, substitution cost, or arithmetic primality.
    ],
    source: [Schubert prime decomposition theorem.],
  ),
  entry(
    id: "H.0292",
    kind: "Definition",
    grade: "definition",
    title: [Tangle composition and skein quotient],
    depends: ("H.0025", "H.0125", "H.0288"),
    statement: [
      A tangle is an embedded $1$-manifold with marked boundary and composes by
      compatible boundary gluing. A skein module is the free module on isotopy
      classes modulo a declared family of local linear relations.
    ],
    transformations: [
      Tangled interiors expose typed interfaces; a skein evaluation is
      receiver-exact when it factors through the declared quotient.
    ],
    boundary: [
      A skein relation is neither ambient-isotopy equality nor positivity
      without a separate theorem.
    ],
    source: [Standard tangle category and skein-module construction.],
  ),
  entry(
    id: "H.0293",
    kind: "Definition",
    grade: "proved-derived",
    title: [Receiver-visible crossing set],
    depends: ("H.0003", "H.0287"),
    statement: [
      For an embedding $k:Gamma arrow.r M^3$ of a one-complex and a generic
      projection receiver $rho:M^3 arrow.r Sigma$, define
      $
        "Cross"_rho(k)
        =
        {(x,y) in Gamma times Gamma:x!=y, rho(k(x))=rho(k(y))}
      $
      together with depth or over/under ordering. This set varies with $rho$
      while ambient isotopy class is separately retained.
    ],
    transformations: [
      Precessing the receiver changes visible crossing events at discriminant
      orientations where genericity fails. In the classical plane/sphere
      setting, Reidemeister moves classify the resulting local diagram changes.
    ],
    boundary: [
      Crossing count is a receiver statistic, not a complete knot invariant or
      a proof of arithmetic irreducibility.
    ],
    source: [Laboratory ray-receiver definition grounded in regular projection theory.],
  ),
  entry(
    id: "H.0294",
    kind: "Definition",
    grade: "definition",
    title: [Simplicial complex, realization, and subdivision],
    depends: ("H.0203", "H.0220"),
    statement: [
      An abstract simplicial complex is a vertex family closed under taking
      subsets. Its geometric realization glues standard simplices along common
      faces. Barycentric subdivision produces a canonically homeomorphic
      realization and induces the same homology.
    ],
    transformations: [
      Triangular and higher simplicial faces can hinge only through declared
      shared faces. Subdivision changes presentation grain while retaining
      topology.
    ],
    boundary: [
      A simplicial complex alone supplies no update law, metric, orientation,
      probability, or physical dynamics.
    ],
    source: [Standard simplicial topology.],
  ),
  entry(
    id: "H.0295",
    kind: "Definition",
    grade: "definition",
    title: [Hausdorff measure and fractal dimension],
    depends: ("H.0223", "H.0250"),
    statement: [
      The $s$-dimensional Hausdorff measure is the limit of infimal
      $sum_i ("diam" U_i)^s$ over covers with diameters bounded by a grain
      tending to zero. The Hausdorff dimension is the critical $s$ where the
      measure changes from infinity to zero.
    ],
    transformations: [
      Scaling complexity is received through all covering grains, not through a
      single rendered zoom.
    ],
    boundary: [
      Hausdorff dimension does not classify fractals, dynamics, or arithmetic
      structure by itself.
    ],
    source: [Hausdorff measure and dimension.],
  ),
)

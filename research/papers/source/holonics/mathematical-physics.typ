#import "schema.typ": entry, bra, ket, braket, ketbra

#let mathematical-physics = (
  entry(
    id: "H.0450",
    kind: "Definition",
    grade: "definition",
    title: [Dimensioned quantity and unit transport],
    depends: ("H.0020", "H.0200"),
    statement: [
      A dimensioned quantity is a member of a one-dimensional torsor or vector
      line associated with a dimension type. Choosing a unit gives a scalar
      coordinate; changing unit rescales that coordinate inversely while
      retaining the quantity.
    ],
    transformations: [
      Tensoring dimension lines composes dimensions. A dimensionless ratio is a
      scalar receiver only after numerator and denominator have been transported
      into dual compatible lines.
    ],
    boundary: [
      Dimensional consistency is necessary but not sufficient for a physical
      law. Equal unit dimensions do not identify source entities or paths.
    ],
    source: [Quantity calculus and dimensional analysis in line-space form.],
  ),
  entry(
    id: "H.0451",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Variational action and Euler--Lagrange transport],
    depends: ("H.0208", "H.0252"),
    statement: [
      A twice differentiable stationary path for
      $
        S[q]=integral_(t_0)^(t_1)L(q,dot(q),t)dif t
      $
      under fixed-endpoint variations satisfies
      $
        frac(d,dif t)frac(partial L,partial dot(q))
        -frac(partial L,partial q)=0.
      $
    ],
    transformations: [
      The action receiver compares neighboring complete paths; integration by
      parts transports the variation from velocity to position and exposes the
      boundary term.
    ],
    boundary: [
      Stationary does not mean globally minimal. The action, admissible
      variations, regularity, and boundary conditions are required data.
    ],
    source: [Euler--Lagrange theorem.],
  ),
  entry(
    id: "H.0452",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Noether symmetry and conserved current],
    depends: ("H.0121", "H.0272", "H.0451"),
    statement: [
      If a differentiable one-parameter transformation leaves an action
      invariant up to a boundary term, then its Euler--Lagrange solutions carry
      a conserved Noether current. In field form,
      $
        partial_mu J^mu=0
      $
      on solutions.
    ],
    transformations: [
      Continuous symmetry, variational identity, local current, and integrated
      charge are exact linked receivers.
    ],
    boundary: [
      Conservation is conditional on the declared action, symmetry, equations
      of motion, and boundary behavior. It is not derived from $partial^2=0$
      alone.
    ],
    source: [Noether's first theorem.],
  ),
  entry(
    id: "H.0453",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Continuity equation across orders of time],
    depends: ("H.0208", "H.0272"),
    statement: [
      If density $rho$ and flux $J$ obey
      $
        partial_t rho+"div" J=s,
      $
      then for a fixed region $Omega$,
      $
        frac(d,dif t)integral_Omega rho dif V
        =
        -integral_(partial Omega)J dot n dif A
        +integral_Omega s dif V.
      $
    ],
    transformations: [
      Local change, boundary transport, and source are three faces of one exact
      balance. Storage inside a region may vary instantaneously while the
      complete interval balance remains conserved when $s=0$.
    ],
    boundary: [
      A nonzero source or unaccounted boundary flux is not forbidden by
      topology; it must be included in the model.
    ],
    source: [Divergence theorem applied to the continuity equation.],
  ),
  entry(
    id: "H.0454",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Circuit chains, Kirchhoff current, and voltage],
    depends: ("H.0205", "H.0144", "H.0453"),
    statement: [
      On an oriented circuit graph, a source-free branch current $i$ satisfies
      $
        B i=0
      $
      at junctions. A node potential $v$ induces branch voltage
      $e=B^*v$, and every cycle $z in ker B$ obeys
      $
        chevron.l e,z chevron.r=0.
      $
    ],
    transformations: [
      Junction balance is a chain boundary law; voltage closure is exact
      cochain evaluation on cycles. Capacitors and inductors add state and
      constitutive time laws rather than violating these incidence identities.
    ],
    boundary: [
      Kirchhoff laws do not determine resistance, capacitance, inductance,
      source behavior, transients, or electromagnetic radiation without the
      corresponding constitutive and field model.
    ],
    source: [Algebraic circuit theory.],
  ),
  entry(
    id: "H.0455",
    kind: "Definition",
    grade: "definition",
    title: [Stress as momentum-flux tensor],
    depends: ("H.0125", "H.0270", "H.0453"),
    statement: [
      In continuum mechanics, Cauchy stress $sigma$ is the linear map whose
      traction on an oriented surface normal $n$ is $t(n)=sigma n$.
      Momentum balance is
      $
        rho dot(v)= "div" sigma+rho b.
      $
    ],
    transformations: [
      Stress is transport of momentum across oriented cuts; pressure, shear, and
      traction are receiver faces of the tensor.
    ],
    boundary: [
      Stress is not heat, scalar loss, or information by definition.
      Constitutive laws determine how material deformation relates to $sigma$.
    ],
    source: [Cauchy stress theorem and continuum momentum balance.],
  ),
  entry(
    id: "H.0456",
    kind: "Definition",
    grade: "definition",
    title: [Thermodynamic state differential and heat boundary deed],
    depends: ("H.0208", "H.0450"),
    statement: [
      Internal energy $U$ is a state function. For a process,
      $
        dif U=delta Q+delta W_("on"),
      $
      where heat and work are path-dependent energy transfers. In a simple
      reversible system,
      $
        dif U=T dif S-p dif V+sum_i mu_i dif N_i.
      $
    ],
    transformations: [
      State difference and boundary transfer are nonidentical receivers of one
      process lineage.
    ],
    boundary: [
      Heat is not a state substance or intrinsic punishment. The differential
      form and sign convention depend on the declared thermodynamic system.
    ],
    source: [First law and fundamental thermodynamic relation.],
  ),
  entry(
    id: "H.0457",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Canonical ensemble and free-energy relation],
    depends: ("H.0019", "H.0351", "H.0411", "H.0456"),
    statement: [
      For discrete finite energies $E_i$ at inverse temperature $beta>0$,
      $
        Z(beta)=sum_i exp(-beta E_i),
        quad
        p_i=frac(exp(-beta E_i),Z(beta)),
        quad
        F=-beta^(-1)log Z.
      $
      The identity
      $
        cal(F)_beta(q)
        =
        sum_i q_i E_i+beta^(-1)sum_i q_i log q_i,
        quad
        D_("KL")(q norm p)
        =
        beta(cal(F)_beta(q)-F)
      $
      for every probability vector $q$, with $0 log 0=0$. Thus relative
      entropy and nonequilibrium free energy are related exactly for this
      declared ensemble.
    ],
    transformations: [
      Energy spectrum, Gibbs recurrence law, partition function, and free energy
      are exact connected receivers in one model.
    ],
    boundary: [
      This does not identify every loss with free energy or every probability
      field with thermodynamics.
    ],
    source: [Canonical ensemble and Gibbs variational principle.],
  ),
  entry(
    id: "H.0458",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Maxwell field in exterior form],
    depends: ("H.0271", "H.0272", "H.0450"),
    statement: [
      On an oriented Lorentzian spacetime, in a fixed unit and sign convention,
      electromagnetic field strength $F$ and current $3$-form $J$ obey
      $
        dif F=0,
        quad
        dif star F=J.
      $
      Hence $dif J=0$.
    ],
    transformations: [
      Field, dual metric receiver, source current, flux, and charge are related
      through exact differential and boundary laws.
    ],
    boundary: [
      $dif^2=0$ gives charge-current consistency after Maxwell's sourced law is
      supplied; it does not derive the law, metric, units, or material response.
    ],
    source: [Maxwell equations in differential-form notation.],
  ),
  entry(
    id: "H.0459",
    kind: "Definition",
    grade: "definition",
    title: [Lorentzian metric, causal cone, and proper time],
    depends: ("H.0270", "H.0274"),
    statement: [
      A Lorentzian metric has signature $(-,+,dots.c,+)$ up to convention and
      has a unique metric-compatible torsion-free connection.
      Nonzero tangent vectors are timelike, null, or spacelike according to the
      sign of $g(v,v)$. Timelike worldlines carry proper time
      $
        tau=integral sqrt(-g(dot(gamma),dot(gamma)))dif lambda
      $
      in units with $c=1$.
    ],
    transformations: [
      The light cone is the receiver-relative boundary between causal tangent
      species determined by the metric.
    ],
    boundary: [
      A generic graph cone, algorithmic affordance cone, or visual camera frustum
      is not a physical light cone without a Lorentzian metric and propagation
      law.
    ],
    source: [Lorentzian geometry.],
  ),
  entry(
    id: "H.0460",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Einstein curvature--source equation],
    depends: ("H.0276", "H.0455", "H.0459"),
    statement: [
      General relativity posits
      $
        G_(mu nu)+Lambda g_(mu nu)
        =
        frac(8 pi G,c^4)T_(mu nu),
      $
      where $Lambda$ is constant and
      $G_(mu nu)="Ric"_(mu nu)-frac(1,2)R g_(mu nu)$. The contracted Bianchi
      identity gives $nabla^mu G_(mu nu)=0$, so a solution owes
      $nabla^mu T_(mu nu)=0$.
    ],
    transformations: [
      Metric curvature and stress--energy flux are linked by a declared
      dynamical field equation; covariance transports it between charts.
    ],
    boundary: [
      Holonic geometry does not derive the physical constants, Lorentzian
      signature, matter coupling, or Einstein equation merely from analogy.
      Replacing $pi$ by an informal arc symbol is not this equation.
    ],
    source: [Einstein field equation and contracted Bianchi identity.],
  ),
  entry(
    id: "H.0461",
    kind: "Definition",
    grade: "definition",
    title: [Quantum state, observable, charge, spin, and mass],
    depends: ("H.0121", "H.0243", "H.0417", "H.0459"),
    statement: [
      A quantum state is a positive normalized functional, or density operator
      in a Hilbert representation. Observables are self-adjoint operators.
      Charge labels a representation of a gauge symmetry; spin labels an
      irreducible representation of the rotation or Lorentz cover; mass labels
      the Casimir invariant $P_mu P^mu$ in a relativistic representation.
    ],
    transformations: [
      State, measurement distribution, gauge sector, rotational holonomy, and
      relativistic representation are distinct connected mathematical faces.
    ],
    boundary: [
      Charge, spin, and mass are not derived merely from triangle orientation,
      polarity, or gyration. A specific symmetry group and representation law
      are required.
    ],
    source: [Quantum mechanics and Wigner representation classification.],
  ),
  entry(
    id: "H.0462",
    kind: "Definition",
    grade: "definition",
    title: [Local observable algebra in quantum field theory],
    depends: ("H.0023", "H.0243", "H.0459", "H.0461"),
    statement: [
      Algebraic quantum field theory assigns an observable algebra
      $cal(A)(O)$ to each admissible spacetime region $O$, covariantly under
      inclusion, with spacelike separated algebras commuting under locality.
    ],
    transformations: [
      Region, inclusion, causal separation, observable algebra, and state are an
      exact local-to-global network rather than one universal scalar field.
    ],
    boundary: [
      The Haag--Kastler axioms are a physical mathematical framework, not proof
      that every information ecology is quantum field theory.
    ],
    source: [Haag--Kastler algebraic QFT axioms.],
  ),
  entry(
    id: "H.0463",
    kind: "Boundary",
    grade: "proved-derived",
    title: [Physical law and holonic translation],
    depends: ("H.0031", "H.0452", "H.0458", "H.0460", "H.0462"),
    statement: [
      A physical theory may be imported as a presented model: state spaces,
      observables, units, geometric structures, evolution equations, symmetry,
      boundary conditions, and empirical receivers. A holonic translation must
      map each named structure and prove preservation of the selected laws.
    ],
    transformations: [
      Shared category, topology, differential, conservation, or symmetry
      carriers explain rigorous analogies between domains without identifying
      their material interpretations.
    ],
    boundary: [
      No metaphor about heat, lightning, gravity, quantum collapse, or
      entanglement substitutes for this translation. Conversely, physical
      mathematics remains a valid source of exact reusable structure.
    ],
    source: [Laboratory physics regrade under the theory-translation portal H.0031.],
  ),
  entry(
    id: "H.0464",
    kind: "Atlas",
    grade: "proved-derived",
    title: [Six-shell, receiver frame, and symmetric-stress counts],
    depends: ("H.0241", "H.0270", "H.0294", "H.0455", "H.0459"),
    statement: [
      Several exact occurrences of six must remain typed apart:

      - a triangle boundary has three vertex incidences and three edge
        incidences, while adjoining its two-dimensional interior adds another
        cell;
      - an $n$-cube has $2n$ codimension-one facets;
      - a symmetric bilinear form on an $n$-dimensional space has
        $n(n+1)/2$ independent components; and
      - an affine orthogonal frame group in dimension $n$ has
        $
          n + binom(n,2) = frac(n(n+1),2)
        $
        translation-plus-rotation generators.

      The facet count and symmetric-tensor count agree for positive $n$ exactly
      when $n=3$. In $3+1$ spacetime dimensions a symmetric stress--energy
      tensor has ten components, split relative to a timelike receiver as
      $
        10 = 1 + 3 + 6,
      $
      namely energy density, momentum/energy flux, and spatial symmetric
      stress.
    ],
    transformations: [
      Receiver choice turns one covariant tensor into density, current, and
      stress faces. Changing receiver recomposes those faces without changing
      the tensor. The numerical coincidences above can therefore guide a
      translation only after the incidence or representation map is supplied.
    ],
    boundary: [
      Six graph hops are not a universal locality horizon. Equal dimensions do
      not provide a canonical isomorphism, and the ten components of a
      four-dimensional stress--energy tensor do not cause the ten-dimensional
      critical superstring result.
    ],
    source: [
      Elementary polytope incidence, Lie-group dimension counting, and
      relativistic stress--energy decomposition.
    ],
  ),
  entry(
    id: "H.0465",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Variational tension and the curvature obligation of a knot],
    depends: ("H.0258", "H.0271", "H.0287", "H.0451", "H.0455"),
    statement: [
      Tension is not a bare crossing count. Given a declared curve energy
      $
        E[gamma]=integral L(gamma(s),dot(gamma)(s)) dif s,
      $
      its first variation is the force covector on admissible deformations; an
      equilibrium curve makes that variation vanish subject to its constraints.

      For a closed twice-differentiable space curve, Fenchel's theorem gives
      total curvature at least $2 pi$. The Fary--Milnor theorem sharpens this
      for every nontrivial knot:
      $
        integral abs(kappa(s)) dif s > 4 pi.
      $
    ],
    transformations: [
      Projection crossings may change under receiver motion while knot type and
      the total-curvature obstruction survive the allowed ambient isotopy.
      A perturbation of a constrained energy minimizer propagates according to
      the selected elastic or wave law, not according to knot type alone.
    ],
    boundary: [
      Total curvature is not physical string tension, voltage, heat, or stored
      energy. Each requires an energy functional, constitutive law, units, and
      boundary conditions. Knot invariance constrains possible embeddings but
      does not determine their dynamics.
    ],
    source: [
      Fenchel's theorem and
      #link("https://arxiv.org/abs/math/0606007")[
        Denne and Sullivan, a new proof of the Fary--Milnor theorem
      ].
    ],
  ),
  entry(
    id: "H.0466",
    kind: "Construction",
    grade: "proved-derived",
    title: [Field-coupled leader growth and later return current],
    depends: ("H.0258", "H.0453", "H.0458"),
    statement: [
      A precise minimal leader model is a moving conductive domain
      $Omega_t$ coupled to a potential:
      $
        op("div")(kappa_t op("grad") phi_t)=-rho_t,
        quad
        J_t=-kappa_t op("grad") phi_t.
      $
      The declared local growth law extends $Omega_t$ along an admissible
      boundary deed derived from the contemporary field. That extension changes
      $kappa_t$ and the boundary, so the potential must be solved again on the
      successor domain. Once a conducting channel joins the relevant boundary
      regions, a later high-current return can traverse the channel.
    ],
    transformations: [
      The leader is topology-building field response; the return stroke is a
      later current afforded by the changed topology. Branching, shielding,
      reconnection, and sideways leaders arise from repeatedly coupling the
      field solve to the changed domain rather than selecting a path in a fixed
      graph.
    ],
    boundary: [
      This is a mathematical construction species, not a complete atmospheric
      lightning simulation. A deterministic instance owes complete initial and
      boundary data plus an exact growth law. Least action does not imply a
      greedy shortest-path search.
    ],
    source: [
      Dielectric-breakdown moving-boundary models and measured
      leader--return-stroke separation in lightning physics.
    ],
  ),
  entry(
    id: "H.0467",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Worldsheet stress closure and critical superstring dimension],
    depends: ("H.0279", "H.0451", "H.0455", "H.0460", "H.0461"),
    statement: [
      In the Ramond--Neveu--Schwarz worldsheet formulation, $D$ coordinate
      bosons and $D$ Majorana fermions contribute matter central charge
      $
        c_"matter"=D+frac(D,2)=frac(3D,2).
      $
      Reparametrization and superconformal ghosts contribute
      $c_"ghost"=-15$. Quantum Weyl consistency requires
      $c_"matter"+c_"ghost"=0$, hence the critical spacetime dimension is
      $D=10$.

      For a nonlinear sigma-model target metric, the leading metric beta
      function is
      $
        beta^G_(mu nu)=alpha' "Ric"_(mu nu)+O(alpha'^2)
      $
      when the other background fields are suppressed. Vanishing worldsheet
      trace anomaly therefore yields the vacuum Einstein equation at leading
      order, while the corresponding renormalization flow begins with Ricci
      flow.
    ],
    transformations: [
      Worldsheet stress conservation and trace closure constrain the dimension
      and the admissible target geometry. Thus physical spacetime dynamics
      appears as a consistency condition of a two-dimensional field theory,
      rather than from counting the components of four-dimensional stress.
    ],
    boundary: [
      Ten is conditional on this superstring worldsheet content and anomaly
      cancellation. Background antisymmetric tensor and dilaton fields, higher
      orders in $alpha'$, and other string formulations add their declared
      terms. This is not a universal maximum dimension for every geometry.
    ],
    source: [
      #link("https://www.damtp.cam.ac.uk/user/tong/string/string.pdf")[
        D. Tong, String Theory
      ], worldsheet central charge and sigma-model beta functions.
    ],
  ),
  entry(
    id: "H.0468",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Eleven-dimensional supergravity closure and the Type IIA circle],
    depends: ("H.0459", "H.0460", "H.0461", "H.0467"),
    statement: [
      Under the conventional assumptions of one timelike direction, local
      supersymmetry with at most 32 real supercharges, and no massless field of
      spin greater than two, eleven is the maximal supergravity spacetime
      dimension. Its bosonic fields have
      $
        44 " graviton modes" + 84 " three-form modes" = 128,
      $
      matching the 128 on-shell gravitino modes.

      Strongly coupled Type IIA string theory opens a circular eleventh
      direction with
      $
        R_11=g_s ell_s,
      $
      and the metric rebase
      $
        dif s_11^2
        =
        exp(-2 phi/3) dif s_10^2
        +
        exp(4 phi/3)(dif y+C_1)^2.
      $
      An M2-brane wrapped around that circle has a $(1+1)$-dimensional
      worldsheet in ten dimensions; the transverse count is retained as
      $11=3+8$ becoming $10=2+8$.
    ],
    transformations: [
      The coupling controls a geometric radius, so the ten-dimensional and
      eleven-dimensional descriptions are neighboring faces of one limiting
      construction. Wrapped and unwrapped objects become different
      lower-dimensional species under the same circle rebase.
    ],
    boundary: [
      Eleven is a maximum only under the stated supergravity assumptions, not
      an absolute theorem that no twelve-dimensional or auxiliary formulation
      can exist. The circle relation is the Type IIA/M-theory duality limit, not
      a derivation of all physical dimensions from holonic counting.
    ],
    source: [
      #link("https://arxiv.org/abs/hep-th/9503124")[
        Witten, String theory dynamics in various dimensions
      ];
      #link("https://arxiv.org/abs/2303.12682")[
        Samtleben, Eleven-dimensional supergravity
      ].
    ],
  ),
  entry(
    id: "H.0469",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Iterated integrals are exactly the homotopy functionals, and their algebra is words],
    depends: ("H.0210", "H.0266"),
    statement: [
      For one-forms $omega_1,dots,omega_m$ and a path $gamma$, the iterated
      integral
      $
        integral_gamma omega_1 dots.c omega_m
        =integral_(0&lt;t_1&lt;dots.c&lt;t_m&lt;1)
          gamma^*omega_1(t_1) dots.c gamma^*omega_m(t_m)
      $
      is a homotopy functional rel endpoints, and every such functional arises
      this way: integration is an isomorphism from the bar complex onto them.
      Their algebra is the shuffle algebra on words in the $omega_i$, with the
      deconcatenation coproduct.
    ],
    derivation: [Chen's de Rham theory for path spaces.],
    transformations: [
      This is the ordered-transport receiver, exactly: it sees the path up to
      homotopy and nothing more, and endpoint evaluation is the strictly coarser
      face that the winding separates from it. Because the carrier is a word and
      composition is concatenation, ordered transport and word combinatorics are
      one algebra rather than two subjects.
    ],
    boundary: [
      Complete for homotopy functionals and blind to everything else. Arc length
      is not homotopy invariant, which is why C.0009 has a witness.
    ],
    source: [Chen, iterated path integrals and loop space homology.],
  ),
  entry(
    id: "H.0470",
    kind: "Boundary",
    grade: "conditional",
    title: [A diagram's value is a word; resummation is condensation, and the emulator is a second chart],
    depends: ("H.0150", "H.0216", "H.0469"),
    statement: [
      The finite part of the scalar three-loop tetrahedral vacuum diagram, in
      each of its ten zero-or-unit-mass cases, reduces to four-letter words in an
      alphabet of seven letters -- each word an iterated integral -- evaluating to
      combinations of $zeta(3)$, $zeta(4)$ and three further constants. A
      diagram's value is therefore a word in the shuffle algebra of H.0469; its
      alternating signs are H.0150's; and the two-leg meeting at each vertex is
      H.0216's cross term.
    ],
    derivation: [
      Quoted from the evaluated case. The resummation claim below is cited
      experimental and computational evidence, not a derivation.
    ],
    transformations: [
      Replacing an infinite family of such words by a closed return is the
      condensation of a far population into a compact realizer. Bold diagrammatic
      Monte Carlo achieves this in a genuinely non-perturbative regime for the
      unitary Fermi gas, cross-validated against ultracold-atom measurement: the
      gas is a second apparatus chart for one law, and the agreement is the
      evidence that the condensation is faithful.
    ],
    boundary: [
      An instance, not a method. It establishes that one diagrammatic series
      admits controlled non-perturbative resummation for one system with one
      validated emulator, and supplies no general convergence criterion, no
      transportable error bound, and no construction. No Feynman rules are given
      here: this says what a value *is* once rules are supplied, and asserts
      nothing about whether any ecology in this corpus has a perturbative
      expansion at all.
    ],
    source: [Tetrahedral vacuum diagram evaluation; Van Houcke et al., bold diagrammatic Monte Carlo versus a Fermi-gas emulator.],
  ),
)

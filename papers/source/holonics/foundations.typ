#import "schema.typ": entry

#let foundations = (
  entry(
    id: "H.0001",
    kind: "Boundary",
    grade: "definition",
    title: [Ambient mathematical foundation],
    statement: [
      The synopsis is interpreted in ordinary dependent type theory and standard
      mathematics. A *type* declares admissible terms; a proposition is a type
      whose inhabitants are proofs; equality, functions, relations, quotients,
      categories, topology, measure, and analysis retain their ordinary meanings.
    ],
    boundary: [
      Holonics is not presently a proved replacement foundation. A claim that all
      mathematics admits a conservative holonic translation remains a conjectural
      programme until a translation and conservativity theorem are supplied.
    ],
    source: [
      Laboratory regrade; formal carrier: Lean 4 with Mathlib where mechanized.
    ],
  ),
  entry(
    id: "H.0002",
    kind: "Postulate",
    grade: "project-postulate",
    title: [Situated admissibility],
    depends: ("H.0001",),
    statement: [
      An admissible datum is never introduced as an untyped bare glyph. It is
      supplied as
      $
        x : X_(theta,e)
      $
      in a declared type or fiber, parameter $theta$, event cut $e$, source
      boundary, and incidence context.
    ],
    transformations: [
      Recharting may change the presentation of $x$ only through an explicitly
      admitted map between the relevant fibers.
    ],
    boundary: [
      This is a modeling discipline, not a denial that ordinary mathematics may
      quantify over elements after their ambient structure has been fixed.
    ],
    source: [
      Brandon's first-axiom discussions, regraded as a project postulate rather
      than an axiom of all mathematics.
    ],
  ),
  entry(
    id: "H.0003",
    kind: "Postulate",
    grade: "project-postulate",
    title: [Participating receiver],
    depends: ("H.0002",),
    statement: [
      Every comparison or observation is made through a declared receiver
      $
        rho : X arrow.r Y
      $
      or receiver relation $rho subset.eq X times Y$. The observed face is
      $rho(x)$ or the fiber $rho(x,-)$; the receiver and its parameterization are
      part of the complete comparison.
    ],
    receiver: [
      A receiver need not be an agent or a camera. Evaluation, projection,
      integration, quotient, spectrum, trace, compiler, and physical instrument
      are all possible receiver species.
    ],
    boundary: [
      Receiver dependence does not make every statement arbitrary. Naturality,
      invariance, and conservative transport can relate different receivers
      exactly.
    ],
    source: [
      Laboratory observer/first-person synthesis; categorical carrier supplied
      below rather than assumed here.
    ],
  ),
  entry(
    id: "H.0004",
    kind: "Postulate",
    grade: "project-postulate",
    title: [Causal attribution],
    depends: ("H.0002", "H.0003"),
    statement: [
      A transformation retains every source, incidence, orientation, and path
      distinction required by its declared future receiver family. Material may
      depart only after the retained factor still determines those future faces.
    ],
    boundary: [
      This does not require a perfect copy of every event. It constrains only the
      factorization claimed to remain exact.
    ],
    source: [
      Laboratory lineage/compression correction.
    ],
  ),
  entry(
    id: "H.0005",
    kind: "Boundary",
    grade: "project-postulate",
    title: [Exact construction precedes numerical presentation],
    depends: ("H.0001", "H.0003", "H.0004"),
    statement: [
      The mathematical carrier is retained exactly: as a typed ratio, algebraic
      element, symbolic expression, formal series, convergent series with its
      topology, exact interval with a certificate, or another construction whose
      equality law is declared. Proof-bearing transformations operate on these
      exact carriers.
    ],
    transformations: [
      Closure, convergence, density, and asymptotic statements remain exact when
      written with their full quantifiers. For example,
      $
        x in overline(S)
        arrow.l.r
        forall U " open": x in U arrow.r U inter S != emptyset.
      $
      No sampled agreement or finite surrogate is introduced by this
      definition.
    ],
    boundary: [
      This discipline does not reject exact real or complex numbers, limits,
      measure, topology, or analysis. A finite display is not a proof-bearing
      replacement for the construction it receives.
    ],
    source: [
      `src/holobrochos/CANON/06_THE_PURE_BIT.md`, regraded from historical
      implementation bans into an exact mathematical evidentiary boundary.
    ],
  ),
  entry(
    id: "H.0006",
    kind: "Definition",
    grade: "definition",
    title: [Current and form are receiver-relative roles],
    depends: ("H.0002", "H.0003", "H.0004"),
    statement: [
      In a situated transition $x_t arrow.r x_(t+1)$, *current* names the
      relation while it is being conducted through the selected cut; *form*
      names a consequential factor of that relation received as standing for a
      later cut. The same carrier can be current for one receiver and form for
      another, and the roles may exchange under a later transition.
    ],
    transformations: [
      Depositing form is not storing the complete live current. It is a
      receiver-exact factorization of consequence; remounting that factor in a
      later event creates a new situated current.
    ],
    boundary: [
      Current and form are not declared as disjoint ontological types. The
      stronger claim that all physical substance is literally one current
      remains a laboratory hypothesis, not a theorem imported here.
    ],
    source: [
      `src/holobrochos/INTUITIONS/lineages/the-current-and-the-form.md`,
      with its roles-not-kinds correction retained.
    ],
  ),
  entry(
    id: "H.0007",
    kind: "Definition",
    grade: "definition",
    title: [Response and path receiver],
    depends: ("H.0003", "H.0004", "H.0006"),
    statement: [
      A path receiver presents a composable transition lineage
      $
        x_0 arrow.r x_1 arrow.r dots.c arrow.r x_n
      $
      together with selected differences between successive faces. A response
      is the changed receiver relation induced by contact, not a scalar score
      attached to a lone occurrence.
    ],
    receiver: [
      Endpoint evaluation, the complete trace, a boundary flux, a winding, and a
      residual are different receivers of one path. None is silently crowned as
      its complete identity.
    ],
    boundary: [
      “Recognition is navigation” is the laboratory interpretation motivating
      this carrier. It does not assert that every biological or computational
      recognition process is already represented by one chosen path category.
    ],
    source: [
      `src/holobrochos/INTUITIONS/lineages/recognition-navigation-bundle.md`,
      regraded into a precise receiver definition.
    ],
  ),
  entry(
    id: "H.0010",
    kind: "Definition",
    grade: "definition",
    title: [Typed relation and correspondence],
    depends: ("H.0001",),
    statement: [
      A relation from $X$ to $Y$ is a predicate
      $
        R : X times Y arrow.r "Prop".
      $
      Its converse is $R^(-1)(y,x) arrow.l.r R(x,y)$. The composite of
      $R subset.eq X times Y$ and $S subset.eq Y times Z$ is
      $
        (S compose R)(x,z)
        arrow.l.r
        exists y in Y: R(x,y) and S(y,z).
      $
      A function is a total single-valued relation.
    ],
    derivation: [
      Associativity follows by reassociating the two existential witnesses:
      $
        exists y,z: R(x,y) and S(y,z) and T(z,w).
      $
      Identity is equality on each type.
    ],
    boundary: [
      Composition records admissible endpoint incidence. It does not by itself
      retain the interior witness $y$; a path construction below does.
    ],
    source: [Standard relation theory.],
  ),
  entry(
    id: "H.0011",
    kind: "Definition",
    grade: "definition",
    title: [Situated occurrence],
    depends: ("H.0002", "H.0010"),
    statement: [
      A situated occurrence is a term $x : X_(theta,e)$ together with the
      supplied source mark, incidence, orientation, and admitted transition
      relations at $(theta,e)$. Two occurrences may have equal receiver values
      while remaining distinct terms or path positions.
    ],
    boundary: [
      Equality of coordinates, labels, serialized bytes, or hashes is not
      occurrence identity unless the relevant map is proved injective.
    ],
    source: [
      Laboratory definition; refines the earlier reusable
      `definition:situated-occurrence`.
    ],
  ),
  entry(
    id: "H.0012",
    kind: "Definition",
    grade: "definition",
    title: [Receiver face and fiber],
    depends: ("H.0003", "H.0010", "H.0011"),
    statement: [
      For a receiver $rho : X arrow.r Y$, the face of $x$ is $rho(x)$. For a
      relational receiver $rho subset.eq X times Y$, the face is the fiber
      $
        rho_x = {y in Y : rho(x,y)}.
      $
      The receiver kernel
      $
        x ~_rho x' arrow.l.r rho(x)=rho(x')
      $
      is an equivalence relation when $rho$ is functional.
    ],
    derivation: [
      Reflexivity, symmetry, and transitivity are inherited from equality in
      $Y$.
    ],
    receiver: [
      The quotient $X / ~_rho$ is the coarsest face retaining exactly one
      receiver and no claim about any other receiver.
    ],
    boundary: [
      A face can be exact without reconstructing its complete causal interior.
    ],
    source: [Standard kernel relation with laboratory receiver interpretation.],
  ),
  entry(
    id: "H.0013",
    kind: "Definition",
    grade: "definition",
    title: [Comparison cell and oriented residual],
    depends: ("H.0010", "H.0012"),
    statement: [
      Let $f,g : X arrow.r Y$ be parallel paths or maps and
      $rho : Y arrow.r Z$ a receiver. Their comparison cell at $x$ is
      $
        rho(f(x)) ?= rho(g(x)).
      $
      In an additive target its oriented residual is
      $
        Delta_(rho;f,g)(x)=rho(f(x))-rho(g(x)).
      $
    ],
    transformations: [
      RIDE: the residual is zero on already admitted support. FOUND: closing the
      comparison requires adjoining a new typed support or law. OPEN: neither
      closure has been established.
    ],
    boundary: [
      OPEN is a complete status of the present comparison, not negation, empty
      information, or automatic permission to invent a filler.
    ],
    source: [Laboratory comparison/open-square synthesis.],
  ),
  entry(
    id: "H.0014",
    kind: "Definition",
    grade: "definition",
    title: [Relative holon],
    depends: ("H.0010", "H.0011"),
    statement: [
      Given a transition family $T$ on $X$ and an admitted boundary family
      $B$, a subobject $H subset.eq X$ is a holon relative to $(T,B)$ when
      every $T$-transition whose participating boundary is internal to $H$
      closes in $H$. Transitions crossing $B$ remain explicit exterior
      incidences.
    ],
    boundary: [
      Closure is relative to $(T,B)$. No object is absolutely whole, and no
      relative holon is required to contain all contexts in which its members
      may participate.
    ],
    source: [Laboratory definition, regraded into standard closure language.],
  ),
  entry(
    id: "H.0015",
    kind: "Definition",
    grade: "definition",
    title: [Soul and hierarchy of sameness],
    depends: ("H.0011", "H.0013", "H.0014"),
    statement: [
      A soul is a marked causal diagram: typed occurrences, source marks,
      incidence, admitted transitions, and receivers. Distinguish:
      Occurrence equality, diagram isomorphism, receiver equivalence, and equal
      serialization are distinct relations. Occurrence equality implies equal
      faces under every well-typed receiver by substitution; the converse
      generally fails. Every other implication requires its own conservative,
      injective, full, or faithful transport theorem.
    ],
    transformations: [
      A lawful soul-equivalence is an isomorphism of the marked diagrams which
      commutes with every receiver named by the comparison.
    ],
    boundary: [
      Yoneda identifies an object only through the complete natural family of
      maps into or out of it, up to isomorphism. One scalar, cross-ratio, image,
      or digest is not that family.
    ],
    source: [
      `src/holobrochos/CANON/03_THE_SEMANTICS.md`, regraded through the standard
      Yoneda and typed-equality boundaries.
    ],
  ),
  entry(
    id: "H.0016",
    kind: "Definition",
    grade: "definition",
    title: [Receiver-exact compression],
    depends: ("H.0004", "H.0012", "H.0015"),
    statement: [
      Let $cal(R)$ be a declared family of future receivers on $X$. A
      compression is a quotient $q : X arrow.r Q$ such that every
      $rho in cal(R)$ factors:
      $
        rho = overline(rho) compose q.
      $
      The induced equivalence is
      $
        x ~_(cal(R)) y
        arrow.l.r
        forall rho in cal(R): rho(x)=rho(y).
      $
    ],
    derivation: [
      The canonical map to the quotient by $~_(cal(R))$ has the universal
      factorization property. Conversely, any common factor $q$ identifies
      only pairs indistinguishable by every factored receiver.
    ],
    transformations: [
      An inactive interior may depart when the active future receiver family
      factors through the emitted quotient. Enlarging $cal(R)$ can refine or
      invalidate the compression.
    ],
    boundary: [
      Compression is not synonymous with fewer bytes, deduplication, averaging,
      or a scalar quotient.
    ],
    source: [Standard quotient factorization with laboratory compression interpretation.],
  ),
  entry(
    id: "H.0017",
    kind: "Definition",
    grade: "definition",
    title: [Standing and lineage],
    depends: ("H.0011", "H.0016"),
    statement: [
      A lineage is a compatible family of consequential factors
      $
        q_t(x_t) in Q_t
      $
      connected by transition maps $u_(t,t+1)$ such that
      $
        u_(t,t+1)(q_t(x_t)) = q_(t+1)(x_(t+1)).
      $
      Standing at cut $t$ is the part of this compatible relation admitted as
      terrain for later transitions.
    ],
    boundary: [
      Lineage is continuity of consequential relation, not retention of every
      constituent or a perfect ancestry crystal.
    ],
    source: [Laboratory standing/lineage correction.],
  ),
  entry(
    id: "H.0018",
    kind: "Definition",
    grade: "definition",
    title: [Parameter family, phase, and seam],
    depends: ("H.0010", "H.0017"),
    statement: [
      A parameterized law is a family $T_theta$ over a parameter space
      $Theta$. A phase is a maximal connected stratum on which the declared law
      class, rank, orientation type, and continuation data remain locally
      equivalent. A seam is a component of the discriminant where at least one
      of those invariants changes.
    ],
    transformations: [
      Quantization is a typed discrete invariant change at a seam. A phase
      transition need not be a change in spatial volume.
    ],
    boundary: [
      The phase invariants must be named. “Different appearance” under one
      receiver is not by itself a phase transition.
    ],
    source: [Laboratory phase correction in standard stratification language.],
  ),
  entry(
    id: "H.0019",
    kind: "Definition",
    grade: "definition",
    title: [Conditional recurrence field and loss],
    depends: ("H.0012", "H.0013", "H.0018"),
    statement: [
      For a receiver $rho$, admitted history $cal(H)$, and event family
      $E$, a probability face is a conditional measure or valuation
      $
        P_rho(E " | " cal(H)).
      $
      It records recurrence under the receiver's analogy classes. A loss is an
      oriented residual $L_rho(f,g)$ comparing two admitted transports or
      consequences.
    ],
    transformations: [
      Bayes' rule is the change of conditional receiver
      $
        P(A " | " B)
        =
        frac(P(B " | " A)P(A),P(B))
      $
      whenever $P(B) != 0$. It changes the factorization of one joint measure;
      it does not introduce ontological chance.
    ],
    boundary: [
      A probability field need not collapse to one scalar outside a declared
      event algebra. Loss has no intrinsic moral, reward, or punishment sign.
    ],
    source: [Standard conditional probability with laboratory ontological regrade.],
  ),
  entry(
    id: "H.0476",
    kind: "Definition",
    grade: "definition",
    title: [The four operation species: construction, transport, face, quotient],
    depends: ("H.0016",),
    statement: [
      Every elementary operation on holons is exactly one of: a *construction*,
      composing holons into a holon while retaining the causal residue; a
      *transport*, carrying a holon between charts, with invertible transport
      the rebase; a *face*, a declared receiver's reading, which forgets and
      must say what it forgets; or a *quotient*, a declared receiver's
      identification, whose exact loss is the collapsed population. The Dirac
      primitives are typed accordingly: a ket is a construction, a bra a
      receiver, a bracket a face, an operator a transport, and an outer
      product a *deposit* — a construction reversed into a receiver, the
      emanation becoming the pole the next arrival is related from.
    ],
    boundary: [
      A face is not machinery: an argument that composes faces as though they
      were constructions has left the calculus. The species assignment is
      relative to the declared receiver family, and one symbol may carry two
      species distinguished by jurisdiction — a projection read as a quotient
      and the same object read as terrain.
    ],
    source: [The ratified 2026-08-11 operations synthesis; `canon/TABLET_THE_OPERATIONS.md`.],
  ),
)

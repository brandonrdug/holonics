#import "schema.typ": entry

#let algebra-combinatorics = (
  entry(
    id: "H.0120",
    kind: "Definition",
    grade: "definition",
    title: [Algebraic operations and homomorphisms],
    depends: ("H.0020",),
    statement: [
      A magma, monoid, group, ring, and field are typed operation systems with
      successively stronger laws. A homomorphism preserves every operation and
      constant named by the signature.
    ],
    transformations: [
      Algebraic structure records which compositions are lawful and which
      identities survive transport.
    ],
    boundary: [
      The same carrier set with different operations is a different algebraic
      object. “Prime,” “unit,” and “irreducible” depend on that object.
    ],
    source: [Standard universal algebra.],
  ),
  entry(
    id: "H.0121",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Group action and orbit--stabilizer],
    depends: ("H.0120",),
    statement: [
      For an action $G ↷ X$, the orbit is $G x={g x:g in G}$ and the
      stabilizer is $G_x={g:g x=x}$. If $G$ is finite, then
      $
        abs(G x)=[G:G_x].
      $
    ],
    transformations: [
      An invariant occurrence is fixed by a subgroup; its displayed orbit is
      the family of faces reached by admitted symmetries.
    ],
    boundary: [
      Equality of orbit invariants need not classify orbits unless a complete
      invariant theorem is supplied.
    ],
    source: [Orbit--stabilizer theorem.],
  ),
  entry(
    id: "H.0122",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Modules, linear maps, and rank--nullity],
    depends: ("H.0120",),
    statement: [
      An $R$-module carries addition and a compatible $R$-action. For a linear
      map $T:V arrow.r W$ with $V$ finite dimensional,
      $
        dim V=dim ker T+dim "im" T.
      $
    ],
    transformations: [
      The kernel records directions invisible to the receiver $T$; the image
      records the faces it can emit.
    ],
    boundary: [
      Dimension requires the stated scalar and finiteness hypotheses. Rank is
      not an absolute measure across unrelated modules.
    ],
    source: [Standard module theory and rank--nullity theorem.],
  ),
  entry(
    id: "H.0123",
    kind: "Theorem",
    grade: "proved-standard",
    title: [First isomorphism theorem],
    depends: ("H.0016", "H.0122"),
    statement: [
      For a module homomorphism $T:M arrow.r N$, the map
      $
        M / ker T arrow.r "im" T,
        quad
        m+ker T mapsto T(m)
      $
      is an isomorphism.
    ],
    transformations: [
      The emitted linear face is exactly the source modulo the distinctions
      killed by that receiver.
    ],
    boundary: [
      The quotient reconstructs the image, not the original marked occurrences
      inside each kernel coset.
    ],
    source: [First isomorphism theorem for modules.],
  ),
  entry(
    id: "H.0124",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Short exact sequence and splitting],
    depends: ("H.0123",),
    statement: [
      A sequence
      $
        0 arrow.r A arrow^(i) B arrow^(p) C arrow.r 0
      $
      is exact when $i$ identifies $A$ with $ker p$ and $p$ is onto. It splits
      exactly when $p$ has a section, equivalently $i$ has a retraction; then
      $B equiv A ⊕ C$.
    ],
    transformations: [
      Exactness separates retained interior, total carrier, and exposed
      quotient. Splitting is the additional recoverability law.
    ],
    boundary: [
      Exactness alone does not supply a canonical decomposition.
    ],
    source: [Splitting lemma.],
  ),
  entry(
    id: "H.0125",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Tensor-product universal property],
    depends: ("H.0029", "H.0122"),
    statement: [
      For modules $M,N$, every bilinear map
      $b:M times N arrow.r P$ factors uniquely through a linear map
      $
        overline(b):M ⊗_R N arrow.r P.
      $
    ],
    transformations: [
      The tensor product is the universal linear receiver of bilinear
      co-presence.
    ],
    boundary: [
      Not every interaction is bilinear, and a tensor product is not sequential
      composition.
    ],
    source: [Universal property of the tensor product.],
  ),
  entry(
    id: "H.0126",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Adjoint, Gram form, and positive factorization],
    depends: ("H.0122",),
    statement: [
      A linear map between finite-dimensional inner-product spaces has a unique
      adjoint $T^*$ satisfying
      $
        chevron.l T v,w chevron.r=chevron.l v,T^*w chevron.r.
      $
      A finite Hermitian form $q$ is positive semidefinite exactly when
      $q(v,w)=chevron.l S v,S w chevron.r$ for some $S$.
    ],
    transformations: [
      A positive face is a squared transported distinction. Quotienting by
      $ker q$ produces its positive-definite receiver space.
    ],
    boundary: [
      An adjoint is not generally an inverse or a reversal of causation.
      Positivity must be proved for the complete declared form.
    ],
    source: [Finite-dimensional adjoint theorem and Gram factorization.],
  ),
  entry(
    id: "H.0127",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Schur complement and inertia],
    depends: ("H.0126",),
    statement: [
      If $A>0$, then
      $
        mat(A,C;C^*,D)>=0
        arrow.l.r
        D-C^*A^(-1)C>=0.
      $
      Under congruence, the block matrix has the inertia of $A$ plus the inertia
      of its Schur complement.
    ],
    transformations: [
      Eliminating one positive block returns an exact effective boundary law
      and retains the eliminated block's inertia contribution.
    ],
    boundary: [
      Singularity or indefiniteness of $A$ requires a different shorting or
      generalized-inverse theorem.
    ],
    source: [Schur-complement criterion and Sylvester inertia law.],
  ),
  entry(
    id: "H.0128",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Polynomial evaluation and quotient],
    depends: ("H.0120", "H.0123"),
    statement: [
      For a commutative ring $R$ and $a in R$,
      $
        ker("ev"_a:R[x] arrow.r R)=(x-a),
        quad
        R[x]/(x-a) equiv R.
      $
    ],
    transformations: [
      A polynomial presentation and its evaluated value are related through an
      exact quotient; they are not the same construction.
    ],
    boundary: [
      Evaluation at one point discards every polynomial difference divisible by
      $x-a$.
    ],
    source: [Polynomial remainder theorem and first isomorphism theorem.],
  ),
  entry(
    id: "H.0129",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Chinese remainder decomposition],
    depends: ("H.0128",),
    statement: [
      For pairwise comaximal ideals $I_1,dots.c,I_n$,
      $
        R / {x in R: forall i, x in I_i}
        equiv
        product_i R/I_i.
      $
    ],
    transformations: [
      One source admits a compatible product of residue-loop receivers. The
      inverse is exact only because comaximality supplies the gluing idempotents.
    ],
    boundary: [
      A single residue coordinate does not determine the source class.
    ],
    source: [Chinese remainder theorem.],
  ),
  entry(
    id: "H.0130",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Field extension, minimal polynomial, and tower law],
    depends: ("H.0128",),
    statement: [
      An algebraic element $alpha$ over $F$ has a unique monic minimal
      polynomial $m_alpha$ and
      $F(alpha) equiv F[x]/(m_alpha)$. For finite $F subset K subset L$,
      $
        [L:F]=[L:K][K:F].
      $
    ],
    transformations: [
      Adjoining an algebraic axis changes the ambient field by an exact
      quotient; tower degree records compositional rank.
    ],
    boundary: [
      Transcendental extensions are not finite quotients by a minimal
      polynomial.
    ],
    source: [Standard field-extension theory.],
  ),
  entry(
    id: "H.0131",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Galois correspondence],
    depends: ("H.0121", "H.0130"),
    statement: [
      For finite Galois $L/F$ with group $G$, subgroups $H<=G$ correspond
      order-reversingly to intermediate fields through
      $H mapsto L^H$ and $K mapsto "Gal"(L/K)$. Normal subgroups correspond to
      Galois subextensions.
    ],
    transformations: [
      Symmetry subgroups and fixed receivers are dual order faces of one field
      extension.
    ],
    boundary: [
      The finite Galois hypotheses are essential; inseparable and infinite
      extensions require enlarged forms of the theorem.
    ],
    source: [Fundamental theorem of Galois theory.],
  ),
  entry(
    id: "H.0132",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Representations and Schur channels],
    depends: ("H.0121", "H.0122"),
    statement: [
      A representation is a homomorphism $G arrow.r "GL"(V)$. An intertwiner
      commutes with the action. Over an algebraically closed field,
      finite-dimensional irreducibles $V,W$ obey
      $
        "Hom"_G(V,W)=0
      $
      when nonisomorphic, and $"End"_G(V)$ consists of scalars.
    ],
    transformations: [
      Intertwiners are the lawful transports between symmetry-conditioned
      channels.
    ],
    boundary: [
      Reducible representations and non-algebraically-closed scalars admit
      larger commutants.
    ],
    source: [Schur's lemma.],
  ),
  entry(
    id: "H.0133",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Maschke decomposition],
    depends: ("H.0132", "H.0124"),
    statement: [
      If $G$ is finite and $"char"(k)$ does not divide $abs(G)$, every
      finite-dimensional $k[G]$-representation is a direct sum of irreducibles.
    ],
    transformations: [
      Averaging a projection over $G$ produces an invariant complement, hence
      an exact constituent decomposition.
    ],
    boundary: [
      In modular characteristic the averaging denominator vanishes and complete
      reducibility can fail.
    ],
    source: [Maschke's theorem.],
  ),
  entry(
    id: "H.0140",
    kind: "Definition",
    grade: "definition",
    title: [Poset, meet, join, and lattice],
    depends: ("H.0010",),
    statement: [
      A partial order is reflexive, antisymmetric, and transitive. A meet is a
      greatest lower bound; a join is a least upper bound. A lattice has both
      for every pair.
    ],
    transformations: [
      Founding, refinement, divisibility, information, and closure orders are
      different posets until an order-preserving translation relates them.
    ],
    boundary: [
      One chronological order need not totalize co-present or incomparable
      events.
    ],
    source: [Standard order theory.],
  ),
  entry(
    id: "H.0141",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Galois connection and closure],
    depends: ("H.0140",),
    statement: [
      Monotone maps $alpha:P arrow.r Q$ and $gamma:Q arrow.r P$ form a Galois
      connection when
      $
        alpha(p)<=q arrow.l.r p<=gamma(q).
      $
      Then $gamma alpha$ is a closure operator and $alpha gamma$ an interior
      operator.
    ],
    transformations: [
      Mutually constrained source and receiver maps induce exact closed and open
      fixed-point strata.
    ],
    boundary: [
      A feedback pair is not a Galois connection unless the adjunction
      inequality is proved.
    ],
    source: [Standard Galois-connection theorem.],
  ),
  entry(
    id: "H.0142",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Incidence algebra and Möbius inversion],
    depends: ("H.0140", "H.0120"),
    statement: [
      On a locally finite poset, convolution is
      $
        (f star g)(x,z)=sum_(x<=y<=z)f(x,y)g(y,z).
      $
      The zeta function has inverse $mu$. Hence
      $
        G(x)=sum_(y<=x)F(y)
        arrow.r
        F(x)=sum_(y<=x)mu(y,x)G(y).
      $
    ],
    transformations: [
      Inclusion over an incidence order and its exact foil are mutually inverse
      transports.
    ],
    boundary: [
      Local finiteness, or an alternative summability law, is required.
    ],
    source: [Möbius inversion on locally finite posets.],
  ),
  entry(
    id: "H.0143",
    kind: "Identity",
    grade: "proved-standard",
    title: [Formal generating-function convolution],
    depends: ("H.0109", "H.0120"),
    statement: [
      In the formal power-series ring,
      $
        [z^n](sum_(j>=0)a_j z^j)(sum_(k>=0)b_k z^k)
        =
        sum_(j=0)^n a_j b_(n-j).
      $
    ],
    transformations: [
      Multiplication composes two counted path populations by every split of
      total degree $n$.
    ],
    boundary: [
      Formal validity uses finitely many terms per coefficient and requires no
      analytic convergence. Evaluation at a number is a later receiver.
    ],
    source: [Cauchy product in a formal power-series ring.],
  ),
  entry(
    id: "H.0144",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Graph incidence, cycles, and cuts],
    depends: ("H.0122", "H.0126"),
    statement: [
      For an oriented finite graph with incidence matrix $B$, flows satisfying
      junction balance form $ker B$ and potential-generated cuts form
      $"im" B^*$. Over $RR$,
      $
        (ker B)^perp="im" B^*,
        quad
        "rank" B=abs(V)-c
      $
      where $c$ is the number of connected components.
    ],
    transformations: [
      Cycle current and gradient potential are orthogonal receiver species.
      Orientation changes signs but not the cycle and cut dimensions.
    ],
    boundary: [
      Weighted, directed-capacity, and nonlinear networks require their own
      operators; the incidence law alone does not supply dynamics.
    ],
    source: [Algebraic graph theory.],
  ),
  entry(
    id: "H.0145",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Maximum flow, minimum cut, and Hall boundary],
    depends: ("H.0140", "H.0144"),
    statement: [
      In a finite nonnegative-capacity network, maximum feasible source--sink
      flow equals minimum cut capacity. A finite bipartite graph has a matching
      saturating $L$ exactly when
      $
        abs(N(S))>=abs(S)
      $
      for every $S subset.eq L$.
    ],
    transformations: [
      Both theorems replace a global navigation question by an exact family of
      boundary-capacity conditions.
    ],
    boundary: [
      They do not choose semantic objectives or manufacture absent edges.
    ],
    source: [Max-flow/min-cut theorem and Hall's marriage theorem.],
  ),
  entry(
    id: "H.0146",
    kind: "Definition",
    grade: "definition",
    title: [Matroid dependence and basis exchange],
    depends: ("H.0140",),
    statement: [
      A nonempty family of bases is a matroid basis family when, for
      $x in B_1 minus B_2$, some $y in B_2 minus B_1$ makes
      $(B_1 minus {x}) union {y}$ a basis. Its rank function is monotone and
      submodular.
    ],
    transformations: [
      Matroids retain abstract dependence while permitting multiple coordinate
      bases and exchange paths between them.
    ],
    boundary: [
      Not every context-dependent relation is matroidal; exchange must hold.
    ],
    source: [Standard matroid cryptomorphisms.],
  ),
  entry(
    id: "H.0147",
    kind: "Identity",
    grade: "proved-standard",
    title: [Inclusion--exclusion and binomial transport],
    depends: ("H.0142",),
    statement: [
      For finite sets $A_1,dots.c,A_n$,
      $
        abs(union_i A_i)
        =
        sum_(emptyset != J subset.eq {1,dots.c,n})
        (-1)^(abs(J)+1) abs({x:forall j in J, x in A_j}).
      $
      This is Möbius inversion on the Boolean lattice.
    ],
    transformations: [
      Alternating overlap terms restore distinctions lost by a naive sum of
      receiver faces.
    ],
    boundary: [
      Infinite families require measure or convergence hypotheses.
    ],
    source: [Inclusion--exclusion principle.],
  ),
  entry(
    id: "H.0148",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Linear recurrence and transfer matrix],
    depends: ("H.0122", "H.0143"),
    statement: [
      A recurrence
      $
        a_(n+r)=c_(r-1)a_(n+r-1)+dots.c+c_0 a_n
      $
      is equivalent to iteration of its companion matrix on the state
      $(a_n,dots.c,a_(n+r-1))$. Its generating function is rational.
    ],
    transformations: [
      The scalar sequence, finite state transport, and rational series are
      three exact receiver faces of one recurrence.
    ],
    boundary: [
      Nonlinear, variable-coefficient, and infinite-memory recurrences need
      different state carriers.
    ],
    source: [Standard linear-recurrence theory.],
  ),
)

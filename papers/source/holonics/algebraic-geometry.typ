#import "schema.typ": entry

#let algebraic-geometry = (
  entry(
    id: "H.0320",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Affine locus and coordinate ring duality],
    depends: ("H.0128", "H.0220"),
    statement: [
      Over an algebraically closed field $k$, Hilbert's Nullstellensatz gives
      $
        I(V(I))=sqrt(I),
        quad
        V(I(V))=V.
      $
      Affine algebraic sets correspond contravariantly to finitely generated
      reduced $k$-algebras.
    ],
    transformations: [
      Equations and their solution loci are contravariant receiver faces of one
      constrained algebraic construction.
    ],
    boundary: [
      The algebraic-closure and finite-generation hypotheses matter; schemes
      retain nilpotents and arithmetic base information beyond reduced loci.
    ],
    source: [Hilbert Nullstellensatz and affine coordinate-ring duality.],
  ),
  entry(
    id: "H.0321",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Prime spectrum and affine scheme],
    depends: ("H.0120", "H.0320"),
    statement: [
      $"Spec"(A)$ is the set of prime ideals with closed sets
      $V(I)={p:I subset.eq p}$. A ring map $A arrow.r B$ induces
      $"Spec"(B) arrow.r "Spec"(A)$ by inverse image, and affine schemes are
      contravariantly equivalent to commutative rings.
    ],
    transformations: [
      A scheme point carries a prime ideal and local algebraic interior; map
      direction reverses under the spectrum receiver.
    ],
    boundary: [
      A prime ideal is not merely a coordinate point, and arithmetic spectra are
      not generally varieties over algebraically closed fields.
    ],
    source: [Affine scheme--ring duality.],
  ),
  entry(
    id: "H.0322",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Localization, structure sheaf, and stalk],
    depends: ("H.0030", "H.0321"),
    statement: [
      On the basic open $D(f) subset.eq "Spec"(A)$,
      $
        cal(O)(D(f))=A_f,
      $
      and the stalk at $p$ is $cal(O)_p=A_p$. Compatible local fractions glue
      uniquely by the sheaf law.
    ],
    transformations: [
      Localization is an exact local receiver inverting the functions visible
      as nonzero on the selected region.
    ],
    boundary: [
      Local equality in one stalk need not imply equality on the complete
      scheme.
    ],
    source: [Structure sheaf of an affine scheme.],
  ),
  entry(
    id: "H.0323",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Fiber product and algebraic base change],
    depends: ("H.0025", "H.0125", "H.0321"),
    statement: [
      For $A arrow.r B,C$,
      $
        "Spec"(B) times_("Spec"(A)) "Spec"(C)
        equiv
        "Spec"(B ⊗_A C).
      $
    ],
    transformations: [
      Co-present algebraic incidence is a pullback; its coordinate receiver is
      the tensor product.
    ],
    boundary: [
      Tensoring can introduce nilpotents, reducibility, or singularity; base
      change does not preserve every property without hypotheses.
    ],
    source: [Affine fiber-product theorem.],
  ),
  entry(
    id: "H.0324",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Projective coordinates and Bézout intersection],
    depends: ("H.0273", "H.0320"),
    statement: [
      Projective algebraic loci are cut out by homogeneous ideals. If two plane
      projective curves over an algebraically closed field have degrees $m,n$
      and share no component, then
      $
        sum_P I_P(C,D)=m n
      $
      with intersection multiplicity.
    ],
    transformations: [
      Projection may change the visible diagram while homogeneous incidence and
      total intersection multiplicity remain exact.
    ],
    boundary: [
      Set-theoretic crossing count omits multiplicity and points at infinity.
    ],
    source: [Projective coordinate theory and Bézout theorem.],
  ),
  entry(
    id: "H.0325",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Noether normalization and dimension],
    depends: ("H.0130", "H.0320"),
    statement: [
      For a finitely generated $k$-domain $A$, there are algebraically
      independent $t_1,dots.c,t_d$ such that $A$ is finite over
      $k[t_1,dots.c,t_d]$, and
      $
        d=dim A="trdeg"_k "Frac"(A).
      $
    ],
    transformations: [
      Intrinsic algebraic dimension is the number of independent axes in a
      finite generic projection, not the number of chosen generators.
    ],
    boundary: [
      Dimension can jump in families, and embedding dimension can exceed
      Krull dimension at singular points.
    ],
    source: [Noether normalization theorem.],
  ),
  entry(
    id: "H.0326",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Zariski tangent and Jacobian seam],
    depends: ("H.0122", "H.0325"),
    statement: [
      For $X=V(f_1,dots.c,f_r) subset.eq AA^n$,
      $
        T_x X=ker J_f(x).
      $
      At expected codimension, maximal Jacobian rank is equivalent to
      smoothness; rank loss marks the singular locus.
    ],
    transformations: [
      The Jacobian determines first-order afforded directions; its rank
      discriminant is a precise seam where local continuation type changes.
    ],
    boundary: [
      A singularity is not inferred from a rendered kink alone. In positive
      characteristic the naive Jacobian criterion needs its standard
      hypotheses.
    ],
    source: [Zariski tangent-space definition and Jacobian criterion.],
  ),
  entry(
    id: "H.0327",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Divisors and Riemann--Roch on a curve],
    depends: ("H.0130", "H.0322", "H.0325"),
    statement: [
      On a smooth projective curve, principal divisors have degree zero. For a
      divisor $D$ and canonical divisor $K$,
      $
        ell(D)-ell(K-D)=deg D+1-g.
      $
    ],
    transformations: [
      Zeros and poles are oriented valuation incidences; Riemann--Roch balances
      their degree against the available global sections and genus.
    ],
    boundary: [
      Divisor class, chosen divisor, and section space are different objects.
    ],
    source: [Riemann--Roch theorem for smooth projective curves.],
  ),
  entry(
    id: "H.0328",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Normalization of an algebraic locus],
    depends: ("H.0130", "H.0321"),
    statement: [
      For a finitely generated domain $A$ over a field, its integral closure
      $tilde(A)$ in $"Frac"(A)$ is finite over $A$. The map
      $
        "Spec"(tilde(A)) arrow.r "Spec"(A)
      $
      is finite and birational and is an isomorphism over the normal locus.
    ],
    transformations: [
      Normalization separates some singular branch presentations while
      retaining the function field.
    ],
    boundary: [
      It is not an isomorphism at every singularity and does not preserve the
      original marked construction.
    ],
    source: [Finiteness of normalization for affine varieties.],
  ),
  entry(
    id: "H.0329",
    kind: "Definition",
    grade: "definition",
    title: [Family, fiber, and discriminant],
    depends: ("H.0018", "H.0323", "H.0326"),
    statement: [
      For a morphism $pi:X arrow.r S$, the fiber at $s$ is
      $X_s=X times_S "Spec"(k(s))$. A discriminant is a declared locus in $S$
      where smoothness, rank, multiplicity, or another named fiber invariant
      fails to continue.
    ],
    transformations: [
      Parameter change moves through a family of interiors; the discriminant
      is the exact algebraic seam of a selected law class.
    ],
    boundary: [
      Different invariants define different discriminants. “Interesting change”
      is not a mathematical discriminant until the failed property is named.
    ],
    source: [Standard scheme-theoretic fibers and discriminant loci.],
  ),
  entry(
    id: "H.0330",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Étale cohomology, Frobenius trace, and purity],
    depends: ("H.0226", "H.0327"),
    statement: [
      For a smooth projective variety $X$ over $FF_q$, the Grothendieck--Lefschetz
      trace formula and cohomological determinant give
      $
        Z(X,T)
        =
        product_i det(1-T "Frob" " | " H^i_("et")(X,QQ_l))^((-1)^(i+1)).
      $
      Deligne's purity theorem places Frobenius eigenvalues on $H^i$ at complex
      modulus $q^(i/2)$.
    ],
    transformations: [
      Point counts, closed arithmetic orbits, cohomological degrees, and the
      zeta spectrum are exact connected receivers. Purity fixes the half-weight
      seam.
    ],
    boundary: [
      The classical-number-field zeta function has no accepted object carrying
      this entire Frobenius/cohomology/purity package.
    ],
    source: [Grothendieck trace formula and Deligne's Weil-conjecture proof.],
  ),
  entry(
    id: "H.0331",
    kind: "Definition",
    grade: "definition",
    title: [Moduli and quotient stack boundary],
    depends: ("H.0027", "H.0121", "H.0329"),
    statement: [
      A moduli functor assigns to each base its family of objects up to the
      declared isomorphism and their pullbacks. A fine moduli space represents
      that functor. When automorphisms obstruct representability, a stack
      retains the groupoid of objects and isomorphisms.
    ],
    transformations: [
      Parameter space and symmetry quotient are inseparable when objects have
      stabilizers; the stack retains that isotropy.
    ],
    boundary: [
      A coarse moduli point need not determine a universal family or automorphism
      lineage.
    ],
    source: [Standard moduli-functor and algebraic-stack definitions.],
  ),
)

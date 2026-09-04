#import "schema.typ": entry

#let logic-category = (
  entry(
    id: "H.0020",
    kind: "Rule",
    grade: "proved-standard",
    title: [Typed equality and substitution],
    depends: ("H.0001",),
    statement: [
      Equality $x =_X y$ is an equivalence relation on terms of one type $X$.
      For every well-typed predicate or construction $P$ on $X$, equality
      permits substitution of $y$ for $x$. Equality across different ambient
      types requires an explicitly supplied transport.
    ],
    transformations: [
      Construction equality implies equality under every function with source
      $X$. Equality under one noninjective receiver need not imply construction
      equality.
    ],
    boundary: [
      A shared glyph, coordinate, unit label, or output value does not create a
      typed equality proof.
    ],
    source: [Identity elimination in dependent type theory.],
  ),
  entry(
    id: "H.0021",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Well-founded induction and recursion],
    depends: ("H.0020", "H.0010"),
    statement: [
      If $prec$ is well founded on $X$ and
      $
        (forall y prec x: P(y)) arrow.r P(x)
      $
      for every $x$, then $forall x: P(x)$. Compatible predecessor data define
      a unique recursive function by the well-founded recursion theorem.
    ],
    transformations: [
      Ordinary induction is the specialization to the predecessor relation on
      $NN$. Structural induction uses the immediate-subterm relation.
    ],
    boundary: [
      A recurring visual pattern is not an induction hypothesis. The carrier,
      well-founded order, base cases, and successor implication must be stated.
    ],
    source: [Standard well-founded induction and recursion theorem.],
  ),
  entry(
    id: "H.0022",
    kind: "Definition",
    grade: "definition",
    title: [Category and free path category],
    depends: ("H.0010", "H.0007"),
    statement: [
      A category has typed objects and arrows, associative composition, and one
      identity arrow at each object. Every directed graph $G$ generates a free
      category $"Path"(G)$ whose arrows are finite composable edge words and
      whose composition is concatenation.
    ],
    receiver: [
      Endpoint evaluation forgets the interior word. The free path category
      retains it until a declared relation quotients paths.
    ],
    boundary: [
      Category composition records lawful composability, not temporal causation
      by itself.
    ],
    source: [Standard category theory and the free-category construction.],
  ),
  entry(
    id: "H.0023",
    kind: "Definition",
    grade: "definition",
    title: [Functor and natural transformation],
    depends: ("H.0022",),
    statement: [
      A functor $F:cal(C) arrow.r cal(D)$ preserves source, target, identities,
      and composition. A natural transformation $eta:F arrow.r G$ obeys
      $
        G(f) compose eta_X = eta_Y compose F(f)
      $
      for every $f:X arrow.r Y$.
    ],
    transformations: [
      Functorial receivers preserve execution composition. A lawful change of
      receiver is natural only when every such square commutes.
    ],
    boundary: [
      A collection of objectwise translations is not a natural transformation
      until the arrow law is proved.
    ],
    source: [Standard category theory.],
  ),
  entry(
    id: "H.0024",
    kind: "Definition",
    grade: "definition",
    title: [Universal property, limit, and colimit],
    depends: ("H.0022", "H.0023"),
    statement: [
      A limit of $F:J arrow.r cal(C)$ is a terminal cone to $F$; a colimit is
      an initial cocone from $F$. Either object is unique up to a unique
      isomorphism compatible with its structure maps.
    ],
    transformations: [
      Products, equalizers, pullbacks, coproducts, coequalizers, and pushouts are
      finite shapes of this one universal law.
    ],
    boundary: [
      A universal object is relative to its diagram and category. It is not an
      absolute total field containing every context.
    ],
    source: [Standard universal-property definition.],
  ),
  entry(
    id: "H.0025",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Pullback and pushout gluing],
    depends: ("H.0024",),
    statement: [
      The pullback $X times_Z Y$ is terminal among pairs mapping compatibly to
      $X$ and $Y$. The pushout $X plus_Z Y$ is initial among objects receiving
      maps from $X$ and $Y$ which agree on $Z$.
    ],
    transformations: [
      Pullback forms a shared compatible interior. Pushout glues two presented
      regions along one declared common boundary.
    ],
    boundary: [
      Neither construction licenses gluing from likeness alone; the comparison
      maps to or from $Z$ are required data.
    ],
    source: [Standard finite-limit and finite-colimit universal properties.],
  ),
  entry(
    id: "H.0026",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Span and cospan composition],
    depends: ("H.0025",),
    statement: [
      In a category with pullbacks, spans compose by pullback. In a category
      with pushouts, cospans compose by pushout. Both compositions are
      associative up to canonical isomorphism and admit identity
      spans or cospans.
    ],
    transformations: [
      Spans compare through a common refinement; cospans compose open systems by
      joining interfaces. They are nonidentical relation species.
    ],
    boundary: [
      Strict associativity requires a chosen strictification or bicategorical
      treatment; canonical isomorphism is the standard statement.
    ],
    source: [Standard span and cospan bicategories.],
  ),
  entry(
    id: "H.0027",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Yoneda relation atlas],
    depends: ("H.0023",),
    statement: [
      For $F:cal(C)^op arrow.r "Set"$,
      $
        "Nat"("Hom"(-,X),F) equiv F(X)
      $
      naturally in $F$ and $X$. Consequently the complete representable
      functor determines $X$ up to isomorphism.
    ],
    transformations: [
      An object can be recovered from the natural family of all admitted
      relations to it. This is the precise categorical boundary behind
      receiver-relative identity.
    ],
    boundary: [
      One hash, scalar, image, cross-ratio, or finite receiver family is not the
      complete representable functor.
    ],
    source: [Yoneda lemma.],
  ),
  entry(
    id: "H.0028",
    kind: "Definition",
    grade: "definition",
    title: [Adjunction, unit, and counit],
    depends: ("H.0023",),
    statement: [
      An adjunction $F ⊣ G$ is a natural bijection
      $
        "Hom"_cal(D)(F X,Y) equiv "Hom"_cal(C)(X,G Y).
      $
      Equivalently it has a unit $eta:1 arrow.r G F$ and counit
      $epsilon:F G arrow.r 1$ satisfying the two triangle identities.
    ],
    transformations: [
      The unit and counit are opposed passages between two description worlds;
      their triangles express exact round-trip coherence.
    ],
    boundary: [
      An adjoint is not generally an inverse. The unit or counit may lose
      distinctions unless it is an isomorphism.
    ],
    source: [Standard adjoint-functor definition.],
  ),
  entry(
    id: "H.0029",
    kind: "Definition",
    grade: "definition",
    title: [Monoidal co-presence],
    depends: ("H.0022",),
    statement: [
      A monoidal category carries a bifunctor $⊗$, a unit object, and
      coherent associator and unitor isomorphisms. A symmetric monoidal category
      additionally has a coherent swap $X ⊗ Y equiv Y ⊗ X$.
    ],
    transformations: [
      $⊗$ models co-present composition; categorical composition models
      succession. Interchanging them requires the monoidal interchange law.
    ],
    boundary: [
      A tensor symbol alone does not specify interaction, entanglement, or
      physical simultaneity.
    ],
    source: [Mac Lane's monoidal-category axioms.],
  ),
  entry(
    id: "H.0030",
    kind: "Definition",
    grade: "definition",
    title: [Presheaf, sheaf, and exact local gluing],
    depends: ("H.0023", "H.0025"),
    statement: [
      A presheaf assigns data $F(U)$ contravariantly to regions and restriction
      maps to inclusions. A sheaf requires that every compatible family on a
      cover glues to one unique section on the covered region.
    ],
    transformations: [
      Restriction gives receiver-relative local faces; the sheaf axiom states
      the exact condition under which those faces determine a common interior.
    ],
    boundary: [
      Local agreement without the overlap equations does not imply a global
      section. Some mathematical data form only presheaves.
    ],
    source: [Standard sheaf axiom.],
  ),
  entry(
    id: "H.0031",
    kind: "Definition",
    grade: "definition",
    title: [Theory, model, and translation portal],
    depends: ("H.0020", "H.0023"),
    statement: [
      A presented mathematical theory consists of a typed signature, axioms,
      and a class of models with structure-preserving maps. A translation
      supplies a map of signatures and an interpretation carrying every source
      axiom to a theorem of the target.
    ],
    transformations: [
      Every domain enters this synopsis through its presented objects,
      relations, operations, models, and receivers. Functorial translations can
      then compare domains without declaring their objects identical.
    ],
    boundary: [
      This portal makes every suitably presented field importable; it is not a
      proof that holonics is conservative, complete, or equivalent to every
      mathematical foundation.
    ],
    source: [Standard model-theoretic presentation; laboratory atlas schema.],
  ),
  entry(
    id: "H.0032",
    kind: "Definition",
    grade: "definition",
    title: [Enriched category and structured parameters],
    depends: ("H.0029",),
    statement: [
      For a monoidal category $cal(V)$, a $cal(V)$-enriched category replaces
      each hom-set by a hom-object $underline("Hom")(X,Y) in cal(V)$ and gives
      composition and identity as morphisms of $cal(V)$. A parameterized
      family is a generalized element
      $
        P arrow.r underline("Hom")(X,Y).
      $
    ],
    transformations: [
      The monoidal structure of $cal(V)$ determines how parameters compose.
      Copying or discarding $P$ requires corresponding comonoid structure; it
      is not supplied by the word “parameter.”
    ],
    boundary: [
      Enrichment does not choose the parameter category or make every resource
      duplicable.
    ],
    source: [Standard enriched category theory and parameterized circuit semantics.],
  ),
  entry(
    id: "H.0033",
    kind: "Definition",
    grade: "definition",
    title: [Indexed category, fibration, and Grothendieck assembly],
    depends: ("H.0023",),
    statement: [
      An indexed category is a pseudofunctor
      $F:cal(R)^op arrow.r "Cat"$. Its Grothendieck construction
      $integral F arrow.r cal(R)$ is a fibration whose fiber at $rho$ is
      $F(rho)$. Cartesian or cocartesian lifts state how objects transport
      along arrows of the base.
    ],
    transformations: [
      Receiver-local ecologies live in fibers. The total category assembles
      their typed transports without becoming a receiver outside the system.
      Lax or oplax transport retains a directed comparison when strict
      naturality does not hold.
    ],
    boundary: [
      The Grothendieck total category is not an absolute global state, and a
      base arrow does not license a lift unless the fibration supplies it.
    ],
    source: [Standard indexed-category and Grothendieck-fibration equivalence.],
  ),
  entry(
    id: "H.0034",
    kind: "Definition",
    grade: "definition",
    title: [Double category and interaction doctrine],
    depends: ("H.0026", "H.0029"),
    statement: [
      A double category has objects, horizontal arrows, vertical arrows, and
      squares with horizontal and vertical composition satisfying
      interchange. A doctrine of open systems may additionally act through
      an operad or module of interface patterns, separating the systems from
      the ways their ports, variables, or boundaries interact.
    ],
    transformations: [
      Sequential evolution, boundary rechart, independent juxtaposition, and
      actual interaction become separately typed compositional directions.
    ],
    boundary: [
      A monoidal coproduct gives juxtaposition only. Contact or co-presence
      requires a declared interaction pattern and its action.
    ],
    source: [Standard double categories, structured cospans, and categorical systems theory.],
  ),
  entry(
    id: "H.0035",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Local sections, global gluing, and obstruction],
    depends: ("H.0030", "H.0033"),
    statement: [
      On a site, every section over a covered region restricts to compatible
      local sections. For a sheaf the converse holds uniquely. Compatible
      local data with nontrivial overlap holonomy cannot be restrictions of
      one global section.
    ],
    transformations: [
      “Global over $U$” means transported local agreement across a cover of
      the boundary-defined region $U$. Nontrivial return around an overlap
      cycle is a local-to-global obstruction.
    ],
    boundary: [
      The theorem supplies no greatest region and no total field. Pairwise
      compatibility alone may be insufficient when higher overlaps matter.
    ],
    source: [The sheaf axiom and standard Čech obstruction theory.],
  ),
  entry(
    id: "H.0036",
    kind: "Definition",
    grade: "definition",
    title: [Information order, algebra, and coalgebra],
    depends: ("H.0021", "H.0023"),
    statement: [
      An information order $x subset.eq y$ says that $y$ extends the
      distinctions carried by $x$. An $F$-algebra $F A arrow.r A$ folds a
      recursively generated structure; an $F$-coalgebra
      $X arrow.r F X$ unfolds observable process structure. Well-founded
      coalgebras support recursion and termination arguments.
    ],
    transformations: [
      Inductive data, streaming state, recursive algorithms, and growing
      standing can be compared without reducing the process to one endpoint
      function.
    ],
    boundary: [
      A path witnesses information growth only under the declared domain or
      synthetic-domain axioms. Not every geometric path is automatically an
      information extension.
    ],
    source: [Standard domain theory, initial-algebra, and coalgebraic recursion.],
  ),
)

# Higher-Dimensional Algebra: Three Sources

## 1. Brown & Porter, "Category Theory and Higher Dimensional Algebra... in neuroscience" (arXiv math/0306223)

### Category (p.3)

Brown–Porter build categories from the function notation "f : X → Y assigns to each element x of
the set X an element f(x) of the set Y" (p.3):

> "the notion of a category C, which consists of a class Ob(C) of 'objects', a set of 'arrows', or
> 'morphisms' f : X → Y for any two objects X, Y, and a composition, giving, for instance,
> f g : X → Z if also g : Y → Z." (p.3)

Composite diagrams, eq. (1)–(2): a linear chain `X →f Y →g Z`, and the equivalent triangle with `X`
mapping to `Y` by `f`, to `Z` by `fg`, and `Y` to `Z` by `g`. Axioms (unnumbered, p.3):

> "The only rules are associativity f(gh) = (fg)h when both sides are defined, and the existence
> of identities 1X at each object X, so that with f as above, 1X f = f = f 1Y."

**Functor and natural transformation are not defined in this paper.** A search of the full text
finds no occurrence of either term in the body; Eilenberg–Mac Lane's "General theory of natural
equivalences" appears only as bibliography item [15]. The paper's formal apparatus is limited to
category and colimit.

### Colimit as gluing (p.2–6)

Section 2 is titled "Category theory and colimits: **gluing and structure**" (p.2). The paper does
**not** use the phrase "local-to-global" in its own prose — that phrase occurs only in the title of
cited reference [7] (R. Brown, "...non-commutative tools for higher dimensional local-to-global
problems", bibliography, p.12). Brown–Porter's own words are "gluing" and "amalgamating":

> "This notion of colimit gives a very general setting in which to describe the process of gluing
> or amalgamating complex structures, together with a description of the method of input to and
> output from these structures." (p.3)

> "Such questions arose from a gluing or colimit problem in topology, namely to describe the
> behaviour of a big object in terms of the behaviour of its parts." (p.8)

Colimit is built from: a diagram D (dots joined by directed arrows in C, p.4); a cocone on D with
vertex C — "a cocone with base D and vertex an object C" (p.4), drawn as C at the apex with arrows
down to every object of D, "such that each of the triangular faces of this cocone is commutative"
(p.4); and the colimit cocone colim(D), through which every other cocone factors uniquely — drawn
with dotted arrows "which combine to make the colimit cocone" and a broken arrow Φ "constructed
from the other information" (p.5). Stripping the old cocone away gives the factorisation
Φ : colim(D) → C (p.5–6).

> "The object colim(D) is 'put together' from, or 'composed of the parts of', the constituent
> diagram D by means of the colimit cocone. From beyond (or above our diagrams) D, an object C
> 'sees' the diagram D 'mediated' through its colimit." (p.5)

The extended illustration is an email E broken by a server S into parts Eᵢ, relabelled Eᵢ′, routed
through servers Sᵢ to a receiver server S_C, which "combines the Eᵢ′′ to produce the received
message ME at C," independent of how the routing was chosen (p.6). Later, in the Questions:
"Information is often 'subdivided' by the sensory organs and is reintegrated by the brain. To
enable different parts of that information to be integrated, there must be some 'glue'" (p.11).

**No dedicated "hierarchical / levels" figure appears in the body.** "Hierarchical" and "level(s)"
occur only in bibliography titles ([10] "hierarchical models for cell systems"; [14]
Ehresmann–Vanbremersch, "Hierarchical Evolutive Systems") and generic phrases ("next level of
understanding of cognition", p.11). The nearest in-body analogue (p.2) is Ehresmann–Vanbremersch's
time-indexed category Cₜ, where "a category evolving with time can then allow evolving structures,
the structures being given as colimits in the category Cₜ at time t" — an evolving, not levelled,
picture.

### Higher dimensional algebra (p.6–11)

> "The aim here is to explain some mathematical ideas with which the authors have been preoccupied
> since the 1960s and 1970s respectively." (p.6) "A basic idea is that we may need to get away from
> 'linear' thinking in order to express intuitions clearly." (p.6)

Eq. (3), p.6: `2 × (5 + 3) = 2 × 5 + 2 × 3`, "more clearly shown by the figure" (4), p.7 — two rows
of tally marks (`|||||` and `|||`) stacked twice, illustrating distributivity pictorially; the
general law `a × (b + c) = a × b + a × c` is a further picture-vs-formula exercise (p.7).

A line subdivided by dots into segments a, b, c, d translates to the word `abcd` (p.7):

> "It is useful to express this intuition as 'composition is an algebraic inverse to subdivision'.
> The labelled subdivided line gives the composite word, abcd." (p.7)

A 2-D grid of dots joined by horizontal and vertical arrows, its enclosed squares "supposed filled
and labelled" (p.7), motivates:

> "It seems that in doubling the number of dimensions from 1 to 2, you need to move from categories
> to double categories, or something similar, based on directed squares rather than on arrows."
> (p.7) "The extra richness involved is that a square can have more complicated relations to other
> squares than can happen in the linear situation." (p.7)

A commutative square (top edge a, left edge c, right edge b, bottom edge d) gives eq. (5), p.8:
`ab = cd,  or  a = cdb⁻¹`.

**Double category (p.8).** Squares compose vertically (`x ◦₁ z`) and horizontally (`x ◦₂ y`):

> "So we get a notion of a double category, whose elements are squares, for which ... the
> composition x ◦1 z is defined if and only if the bottom edge of x is the same as the top edge of
> z, and similarly (but right and left edges) for x ◦2 y. Thus the compositions are partially
> defined, under geometric conditions. ... On these compositions, we have to impose all the obvious
> geometric rules." (p.8)

**"Interchange" and "double groupoid" never occur in this paper** — only "double category" (p.8)
and "double category with connections" (p.10). "The obvious geometric rules" is their own name for
the standard interchange law; its usual form in their ◦₁/◦₂ notation, `(a ◦₂ b) ◦₁ (c ◦₂ d) =
(a ◦₁ c) ◦₂ (b ◦₁ d)`, is supplied here, not written out by Brown–Porter.

**Cube problem (p.8–9).** "The surprising thing is that to determine a commutative cube needs some
new ideas" (p.8): "A cube has six faces, which can divide into two groups of three" (p.8), and one
would like the two composites of ∂-faces, eq. (6) p.9 (two rows of boundary symbols `∂²₀ ∂³₁ | ∂¹₀`
and `∂¹₁ | ∂³₀ ∂²₁`, arranged as a would-be rectangular array) to agree, but:

> "Unfortunately, this does not make sense because the little squares do not form a rectangular
> array, and also because the edges of each block are not correct to give equality." (p.9)

Filling the corners gives the expanded equality (7), p.9 (same ∂-symbols, extra corner cells).
"In dimension 1, you are limited to staying still, moving forward, or moving backward. In dimension
2, you can also turn left or right. This is what needs to be modelled formally." (p.9)

**Thin squares and connections (p.9–10).** Three "forms of horizontal and vertical identities" —
squares filled with 1's and one edge a — plus two connections, squares split by a diagonal into
triangles labelled a and 1: `Γa`, `Γ′a` ("turning left or right", p.9). Rules (i)–(iv), p.10, e.g.
`[Γ′a Γa] = ε1a`, `(iv) [Γa ε1b; ε2b Γb] = Γ(ab)`. **"Cubical"/"globular" never occur in the body**
— only in bibliography title [2] (Al-Agl–Brown–Steiner, "the equivalence between a globular and
cubical approach"); the paper builds entirely on the cubical (squares/cubes) side without naming
or arguing that comparison itself.

A worked calculation (p.10–11) rewrites a labelled a,b,c,d figure via the connection rules into two
equal simplified diagrams: "2-dimensional rewriting looks like a new kind of manipulation" (p.10);
"rewriting has been carried out in three dimensions ... is not easy to handle" (p.11).

---

## 2. Leinster, "Topology and Higher-Dimensional Category Theory: the Rough Idea" (arXiv math/0106240)

### n-category sketch (p.4–5)

> "'Definition' Let n ≥ 0. An n-category consists of • 0-cells or objects, A, B, . . . • 1-cells or
> morphisms, drawn as A →f B • 2-cells A ⇒α B ('morphisms between morphisms') ... • 3-cells [drawn
> with Γ perpendicular to the page] • ... • all the way up to n-cells • various kinds of
> composition ... and so on in higher dimensions (which I won't attempt to draw); and similarly
> identities. These compositions are required to 'all fit together nicely'—a phrase hiding many
> subtleties." (p.4–5)

Named compositions: ordinary `g∘f : A → C`; vertical `β∘α` of 2-cells sharing a 1-cell; horizontal
`α′ ∗ α` of 2-cells along a shared object ("the ∗ notation is traditional but not particularly
well-chosen", p.5). "∞-categories (also known as ω-categories) are defined similarly, by going on
up the dimensions forever instead of stopping at n." (p.5) A cubical alternative is flagged and set
aside: a square 2-cell `•→• ⇓ •→•` — "something other than an n-category." (p.5)

**Weak vs strict:** "composition in Π∞(X) isn't genuinely associative; nor is it unital, and nor
are the cells genuinely invertible (only up to homotopy). We're therefore interested in weak
n-categories ... rather than strict n-categories, where associativity etc. hold in the strict
sense." (p.6) "The difference between the weak and strict theories is genuine and nontrivial: ...
every weak 2-category is equivalent to some strict one, ... [but] neither of these things is true
in dimensions ≥ 3. ... there exist spaces X such that the weak 3-category Π3(X) is not equivalent
to any strict 3-category." (p.7) "From now on, 'n-category' will mean 'weak n-category'." (p.7)

### The fundamental n-groupoid Πₙ(X) (p.6)

> "Any topological space X gives rise to an ∞-category Π∞(X) (its fundamental ∞-groupoid), in
> which • 0-cells are points of X ... • 1-cells are paths in X (parametrized, i.e. maps [0,1] → X)
> ... • 2-cells are homotopies of paths (relative to endpoints) ... • 3-cells are homotopies of
> homotopies of paths (i.e. suitable maps [0,1]³ → X) • ... • composition is by pasting paths and
> homotopies." (p.6) "You can also truncate after n steps to obtain Πn(X), the fundamental
> n-groupoid of X: e.g. Π1(X) is the familiar fundamental groupoid." (p.6) "(The word 'groupoid'
> means that all cells of dimension > 0 are invertible.)" (p.6)

### ∞-category examples (p.6–9)

**Top** (p.7): 0-cells topological spaces; 1-cells continuous maps; 2-cells `X ⇒ Y` = homotopies
between f, g; 3-cells homotopies between homotopies, "suitable maps `[0,1]² × X → Y`"; composition
"as expected."

**ChCx** (p.7): 0-cells chain complexes; 1-cells chain maps; 2-cells chain homotopies; 3-cells
`A ⇒ B` = homotopies between homotopies, "maps Γ : A → B of degree 2 such that `dΓ − Γd = β − α`";
composing two chain homotopies admits "two equally reasonable ways of doing it: one 'left-handed',
one 'right-handed'" (p.7), so "weakness of the resulting ∞-category is inevitable" (p.8). "In a
reasonable world there ought to be some kind of map Chains : Top → ChCx." (p.8)

**Bord** (p.8–9), an ∞-category of (co?)bordisms — described in full below.

### Bord in full detail (p.8–9)

**0-cells:** 0-manifolds ("compact, smooth, oriented"); "A typical 0-cell is • • • •" (four points,
p.8). **1-cells:** "1-manifolds with corners, i.e. cobordisms between 0-manifolds" — the pictured
example is captioned "a 1-cell from the 4-point 0-manifold to the 2-point 0-manifold" (p.8). In
Atiyah–Segal-style TQFT one would "stop here and take isomorphism classes of the 1-cells ... to
make a category. We avoid this (unnatural?) quotienting out and carry on up the dimensions." (p.8)
**2-cells:** "2-manifolds with corners" — two alternative pictures joined by "or" (p.8),
described in detail below. "Here N is a 2-cell L ⇒ L′, where L = L′ = • •, M = [cup over cap], M′ =
[two vertical strokes]." (p.8) "I've left the orientations off the pictures, but N is meant to be
oriented so as to agree with the orientations of M and M′." (p.9) "Khovanov ... discusses TQFTs
with corners in the language of 2-categories; he'd stop here and take isomorphism classes ... to
make a 2-category. Again, we do not quotient out but keep going up the dimensions." (p.9)
**3-cells, 4-cells, ...:** "defined similarly" (p.9). **Composition:** "gluing of manifolds" (p.9).
(A closing aside proposes n-vector spaces for "extended TQFTs": "A 0-vector space is a complex
number; a 1-vector space is an ordinary vector space," p.9.)

### Page-8 figures as components

**Figure A — the 1-cell cobordism picture (p.8).** Four disjoint pen-strokes in a loose horizontal
cluster, no ruled boundary line (unlike the 2-cell figures, no dotted slab here): (i) a cup-shaped
arc (∪), both endpoints dotted, curving up-and-over, arrowhead on its right branch pointing
up-right; (ii) a smaller hook-shaped arc curling back on itself, two close endpoint dots, its own
arrowhead; (iii) one fully closed loop (a small circle), no endpoint dots, its own arrowhead — the
free component; (iv) a short diagonal arc, dot to dot, arrowhead up-right. Leinster's caption reads
the whole assembly as one 1-cell "from the 4-point 0-manifold to the 2-point 0-manifold": the six
endpoint dots on arcs (i, ii, iv) realise that 4+2 boundary (four source, two target), while loop
(iii) is an extra component disjoint from the boundary.

**Figure B — the "trousers"/pair-of-pants 2-cell (p.8, left-hand alternative).** *Slab:* two
parallel parallelogram planes, dotted outlines in oblique perspective, one lower, one upper.
*Bottom boundary:* one closed loop (circle) on the lower plane, dashed arc marking its hidden rear
half. *Top boundary:* two closed loops side by side on the upper plane. *Corners:* none — every
boundary curve is smooth; the cornerless alternative. *Orientation:* not drawn ("I've left the
orientations off the pictures," p.9). *Cell notation:* unlabelled; offered as the "or" alternative
to Figure C.

**Figure C — the surface N with corners (p.8, right-hand, the one named in the text).** *Slab:* the
same two dotted planes, with a dashed vertical segment and dashed hidden portions of the lower
plane, plus a small label-and-arrow "N" pointing at the surface. *Top boundary curve, M:* a
cup-over-cap pair of arcs (⌣ above ⌢), labelled M, meeting the top plane at 2 corner points.
*Bottom boundary curve, M′:* two straight parallel vertical strokes ( | | ), labelled M′, meeting
the bottom plane at 2 corner points. *Corners:* 4 total (2 top, 2 bottom) where the wavy sheet
meets the two straight vertical edges — the "manifold with corners" case, contrasted with Figure
B's smooth one. *Orientation:* left off the drawing; stated in prose to agree between M, N, M′.
*Cell notation:* "N is a 2-cell L ⇒ L′" as the standard lens/eye diagram — apex points L (left),
L′ (right), upper arc M, lower arc M′, double arrow inside labelled N, i.e. N : M ⇒ M′, with
L = L′ = • •.

### Degenerate n-categories / the periodic table (Section 3, p.9–13)

Degeneracies, each with its governing equation: one-object category = monoid, `morphism in C =
element of M`, `◦ in C = · in M` (p.9); one-0-cell 2-category = monoidal category, `1-cell in C =
object of M`, `2-cell in C = morphism of M`, `composition •→•→• in C = ⊗ of objects in M`,
horizontal 2-cell composition `= ◦ of morphisms in M` (p.10); one-object monoidal category =
commutative monoid by the Eckmann–Hilton argument (p.10), corollary "π2(X, x0) is abelian" (p.10);
one-0-cell-one-1-cell 3-category = braided monoidal category — a monoidal category with a braiding
`A⊗B →β A,B B⊗A` for each A, B, axioms **not including** `(A⊗B →β A,B B⊗A →β B,A A⊗B) = 1` (p.10–11),
canonical example **Braid** (objects the naturals; morphisms braids up to deformation, none m→n for
m≠n; tensor by placing side by side; braiding "left over right" — "Notice how βn,m ◦ βm,n is not
the identity braid", p.11); and for r ≥ 4, an r-category with only one i-cell for each i < r−1 is
(conjecturally) a symmetric monoidal category, `βB,A ◦ βA,B = 1` for all A, B — "the situation's
stabilized" (p.11).

**Definition:** "a k-monoidal n-category [is] a (k + n)-category with only one i-cell for each
i < k." (p.11) Periodic table (p.12), columns n = 0..3, rows k = 0..6 ("," = same as cell above;
X = unnamed):

| k\n | 0 | 1 | 2 | 3 |
|---|---|---|---|---|
| 0 | set | category | 2-category | 3-category |
| 1 | monoid | monoidal category | monoidal 2-category | monoidal 3-category |
| 2 | commutative monoid | braided mon cat | braided mon 2-cat | braided mon 3-cat |
| 3 | ,, | symmetric mon cat | X | X |
| 4 | ,, | ,, | symmetric mon 2-cat | X |
| 5 | ,, | ,, | ,, | symmetric mon 3-cat |
| 6 | ,, | ,, | ,, | ,, |

A legend arrow (↙, p.11) reads "take just one-object things" (the direction of increasing k). "The
X's could be replaced by more terminology, e.g. the first is sometimes called 'sylleptic monoidal
2-category', but it doesn't matter what that means." (p.12)

**Stabilisation hypothesis:** "The main point is that the table stabilizes for k ≥ n + 2 — just
like πk+n(Sᵏ). So if you overlaid a table of the homotopy groups of spheres onto the table above
then they'd stabilize at the same points." (p.13) "Roughly, the fact that the prototypical braided
monoidal category Braid is not symmetric comes down to the fact that you can't usually translate
two 1-dimensional affine subspaces of 3-dimensional space past each other; and this is the same
kind of dimensional calculation as ... proving that the homotopy groups of spheres stabilize."
(p.13)

---

## 3. MathWorld, "Hypergraph" (and linked pages)

> "A hypergraph is an ordered pair H=(V,E) consisting of a set V of vertices and a family E of
> subsets of V called hyperedges."

**Hyperedge** (own page): "A hyperedge is a member of the family of vertex subsets that defines a
hypergraph. Its size is its cardinality. A hyperedge consisting of two distinct vertices is an
ordinary graph edge, while a hyperedge may in general contain any number of vertices allowed by
the convention being used."

**k-uniform:** "A hypergraph is k-uniform if every hyperedge has size k"; "An ordinary simple graph
is a 2-uniform hypergraph." **Degree:** "The degree of a vertex v is the number of hyperedges
containing v."

**Incidence matrix:** `M_ij = 1 if v_i ∈ e_j; 0 otherwise` — the bipartite graph's incidence matrix,
vertices in one part and hyperedges in the other.

**Vertex–vertex adjacency matrix and information loss:** `A = MM^T − diag(MM^T)`; "Such a matrix
representation generally loses information about which collections of more than two vertices
belong to the same hyperedge."

**Levi graph / incidence graph** (own MathWorld page, titled "Levi Graph"): "The Levi graph
L(P,B), also called the incidence graph, of a configuration (P,B) with v points P={p1,...,pv} and b
lines ('blocks') B=(B1,...,Bb) is a bipartite graph with 'black' vertices P, 'white' vertices B, and
an edge between pi∈P and Bj∈B iff pi∈Bj" (Coxeter 1950; Pisanski and Randić 2000). For symmetric
n_k configurations the Levi graph is k-regular bipartite on 2n vertices, nk edges; dual
configurations share the same Levi graph with vertex classes interchanged. The separate "Incidence
Graph" MathWorld page is a stub (header and "See also → Levi Graph" only, no independent
definition).

**Bipartite graph** (own page; no mention of hypergraphs/Levi graphs): "A bipartite graph, also
called a bigraph, is a set of graph vertices decomposed into two disjoint sets such that no two
graph vertices within the same set are adjacent."

**Graph-case incidence matrix** (MathWorld "Incidence Matrix" page): "The incidence matrix of a
graph gives the (0,1)-matrix which has a row for each vertex and column for each edge, and
(v,e)=1 iff vertex v is incident upon edge e" (Skiena 1990, p.135); line-graph identity
`L = CᵀC − 2I`.

**References.** Hypergraph: Berge, *Graphs and Hypergraphs* (Elsevier, 1973); Berge, *Hypergraphs:
The Theory of Finite Sets* (North-Holland, 1989). Incidence Matrix: Kirchhoff, *Ann. Phys. Chem.*
72, 497–508 (1847); Skiena, *Implementing Discrete Mathematics* (1990) pp.135–136; Bruck & Ryser,
*Canad. J. Math.* 1, 88–93 (1949). Levi Graph: Coxeter, "Self-Dual Configurations and Regular
Graphs," *Bull. Amer. Math. Soc.* 56, 413–455 (1950); Pisanski & Randić, "Bridges between Geometry
and Graph Theory," in *Geometry at Work* (MAA, 2000) pp.174–194. Bipartite Graph: Chartrand,
*Introductory Graph Theory* (Dover, 1985); Read & Wilson, *An Atlas of Graphs* (OUP, 1998); Saaty &
Kainen, *The Four-Color Problem* (Dover, 1986); Skiena §5.5.2 (1990); Sloane OEIS A033995;
Steinbach, *Field Guide to Simple Graphs* (1990).

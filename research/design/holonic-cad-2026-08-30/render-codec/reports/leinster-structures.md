# Structures in Leinster, "Structures in higher-dimensional category theory" (math/0109021)

Source: pdftotext -layout dump of the 81-page arXiv v1 (Sep 2001, text written 1998). Page
numbers below are the paper's own running page numbers, recovered from the plain-number footer
lines in the extraction and cross-checked against section boundaries (Contents page 2 shows
Chapter I p.11, II p.29, III p.48, IV p.64, Bibliography p.75). Notation from the source uses
Paul Taylor diagrams (ASCII-rendered arrows); I transcribe prose/equations verbatim in Unicode
and describe (not reproduce) the ASCII pasting-diagram art.

## 1. Definitions of shapes of cells

**Globular set** (p.15, Example I.1.3(h)). Given as an instance of the general (S,✻)-multicategory
machinery, not a standalone chapter:
> "A globular set is a diagram ··· Xn+1 ⇉ Xn ⇉ ··· ⇉ X1 ⇉ X0 (with s,t maps at each stage) in Set
> satisfying the 'globularity equations' ss = st and ts = tt : Xn+1 → Xn−1."
It is noted that "the underlying graph of a strict ω-category is a globular set: Xn is the set of
n-cells, and s and t are the source and target functions," and that globular sets form a presheaf
category [Gᵒᵖ, Set] (p.15), hence cartesian.

**Strict ω-category / free strict ω-category monad** (p.34–35, II.2 Formal Outline). "The category
S is that of globular sets... The monad ✻ is the free strict ω-category monad. In outline, a strict
ω-category consists of a globular set X and for each n ≥ k a binary composition function
X(n) ×_{X(k)} X(n) → X(n) and an identity function X(k) → X(n), satisfying the appropriate
source-target relations, and such that the compositions and identities obey strictly all the
possible associative, identity and interchange laws" (p.34).

**Trees / n-globs, and the free monad construction** (II.3, p.35–41). An *n-glob* is a globular
diagram representing an element of 1✻(n); a *tree* is the alternative combinatorial presentation
Batanin uses. Formally (p.38–39): "we may define an n-stage tree (n∈N) to be a diagram
τ(n) → τ(n−1) → ··· → τ(1) → τ(0) = 1 in the category ∆ of all finite ordinals." The
source/target ∂τ truncates the top stage. The free strict ω-category monad is then built from: a
tree (a diagram in ∆), a globular set τ̂ attached to each tree, X^τ = maps(τ̂, X), and
X✻(n) = ⨆_{τ∈Tr(n)} X^τ (p.42).

**Cubical set / n-cubical set** (II.6, p.44–45). "Let Cube_n be the category with objects: subsets
D of {0,1,...,n−1}; maps D → D′: the inclusion D⊆D′, together with a function D′\D → {0,1} (in
which context 0 should be read as 'source' and 1 as 'target'); composition: place functions
side-by-side" (p.44–45). Then: "we define an n-cubical set to be a functor Cube_n^op → Set"
(p.45). A 2-cubical set is unpacked as X∅ = 0-cells, X{0} = horizontal 1-cells, X{1} = vertical
1-cells, X{0,1} = 2-cells (p.45), matching the classical double-category graph. No cubical
*connections* are defined; the survey explicitly stops short: "The final step of the analogy would
be to develop an appropriate notion of contraction in the cubical setting... This has not, as far
as I know, been carried out" (p.47).

**Simplicial set / simplicial category — not independently defined.** The survey never states
simplicial-set axioms. It uses ∆ (finite ordinals) as (a) the shape category recovering categories
as functors ∆ᵒᵖ→Set: "A category is a finite-limit-preserving functor ∆ᵒᵖ ✲ Set" (p.29, echoing
p.4's remark that Tamsamani's definition "generalizes the correspondence between a category and
its nerve ∆ᵒᵖ ✲ Set"), and (b) as a derived object: "the free (Set/S1, T1)-structured category on
1 is the simplicial category ∆" (p.69), obtained by pasting the terminal plain multicategory. No
simplicial identities are transcribed anywhere in the text.

**Opetope** (IV.1, p.64–67). Informal definition: "In a nutshell, there is one 0-opetope and an
(n+1)-opetope is a pasting of n-opetopes" (p.64). "The unique 0-opetope (with 'ope' pronounced as
in 'operation') is drawn as •. The only pasting-together of •'s ('0-pasting diagram') is • itself,
so there's just one 1-opetope... k copies of • → • can be pasted together end-to-end for any k∈N...
The set of 2-opetopes is therefore isomorphic to N" (p.64). "A 3-opetope is formally just a
2-pasting diagram" (p.65) — i.e. opetopes are defined by mutual induction with pasting diagrams.
Formally (IV.1, p.65–66): S₀ = 1, T₀ = id on Set/S₀; inductively (S_{n+1} → S_n) = T_n(S_n →_1
S_n), and T_{n+1} := the free (Set/S_n,T_n)-operad monad on Set/S_{n+1}. "Start with S0 = 1 and
T0 = id, the identity monad on Set≅Set/S0" (p.65). S₁=1 (the 1-opetope), S₂=ℕ (2-opetopes), and
generally Sₙ₊₁ is the underlying set of the free (Set/Sₙ,Tₙ)-operad monad's output.

**Pasting diagram** (IV.2, Definition IV.2.1, p.70). "The structured category of n-pasting
diagrams, PDₙ, is the free (Set/Sₙ, Tₙ)-structured category on the terminal (Set/Sₙ, Tₙ)-
multicategory." Its image under the forgetful functor to Set is the *category of n-pasting
diagrams* pdₙ, whose "object-set... is S_{n+1}, the set of (n+1)-opetopes or, as we prefer to
think of them at the moment, n-pasting diagrams" (p.70); morphisms remove interior
(n−1)-dimensional faces. pd₀ = 1, pd₁ = ∆, and pd₂ is identified with the *category of trees*
(IV.3, p.71): "We may define a tree to be a 2-pasting diagram: that is, a member of S3" (p.71).

**Bicategory and its coherence data** (Preliminaries, p.6–10). Data given informally by naming
its cells and composites rather than by full axiom list: 0-cells A,B,...; 1-cells f,g,...;
2-cells α,β,...; vertical composite β∘α (or βα); horizontal composite α′∗α (p.6). A monad in a
bicategory (used later to define multicategories) is spelled out fully with two commuting diagrams
(unit/associativity) — see §3 below. **The pentagon and triangle coherence diagrams for a
bicategory's associator/unitors are never displayed or named in this text** — the words
"pentagon," "triangle," "associator," and "unitor" do not occur anywhere in the source. The
preliminary chapter states its "basic definitions are taken from [Bén] and [Gray]" (p.5) and
proceeds directly to composite/duality/coherence-theorem statements without restating the
classical axioms. The one displayed axiom system in this area is the **unbiased category/
bicategory** (Bias, p.9–10): for a sequence of composition functions c_A indexed by object
sequences, "if s,t: C(An−1,An)×···×C(A0,A1) → C(A0,An) are two 1-terms, then s = t" (p.9–10) —
i.e. coherence is stated as "all derived composites of a given source/target are equal," not as a
finite pentagon/triangle pair.

**Tricategory** (III.4, p.56, biased, following [GPS]/[Bén]). "A tricategory T consists of a
collection T0 of objects, a bicategory T(A,B) for each pair (A,B) of objects, composition and
identity homomorphisms T(B,C)×T(A,B) → T(A,C) and 1 → T(A,A), and then various coherence cells
satisfying some axioms" (p.56); explicit axioms are not transcribed (deferred to [GPS]).

**Gray-category** (III.2, Definition-style, p.53). "Gray-categories are defined to be algebras
for the 3-operad Gy. This in turn is defined to be the 3-operad got by taking the 2-operad Ssq
[the sesquicategory operad] and contracting from dimension 2 to dimension 3": Gy(τ) = Ssq(τ) for
n∈{0,1,2}, and Gy(τ) = Ssq(∂τ)×Ssq(∂τ) for n=3 (p.53). Turning a Gray-category into a tricategory
requires a *non-canonical* choice of horizontal composite of 2-cells: "define the horizontal
composite β∗α of [α:f⇒f′ over A→B, β:g⇒g′ over B→C] as βf′∘gα" (p.56).

**Sesquicategory** (III.1, p.49–51). "A sesquicategory consists of a category C and a
factorization Cᵒᵖ×C ⇢ Cat, Hom: ↓ ob → Set" (p.49): for each A,B∈C₀ a category C(A,B) whose
objects are morphisms A→B; morphisms of C = 0-cells, morphisms of C = 1-cells, morphisms inside
C(A,B) = 2-cells. Equivalently presented as a truncated globular set C2⇉C1⇉C0 with 1-cell
composition/identity, vertical 2-cell composition/identity, and two "whiskering" composites
f▷α, α◁f — but *no* specified horizontal composite of 2-cells (p.49–50); this is exactly what a
2-category adds.

**Multicategory / (S,✻)-multicategory** (Chapter I, general definition via free monads). Plain
multicategory (p.11): "collection C₀ of objects, and arrows like s1,...,sn →ᵃ s..., together with
composition functions and identity elements obeying associativity and unit laws." General
construction: for (S,✻) cartesian, build the Kleisli bicategory of spans B (Construction I.2.1,
p.16–17: 0-cells = objects of S; 1-cells R→S = spans R✻←A→S; composition via chosen pullbacks).
Then **Definition I.2.2** (p.17): "an (S,✻)-multicategory is a monad in the associated bicategory
B of Construction I.2.1." Concretely it "consists of a diagram C₀✻ ←ᵈ C1 →ᶜ C0 in S and maps
C₀→C₁ (ids), C1∘C1→C1 (comp) satisfying associative and identity laws" (p.17). This is exactly the
concept later called a *generalized multicategory* or *T-multicategory* in the literature — the
survey's own name for it throughout is "(S,✻)-multicategory"; the word "T-multicategory" itself
does not occur in this text. C₀=1 gives an "(S,✻)-operad" (p.17). Examples instantiate this single
definition as: plain categories ((Set,id), p.19), plain multicategories/operads
((Set,free-monoid), p.19–20), discrete opfibrations ((Set,−+1), p.20), Soibelman-style
tree-labelled structures ((Set,tree monad), p.20–21), and — the one used for weak ω-categories —
Batanin operads ((Globular sets, free strict ω-category), p.21, I.2.5(f)).

**fc-multicategory — not present.** No "fc-multicategory" (the "functor-cospan" multicategory of
later Leinster/Cheng/Cruttwell–Shulman work) occurs anywhere in this 1998 text; the closest
concept offered is the general (S,✻)-multicategory above, which specializes (via
(S,✻)=(Cat,free-strict-monoidal-category), p.21 I.2.5(e)) to "Cat-enriched" multi-object
structures but the survey never names or isolates an fc-multicategory as such.

**Operad.** Plain operad (p.11): "a sequence C(0),C(1),... of sets together with an 'identity'
element of C(1) and 'composition' functions C(n1)×···×C(nk)×C(k) → C(n1+···+nk), obeying
associativity and identity laws." General: "an (S,✻)-multicategory on C₀, or if C₀=1 an
(S,✻)-operad" (p.17). "For us, an operad is a multicategory with just one object" (p.5).

**Weak/lax n-category — three approaches presented:**

1. *Leinster's variant of Batanin's operadic definition* (II.5, p.43–44, the survey's main
   result). A **contraction** on a collection C→Tr, **Definition II.5.1** (p.44): "A contraction
   ψ on C is a function assigning to each τ∈Tr(n) and matching pair (f,f′) for ∂τ, an element
   ψ(f,f′)∈C(τ) such that s(ψ(f,f′)) = f and t(ψ(f,f′)) = f′." K is defined as the *initial*
   operad-with-contraction. **Definition II.5.2** (p.44): "A lax ω-category is an algebra for K.
   A lax n-category is a lax ω-category whose underlying globular set is n-dimensional." (The
   preface, p.2, notes the author would now say "weak" rather than "lax.")
2. *Tamsamani(-Simpson)* — mentioned, not defined in detail (p.4, p.29): "Zouhair Tamsamani has
   made a definition which generalizes the correspondence between a category and its nerve
   ∆ᵒᵖ ✲ Set" (p.4); "In [Tam], a lax n-category is a functor (∆n)ᵒᵖ ✲ Set satisfying three
   axioms" — truncatability, a finite-limit-preserving generalization, and a degeneracy condition
   — but "the present author's ignorance prevents further discussion" (p.29). No formal statement.
3. *Baez–Dolan/opetopic (Hermida–Makkai–Power)* — the survey deliberately builds only the
   supporting apparatus (opetopes Sₙ, monads Tₙ, pasting-diagram categories pdₙ, the slicing
   construction, IV.4) and explicitly declines to state the resulting n-category definition:
   "There is no attempt to describe the opetopic approach as a whole; the theory of Chapter I
   seems less well suited to this style than to Batanin's" (p.4). No Penon definition and no
   independent Street definition appear; Street is cited only as having "produced an account of
   Batanin's work" ([St3], p.30).

## 2. Notation and diagrammatic conventions

- 0-cells: capital letters A,B,C,... drawn as bare dots • in pictures; 1-cells: lower-case
  f,g,h,... drawn as straight arrows →; 2-cells: Greek α,β,γ,... drawn as double-shafted arrows
  ⇒ (Paul-Taylor-style, rendered in the ASCII dump as curved "❘ ❄ ✒"-glyphs) between two parallel
  1-cells; identity 1-cells/2-cells are undecorated. (p.6, "Basic terminology.")
- Vertical composition of 2-cells is written β∘α or βα; horizontal composition α′∗α (p.6).
- Whiskering (1-cell composed with a 2-cell on either side) is written αf and fα (p.50, Fig III.a).
- 3-cells are drawn as ⇛-style triple arrows between parallel 2-cells, e.g. "δ ⇛ δ′" (p.32, diagram
  in the contraction-principle discussion); the survey has no separate symbol name for this arrow
  beyond the picture itself.
- Trees are drawn with leaves at the bottom and root at top (or vice versa depending on the
  figure), nodes as •, and are used interchangeably with n-globs to index composition shapes
  (p.35–42); "the collections of m-globs and of n-globs are considered disjoint, when m ≠ n" (p.35).
- Cuboids (cubical composites) are drawn as literal boxes with a small "compass" glyph fixing which
  axis is which coordinate (p.45–46).
- Opetopes are drawn with input edges at top, output edge at bottom: "one can think of the top
  edges of a 2-opetope as being inputs and the bottom edge as an output; in forming a pasting
  diagram the rule is that input edges paste to output edges" (p.64).
- Source/target reading convention, uniform across shapes: for a k-stage tree/glob/opetope τ, its
  source and target ∂τ are BOTH obtained the same way — by "truncating" or "removing all the nodes
  at height n" (p.38 for trees) — i.e. source and target of a top-dimensional cell are read off the
  same combinatorial boundary operation, disambiguated only by the labelling data attached (this is
  explicit for trees, p.38, and echoed for cuboids, p.46, and opetopes, p.65).
- Dual bicategory: reverse 1-cells, keep 2-cells: "we may form a dual bicategory Bᵒᵖ by reversing
  the 1-cells but not the 2-cells" (p.7).
- No string-diagram convention is used anywhere in the text; all composition is drawn with the
  globular/pasting-diagram/cuboid picture language above, plus ordinary commutative-square diagrams
  for monad/functor axioms.

## 3. Displayed equations / axioms (plain Unicode)

- **Globularity relations** (p.15): ss = st and ts = tt : X_{n+1} → X_{n−1}.
- **Cartesian monad conditions**, Definition I.1.2 (p.12): (a) η and µ are cartesian natural
  transformations — the naturality squares for η and µ are pullbacks; (b) (−)✻ preserves
  pullbacks. A category is *cartesian* iff it has all finite limits (Def I.1.1, p.12).
- **Strongly regular equation** (p.13): example given, (x.y).z = x.(y.z) and (x↑y)↑z = x↑(y.z),
  contrasted with non-strongly-regular x+(y+(−y)) = x, x.y = y.x, (x.x).y = x.(x.y).
- **Monad-in-a-bicategory axioms** (p.7–8, used to define multicategories in general): the unit
  and associativity diagrams for t: A→A, η: 1⇒t, µ: t∘t⇒t — "t∘1 ≅ t∘t ← 1∘t (via tη, ηt), and
  t∘(t∘t) ≅ (t∘t)∘t → t∘t → t (via tµ, µt, µ) commute."
- **Unbiased-category coherence axiom** (p.9–10): for two derived 1-terms s,t built from the
  composition functions c_A by (nullary/binary) products and composition, "s = t" — i.e. *any* two
  parallel composites of the c_A's are declared equal (this is the survey's substitute for the
  classical finite pentagon/triangle axioms).
- **Free-multicategory recursion** (p.28): A(0) = G1, A(n+1) = G0 + G1∘A(n) (colimit gives the free
  multicategory); specialized to (Set,id), G0=1: A(n+1) = 1 + G∘A(n), "the free monoid on a set."
- **Strict ω-category laws** (p.34): compositions/identities "obey strictly all the possible
  associative, identity and interchange laws" (not spelled out equation-by-equation).
- **Interchange law**, named explicitly (p.33): two ways of composing a square of 2-cells built
  from "do-nothing" on 0-cells and ordinary composition on 1-cells give "two different ways of
  composing [the same square]... familiar from the interchange law."
- **Associativity example for tree/opetope composition** (p.42): f∘(f1∘(f11,f12,f13), f2) =
  (f∘(f1,f2))∘(f11,f12,f13,1).
- **Cubical set functor axiom** (p.45): X is an n-cubical set iff X = functor Cube_n^op → Set;
  Cube_n composition is "place functions side-by-side."
- **Discrete-opfibration pullback condition** for algebras (p.22): the square
  D₀✻←D1 over C₀✻←C1 (via f₀✻,f1) must be a pullback.
- **Contraction axiom**, Definition II.5.1 (p.44): s(ψ(f,f′)) = f and t(ψ(f,f′)) = f′.
- **n-dimensional globular set condition** (p.44): X is n-dimensional iff for all m≥n, s = t :
  X(m+1) → X(m) and this map is an isomorphism.
- **Gray-category "top-dimension" principle**, illustrated not axiomatized directly (p.53): the two
  horizontal-composite candidates γ1 = βf′∘gα and γ2 = g′α∘βf for a square of 2-cells differ by "a
  (canonical) invertible 3-cell," not by equality.
- **No pentagon or triangle equation is transcribed anywhere in the source** (confirmed by full-text
  search: the strings "pentagon," "triangle," "associator," "unitor" do not appear).

## 4. Example structures given as data

- **1✻, the free strict ω-category on the terminal globular set 1**: fully worked as the running
  example of II.3 (p.35–42) — its typical 2-glob is drawn (p.35, diagram II.C), its binary/nullary
  compositions are drawn (p.36, "typical binary compositions"), and its tree presentation is
  derived (p.37–41).
- **The terminal multicategory / operad "1"** (p.26): "one object and, for each n∈N, one arrow" —
  shown to generate ∆ (finite ordinals, with + as tensor) as its free monoidal category (p.26,
  diagram I.B).
- **The 2-operad Ssq for sesquicategories** (p.52): explicitly presented by generators (one
  element of Ssq(τ) for each 1-stage and 2-stage tree τ) and relations (Fig. III.a, p.51).
- **The 3-operad Gy for Gray-categories** (p.53): Gy(τ)=Ssq(τ) for n≤2, Gy(τ)=Ssq(∂τ)×Ssq(∂τ) for
  n=3 — a fully explicit small example of an n-operad built by "contracting" a lower operad.
- **2-Cat as a worked Gray-category** (III.3, p.54–55): small 2-categories, homomorphisms, strong
  transformations, modifications — all compositions enumerated pictorially.
- **The tree hhx1,x2,hii, x3, hx4,x5ii ∈ X✻** (p.14): a fully drawn concrete tree-monad element,
  used to illustrate the free-monoid-on-Set monad before generalizing to (S,✻).
- **"Periodic table" of degenerate n-categories — not present.** No table of this kind (the
  Baez–Dolan-style grid of categories/monoidal categories/braided monoidal categories/… by
  dimension and degree of degeneracy) appears anywhere in this survey; the closest statement is the
  prose remark (p.33) that "a lax n-category is a lax ω-category all of whose m-cells are
  identities when m > n," with no accompanying table.
- **Small Gray^(n)-category tower** (Definition III.7.1, p.62): Gray^(1)-category = small category;
  Gray^(2)-category = small 2-category (as a sub-bicategory of Cat); Gray^(3)-category = small
  Gray-category (as a sub-tricategory of 2-Cat) — an explicit worked table-like sequence, though
  presented as prose bullets, not a table.

## 5. Relations between shapes

- **Globular vs. cubical**: presented as two parallel instances of exactly the same
  (S,✻)-operad-with-contraction machinery — "It runs in very close parallel with our approach to
  n-categories, hence its inclusion in this chapter" (p.44). The correspondence is stated
  explicitly: cubical operads relate to cuboids exactly as Batanin operads relate to trees — "A
  Batanin operad associates to each tree a set... a cubical operad associates to each cuboid a
  set" (p.47).
- **Globular vs. simplicial**: only a passing analogy/speculation. The survey notes a possible but
  unexplored "connection here with Tamsamani's n-categories" between the globular contraction
  approach and simplicial (∆ⁿ)ᵒᵖ→Set functors, immediately followed by "the present author's
  ignorance prevents further discussion" (p.29).
- **Globular vs. opetopic**: opetopes are shown to be a strict generalization-by-dimension of the
  same operad/multicategory machinery of Chapter I, but *not* isomorphic in shape to trees/globs —
  the survey stresses "these trees differ from those of Example I.1.3(f) and Chapter IV, in both
  minor details and intent" (p.37–38); and the trees pd₂ classifies "are not the Batanin trees of
  Chapter II" (p.71).
- **Which shape is used for which purpose**: globular (Chapter II) for the main weak-∞-category
  definition; cubical (II.6) for n-tuple/double categories; opetopic (Chapter IV) purely to
  reconstruct, via free (S,✻)-multicategories, the combinatorics (opetopes, pasting diagrams,
  trees, slicing) underlying the Baez–Dolan/HMP approach, explicitly *not* to restate their
  n-category definition (p.4, p.65–66).
- **Pasting diagrams as the universal indexing device**: "the ways of composing globs are indexed
  by globs themselves" (p.36) and, identically, "an element of C(τ) can be thought of as a way of
  composing a diagram of shape τ" for cuboids (p.47) and for opetopes (IV.1, p.66–67) — the survey
  treats "shape indexes its own composition" as the organizing principle common to every one of the
  four cell-shapes it studies.
- **Trees ↔ 2-pasting diagrams ↔ opetopes**: "there is a one-to-one correspondence between
  2-pasting diagrams and trees" (Figure IV.a, p.71), and a 3-opetope "is formally just a 2-pasting
  diagram" (p.65) — so for n=2 the three notions (Batanin-style tree-index, pasting diagram,
  opetope) collapse to isomorphic sets, while for general n they remain related but distinct
  constructions built by the same free-monad recursion.

## Notes on scope/omissions

No Penon definition and no independent Street definition of weak n-category are given anywhere in
this survey (Street is cited only for an exposition of Batanin's approach, [St3]). The words
pentagon/triangle/associator/unitor never occur; classical bicategory coherence is cited to
[Bén]/[Gray] rather than restated. "fc-multicategory" and "T-multicategory" as terms do not occur;
the survey's uniform name for the generalized-multicategory concept is "(S,✻)-multicategory." No
"periodic table" of degenerate n-categories appears.

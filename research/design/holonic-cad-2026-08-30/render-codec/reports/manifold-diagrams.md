# Manifold diagrams and tame tangles (Dorn–Douglas, arXiv:2208.13758v1) — extraction

Source: plain-text pdftotext -layout of the 112-page paper. Page numbers below are the paper's
own running page numbers (footer digits in the text), not PDF page indices.

## 0. Introduction (read in full, p.1–15)

Manifold diagrams generalize Joyal–Street string diagrams to higher dimensions; they are
"geometrically dual to the more familiar representation of ... compositions by diagrams of
cells" (p.4). Tame tangles are "embedded manifolds that can likewise be interpreted
categorically" (p.4). The paper's two headline definitions, given informally in the overview
(p.5–8):

> "Definition 1. A manifold n-diagram is a framed conical tame stratification of the open
> n-cube." (p.6)

> "Definition 2. A tame m-tangle in dimension n is an m-manifold tamely embedded in the open
> n-cube which is framed transversal." (p.7)

The combinatorial counterparts of meshes are **n-trusses**: "the structured (namely,
combinatorially framed) entrance path posets of meshes" (p.6). The central classification
result is stated informally as:

> "Theorem 3 (Combinatorialization of manifold diagrams resp. tame tangles). Manifold diagrams
> up to framed stratified homeomorphism are classified by combinatorial manifold diagrams. Tame
> tangles up to framed stratified homeomorphism are classified by combinatorial tangles." (p.6–7)

Stability of tangle singularities is summarized as:

> "Theorem 5 (Stable tangle singularities in dimension ≤ 4)... 1. There is one stable 1-tangle
> singularity in dim 2 and dim 3. 2. There are three stable 2-tangle singularities in dim 3...
> 3. There are four stable 2-tangle singularities in dim 4." (p.8)

and duality of manifold/cell diagrams:

> "Observation 4 (Manifold diagrams dualize to cell diagrams). Up to framed stratified
> homeomorphism, manifold and cell diagrams are in correspondence by geometric dualization."
> (p.7)

Related-work section (p.9–10) traces manifold diagrams from Joyal–Street (2-dim, "string
diagrams"), McIntyre/Trimble (3-dim, "surface diagrams", unfinished), Bar–Vicary's 4-diagram
generators/relations, and the authors' own prior book [DD21] which introduced trusses and
meshes with sketch definitions of manifold diagrams/tame tangles that this paper completes.
Tangle theory is traced to knot-theoretic 1-tangles, Baez–Dolan's "tangle hypothesis," and
classical singularity theory (Morse, Cerf, Thom, Mather, Arnold, Wall).

## 1. Framing of ℝⁿ / framed space

The general notion ("n-framed space", Terminology 1.3.44, p.35) underlies everything drawn in
the paper:

- An **n-framed chart** (U, γ) in a space X is an embedding γ : U ↪ ℝⁿ of a subspace U ⊂ X.
- A map F : X → Y is **framed** on given charts (U, γ) ⊂ X, (V, ρ) ⊂ Y if it restricts to
  U → V such that for every i, writing π>i : ℝⁱ × ℝⁿ⁻ⁱ → ℝⁱ for the projection, there is a
  continuous partial map Fᵢ : ℝⁱ → ℝⁱ with π>i ∘ ρ ∘ F = Fᵢ ∘ π>i ∘ γ.
- Two charts are **framed compatible** if the identity is a framed map on their overlap.
- An **n-framing structure** is an atlas of framed-compatible charts covering X; a **flat**
  n-framing structure is one containing a **global** chart (X, γ).
- A map between framed spaces is **framed** if it is framed on charts locally around every point.

"Note that, given a flat n-framed space (X, A), any global n-framed chart (X, γ) ∈ A determines
(X, A) up to framed homeomorphism; we therefore often denote flat framed spaces by giving a
single global n-framed chart (X, γ)" (p.35–36). Coordinate axes of ℝⁿ are always labeled by
**categorical directions**:

> "Remark 1.3.45 (Categorical directions of ℝⁿ). We refer to the (n − k)th coordinate of ℝⁿ as
> its 'kth categorical direction'. We usually label the coordinate axes of ℝⁿ by their
> categorical directions: that is, we label the coordinate axes of ℝⁿ = (ℝ × ℝ × ... × ℝ) by
> (n, n − 1, . . . , 1). We also often use 'k-arrows' (arrows with k parallel lines) with the
> convention that k-arrows point in the kth categorical direction." (p.36)

This is the drawing convention: the last (nth) coordinate is direction 1, the first coordinate
is direction n; k-arrows (k parallel lines) drawn on strata indicate their categorical/framing
direction and later become "k-cells" in cell diagrams. Every n-mesh (and n-mesh bundle) carries
a *canonical* flat n-framing structure — "coordinatizations" — built inductively from the tower
of 1-mesh bundles (Observation 1.3.49, p.37); open n-meshes coordinatize onto the open cube
Iⁿ = (−1,1)ⁿ ⊂ ℝⁿ (Observation 1.3.51, p.37). The open n-cube Iⁿ and closed cube Iⁿ ⊂ ℝⁿ are
always regarded as flat n-framed spaces with the standard framing (Notation 2.1.1, p.44).

## 2. Meshes (n-meshes, framed regular cell complexes)

**1-mesh** (Definition 1.2.1, p.17): "A 1-mesh M is a stratified framed contractible 0- or
1-manifold, whose strata are open 0- or 1-disks." 1-meshes may be closed (compact), open (an
open interval), or mixed. A **coordinatization** γ of a 1-mesh is a framed bounded embedding
γ: M ↪ ℝ (Terminology 1.2.4, p.17), giving lower/upper bounds γ₋, γ₊.

**1-mesh bundle** (Definition 1.2.8, p.18): a stratified bundle p: M → B with a chosen 1-mesh
structure Mᵇ on each fiber, satisfying *coordinatizability* (a global bundle embedding
γ: M ↪ B×ℝ restricting to fiberwise coordinatizations, with continuous bounding sections) and
*0-constructibility* (fiber-dimension-0 strata lift entrance paths uniquely, preserving fiber
dimension).

**n-mesh** (Definition 1.3.1, p.28): "An n-mesh M is a tower of 1-mesh bundles
Mₙ → Mₙ₋₁ → ... → M₁ → M₀ = ∗." (i.e. pₙ: Mₙ→Mₙ₋₁, ..., p₁: M₁→M₀=∗). If the base is trivial one
just speaks of n-meshes. **n-mesh bundles** (Definition 1.3.6, p.29) generalize this over an
arbitrary base stratification B, ending in M₀ = B. The role of n-meshes: "the role of n-meshes
is precisely to 'cellulate' other stratifications (such as manifold diagrams)" (p.28); all
strata of the total stratification Mₙ are k-cells, k ≤ n. Open/closed n-meshes are those whose
constituent 1-mesh bundles are all open/closed (Terminology 1.3.10, p.29).

## 3. Trusses (n-trusses, combinatorial dual of meshes; bundle/tower structure)

**1-truss** (Definition 1.2.14, p.19): "A 1-truss T = (T, ≤, dim, ≺) is a poset (T, ≤) together
with a 'dimension' map dim: (T, ≤) → [1]ᵒᵖ and a 'frame order' (T, ≺), for which we can find a
1-mesh M such that there exists poset isomorphism φ: (T,≤) ≅ Entr(M), compatible with dim and
with the frame order (s ≺ t iff φ(s) ≺ φ(t))." T is called the **fundamental 1-truss** of M
(notation FTrs M), and M the **classifying 1-mesh** of T (notation CMsh T). Purely
combinatorially (Alternative Definition 1.2.17, p.20): "A 1-truss is a poset (T,≤) together with
a full and conservative functor dim: (T,≤) → [1]ᵒᵖ, and with a second order (T,≺) which is
total, and whose generating arrows t ≺ s satisfy either t<s or s<t." The **frame order** ≺
(Notation 1.2.13, p.19) is defined via coordinatizations: s ≺ t iff γ(s) < γ(t) for a
coordinatizing embedding γ: M ↪ ℝ.

**n-truss** (Definition 1.3.2, p.28): "An n-truss T is a tower of 1-truss bundles
Tₙ → Tₙ₋₁ → ... → T₁ → T₀ = ∗." This is the entrance-path-poset analogue of an n-mesh:
"fundamental n-truss FTrs M" of an n-mesh M is the tower of FTrs pᵢ (Notation 1.3.3, p.28).
**Cell dimension** in an n-truss (Remark 1.3.5, p.29): for x ∈ Tₙ write xᵢ = q>ᵢ(x); dimᵢ(x) is
the dimension of xᵢ in the ith 1-truss fiber; dim(x) := Σᵢ dimᵢ(x) is a poset map
Tₙ → [n]ᵒᵖ. **n-truss bundles** (Definition 1.3.7, p.29) are towers over an arbitrary base poset
P. The category of n-trusses and their **bordisms** Tₙ (built by n-fold application of the
functor T₁(−) to the terminal category, Definition 1.3.20/Observation 1.3.21, p.30) classifies
n-truss bundles: bundles over a poset P correspond to functors P → Tₙ.

**Entrance/exit path posets** (Recollection 1.1.2, p.13): for a prestratification (X,f), the
entrance path preorder Entr(f) has strata as objects and generating arrows s→r whenever s∩r̄≠∅
(closure of r meets s); Entr(f)ᵒᵖ is the **exit path preorder**, written Exit(f). If Entr(f) is
a poset, (X,f) is called a *stratification*.

## 4. Mesh–truss duality

**Truss dualization** (Definition 1.2.37/1.4.5, p.22 and p.38): the dual of T=(T,≤,dim,≺) is
T† = (T,≤ᵒᵖ,dimᵒᵖ,≺); this is an involution † : Tₙ ≅ (Tₙ)ᵒᵖ on n-trusses and gives an
isomorphism † : T̄rsₙ ≅ T̊rsₙ between the closed-cellular and open-cocellular subcategories.
Duality is defined for meshes by transport of structure: "meshes M and N are dual iff
FTrs(M) = FTrs(N)†" (Terminology 1.2.39, p.23).

> "Theorem 1.4.2 (Equivalence of meshes and trusses, [DD21, Thm. 4.2.1]). The functors
> FTrs : M̄eshₙ → T̄rsₙ and FTrs : M̊eshₙ → T̊rsₙ are weak equivalences of ∞-categories." (p.38)

> "Corollary 1.4.6 (Dualization of n-meshes). There is an ∞-functor † : M̄eshₙ ≃ M̊eshₙ determined
> by requiring FTrs ∘ † = † ∘ FTrs. The functor is a weak equivalence." (p.39)

Geometrically, dualization "mirrors the dualization functor C ↦ Cᵒᵖ of categories .. passes to
dual cell structures in the spirit of classical Poincaré duality" (p.22).

## 5. Framed/tame stratifications and their combinatorialization

**Tame stratification** (Definition 1.4.12, p.40): "A tame stratification (X, f, γ) is a
stratification (X, f) of a flat framed space (X, γ) that has a mesh refinement." A **mesh
refinement** M ↠ f is a framed strict coarsening of the total stratification Mₙ of a mesh M
onto f (Terminology 1.4.11, p.40). Tame stratifications were called "flat framed stratifications"
in the authors' earlier book [DD21].

> "Theorem 1.4.16 (Coarsest refining meshes). Every tame stratification f has a unique 'coarsest
> refining mesh' M ↠ f, satisfying that any other mesh refinement M′ ↠ f factors through M ↠ f
> by a unique strict n-mesh coarsening M′ → M." (p.40)

A stratified truss (T,f) is **normalized** ("in normal form") if every truss coarsening out of
it is the identity (Definition 1.4.17, p.41).

> "Theorem 1.4.24 (Combinatorialization of tame stratifications). Tame stratifications up to
> framed stratified homeomorphism are in 1-to-1 correspondence with normalized stratified
> trusses." (p.42)

The correspondence: f ↦ NFTrs f := FTrs(Mf, f), where Mf is the coarsest refining mesh
(Notation 1.4.25, p.42). This machinery ("framed tame topology and framed combinatorial topology
are locally the same thing," p.6) is the engine behind every combinatorialization theorem below.

## 6. Manifold diagrams

**Framed conical stratification** (Definition 2.1.3, p.44): given (Iⁿ, f) and x ∈ Iⁿ, f is
"(tame) framed conical at x if there is a (tame) link (∂Iⁿ⁻ᵏ, lₓ) and a (tame) framed stratified
neighborhood φ: Iᵏ × (Iⁿ⁻ᵏ, c(lₓ)) ↪ (Iⁿ, f) such that x ∈ Iᵏ × {0}", where 0 is the cone point.
"(In , f ) is (tame) framed conical if it is (tame) framed conical at all x ∈ Iⁿ." A **link** is
a stratification (∂Iⁿ, l) of the cube boundary; the open cone c(∂Iⁿ) is identified with Iⁿ
itself.

**Manifold n-diagram** (Definition 2.1.5, p.44): "A manifold n-diagram (Iⁿ, f) is a tame
stratification of the open cube that is tame framed conical." Consequence (Remark 2.1.6, p.44):
strata are k-manifolds (0≤k≤n), each locally homeomorphic to Iᵏ via restriction of the
projection Iⁿ → Iᵏ. A **compact manifold n-diagram** (Definition 2.1.12, p.46) is the same
condition on closed cube Iⁿ using "corner neighborhoods" Iσ × (Iᵏ, c(lₓ)), σ ∈ Pⁿ⁻ᵏ, P={∅,−1,+1}
(Definition 2.1.11, p.46).

**Combinatorial manifold diagram** (Definition 2.2.10, p.51): "A combinatorial manifold
n-diagram (also called a 'manifold diagram n-truss') is a normalized open stratified n-truss
(T,f) that is combinatorially conical." **Combinatorially conical** (Definition 2.2.9, p.51): at
x∈Tₙ the stratified truss neighborhood (T≤ˣ, f≤ˣ) normalizes to a product T̊ᵏ × (Cₓ,cₓ) of the
open k-cube truss and a stratified open cone (n−k)-truss.

> "Theorem 2.3.3 (Combinatorialization of manifold diagrams). Framed stratified homeomorphism
> classes of manifold n-diagrams are in 1-to-1 correspondence with combinatorial manifold
> n-diagrams: the correspondence takes (Iⁿ, f) to NFTrs(Iⁿ, f)." (p.57)

An analogous Theorem 2.3.8 (p.58–59) handles the compact case.

**Cell diagrams (the geometric dual)**: "A cell n-diagram (X, f) is a tame stratification that
is dual to a manifold n-diagram" (Definition 2.4.3, p.61); combinatorially, a **combinatorial
cell n-diagram** is a normalized closed stratified n-truss that is **combinatorially facetal**
(Definitions 2.4.9–2.4.10, p.62–63): its closure at every x normalizes to a product T̄ᵏ × facet.
"Observation 2.4.5 (Duality between manifold and cell diagrams). Framed stratified homeomorphism
classes of manifold n-diagrams and cell n-diagrams correspond bijectively by dualization"
(p.62). Cell diagrams can be read as classical point-and-arrow *pasting diagrams* by replacing
non-degenerate k-cells with k-arrows and degenerate k-cells with headless k-identity arrows
(Remark 2.4.15, p.63); "a 'k-arrow' is drawn with k parallel lines, the exception being an
identity 1-arrow, which is drawn with 2 lines as '='" (p.63) — matching the categorical-direction
convention of §1 above. This is exactly how meshes cellulate ("triangulate ... with framed
regular cells") manifold diagrams for drawing purposes (Fig. I.2, p.5).

## 7. Tame tangles and tameness

**Tame embedding** (Definition 3.1.2, p.66): an embedding f: W ↪ X of a flat framed space X is
tame if the stratification it defines (components of W and of X∖W) is a tame stratification.

**Framed transversality — the "tameness" condition on embeddings** (Definition 3.1.4, p.66),
defined inductively on transversal dimension k of points x ∈ W (m = dim W):
- x is **m-transversal** if it has a tame framed stratified neighborhood Iᵐ×(Iⁿ⁻ᵐ, ce(l)) with
  l the empty link, x ∈ Iᵐ×0.
- for k<m, assuming x is not j-transversal for j>k: x is **k-transversal** if it has a framed
  stratified neighborhood Iᵏ×(Iⁿ⁻ᵏ, ce(l)) with l = (Sᵐ⁻ᵏ⁻¹ ↪ ∂Iⁿ⁻ᵏ) a tame link, x∈Iᵏ×0, *and*
  all points off the cone stratum are jᵧ-transversal for jᵧ > k.

"We say f is a tame framed transversal stratification if all points x ∈ W are kₓ-transversal
points of W for some 0 ≤ kₓ ≤ m." A point is **regular** if k = dim(W), **singular** if k = 0
(Terminology 3.1.6, p.67).

**Tame tangle** (Definition 3.1.8, p.66): "A tame m-tangle f = (W ↪ Iⁿ) is a tame embedded
m-manifold such that f is a tame framed transversal stratification." (Compact version:
Definition/Remark 3.1.12, p.67–68, using corner neighborhoods.)

**Combinatorial transversality** (Definition 3.1.18, p.69): a stratified open n-truss (T, f:Q↪Tₙ)
is combinatorially m-dim k-transversal at x if there is an open cone (n−k)-truss C with subposet
D ↪ Cₙ₋ₖ containing the cone point >, D∖> an (m−k−1)-sphere, and
(T≤ˣ, f≤ˣ) ≅ T̊ᵏ × (C, D↪Cₙ₋ₖ). "**Tangle truss**" (Definition 3.1.22, p.69) = combinatorial
tangle = normalized stratified open n-truss that is combinatorially m-dim transversal at every
point.

> "Theorem 3.1.25 (Combinatorializing tame tangles). Framed stratified homeomorphism classes of
> tame m-tangles in Iⁿ are in 1-to-1 correspondence with m-tangle n-trusses, by taking tame
> tangles f = (W ↪ Iⁿ) to their fundamental stratified trusses NFTrs f." (p.70)

**Refinement to manifold diagrams**: the **transversal stratification** tstr(f) of a tame tangle
(strata = components of the k-transversal loci, all k, plus the complement, Definition 3.1.29,
p.71) satisfies

> "Theorem 3.1.32 (Tangles refine to manifold diagrams). Given a tame tangle f, then the
> transversal stratification tstr(f) of the tangle is a manifold diagram." (p.71)

i.e., a tame tangle's stratum-by-critical-locus refinement always is a manifold diagram — the
formal bridge between the two central notions.

## 8. Singularities, perturbation, stability

**Tangle singularity** (Definition 3.2.26, p.82): an m-tangle n-truss (T,f) is an
**m-singularity** if T is an open cone truss (equivalently, the cone of a tame link whose cone
point has transversal dimension 0). **Perturbation** (Definition 3.2.29, p.83): a tangle truss
bundle over [1]ᵒᵖ = (0←1) such that every point of the special (0) fiber's tangle manifold lifts
to some point of the generic (1) fiber's tangle manifold; written (q,h): (T,f) ⇝ (S,h).

**Stability** (Definition 3.2.35, p.85): "An m-singularity (T, f: Q↪Tₙ) is stable if there
exists no perturbation (T,f) ⇝ (S, g: W↪Sₙ) such that for all x∈W we have #Q > #W≤ˣ" — i.e. it
cannot be perturbed into anything of strictly smaller poset cardinality. **F-equivalence**
(Definition 3.2.36, p.85): stable (T,f), (S,g) are F-equivalent ("framed isotopic") if joined by
a path (T,f)→(S,g); classes are **F-orbits**. **Inductive stability** (Definition 3.2.37, p.85):
a stable singularity all of whose perturbations to other stable singularities are trivial
(product with [1]ᵒᵖ).

## 9. Elementary singularities in low dimensions (the classification)

**Basic tangle singularities up to ambient dimension 2** (Example 3.2.27/Fig. 3.11, p.83): a
single 0-tangle singularity in dim 1 (denoted A₁⁰ᵈ, or **pt**); two 1-tangle singularities in
dim 2, together denoted A₁¹ᵈ or simply **A₁**; a single 0-tangle singularity in dim 2, denoted
A₁⁰ᵈ⊕.

**Proposition 3.3.2 / Theorem 5.2 — stable 2-tangle singularities in I³** (p.87): "Up to
reflection and F-equivalence, there are three stable 2-singularities in I³, namely, those
depicted in Fig. I.5." They are named:

> "Remark 3.3.3 (Naming and counting stable 2-tangle singularities). The three singularities ...
> will be called 'extrema', 'saddles', and 'cusps' respectively. Symbolically, we also refer to
> extrema and saddles together as the A₂¹ᵈ singularities, and to the cusps as the A₂
> singularities." (p.87)

("in total there are eight F-equivalence classes ... applying all available reflections.")

**Proposition 3.3.6 — stable 1-tangle singularities in dim 3** (p.90): "Up to F-equivalence and
reflection, there is one stable 1-tangle singularity in I³" — denoted **A₁⊕**, the "cone" where
two 0-sphere link points lie one in source, one in target 2-cube. (A non-inductively-stable
variant is also pictured, Fig. 3.24.)

**Proposition 3.3.7 — stable 2-tangle singularities in I⁴** (p.91): "Up to reflection and
F-equivalence, there are four stable 2-singularities in I⁴": three obtained by *stabilizing* the
dim-3 extrema/saddle/cusp singularities (named A₂¹ᵈ⊕ and A₂⊕□ in the figure captions, Fig. 3.25),
plus a genuinely new fourth singularity — "the ability to braid points in the plane provides the
link of a new singularity which trivializes the braid" (p.91), the **braid-trivializing
singularity** (Fig. 3.26).

**Remark 3.3.9 — 3-tangle singularities in dim 4** (p.93, not rigorously proven): "there are nine
classes of stable singularities in this case ... organized into five 'types'" (Fig. 3.30): named
**A₁⇔₃A₂¹ᵈ**, **A₂⇔₍₃,₂₎A₂¹ᵈ**, **A₂⇔₍₃,₁₎A₂¹ᵈ**, **A₁⇔₃A₂**, **A₃⇔₍₃,₂,₁₎A₂** (=A₃),
**A₁⇔₂A₂**. Two coincide (Observation 3.4.7, p.99) and are jointly denoted **D₂** (Terminology
3.4.8, p.100). The paper additionally constructs and names **D₃** (Example 3.4.11, p.101, a
"triple binary relator") and **D₄**, "in Thom's classification also known as the 'elliptic
umbilic singularity'" (p.100) — stable but not inductively stable, perturbing to a binary
relator of D₃ singularities.

## 10. Relation to Morse theory / classical singularity theory

The paper explicitly aligns its 2-tangle singularities with classical germs (p.93):

> "1. The counterpart of A₂¹ᵈ are the 'Morse singularities' f(x₁,x₂) = ±x₁² ± x₂²,
> 2. The counterpart of A₂ are the 'Morse-Cerf singularities' f(x₁,u₁) = ±x₁³ ± u₁x₁."

Section 3.4.1 (p.94) recalls: map germs f:(ℝᵐ,0)→(ℝᵖ,0) up to right (G=ℛ, p=1) or left-right
(G=𝒜, p>1) equivalence; **ℛ-finiteness** = **ℛ-determinacy** (Mather); Arnold's **ADE
classification** of ℛ-simple ℛ-orbits: Aₖ germs x₁^(k+1) (k>1); Dₖ germs x₁(x₁±x₂^(k-1));
E₆,E₇,E₈ germs x₁³+x₂⁴, x₁³+x₁x₂³, x₁³+x₂⁵. "Thom's original seven 'elementary singularities'
exactly describe those orbits up to codimension 5, which are A₂, A₃, A₄, A₅, D₄±, D₅" (p.94).
**Heuristic 3.4.2** (p.96, "Translation of G-simple G-orbits to F-orbits") builds a tame tangle
singularity from a G-simple G-orbit via the u-parametrized graph Γ̃f of a miniversal unfolding
F(x,u)=(fᵤ(x),u), intersected with a framed cube embedding; **Example 3.4.3** (p.96) translates
f(x₁,x₂)=x₁²+x₂² (extremum), g(x₁,x₂)=x₁²−x₂² (saddle), h(x₁)=x₁³ unfolded as hᵤ₁=x₁³−u₁x₁
(cusp) into the three dim-3 tangle singularities of Proposition 3.3.2. **Terminology 3.4.4**
("binary relators") organizes Aₖ singularities as relators of Aₖ₋₁'s composed with each other,
generalizing to the ⇔ₖ notation. Observation 3.4.17 and Conjectures 3.4.18–3.4.21 (p.106–108)
speculate that in dimension ≤4 all smooth structures are captured by tame tangles up to framed
stratified homeomorphism (Hypothesis 6, restated formally).

## 11. How diagrams are drawn (the role of the framing)

Pictures are built from the canonical flat framing of the ambient cube/mesh, using categorical
directions and k-arrows (§1 above, p.36); n-meshes "cellulate" (like a triangulation, but with
framed regular cells) both manifold diagrams and — via dualization — cell diagrams, whose
"pasting diagram" reading uses non-degenerate/degenerate k-cells drawn as k-arrows or
k-identities (Remark 2.4.15, p.63). For higher tangles the paper adopts an explicit *projection*
convention rather than classical over/under crossing notation:

> "Notation 3.4.10 (Projecting 2-tangles). Going forward, we often depict 2-tangles in I³ by the
> projections of their 'non-regular points' (i.e. points of transversal dimension < 2) along
> I³ → I² ... we usually also add, in color, the deformation that happens in between any of the
> sampled slices ... since the notation is ambiguous ... we usually provide an 'initial
> condition' given by at least one full picture of a 2-tangle in the 3-cube I³." (p.101)

4-manifold-diagram examples are similarly drawn by "sampling at slices {tᵢ}×I³ of the 4-cube
I⁴" with small/big dots for 1- and 0-manifold strata and color tracking evolution across time
slices (Example 2.1.7, p.44–45). The paper never introduces "geometric vs. combinatorial faces"
as a separate named dichotomy; instead the operative distinction throughout is *topological*
(manifold/cell diagrams, tame tangles, as actual stratified/embedded spaces) vs. *combinatorial*
(trusses/tangle trusses, as structured posets) — related one-to-one by the NFTrs/CMsh
correspondence and its several combinatorialization theorems (§§5,6,7 above).

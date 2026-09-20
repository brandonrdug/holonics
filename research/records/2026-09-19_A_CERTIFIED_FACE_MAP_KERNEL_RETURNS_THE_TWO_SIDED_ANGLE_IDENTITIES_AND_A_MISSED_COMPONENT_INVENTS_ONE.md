# A certified face-map kernel returns the two-sided-angle identities, and a missed component invents one

**Date:** September 19, 2026. **Status:** first instance of the
[identity atlas](../../docs/plans/THE_IDENTITIES_OF_A_CONFIGURATION_ARE_THE_KERNEL_OF_ITS_FACE_MAP.md)
contract (I1–I8, as corrected by the September 19 audit), advancing
[#49](https://github.com/brandonrdug/holonics/issues/49) for the helical-pair consumer
[#48](https://github.com/brandonrdug/holonics/issues/48). **Truth status is per claim.** Classical
results are `proved-standard` with their names inline; what is new here is not a theorem but a
**mechanism that returned theorems and certified every basis vector of what it returned**.

## The question this instance answers, and the one it does not

[definition] *Given a configuration with a rational parametrization, a finite receiver family and a
degree — and no table of identities anywhere on the path — which identities does the kernel of the
face map return, which survive exact certification on every declared chart, and what exactly is
still owed before "all degrees" may be said?*

The question it does **not** answer is whether the ideal the certified generators generate is the
whole face-map kernel in every degree. That obligation is named below and is not discharged.

## What the owner is

[implemented-exact] `crates/holonic-engine/src/identity_atlas.rs`. A configuration declares a
receiver family, a bounded monomial family, and **a list of rational charts with one common
nonvanishing denominator each**. The face map is evaluated at exact integer parameter points; its
kernel comes from `exact_linear::kernel_basis`; each basis vector is certified by **exact
substitution of the parametrization on every declared chart** — the substituted numerator must be
the zero polynomial, not small — and a vector that fails returns its nonzero remainder together
with an admissible counterexample point, **which the walk then adds as a sample**. A spurious
sampling direction therefore removes itself rather than being argued away.

[implemented-exact] The certified identities are reduced by increasing degree to the **elementary
generators**, those are completed to a Gröbner basis under graded lex (Buchberger with the product
and chain criteria and the normal selection strategy), and every certified identity is reduced
modulo that closure. That is **bounded-degree completeness**. `Millennium/Border.lean` supplied no
completion engine and none was inferred from its filename; the algorithm is implemented here.

## T0 — one angle, the curvature a variable

[implemented-exact; computational-witness] Receivers `{C, S, Curv}`, charts the two windings of the
half-angle parametrization `C = ε(1 − k t²)/(1 + k t²)`, `S = 2εt/(1 + k t²)`, domain
`1 + k t² ≠ 0`. At degree `(2, 1)` — degree ≤ 2 in `(C, S)` and ≤ 1 in the curvature — the declared
family has 12 monomials, the certified filtered dimension is 11, and the kernel is
**one-dimensional with generator `C² + k S² − 1`**, certified on both windings; its support is a
three-column circuit that `matroid_chow` reads as `U(2, 3)` with reduced characteristic magnitudes
`(1, 2)`. At degree `(4, 2)` the family has 45 monomials, the filtered dimension is 33 and the
kernel is **twelve-dimensional**; every one of the twelve reduces to zero modulo that single
generator in 14 steps. They are its bounded-degree consequences, not new generators.

[proved-standard] The relation itself is the rational parametrization of a conic. What is returned
here is that a machine with no trigonometric knowledge produced it as the unique generator of a
declared kernel and proved it.

## T1 — two angles and their sum, uniformly in `k`

[implemented-exact; computational-witness] Receivers `{C₁, S₁, C₂, S₂, C₃, S₃, Curv}` with
`(C₃, S₃)` the two-sided cosine and sine of `θ₁ ⊕_k θ₂`, charted in all four windings
`(ε₁, ε₂) ∈ {±1}²` — the sum's winding is **not free**: `ε₃ = ε₁ε₂` is forced by the group law.
The declared family has 56 monomials; the certified filtered dimension is 44 and the kernel is
**twelve-dimensional**, every vector certified on all four windings. I4's reduction by increasing
degree returns **six elementary generators and six consequences**, and the six the machine chose
are the sine addition law, its two inverse-angle companions, and three Pythagorean-plus-cosine
relations uniformly in `k`:

```text
S₃ = S₁C₂ + C₁S₂        C₁ = C₂C₃ + k S₂S₃        C₂² + k S₂² = 1        (and their partners)
```

with `C₃ = C₁C₂ − k S₁S₂` in the certified span. Buchberger closes those six into a
**twelve-member** Gröbner basis under graded lex (66 S-pairs, 40 discharged by the chain criterion,
3 ms), and every certified identity reduces to zero modulo it: **bounded-degree completeness holds**.
The six consequences include `Curv` times each degree-2 law — an **ideal** consequence that is a
monomial multiple — and `C₃² + k S₃² − 1`, which is an ideal consequence that is **not** a monomial
multiple of the generators. That second kind is exactly why I4 must reduce rather than assume
`F · Id_(d−1)` is complete in a filtered chart, and it occurs in the smallest interesting instance.

[proved-standard] Specializing `k = 1, 0, −1` gives the circular, Galilean and hyperbolic addition
laws with no separate proof. The Lean owner states them once, uniformly in `k`.

## The collapses, each kernel computed independently

[implemented-exact; computational-witness] Each collapse is walked as its own configuration and its
certified kernel is reduced against the **transported** generic ideal, never assumed equal to it.

| collapse | declared charts | certified identities | specialized kernel ⊆ transported ideal | extra special-fibre relations |
|---|---|---|---|---|
| `k = 1` circular | four windings | 9 | yes | none |
| `k = −1` hyperbolic | four windings | 9 | yes | none |
| `k = 0` Galilean | four windings | 10 | yes | none |
| `k = 0` Galilean | **principal winding only** | **22** | **no** | **19**, including `C₁ − 1` |

The `k = 0` four-winding fibre gains one identity over the `k = ±1` fibres —
`C₁S₁ + C₂S₂ − C₃S₃`, which the collapse creates and which the transported ideal already contains.

[interpretation] The last row is the point of the table. At `k = 0` the fibre of the two-sided
circle is `C² = 1`, whose two components are `C = +1` and `C = −1`. The principal winding covers
only the first. On that chart family alone, `C₁ − 1` substitutes to the **zero polynomial** and is
certified — and it is not an identity of the fibre. The half-turn winding refuses it and returns an
exact counterexample point. This is the contract's `V(xy)` charted only on `y = 0` wrongly
certifying `y`, reproduced in the configuration the atlas is actually for, and it is run as a test
rather than mentioned as a caution.

[interpretation] In the notation the windings are the object, not the sign: the four charts are
indexed by two half-turns, and `−1 = e^{iπ}` is which one. The coverage certificate a collapse owes
is the statement of **which windings it declares**.

## T2 — three helical axes, and the transfer principle as one polynomial identity

[proved-standard] (Study; Kotelnikov; Clifford; Jacobi.) For screws `ξ_i = (u_i, v_i)` the Killing
form is `K_ij = u_i · u_j` and the reciprocal (Klein) form is `R_ij = u_i · v_j + v_i · u_j`. The
two-sided Gram is `G = K + ι R` with `ι² = k`. Jacobi's adjugate theorem

```text
(G₁₁G₂₂ − G₁₂²)(G₁₁G₃₃ − G₁₃²) − (G₁₁G₂₃ − G₁₂G₁₃)² = G₁₁ · det G
```

holds over **any** commutative ring, hence over `A_k = ℚ[k][ι]/(ι² − k)`. `G₁₁G₂₂ − G₁₂²` is
quadrance × spread of the pair `(1, 2)`; `G₁₁G₂₃ − G₁₂G₁₃` is the cross at axis 1, the numerator of
the law of cosines; `G₁₁` is the quadrance of axis 1 and its `ι`-part `R₁₁ = 2h₁Q₁` is the pitch
receiver. Splitting the identity into its `1`-part and its `ι`-part gives **two** polynomial
relations among those receivers: the transferred law of cosines and the transferred law of sines
for the helical triple, uniformly in `k`. At `k = 0` this is the dual-angle (screw) law for three
lines.

[implemented-exact; computational-witness] Both components were returned by the same kernel
machinery on a polynomial chart over the two-sided Gram data. The declared family has 132
monomials, the certified filtered dimension is 129, the kernel is **three-dimensional**, and I4's
reduction returns exactly **two elementary generators — the `1`-part and the `ι`-part — with the
third certified identity `Curv ×` the `ι`-part as their consequence**:

```text
Qua1·GramR + Pit1·GramK − SpQ12K·SpQ13R − SpQ12R·SpQ13K + 2·CrossK·CrossR = 0
Qua1·GramK − SpQ12K·SpQ13K + CrossK² + k(Pit1·GramR − SpQ12R·SpQ13R + CrossR²) = 0
```

Every certified identity was then checked on **real rational screws** — the three axis directions
`(3,4,0)`, `(0,5,12)`, `(8,−1,4)` with rational moments — at `k = 1, 0, −1`, and holds at each.

[source-audit; see the receipts below] These relations are **new to the helical record**: that
record carries `K` and `R`, the Klein null cone and the hand, and states that no owner composes
them, but it does not carry a law of sines or cosines for three axes in those receivers. They are
**not new mathematics**: the `1`-part is Jacobi's adjugate identity and the transfer is Study's
classical principle. The novelty claim is therefore exactly "new to that record, and composed here
for the first time in this repository", and no broader claim is made.

## What this instance measured, and what that measurement is not

[implemented-exact] The **filtered Hilbert dimension** `|Mon| − dim ker` is the cumulative Hilbert
function of the received filtration through the declared degree. Before certification the sampled
rank is a **lower bound** on it: one sample at `x = 0` gives rank 1 for `{1, x, x²}` whose filtered
dimension is 3, and that example is a test in this module. After every basis vector is certified,
the two coincide.

[definition] The Hilbert function counts **independent algebraic faces**. It is not encoded bits,
not runtime and not the preservation of any continuing conduct. The certificate term counts, the
certificate coefficient bit lengths and the wall clocks are reported as separate columns for that
reason, and Holonic Compression's executable codec still owes its decoder, its retained fibre and
its own cost.

## What is still owed

[open] **`J = ker(face map)` in all degrees.** Buchberger's criterion certifies a Gröbner basis *of
the ideal supplied*; `{x}` is already a Gröbner basis and does not generate `⟨x, y⟩`. Bounded-degree
completeness is what this instance returns. The all-degree claim needs elimination from a complete
source presentation with denominator saturation, or an independently certified Hilbert bound.
[established-bounded] For T1 there is a short argument — `C² + kS² − 1` is linear in `k` with unit
content, hence irreducible, the quotient is a domain, and the dimensions agree — but it is a hand
argument, it is not machine-certified in this instance, and the returned claim stays at bounded
degree.

[open] **Syzygies.** `derivation_atlas` measures route-space homology; that is not a resolution of
the syzygies of these identities without a connecting chain map, and none is supplied.

[open] **The Chow reading at scale.** `matroid_chow::Matroid::from_rank_table` is presented by the
complete rank function over `2^|E|` subsets and accepts simple matroids only. The circuit of a
certified identity is small enough to hand over — `C² + kS² − 1`'s support is `U(2, 3)` — but a
fifty- or hundred-column family is refused by extent, and the simplification (loops, parallel
classes) plus the identity circuits are returned instead.

[implemented-exact; measured] **The wall, and its owner.** The cost is the reduced row echelon
form of an `N × |Mon|` exact rational matrix: cubic in `|Mon|` with rational coefficient growth on
top. Measured on one optimized thread, T1 walks 56 columns in 11 ms and 168 columns in 115 ms — a
factor of 10 for a factor of 3 in width, and a factor of 10 again unoptimized — and head degree 5 is
refused **by type** at 513 monomials against the declared ceiling of 512. The certificates are
small: 20 terms and 52 coefficient bits for T0's generator, 2264 terms and 7568 bits for the whole
of T1's twelve, 227 terms and 562 bits for T2's three. The binding cost is therefore between head
degree 3 and head degree 4 of T1, and at the uniform-in-`k` helical family's 132 columns (40 ms).
That is the next consumer of
[#50](https://github.com/brandonrdug/holonics/issues/50)'s certificate-bearing rank/kernel/solve,
and nothing in this instance waited on it.

## Prior art run before anything was founded

```text
[source-audit 2026-09-20 27c72825] 'identity atlas|identity_atlas|IdentityAtlas|face map kernel|vanishing ideal'
  -> 14 files, 0 record titles. The only same-named owner is
  crates/holonic-engine/examples/the_material_founds_the_identity_atlas.rs, which recovers an atlas
  of identities from Lean SOURCE TEXT by statement grammar. It is a different object from the
  algebraic face-map kernel and does not compose it.
[source-audit 2026-09-20 27c72825] 'multivariate polynomial|Multivariate|monomial order|lex order|grevlex|S.?pair|buchberger'
  -> 377 files, none a Rust owner: rational_polynomial is univariate and bivariate and says so.
[source-audit 2026-09-20 27c72825] 'desnanot|dodgson|adjugate|jacobi determinant identity|gram determinant'
  -> 22 files, none composing the adjugate identity for a two-sided Gram.
[source-audit 2026-09-20 27c72825] 'law of cosines|law of sines|spread law|quadrance|rational trigonometry|transferred law'
  -> 27 files, 0 record titles; the hits are this contract and unrelated prose.
[source-audit 2026-09-20 27c72825] 'killing form|reciprocal form|klein form|screw theory|dual angle|two-sided gram|helical axis'
  -> 4 files. Zero owners before this module.
[source-audit 2026-09-20 27c72825] 'hilbert function|hilbert series|filtered dimension|algebraic redundancy|polynomial identity testing'
  -> 5 files, all contract prose.
```

Records read before founding: the helical-pair record
[THE_TRIGONOMETRY_OF_A_HELICAL_PAIR_IS_TRIGONOMETRY_OVER_A_TWO_SIDED_ANGLE](2026-09-19_THE_TRIGONOMETRY_OF_A_HELICAL_PAIR_IS_TRIGONOMETRY_OVER_A_TWO_SIDED_ANGLE.md)
in full, and the contract it is subordinate to in full.

## The exterior verification

[proved-standard; axiom-clean] `formal/elementary-holonics/ElementaryHolonics/Geometry/TwoSidedIdentityAtlas.lean`
states seven theorems: the T0 certificate in numerator form and in divided form with its
denominator hypothesis, the two T1 addition laws uniformly in `k`, the Galilean coverage falsifier
as an explicit point of the second component, and the two T2 transferred laws over an arbitrary
commutative ring. Each lowers to `linear_combination`, `field_simp; ring` or `ring`. `#print axioms`
reports `propext`, `Classical.choice` and `Quot.sound` only — no `sorryAx` — and the file builds in
about three seconds against the pinned Mathlib. Lean is exterior verification here and was not the
discovery.

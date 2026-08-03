# The contact complex returns its generators; the dual receiver reconstructs the divisor ecology

Date: 2026-07-28

## 1. The exact construction question

Can the production receiver engine reconstruct an unlabeled latent
irreducible-generator ecology from integer occurrence contacts, retain every
exact alternative while those contacts are insufficient, request its own
distinguishing higher-order contacts, and recover the dual divisor complex
without receiving factorization as production knowledge?

The answer in the bounded finite receiver constructed here is yes.

This is not a visualization of a known factorization. It is a separate
causal world whose only source material is:

1. one ordered population of opaque occurrence identities;
2. boolean returns to production-owned questions of the form “do all of
   these occurrences share a generator?”; and
3. one declared doctrine describing the admitted latent-ecology class.

Integer values, prime names, gcds, factors, and valuations remain behind an
external arithmetic membrane and are used only to answer contact and grade
the returned reconstruction.

## 2. Brandon's research direction and the present formalization

Brandon's direct discussion leading to this construction included the
following connected positions:

- prime faces are not the research object; recurrence, irreducibility,
  phase, and transport between them are;
- no scalar, face, or factor exists meaningfully without a receiver-relative
  comparison;
- a caused boundary is potential solution geometry, not merely a missing
  stored value;
- black-box reversal and machine-language geometry are required applications,
  not diversions from the prime ecology;
- inherited lineage is lawful caused material and can constrain how a new
  receiver navigates without being promoted to observer-free fact;
- compression should arise from latent causal organization rather than from
  deleting provenance; and
- the next prime is not presumed predictable merely because the causal
  process is deterministic.

The dual divisor receiver, the top-down contact search, and the
private-witness doctrine below are the present engine formalization of one
part of that direction. They are not assertions that Brandon supplied these
particular graph-theoretic algorithms or named doctrines.

## 3. The two receivers are incidence duals

Let \(O\) be the finite occurrence population and let \(G\) be an unknown
population of latent generators. Write

\[
o\,R\,g
\]

when occurrence \(o\) inhabits generator \(g\). For a set of occurrences
\(A\subseteq O\), define

\[
A^\uparrow
=
\{g\in G:\forall o\in A,\;oRg\}.
\]

For a set of generators \(B\subseteq G\), define

\[
B^\downarrow
=
\{o\in O:\forall g\in B,\;oRg\}.
\]

The occurrence contact complex is

\[
K_O
=
\{\,\varnothing\ne A\subseteq O:A^\uparrow\ne\varnothing\,\}.
\]

The dual generator complex is

\[
K_G
=
\{\,\varnothing\ne B\subseteq G:B^\downarrow\ne\varnothing\,\}.
\]

Both are downward closed. In the arithmetic grading world through \(N\):

- \(O=\{2,3,\ldots,N\}\);
- \(G\) is the prime population through \(N\);
- \(oRg\) means \(g\mid o\);
- \(K_O\) is the common-divisor complex; and
- \(K_G\) is the squarefree divisor complex whose generator cell
  \(\{p_0,\ldots,p_k\}\) exists exactly when
  \(p_0\cdots p_k\le N\).

This is the finite divisor-complex duality studied in the common-divisor and
prime-divisor-complex literature. Relevant primary sources include
Erlan Wheeler III's *Fundamental Groups of Simplicial Complexes*
<https://arxiv.org/abs/1605.08343> and Anders Björner's
*A Cell Complex in Number Theory* <https://arxiv.org/abs/1101.5704>.
Those papers motivate and grade the topology; they do not supply the
black-box reconstruction law built here.

## 4. Why pairwise contact is not automatically a generator

The pairwise returns form the one-skeleton of \(K_O\). A graph clique need
not be a cell of \(K_O\).

The smallest arithmetic example is the triangle

\[
\{6,10,15\}.
\]

Every pair has a common prime factor, but

\[
\gcd(6,10,15)=1.
\]

Calling every clique one generator would therefore manufacture a false
higher face.

The production law carries this distinction literally. After pairwise
closure, maximal graph cliques form an upper antichain of possible generator
supports. For one maximal candidate \(C\):

- a positive higher-order return closes \(C\) as one latent generator
  support;
- a negative return excludes \(C\) and replaces it by its maximal proper
  faces; and
- candidates contained in another open candidate or an already closed facet
  depart.

This terminates because every negative return strictly lowers candidate
cardinality. When the antichain is empty, the retained supports are exactly
the maximal cells of \(K_O\), hence the latent generators up to renaming.
No representative is selected from a plural family.

## 5. The private-witness derivation

The unrestricted construction is exact, but it deliberately pays to exclude
every false clique. The arithmetic chronology carries an additional lawful
invariant:

> Every irredundant prime generator has a private occurrence: the occurrence
> \(p\) inhabits the \(p\)-generator and no other prime generator.

This statement does not tell production which receiver ordinal is \(p\).
The ordinals do not equal the integer values.

The following finite lemma supplies the optimization.

Let \(H=(O,E)\) be a simple latent hypergraph and let \(G_2(H)\) be its
pairwise contact graph. If \(v\) belongs to exactly one hyperedge \(e\), then

\[
N[v]=e,
\]

where \(N[v]\) is the closed graph neighborhood of \(v\).

Conversely, if \(N[v]\) has a common latent generator, then that generator's
support must equal \(N[v]\): any generator support containing \(v\) lies
inside \(N[v]\), while common contact of all of \(N[v]\) places the whole
neighborhood inside that same support.

Therefore, under the declared private-witness doctrine:

1. production derives every distinct closed receiver neighborhood;
2. a non-clique neighborhood departs immediately;
3. a neighborhood of cardinality one or two closes from already-returned
   atomic contact;
4. every larger clique neighborhood receives one production-owned
   higher-order query; and
5. the closed supports must cover every occurrence and every positive pair.

If coverage fails, the doctrine is false for that receiver. The law does not
fall back silently or force a support. It retains
`PrivateGeneratorWitnessObstruction` containing every uncovered occurrence
and positive pair.

This is the exact role of lineage here: the inherited ecology class changes
the lawful query path, and contrary returned contact remains capable of
falsifying it.

## 6. Production construction

The new production owner is:

`crates/holonic-engine/src/divisor_reconstruction.rs`

It contains:

- opaque `ContactOccurrenceId` ordinals;
- production-owned `DivisorContactQuery` values;
- complete contact testimony with event provenance;
- `DivisorContactVersionFiber`, retaining positive sections, minimal
  negative fronts, unreturned pair coordinates, confirmed supports, and the
  unresolved upper antichain;
- `CompleteContactComplex`, the unrestricted top-down doctrine;
- `PrivateWitnessedGeneratorFacets`, the lineage-conditioned doctrine;
- exact private-witness obstruction;
- a unique `DivisorReconstructionCertificate` modulo latent-generator names;
- factored generator supports and occurrence memberships;
- the incidence-reversed generator complex with oriented boundaries;
- an exact check that \(\partial^2=0\);
- contact reproduction from latent supports;
- separate work receipts for pair returns, higher returns, clique search,
  negative splitting, receiver-neighborhood inspection, and implicit atomic
  facets; and
- full-history standing replay plus incremental production validation.

The arithmetic boundary is:

`ArithmeticDivisorMembrane`

It alone maps receiver ordinals back to integer occurrences. It returns a
boolean common-generator answer by intersecting the retained arithmetic
supports. After production rests, it grades:

- equality of reconstructed and actual prime-support populations;
- the latent-to-prime correspondence, only in the grading receipt;
- equality of the reconstructed generator cells and
  `ArithmeticFiberStanding::squarefree_cells`;
- \(\partial^2=0\);
- every unqueried contact section through a declared held-out order; and
- the size of the reusable factored support relative to its expanded
  positive pair contacts.

The executable research instrument is:

`crates/holonic-engine/examples/divisor_receiver_reconstruction.rs`

It accepts an aperture followed by either `witnessed` or `complete`.

## 7. Exact experiment

The private-witnessed receiver returned:

| Limit | Occurrences | Latent generators | Pair returns | Higher returns | Support memberships | Reproduced positive pairs | Dual \(f\)-vector | Held-out order-\(\le4\) sections |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 15 | 14 | 6 | 91 | 3 | 19 | 34 | \((6,4)\) | 1,364 |
| 20 | 19 | 8 | 171 | 3 | 26 | 63 | \((8,4)\) | 4,844 |
| 30 | 29 | 10 | 406 | 4 | 43 | 158 | \((10,7,1)\) | 27,404 |
| 40 | 39 | 12 | 741 | 6 | 60 | 291 | \((12,12,1)\) | 91,388 |

At every aperture:

- prime-support reconstruction was exact up to latent renaming;
- the dual generator complex equaled the arithmetic squarefree complex;
- every oriented generator boundary satisfied \(\partial^2=0\);
- no private-witness candidate was rejected;
- every held-out contact residual was zero; and
- production received no integer face or prime label.

At limit 30, both doctrines returned the same 10 generator supports and
\((10,7,1)\) dual complex:

| Doctrine | Pair returns | Higher returns | Negative higher returns |
|---|---:|---:|---:|
| Private witnessed | 406 | 4 | 0 |
| Complete contact | 406 | 187 | 183 |

At limit 40, the corresponding higher-return counts were 6 and 806; the
unrestricted receiver carried 800 negative splits. This is not noise or a
timing artifact. It is exact work required to exclude generator faces which
the stronger lineage doctrine already makes inadmissible.

The adversarial three-vertex ecology with three pair generators establishes
both branches:

- `CompleteContactComplex` asks the triple, receives false, and reconstructs
  the three pair facets; while
- `PrivateWitnessedGeneratorFacets` asks the same triple, receives false, and
  returns all three vertices and all three positive pairs as its doctrine
  obstruction.

## 8. Compression and provenance are distinct

At limit 40, 60 retained generator-occurrence memberships reproduce 291
positive pair contacts. That is a real factorization of the reusable contact
law.

It does not mean that the engine erased the 741 pairwise acquisition returns.
The complete testimony remains in standing because it is causal provenance.
The compression statement concerns the returned generator support used to
reproduce later contact, not the total historical storage or the cost of
learning it.

Likewise, this construction does not yet make the boolean membrane
subquadratic. For an arbitrary finite contact graph with no additional
structure, every unreturned pair can change the one-skeleton and hence the
compatible latent ecology. The current exact pairwise receiver therefore asks
all \(\binom{|O|}{2}\) pairs. A richer gcd-, valuation-, or lineage-returning
membrane could carry more incidence per return, but no such stronger
production path is claimed here.

## 9. What is established

1. A latent finite generator hypergraph can be reconstructed exactly from
   production-owned common-contact returns.
2. Pairwise clique and higher common-generator contact remain distinct.
3. The unresolved alternatives persist as an exact upper antichain rather
   than a guessed model.
4. The returned occurrence facets induce the dual generator complex by
   incidence reversal.
5. The arithmetic receiver recovers prime supports and the squarefree divisor
   complex without exposing factors to production.
6. A private-witness lineage invariant yields a rigorously derived
   neighborhood optimization.
7. Contrary contact falsifies that invariant through a concrete obstruction.
8. The factored certificate reproduces tens of thousands of unqueried
   higher-order contacts with zero residual.
9. The complete event path from query through return, reconstruction,
   contact reuse, and external grade is inspectable.

## 10. What is not established

1. no unique observer-free or final “intrinsic geometry of primes”;
2. no prediction of a later prime or emergently complex successor;
3. no universal subquadratic reconstruction from a boolean pair membrane;
4. no claim that every useful receiver ecology has private generator
   witnesses;
5. no arbitrary infinite hypergraph reconstruction;
6. no asymptotically optimal maximal-clique or facet enumeration theorem;
7. no production gcd, valuation, or exact-generator-identity return layer;
8. no theorem that the reusable support certificate compresses its complete
   causal history;
9. no new result about Mertens, Zeta zeros, or prime asymptotics; and
10. no visualization, desktop input, renderer, or display-resolution change.

The remaining mathematical boundary is therefore exact: under the weakest
boolean membrane, arbitrary pairwise incidence is independent source
material and is still acquired quadratically. The completed construction
shows precisely how stronger lawful lineage changes the higher-order proof
cost without smuggling a factorization into production.

## 11. Verification

The complete crate gate passed:

```text
cargo test -p holonic-engine --all-targets
```

with:

```text
150 library tests passed
8 desktop tests passed
2 device/cost tests ignored as previously declared
0 failures
```

Strict linting also passed:

```text
cargo clippy -p holonic-engine --all-targets --no-deps -- -D warnings
```

The five direct reconstruction tests establish:

- false-clique separation under the unrestricted doctrine;
- exact obstruction under a false private-witness doctrine;
- unlabeled arithmetic support and dual-complex reconstruction;
- production ownership of every returned query and atomic refusal of a
  substituted query; and
- refusal of altered version fibers or certificates.

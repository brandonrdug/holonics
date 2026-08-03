# THE HORN EMITS THE COEFFICIENT FAMILY; THE RECEIVER MEASURES ITS REFINEMENT

**Date:** 2026-07-27  
**Status:** RATIFIED FOLLOW-ON CONSTRUCTION / PRODUCTION HORN RESOLUTION BUILT /
EXACT CRT FILLER FAMILIES BUILT / RECEIVER-RELATIVE REFINEMENT BUILT /
NO DESKTOP OR DEVICE CHANGE

## Present question

After the topology-forming prime ecology exposed the open horn on
\(\{2,3,5\}\), Brandon ratified the following correction:

> The inherited polynomial \(x^2+x+11\) is not the filler ontology. It is one
> visible face of an exact family of continuations already constrained by the
> horn. Can the production law derive and retain that family without the
> application supplying a polynomial answer?

The construction question was therefore:

> Given an open prime horn, can its actual boundary phases generate all exact
> missing-receiver continuation strata, glue those local conditions into
> integer-polynomial coefficient families by CRT, fill the horn from the
> existence of those families, and expose later-prime refinement as exact
> receiver-relative cardinality rather than stochastic sampling?

This record distinguishes Brandon's research direction, the mathematical
formalization chosen here, and the behavior established by the engine.

## 1. Brandon's direction and the construction correction

Brandon's earlier messages did not ask for a universal reconstruction law or
for an assertion made in advance of computation. They asked for a machine in
which:

- a missing boundary is a real potential geometry;
- abduction follows already-caused partial relations;
- deduction performs exact compatibility transport;
- induction retains a reusable family rather than one lucky answer;
- recurrence means that the continuation geometry is implicit in the caused
  relations;
- probability and loss are derived from receiver partitions rather than
  attached random scalars; and
- a presentation is never confused with the complete holon it presents.

The prior grading control inherited the concrete polynomial

\[
x^2+x+11.
\]

That was lawful inherited material, but it did not test whether the horn
could emit its own continuation space. The correction does not ban inherited
mathematics. It adds a distinct production event whose input is only the
identity of an already-open horn.

## 2. Exact formalization

### Boundary continuation

Let

\[
h=(S,\partial S)
\]

be a retained open horn on an ordered prime support

\[
S=\{p_0,\ldots,p_n\}.
\]

For every immediate face

\[
F_i=S\setminus\{p_i\}
\]

and every concrete inherited phase witness on that face, the engine records:

1. the source polynomial degree \(d\);
2. the exact reduced source polynomial in each receiver \(p\in F_i\);
3. the required factor/Frobenius phase \(\tau\); and
4. the missing receiver \(p_i\).

The local continuation stratum is

\[
U_{p_i}(d,\tau)=
\left\{
g\in\mathbb F_{p_i}[x]:
g\text{ monic},\ \deg g=d,\ \tau\in\operatorname{phase}(g)
\right\}.
\]

An empty \(U_{p_i}\) is retained as an obstruction. A nonempty \(U_{p_i}\)
is a realised continuation branch.

### Coefficientwise CRT

For one \(g\in U_{p_i}(d,\tau)\), combine its coefficient residues with the
fixed source-face reductions. Since the receivers are distinct primes,
coefficientwise CRT gives one residue vector

\[
\mathbf a_g\in(\mathbb Z/M_S\mathbb Z)^d,
\qquad
M_S=\prod_{p\in S}p.
\]

That vector presents the affine integer-polynomial torsor

\[
\mathcal T_g=
\left\{
x^d+\sum_{j=0}^{d-1}(a_{g,j}+M_S z_j)x^j:
\mathbf z\in\mathbb Z^d
\right\}.
\]

The branch is the exact union

\[
\mathcal P_{F_i,\tau}
=
\bigcup_{g\in U_{p_i}(d,\tau)}\mathcal T_g.
\]

The complete horn filler space is the collection of all oriented boundary
branches:

\[
\mathcal P_h=
\coprod_{(F_i,\tau)}\mathcal P_{F_i,\tau}.
\]

It is generally a finite union of affine torsors, not one torsor. The engine
therefore names the whole object `HornFillerSpace`, each orientation
`HornFillerBranch`, and each coefficient coset
`MonicPolynomialTorsor`.

### Implicit recurrence rather than a representative cache

The standing object does not store every finite representative. It retains:

- the exact fixed source sections;
- the missing receiver;
- the required phase stratum;
- the exact stratum cardinality;
- the CRT modulus; and
- complete causal lineage.

Finite local polynomials and torsor representatives are materialized only
when a receiver asks for them. Membership of an arbitrary monic integer
polynomial is tested directly by reduction into the fixed source receivers
and factorization in the missing receiver.

This is the computational form of the recurrence correction: the family is
present as a lawfully constrained preimage, not as a cached list and not as a
chosen least-coefficient answer.

## 3. Exact stratum cardinality

For a prime \(q\), the number of monic irreducibles of degree \(k\) is derived
recursively from

\[
q^n=\sum_{k\mid n}kN_q(k).
\]

The engine then performs a finite factor-exponent dynamic program. It counts
monic degree-\(d\) factorizations in which exactly the requested population
of degree, multiplicity, and Frobenius-order constituents occurs. Since an
irreducible degree-\(k\) finite-field factor has Frobenius return order \(k\),
an incompatible requested order has cardinality zero.

This count is exact and is re-derived during standing validation. The full
ambient population is enumerated only for an explicit inspection receipt.
The law carries a declared finite local-section limit. If \(q^d\) exceeds
that membrane, the entire horn-resolution event is refused without partial
standing.

## 4. Production construction

The production owner remains:

`crates/holonic-engine/src/prime_ecology.rs`

### New event

`PrimeEcologyEvent::ResolveHorn` supplies:

- one fresh event identity; and
- one ordered open-horn support.

It supplies no polynomial coefficients, phase choice, local factorization,
or selected branch.

The law:

1. verifies that the horn exists and is open;
2. snapshots every immediate boundary face and its contemporary phase
   witnesses;
3. derives every boundary continuation backed by a concrete inherited
   polynomial;
4. derives the exact missing-receiver stratum cardinality;
5. retains fixed reductions and the CRT preimage law;
6. adds a distinct induced phase witness for every nonempty branch;
7. reconciles the complete phase topology; and
8. fills the horn and founds the higher cell when at least one branch is
   realised.

The event commits atomically. A repeated event, a closed horn, a malformed
support, or a local search space beyond the declared membrane leaves the
standing unchanged.

### Distinct material

The following remain distinct:

- `InheritedProbe`: supplied prior polynomial material;
- enacted `PolynomialPrimeFiber`: a prime's exact reception of that material;
- `PotentialPrimeHorn`: a proposed boundary with no common contemporary
  constituent;
- `HornFillerBranch`: an induced continuation family emitted by a boundary
  phase; and
- `PrimePhaseCell`: an induced caused cell witnessed by compatible material.

No member of a filler family is inserted as an inherited probe. No canonical
representative is allowed to determine later receivers on behalf of the
whole family.

## 5. The \(\{2,3,5\}\) horn

The inherited probes remain

\[
\Phi_3,\qquad\Phi_5,\qquad\Phi_7.
\]

They produce:

- a degree-four phase on the face \(\{2,3\}\);
- a degree-two phase on the face \(\{2,5\}\); and
- a degree-six phase on the face \(\{3,5\}\).

No one inherited phase is shared by all three primes, so the triangular
boundary is open.

Resolving only the support \(\{2,3,5\}\) derives:

| Source face | Missing receiver | Degree | Exact torsor population |
|---|---:|---:|---:|
| \(\{2,3\}\), from \(\Phi_5\) | \(5\) | 4 | 150 |
| \(\{2,5\}\), from \(\Phi_3\) | \(3\) | 2 | 3 |
| \(\{3,5\}\), from \(\Phi_7\) | \(2\) | 6 | 9 |

All three branches are nonempty. They become three distinct common induced
phase witnesses and fill the horn.

### The quadratic branch

The \(\Phi_3\) face fixes

\[
f(x)\equiv x^2+x+1\pmod 2,
\qquad
f(x)\equiv x^2+x+1\pmod 5.
\]

The missing receiver \(3\) has exactly three monic irreducible quadratics.
Coefficientwise CRT yields three torsors modulo \(30\), represented
coefficient-first by

\[
(a_0,a_1)\equiv(1,21),\ (11,1),\ (11,11)\pmod{30}.
\]

Thus

\[
x^2+x+11
\]

is one member of the second torsor:

\[
x^2+(1+30r)x+(11+30s),
\qquad r,s\in\mathbb Z.
\]

It is neither the unique filler nor a value selected by the engine.

## 6. Receiver-relative probability and loss

For a branch of degree \(d\) and a new prime receiver \(q\nmid M_S\), every
parent coefficient torsor refines into exactly

\[
q^d
\]

children modulo \(qM_S\). The refinement map

\[
(\mathbb Z/qM_S\mathbb Z)^d
\longrightarrow
(\mathbb Z/M_S\mathbb Z)^d
\]

is a finite covering with fiber cardinality \(q^d\).

The engine's refinement receipt groups all \(q^d\) local sections by their
exact finite-field factorization signatures. For the quadratic branch and
receiver \(7\):

| Local receiver stratum | Sections | Exact relative measure |
|---|---:|---:|
| irreducible | 21 | \(3/7\) |
| repeated root | 7 | \(1/7\) |
| split with distinct roots | 21 | \(3/7\) |

Nothing was rolled or sampled. The measure is normalized cardinality inside
the declared receiver fiber.

Relative to \(\{2,3,5\}\), the 49 children of one parent are
indistinguishable. Receiver \(7\) distinguishes them. Forgetting receiver
\(7\) collapses that refinement fiber. In this construction, probability is
the measure of a deterministic receiver stratum and loss is the refinement
topology erased by the quotient.

This is a rigorous bounded instance of the proposed geometric probability
ontology. It is not yet a universal probability theory.

## 7. Exact grading

The bounded instrument

`crates/holonic-engine/examples/prime_ecology_calibration.rs`

now supplies three cyclotomic probes and a horn-resolution event. It no
longer supplies `x^2+x+11`.

The run through 31 returned:

| Receipt | Exact value |
|---|---:|
| Founded primes | 11 |
| Inherited probes | 3 |
| Induced filler spaces | 1 |
| Polynomial prime fibers | 33 |
| Phase \(f\)-vector | \(\{1:41,2:54\}\) |
| Combined arithmetic/phase \(f\)-vector | \((11,48,55)\) |
| Open horns before resolution | 1 |
| \(\{2,3,5\}\) filled by support-only resolution | true |
| Branch torsor populations | \(150,3,9\) |
| \(x^2+x+11\) belongs to the quadratic family | true |
| Receiver-7 covering degree | 49 |
| Receiver-7 stratum populations | \(21,7,21\) |
| Selected \(\{2,3,5\}\) geometry survives enlargement | true |
| Probe-first/integer-first final geometry agrees | true |
| Equivalent coefficient presentation agrees | true |

The inherited-fiber factorization work across the 33 prime/probe fibers was

\[
(660,180,159,191)
\]

for gcd divisions, Frobenius columns, row eliminations, and Berlekamp shifts.
Horn stratum counts are separate exact combinatorial work and are not hidden
inside those figures.

The first explicit implementation stored all filler representatives. Routine
validation then repeated finite-field searches. It was rejected before this
record was accepted. The standing now retains the exact stratum and CRT
preimage law; the already-built through-31 binary completes in approximately
0.12 seconds on the grading host, while explicit quadratic refinement remains
available on demand. That timing is execution testimony, not an asymptotic
theorem.

## 8. What is established

- An open horn can cause polynomial filler material without receiving
  polynomial coefficients from the application.
- Every concrete inherited boundary phase emits an oriented continuation
  condition.
- Exact finite-field stratum cardinality distinguishes realised and
  obstructed branches.
- Coefficientwise CRT defines complete affine integer-polynomial families.
- The family, not a least representative, enters standing.
- A realised family can witness and fill a higher phase cell while the
  original horn remains in lineage.
- The \(\{2,3,5\}\) horn emits three exact branches containing
  \(150\), \(3\), and \(9\) torsors.
- \(x^2+x+11\) is verified as one family member without having been supplied
  as the answer.
- A later receiver gives an exact finite covering and phase partition.
- Normalized stratum cardinality supplies one rigorous receiver-relative
  probability, and the forgotten covering fiber supplies one exact account
  of loss.
- The support-only transition is atomic and invariant under the accepted
  prime/probe choreography control.

## 9. Exact boundary of the result

- Boundary continuation currently uses concrete inherited polynomial
  witnesses. A filler branch is not yet reused as the source of a further
  horn-resolution branch.
- The engine derives every immediate-face continuation independently. It does
  not yet form intersections between same-degree branches as new induced
  polynomial material.
- A filler family witnesses topology only on the support which caused it.
  Refinement through another founded prime is an exact inspection receipt; it
  does not automatically choose one stratum or change standing.
- Local stratum derivation is finite and bounded by the declared
  `max_horn_local_sections`. The current counting algorithm is exact but is
  not an unbounded symbolic factorization-stratum engine.
- The construction is monic, univariate, and coefficientwise over distinct
  prime receivers. Prime powers, arbitrary ideals, multivariate schemes,
  syzygies, and derived intersections are not supplied by this law.
- The phase quotient remains probe/branch identity, degree, Frobenius order,
  multiplicity, and population. It is not asserted to be the complete
  intrinsic geometry of primes.
- The receiver-relative cardinalities above do not establish a universal
  probability axiom, stochastic dynamics, semantic-information completion,
  P=NP theorem, or asymptotic complexity result.
- No desktop input, terminal receiver, visible resolution, renderer, CUDA
  kernel, or device ABI changed.

## Production owners

- `crates/holonic-engine/src/prime_ecology.rs`
  - `PrimeEcologyEvent::ResolveHorn`
  - `HornFillerSpace`
  - `HornFillerBranch`
  - `MonicLocalPolynomialStratum`
  - `MonicPolynomialTorsor`
  - `HornFillerRefinementReceipt`
  - `PrimeEcologyLaw`
  - `PrimeEcologyStanding`
- `crates/holonic-engine/examples/prime_ecology_calibration.rs`
  - bounded reporting instrument only

## Verification

Accepted headless verification:

- `cargo fmt --all -- --check`;
- `cargo test -p holonic-engine --all-targets --no-fail-fast`;
  - 115 library tests passed;
  - 8 desktop tests passed;
  - 2 previously declared device/cost tests remained ignored;
- `cargo clippy -p holonic-engine --all-targets --no-deps -- -D warnings`;
  - clean; and
- `cargo run -q -p holonic-engine --example prime_ecology_calibration -- 31`;
  - exact receipts matched the table above.

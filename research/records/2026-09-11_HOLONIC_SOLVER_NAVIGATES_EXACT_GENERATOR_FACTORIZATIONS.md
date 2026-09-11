# A Holonic Solver navigates exact generator factorizations

[project-postulate] Brandon's September 11 direction couples matrix/tensor operations,
normalization, canonical zero products, Gamma and transcendental generators with automatic
algorithm discovery. The requested pivot is a **Holonic Solver**: navigate representations of
a constrained operation, retain their causal/state/receiver conditions, and return executable
generators with their differences and work. This return implements a bounded exterior synthesis
example through existing exact owners and formalizes its certificate. Native Athena is unchanged.

## AlphaTensor supplies the right kind of target

[established-bounded; source-inspected] The supplied
[AlphaTensor repository](https://github.com/google-deepmind/alphatensor) was inspected at HEAD
`1949163da3bef7e3eb268a3ac015fd1c2dbfc767`. It publishes tensor factorizations, benchmarking,
nonequivalence data and recombination code. Standard-arithmetic and characteristic-two results
have separate files. Its release is useful algorithm/evidence apparatus; no AlphaTensor model
was trained or installed in this pass.

[definition] For a bilinear target with coefficients T, search for U,V,W satisfying

\[
T_{oij}=\sum_r W_{or}U_{ri}V_{rj}.
\]

Each r becomes one product of linear forms. The residual is the complete coefficient tensor,
not a loss on a few sampled inputs. A zero residual gives the requested bilinear map at every
input in the declared ring. Finding a decomposition supplies an upper bound on product count;
absence within a bounded candidate grammar is not a global tensor-rank lower bound.

[proved-derived; formal-checked] `Mathematics/GeneratorFactorization.bilinear_factorization`
proves the induced identity over arbitrary commutative rings and finite input/factor populations:

\[
\sum_r W_{or}(\sum_i U_{ri}x_i)(\sum_j V_{rj}y_j)
=\sum_{ij}T_{oij}x_i y_j.
\]

The proof is independent of the search process. A characteristic-two certificate must still be
interpreted in its declared field; it does not silently become a characteristic-zero certificate.

[established-bounded; source-inspected] AlphaTensor's
[recombination owner](https://github.com/google-deepmind/alphatensor/blob/1949163da3bef7e3eb268a3ac015fd1c2dbfc767/recombination/recombination.py)
allocates smaller factorizations to larger blocks and omits products whose outputs are unused.
It explicitly corrects the tensor's transposed-output convention. This is useful locality and
receiver transport, not just “minimize a rank.” Actual execution cost also depends on additions,
coefficient size, retained intermediates, layout and transfer.

## The operations in the supplied references

| Operation | Mathematical action | Constraint/fibre consequence |
|---|---|---|
| Matrix product AB | Contract the matching intermediate index; compose linear actions | Preserve the index/port join and order; equal final maps need not identify execution histories |
| Matrix-vector product Ax | Execute that action on one current | Equality at one x is weaker than equality of the complete map |
| Strassen factorization | Recombine products of linear block forms to implement the same matrix product | An alternative circuit; additions and stored intermediates matter alongside product count |
| Hadamard matrix product A∘B | Multiply aligned entries | A local multiplicative interaction/mask; its zeros may collapse input directions |
| All-ones matrix J | Hadamard identity; ordinary multiplication sends x to (Σx)1 | The same object is neutral in one operation and rank-one in the other |
| Ordinary identity I | Neutral for composition | Hadamard multiplication by I instead retains only the diagonal |
| Canonical Hadamard product | Represent an analytic function through zero factors and the required exponential/normalization data | Preserve multiplicities, convergence/tails and the zero-free factor; zeros alone need not identify the function |

[proved-standard] The operation distinctions follow the supplied
[matrix multiplication](https://mathworld.wolfram.com/MatrixMultiplication.html),
[Strassen](https://mathworld.wolfram.com/StrassenFormulas.html),
[entrywise product](https://mathworld.wolfram.com/HadamardMatrixProduct.html),
[unit matrix](https://mathworld.wolfram.com/UnitMatrix.html) and
[canonical product](https://mathworld.wolfram.com/HadamardProduct.html) references. The linked
matrix-vector page did not return through the web reader; its contraction is the one-column
specialization and is directly implemented by the inspected `ExactRatMatrix::apply` owner.

[proved-derived] For n>0 over the real/rational chart, J²=nJ, so P=J/n is a projection and
`ker J={x:Σx=0}`. Its quadratic face is xᵀJx=(Σx)². Thus a null family really is present,
but it belongs to the chosen operation/receiver. The normalized exponential has the opposite
common-mode blindness: adding c1 changes none of its probabilities. Its differential
`diag(p)−ppᵀ` is a positive semidefinite weighted Laplacian/variance form.

[proved-derived; source-inspected] These normalization relations already have owners:
`HolonicAdjointNormalization.face_add_common`, the algebraic `laplacianReturn` and its
quadratic form, centered sections and `sigmoid_is_binary_normalized_exponential`.
The sigmoid is a two-alternative receiver chart. These facts do not install dense all-to-all
semantic contact in HNN or turn normalization into a source identity.

## An actual automatic synthesis return

[established-bounded; implemented-exact] The new
[Rust example](../../crates/holonic-engine/examples/generator_factorization.rs) calls the standing
`ExactRatMatrix::preimage_fibre`, `preimage_obstruction`, `apply` and `multiply` methods. It adds
no private elimination engine. The source target is complex multiplication in real coordinates:
`(a,b),(c,d) -> (ac−bd,ad+bc)`.

[definition] Its declared finite input-form grammar is a, b, a+b, a−b on the left and the
corresponding c,d forms on the right. There are 16 product atoms. For each support of at most
three atoms, exact preimage solving finds all compatible output coefficients as particular plus
kernel. The selected coefficient representative is explicit, and its fibre is retained. An
inconsistent support can return an annihilating covector that separates the target from its image.

[established-bounded; computational-witness] The complete run returns:

| Products in candidate support | Supports checked | Valid supports |
|---:|---:|---:|
| 1 | 16 | 0 |
| 2 | 120 | 0 |
| 3 | 560 | 16 |

These are distinct returned supports, not 16 proven inequivalent algorithms. The declared cost
order prefers fewer products, then fewer nonunit output scales, then fewer additions. It selects

\[
p=ac,\quad q=bd,\quad r=(a+b)(c+d),\qquad
\operatorname{Re}=p-q,\quad\operatorname{Im}=r-p-q.
\]

This rediscovers the familiar three-product algorithm without supplying that decomposition to
the search. It uses five linear additions/subtractions versus the direct formula's two, while
reducing four bilinear products to three. No wall-time speedup is claimed. Every returned support
has its actual zero coefficient residual checked; `selected_three_product` also proves the
selected identity in Lean for all inputs. The
[receipts](2026-09-11_generator_factorization_receipts/exact-synthesis.json) retain the factors,
output coefficient fibres, search scope and representative obstruction covectors.

## The same solve reaches π and e generator blocks

[proved-derived; formal-checked] The existing ratio-series state is (a,S), and a block acts as
`(a,S) -> (αa,S+βa)`. Its matrix is

\[
B=\begin{pmatrix}\alpha&0\\\beta&1\end{pmatrix}.
\]

`GeneratorFactorization.blockMatrix_compose` now identifies chronological block composition
with the reversed matrix product. The matrix omits the index advance; `Block.length` retains
that clock and the existing future-word theorem uses it.

[established-bounded; implemented-exact] Given a target three-step block and a candidate first
ratio t, the Rust example solves `v+w=β−t`, `w=α` through the same exact preimage owner, then
recovers the route `(t,v/t,w/v)` where both denominators are nonzero. Its candidate t values are
the supplied source block's own ratios. It returns three exact routes for each of these sources:

| Source | One returned alternative route | Complete block |
|---|---|---|
| arctan(1/5), a Machin arm | `(−3/125,−103/225,−3/3605)` | `(length,α,β)=(3,−1/109375,−4273/328125)` |
| factorial series for e | `(1/2,2,1/6)` | `(3,1/6,5/3)` |

The current term and partial sum differ inside those routes and rejoin at the complete block
boundary. The executable checks the next canonical ratio/state as well. The prior generic
`RatioSeriesTransport.general_route_family` and clocked future theorem establish the algebraic
family; this run obtains the coefficients by solving constraints. It has not discovered a new
identity for π or e, and individual alternative microsteps are not asserted to be the original
series terms. The original analytic tail receiver is reattached at the matched indexed boundary.

## Gamma is compact in a shift chart

[proved-standard] Gamma satisfies `Γ(z+1)=zΓ(z)` away from the relevant poles. The recurrence
alone leaves a periodic multiplicative freedom; positive log-convexity and normalization on the
positive real axis select Gamma by Bohr–Mollerup, followed by its analytic continuation.
See [DLMF's functional relations](https://dlmf.nist.gov/5.5). Hölder's theorem concerns the absence
of an algebraic differential equation over ℂ(z), not the absence of an executable shift law;
the [Galoisian treatment](https://arxiv.org/abs/1404.3611) gives that precise classification.
The older record's inference from `shift=exp(derivative)` alone has been corrected.

[proved-derived] Differentiating the shift relation where holomorphic gives the first-jet
passage

\[
\binom{\Gamma(z+1)}{\Gamma'(z+1)}
=\begin{pmatrix}z&0\\1&z\end{pmatrix}
\binom{\Gamma(z)}{\Gamma'(z)}.
\]

For n steps, the complete multiplier is the rising factorial P_n(z)=∏_{k<n}(z+k), and the
matrix becomes `[[P_n,0],[P_n′,P_n]]`. This is a finite algebraic description of the transfer
while the initial analytic germ, normalization, pole domain and tail remain part of the source.

[proved-derived; formal-checked] `jetAct_compose` proves the exact product rule for those
blocks. The shift and coordinate multiplication obey `[S,Z]=S`; the new
`shift_coordinate_commutator` checks the pointwise identity. Thus a solver must preserve the
noncommuting shift algebra even though its fixed-coordinate block coefficients are scalars.

[established-bounded; computational-witness] The executable compiles three Gamma-jet shifts at
z=1/2 through `ExactRatMatrix::multiply` and verifies the complete matrix

\[
\begin{pmatrix}15/8&0\\23/4&15/8\end{pmatrix}.
\]

This is a transfer on any supplied value/derivative pair, not a guessed numerical Gamma value.
With the standard Γ(1/2)=√π source it gives Γ(7/2)=15√π/8. The finite jet certificate does not
assert that Gamma satisfies a finite-order algebraic ODE or that every hypertranscendental
function admits this same difference law.

## The starred Hadamard product and RH

[proved-standard] The analytic product uses zero factors together with exponential and Gamma
normalization; [DLMF 25.2.12](https://dlmf.nist.gov/25.2#E12) gives the ζ representation. The
prime Euler product initially belongs to Re s>1. Canonical zero products and the folded heat
source provide other analytic charts with their own convergence and domain requirements.

[proved-derived; source-inspected] The existing `RH/FosterProduct` retains the paired factors,
multiplicities, summable inverse-square control and logarithmic derivative. Its index counts
both members of each pair, so the compared product is paired/squared; the normalization owner
must travel with it. Product regrouping and block evaluation can be solver operations, but they
cannot silently change multiplicity, lose the zero-free exponential factor or omit the tail.

[definition] There are two related solver targets. One searches cheaper implementations of an
already specified source/receiver map. The other searches for a new mathematical certificate,
such as a source-qualified positive form or a sharper zero-free bound. An exact tensor
factorization solves the first target; it does not by itself discharge the second. A returned
RH improvement must verify its source, sign/domain, remainder and clock map. This makes the
upper/lower-bound question a precise constraint task rather than a change to a printed scalar.

## Holonic Solver: composition of existing owners

[historical; source-inspected] `TABLET_THE_FLOW` §7.6 records Brandon's ruling to lift and
supersede the old laboratory solver idea, not restore its implementation. The frozen algebra
and manifold records treat a constraint as an ecology of realizations. Current foundations
include `exact_linear`, `derived_factor_cover`, `material_factorization`, receiver-history
compression and the domain-specific exact CUDA realizer. None alone is a general synthesizer.

[definition] The shared solver passage is:

1. Carry a source constraint with its ring/domain, actual local ports, seed/clock and receiver.
2. Propose admitted representations using existing composition, factorization, restriction,
   shift/recurrence and rebase operations. Locality belongs to those supports and dependencies.
3. Solve their coefficient/compatibility equations through existing exact owners; retain free
   parameters and actual obstruction witnesses.
4. Verify the full target relation, decoder and future scope. Retain singular charts and analytic
   remainders. A single matching output or a low residual scalar is not full-map equality.
5. Compare complete work, span, coefficient/intermediate size and transfer in a declared resource
   chart; retain alternatives when those costs do not order.
6. Reuse the returned generator through the same source/receiver boundary, reopening its family
   when a changed contact or requested receiver exposes a missing distinction.

[interpretation] This makes “compression is intelligence is navigation” operational: navigate
among constrained realizations, derive a useful executable description, and use it to produce
consequences at the requested receiver. The bounded synthesis above demonstrates this mechanism
at exact algebraic scope. It is not a new universal qualitative grade from product count alone.

[definition] For Athena, first use such synthesis on a pure admitted local operation/encoding
segment. Reordering an entire mutable ecology also owes its material, occurrence, emission and
successor law. The existing producing-family incorporation remains a semantic construction to
derive; a tensor optimizer cannot turn compatible alternatives into observed facts. Lean remains
exterior verification, and the current Rust search is exterior apparatus. Native productive
construction must use resident owners; no CPU search or proof kernel is inserted into inference.

## Verification and next use

[established-bounded; process-audit] The executable ran successfully through the existing engine
library with `cargo run -p holonic-engine --example generator_factorization --no-default-features`.
Its final receipts include 696 support checks, 16 valid decompositions, six reconstructed ratio
routes and the Gamma-jet matrix. The new generic certificate, selected identity, block-matrix
bridge, shift commutator and jet composition pass Lean; `Framework.Computation` imports the owner.
`lake build ElementaryHolonics.Framework.Computation` passes (8,892 jobs including replayed
dependencies), and the complete research umbrella `lake env lean ElementaryHolonics.lean` passes.
The example passes its final Rust 2024 formatting check. The release's other runtime/architecture
families were not rerun. Native Athena state is unchanged.

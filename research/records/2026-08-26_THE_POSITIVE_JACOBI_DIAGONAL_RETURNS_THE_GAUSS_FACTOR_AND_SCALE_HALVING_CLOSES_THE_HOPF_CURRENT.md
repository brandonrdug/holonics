# The positive Jacobi diagonal returns the Gauss factor and scale halving closes the Hopf current

Date: 2026-08-26  
Scope: BSD prime family, Jacobi products, exact scale transport, Hopf source census, Brandt
receiver, and the reusable local-to-global fixed-point law

## Returned theorem

[proved-derived; formal-checked] `FamilyTunnellJacobiGaussFactor.lean` constructs the source factor
which had remained open in the prime-family BSD passage:

```text
B * (A + C) * (A - C) = weightedQuarterSquareTheta 1.
```

Here `A`, `B`, and `C` are the exact quarter-square residue streams already reconstructed from the
integral Jacobi source.  The theorem is not an algebraic assumption over anonymous power series.
It is the composite of the positive Jacobi diagonal, its two reflected integer roots over every
pronic address, coefficientwise completion of the returned finite product, and exact dilation of
the source factor populations.

[proved-derived; formal-checked] This factor composes with the already checked weighted
quarter-square/Hecke identity and returns the unconditional source law

```text
hopfHeckeThetaCurrent = 8 * heckeCoefficientSeries.
```

The Hopf current law is no longer a premise of the prime Brandt census.

## The anti-Zeno local-to-global mechanism

[proved-derived; formal-checked] The central product cancellation is first proved at every finite
aperture.  The distinct-part and odd-part products reassemble after the exact scale-two chart.  For
each fixed coefficient, omitted factors lie strictly beyond that coefficient, so the finite
products stabilize to the completed product without an estimate or analytic truncation error.

Let `F` be the completed cancellation body.  The source recurrence proves exactly

```text
F(X) = F(X^2),
F(0) = 1.
```

At a positive odd address the right side has zero coefficient.  At a positive even address it
returns the coefficient at the strictly smaller address `n/2`.  Strong induction therefore forces
every positive coefficient to vanish and returns `F = 1`.  This is a reusable stopping law for the
fractal/Zeno pattern: a repeated local-to-global deed closes when its rebase carries a well-founded
rank which strictly decreases outside the terminal face.

## Prime Brandt consequence and the remaining fibre

[proved-derived; formal-checked] `FamilyTunnellPrimeThetaBalance.lean` now proves that the single
remaining coefficient law

```text
coeff p (unitSquareTheta 1 ^ 4)
  = coeff p jacobiFourSquareLambertSeries
```

forces zero Brandt eigen-defect and the equivalent primitive/cubic census at every admitted odd
prime.  The discharged Hopf law no longer appears in these strengthened corollaries.

[proved-derived; formal-checked] `FamilyTunnellJacobiFourSquareSource.lean` reconstructs the source
as 256 residue-addressed shells.  `FamilyTunnellJacobiQuarticProduct.lean` removes that chart by an
explicit equivalence and proves, for every address,

```text
coeff n (unitSquareTheta 1 ^ 4) = card(totalFourSquareShell n).
```

`FamilyTunnellJacobiFourSquareClosure.lean` and the unaddressed theorem together identify the exact
surviving defect as

```text
card(totalFourSquareShell n) - 8 * jacobiDivisorCurrent n.
```

[proved-derived; formal-checked] The constant-address mismatch has been removed explicitly:
`completedJacobiFourSquareLambertSeries = 1 + jacobiFourSquareLambertSeries` retains the unique
norm-zero occurrence, and `FamilyTunnellJacobiQuarticProduct.lean` proves that equality of the
completed series is equivalent to the positive shell/divisor law at every address.  The new
`FamilyTunnellJacobiFourSquareEulerReturn.lean` constructs the outer Euler current `X d/dX`, proves
its addressed coefficient and Leibniz laws, and proves that this current plus the constant face
reconstructs the complete series.  The same owner proves the exact dilation law

```text
EulerCurrent(F(X^k)) = k * EulerCurrent(F)(X^k),
```

so a scale reindexing retains the acting scale as returned current rather than losing it in the
power-series chart.  Therefore the whole Jacobi passage is now equivalent to one
exact differentiated-current equality:

```text
EulerCurrent(unitSquareTheta 1 ^ 4)
  = EulerCurrent(completedJacobiFourSquareLambertSeries).
```

Any source proof of that equality closes the shell/divisor family uniformly and fires the existing
prime Brandt and cubic consequences.

[proved-derived; formal-checked] The receiver side is now decomposed further without an imported
four-square theorem.  Multiplication by four is proved to be an exact address equivalence between
the complete divisor population of `m` and the four-divisible divisor fibre of `4m`.  Consequently

```text
jacobiDivisorCurrent(n)
  = ordinaryDivisorCurrent(n)
      - if 4 | n then 4*ordinaryDivisorCurrent(n/4) else 0.
```

The connection coefficient

```text
C(n) = sigma(n) - [2|n] 5*sigma(n/2) + [4|n] 4*sigma(n/4)
```

and its exact power series are constructed.  Its origin coefficient is zero.  The completed
Lambert receiver satisfies `EulerCurrent(F)=Connection*F` if and only if the explicit strict
successor recurrence

```text
(m+1) D(m+1) = C(m+1) + 8 * sum_{j<m} C(j+1) D(m-j)
```

holds.  `powerSeriesEuler_ode_unique` proves by strong induction that any two integer series with
the same origin and this common connection are identical.  Thus the anti-Zeno global gluing law
reduced the remaining mathematics to two constitutive source laws—the product Euler law and the
displayed divisor recurrence—rather than another repetition of finite coefficient checks.

[proved-derived; formal-checked] The product Euler law is now closed by
`FamilyTunnellJacobiFiniteEulerConnection.lean` and
`FamilyTunnellJacobiCompletedEulerConnection.lean`.  A single factor `1-X^d` returns
`-dX^d` together with its explicit geometric predecessor fibre.  Finite factor populations add
their connections.  At scale `k`, every positive rebased address `k*m` stabilizes exactly to
`-k*sigma(m)`, and coefficientwise stabilization transports this law to the actual completed
`q`-Pochhammer body.

The completed factor population is then partitioned into its odd and even generator charts.  The
positive odd unit-orientation body `P` satisfies the exact cross-multiplied eta law

```text
P * (E_1 * E_4) = E_2^2.
```

No inverse eta quotient is installed.  Subtracting the known right-factor connection from the
total product connection returns the connection of `P`; Jacobi's positive unit product and its
fourfold repetition then prove

```text
EulerCurrent(unitSquareTheta 1 ^ 4)
  = thetaQuarticConnection * (unitSquareTheta 1 ^ 4).
```

The completed theorem audit contains only `propext`, `Classical.choice`, and `Quot.sound`; it has
no `sorryAx`.

[proved-derived; formal-checked] `FamilyTunnellJacobiDivisorConvolutionReduction.lean` now derives
`JacobiDivisorConnectionRecurrence`, the complete theta--Lambert identity, and every positive
four-square shell/divisor coefficient from one explicit proposition,
`DoubledDivisorConvolutionFormula`.  The reduction proves divisor-current doubling, exact parity
reindexing, the ordinary Besge convolution formula, and cancellation of the cubic divisor faces.
Its terminal audit contains no `sorryAx`.

[open] The sole remaining differentiated source deed is now the level-two convolution identity

```text
24 W_2(n)
  = 2 sigma_3(n) + (1-3n) sigma_1(n)
    + 8 sigma_3(n/2) + (1-6n) sigma_1(n/2),
```

with half-address terms zero at odd `n`.  This is Huard--Ou--Spearman--Williams equation `(4.4)`;
its finite source proof proceeds through their six-term positive-quadruple reindexing theorem.
Once inhabited, the checked consumer reconstructs Jacobi's complete ordered four-square
shell/divisor law and returns `card(totalFourSquareShell p) = 8(p+1)` at every odd prime.  The
alternate source path remains the integral eight-orientation fibre over every projective direction.

## Exact finite source map for the level-two current

[proved-standard] Theorem 1 of Huard--Ou--Spearman--Williams,
[“Elementary Evaluation of Certain Convolution Sums Involving Divisor
Functions”](https://people.math.carleton.ca/~williams/papers/pdf/249.pdf), is the finite
reindexing owner needed here.  For an integer-valued function `f(a,b,x,y)` satisfying

```text
f(a,b,x,y) - f(x,y,a,b)
  = f(-a,-b,x,y) - f(x,y,-a,-b),
```

it equates the sum, over positive `a,b,x,y` with `a*x+b*y=n`, of

```text
f(a,b,x,-y)       - f(a,-b,x,y)
+ f(a,a-b,x+y,y)  - f(a,a+b,y-x,y)
+ f(b-a,b,x,x+y)  - f(a+b,b,x,x-y)
```

with the sum, over positive divisors `d | n` and `0 < x < d`, of the boundary population

```text
f(0,n/d,x,d)          + f(n/d,0,d,x)
+ f(n/d,n/d,d-x,-x)   - f(x,x-d,n/d,n/d)
- f(x,d,0,n/d)        - f(d,x,n/d,0).
```

[proved-standard] The source proof partitions the positive quadruple population into the diagonal
`a=b` and the two oriented off-diagonal regions `a<b` and `a>b`.  Explicit affine reindexings pair
the two off-diagonal regions with opposite signs; the surviving diagonal is exactly the divisor
boundary above.  Thus the theorem is already a source-to-boundary conservation law: it does not
infer equality from cardinality, and it retains the six oriented terms until their actual
reindexing cancels them.

[proved-standard] Section 4 instantiates this theorem with
`f(a,b,x,y)=(2*a^2-b^2) F_k(x)`, where `F_k` is the exact divisibility indicator.  For `k=2`, the
two congruence-addressed positive quadruple populations satisfy

```text
A_2(n) + B_2(n)
  = (if 2 | n then 4 W_1(n/2) else 0) + 2 W_1(n) - 4 W_2(n).
```

Together with the instantiated finite theorem this returns

```text
48 W_2(n)
  = 12 W_1(n) - sigma_3(n) + sigma_1(n)
    + (if 2 | n then
         24 W_1(n/2) + 6 sigma_3(n/2) - 6n sigma_1(n/2)
       else 0).
```

Substitution of the ordinary Besge law at addresses `n` and `n/2`, followed by exact integer
algebra, gives equation `(4.4)` displayed above.  At odd `n` the half-address population is empty;
no fractional index or rounded coefficient is introduced.

[proved-derived; formal-checked] `FamilyTunnellJacobiHuardParityReindexing.lean` now closes the
second gate directly from exact divisor fibres.  The even quotient current is the scale-two
dilation of the ordinary divisor stream, the two mixed products both return `W_2(n)`, and their
intersection returns `W_1(n/2)` exactly when `2 | n`.  Their inclusion--exclusion sum inhabits
`HuardParityReindexing`; its audit contains no `sorryAx`.

[proved-derived; formal-checked] `FamilyTunnellJacobiHuardLevelTwoSource.lean` now owns the bounded
positive quadruple and divisor-boundary populations, the summand-preserving diagonal bijection
`(a,a,x,y) -> (x+y,y)`, and source-faithful affine transports for both off-diagonal strata.
`FamilyTunnellJacobiHuardSpecialization.lean` separately constructs the exact divisibility
indicator, the polynomial source, its oriented difference, and the two required symmetries.

[proved-derived; formal-checked] The source file now composes its `a<b` affine transport,
factor/cofactor swaps, and self-inverse `a>b` turn into `huardOffDiagonalCancellation_proved`.
Together with the diagonal boundary bijection this returns the unconditional
`huardOrientedTheoremOne`.  Both terminal audits contain only `propext`, `Classical.choice`, and
`Quot.sound`.

[proved-derived; formal-checked] The explicit source evaluation edge is closed.
`FamilyTunnellJacobiHuardCarrierBridges.lean` constructs exact sigma reindexings from each retained
positive-quadruple carrier to `huardMinusCurrent`, `huardPlusCurrent`, and
`scaledDivisorConvolution`.  The last bridge requires the source's exact domain `0 < k`; the
unrestricted `k=0` statement is false because its positive cofactor indicator vanishes while the
nominal convolution need not, so the invalid extension was rejected.

[proved-derived; formal-checked] `FamilyTunnellJacobiHuardBoundaryEvaluation.lean` flattens the
divisor boundary, applies the `t -> d-t` and `d -> n/d` reflections, evaluates the row polynomials,
and reindexes the `k`-divisible scale fibre without a fractional address.
`FamilyTunnellJacobiHuardEvaluation.lean` proves that the original six `f` faces and the three
oriented `g=f-f∘swap` faces agree globally, combines all four returns, and inhabits
`SpecializedSixTermEvaluation` and `HuardLemmaOneCleared`.

[proved-derived; formal-checked] The unconditional composition in
`FamilyTunnellJacobiHuardClosure.lean` now returns `DoubledDivisorConvolutionFormula`, the complete
Jacobi theta--Lambert identity, every positive four-square shell/divisor law, and zero norm-one
odd-prime Brandt defect.  The terminal audits contain only `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorryAx` or admitted source identity.

## What the Brandt return propagates—and what it does not

[proved-derived; formal-checked] The zero `brandtPrimeEigenDefect` returned by the Jacobi source is
the exact norm-one calibration of the odd-prime two-class Brandt action.  It compares the first
prime neighbor census with `heckeCoeff p`.  It does not quantify over the Tunnell coefficient
address `n`, so it cannot silently be promoted to the full half-integral Hecke eigen-current.

[proved-derived; formal-checked] `FamilyTunnellOddHeckeDoubleCount.lean` has already completed the
uniform source half.  At every `n` it retains the odd-coordinate aperture, the nonzero projective
direction, the zero-residue quotient fibre, and the exact neighbor point, and proves that their
signed return is

```text
fullCoeff(p^2*n) + jacobiSym(-n,p)*fullCoeff(n)
  + p*[p^2|n]*fullCoeff(n/p^2).
```

[open] The shortest downstream BSD edge is now the class-preserving successor return

```text
oddTunnellNeighborReturn(p,n) = heckeCoeff(p) * fullCoeff(n)
```

for every `n`.  In the existing holonic spelling this is a concrete family of cancelling swings on
`tunnellHeckeCarrier p n`, or an addressed two-class Brandt correspondence with the same signed
total.  The norm-one Jacobi theorem fixes its local eigenvalue.  Exact interchange of the two
Brandt classes with every neighbor successor is the anti-Zeno law that must propagate that value
uniformly; the already proved double count then returns `IsHalfIntegralHeckeEigenAt`, and the
checked Shimura recurrence can consume it at every prime-power depth.

[proved-derived; formal-checked] The finite local-to-global algebra has now been separated from
that source residual.  `FamilyTunnellBrandtTwoClassInterchange.lean` proves that a two-class action
with one common aperture, exact off-diagonal interchange, and signed norm-one calibration acts on
the retained class difference by the calibrated scalar at every coefficient address.  It also
formalizes the source-weighted law and derives raw interchange only from an explicit equality of
nonzero unit weights.  This is the uniform successor theorem; no iteration over a coefficient
aperture remains in it.

[proved-standard] In the standard Brandt convention, prime-neighbor matrices are regular away from
the level and satisfy weighted self-adjointness with the right-order unit indices; see
[Voight, *Quaternion Algebras*, §41.1](https://link.springer.com/chapter/10.1007/978-3-030-56694-4_41).

[proved-standard] Tunnell's original argument proves the required half-integral Hecke eigenforms
through the level-128 modular-form space and residue-support separation rather than through a
Brandt matrix; see [Tunnell 1983, pp. 327--330](https://doi.org/10.1007/BF01389327).

[open] The shortest unproved source object is therefore not another scalar identity.  It is the
destination-classified Brandt neighbor carrier: every source class and projective direction must
return an integral neighbor together with an exhaustive first/second target-class witness,
reverse-direction lineage, its stabilizer weight, and the exact coefficient-population double
count.  The present quaternion embeddings prove the two ternary norms inside Hamilton's algebra,
but do not yet identify them as the trace-zero right-order lattices of the two ideal classes.  That
identification—or an exhaustive determinant-64 ternary reduction proving the same target
classification—is the remaining source-specific edge consumed by the checked anti-Zeno theorem.

[proved-derived; formal-checked] `FamilyTunnellBrandtCalibratedInterchange.lean` then removes the
last scalar input from that edge.  From an actual first-row norm-one fibre of size twice the
diagonal destination fibre and the common aperture `p+1`, the unconditional Jacobi theorem proves
`diagonalFirst-offDiagonalFirst=heckeCoeff(p)`.  Its terminal composition therefore requests only
the source-geometric destination classification and exact population double count; the eigenvalue
calibration is no longer a caller hypothesis.  All three terminal axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.

[proved-derived; formal-checked] `FamilyTunnellBrandtNeighborWorldTube.lean` now returns one common
source carrier with two retained class apertures.  An occurrence owns its source class, projective
isotropic direction, corrected integral lift, rational neighbor membership, and quadratic
receiver.  Each source aperture has exactly `p+1` directions, the complete carrier has
`2*(p+1)`, and every actual neighbor reading is integral.  The construction deliberately has no
destination label: that absence is the geometric classification edge rather than a scalar defect.

[proved-derived; formal-checked] `FamilyTunnellBrandtDestinationClassification.lean` constructs the
next exact source map.  First- and second-pivot congruence normal forms replace each unbounded polar
kernel, and every actual neighbor is proved exactly the image of an explicit additive
`ℤ⁴ →+ ℚ³` coordinate map.  This is a surjective presentation with its non-injective reconstruction
fibre retained, not an asserted basis.

[proved-derived; formal-checked] `FamilyTunnellBrandtRelationKernel.lean` identifies that complete
fibre.  For either pivot, zero return is equivalent to being an integral multiple of one explicit
relation generator.  The source-specific passage derives the adjusted lift's polar-kernel normal
form from self-polar `=2Q` and the existing `p²` norm divisibility, and returns a generator whose
fourth coordinate is exactly `p` for every actual first-class, second-class, or fused occurrence.
`FamilyTunnellBrandtNeighborQuotient.lean` proves the additive chart range is exactly the actual
neighbor subgroup and returns the first-isomorphism passage `ℤ⁴/ℤg ≃+ actualNeighbor`.  The remaining
`FamilyTunnellBrandtNeighborQuadraticQuotient.lean` then descends the source receiver and proves its
quotient readings are integral, nonnegative, and zero only at the origin.  The remaining Jones--Pall
deed is therefore the global Gram reduction of this exact positive cyclic quotient.

[counterexample; formal-checked] `FamilyTunnellBrandtGlobalSeparation.lean` proves the class fibre
cannot be discarded.  At every odd prime the two reduced receivers are exactly equivalent, while
globally no bijection of integral triples can preserve the two quadratic readings because the first
class represents one and the second does not.  This is the precise local/global separator: the
local chart transports directions but does not identify global destination classes.

[proved-derived; formal-checked] `FamilyTunnellBrandtGenusInvariants.lean` records the exact two
half-polar Gram matrices, proves both determinants are `64`, proves both integral quadratic
receivers positive definite, and upgrades the odd-prime chart to an additive quadratic isometry.
Thus the destination theorem begins with checked determinant, positivity, and local transport data
for the two target representatives.  These target invariants do not by themselves classify the
actual returned neighbor.

[proved-derived; formal-checked] `FamilyTunnellBrandtMinkowskiBounds.lean` supplies the first actual
reduction lemma: a bounded `Q₁` norm forces exact independent coordinate-square bounds, and its
level-one box contains exactly `(0,±1,0)`.  Its completed-square chart gives the corresponding
exact bounds for `Q₂` and proves `Q₂` cannot represent one.  These finite reductions are not
promoted to the determinant-64 classification.

[proved-derived; formal-checked] `FamilyTunnellBrandtNeighborRankThree.lean` constructs exact
additive injections between every actual source-addressed neighbor and `ℤ³`, proves finite free
rank exactly three, and returns a `Fin 3` integral basis.  The proof uses the two exact scale
passages: multiplication by `p` returns the integral numerator of a neighbor point, while the
`p`-scaled source lattice embeds into the neighbor.

[proved-derived; formal-checked] `FamilyTunnellBrandtNeighborGram.lean` descends the integer
quadratic receiver and its full polar form `Q(x+y)-Q(x)-Q(y)` to the quotient.  It proves symmetry,
additivity in both variables, the diagonal law `B(x,x)=2Q(x)`, and returns the actual integral
three-by-three full Gram matrix in the constructed basis.  The two target full-polar determinants
are exactly `512=2³·64`.

[proved-derived; formal-checked] `FamilyTunnellBrandtNeighborDiscriminant.lean` places that actual
basis in the common rational ambient chart and proves the exact pullback and determinant laws

```text
G_actual = Tᵀ G_source T,
det(G_actual) = 512 det(T)².
```

It also proves `det(G_actual)=512` exactly equivalent to `det(T)²=1`.  The remaining discriminant
edge is therefore the genuine Kneser common-index/covolume theorem, not a missing Gram construction.

[proved-derived; formal-checked] `FamilyTunnellBrandtNeighborCommonIndex.lean` proves the complete
common-index and covolume edge.  The source polar functional is surjective onto `ZMod p`, so its
kernel has source-side index `p`.  The fourth coordinate modulo `p` descends through the cyclic
relation, is surjective on the neighbor quotient, and gives neighbor-side index `p`.  Both cores
are transported into the same rational ambient chart; the primitive `v/p` belongs to the neighbor
but not the integral source, so primality and the relative-index tower force those two cores to be
equal.  Exact integral bases of the source, neighbor, and common core are promoted to rational
bases without changing their vectors, and their additive closures recover the original lattices.
The equal nonzero indices therefore force `|det(T)|=1` and `det(T)²=1`; composing the existing
pullback law proves `det(G_actual)=512` for every occurrence without assuming a destination class.

[proved-derived; formal-checked] `FamilyTunnellBrandtDistinctNeighbors.lean` proves that the
projective-direction maps into actual neighbors are injective for both source forms.  Membership of
one fractional generator in the other neighbor clears to an exact proportionality modulo `p`; the
normalized affine or infinity pivot then fixes the scalar and all coordinates.  The full `p+1`
aperture therefore retains every addressed neighbor without collision.

[proved-derived; formal-checked] `FamilyTunnellBrandtKneserReverse.lean` turns those injective maps
into two exact `p+1` outgoing neighbor populations.  An actual neighbor in either population has a
unique normalized source direction, and each occurrence returns both index-`p` core receipts, the
actual determinant `512`, and the uncollapsed covolume pullback formula.  This is reverse incidence
before quotienting by global destination class; that final quotient still waits on Jones--Pall.

[receiver-insufficiency-counterexample; formal-checked]
`FamilyTunnellBrandtDestinationReduction.lean` proves why that discriminant edge cannot finish the
destination theorem by itself.  The positive form `Q₃=x²+y²+64z²` has the same half/full
determinants `64/512`, but has four norm-one points, whereas `Q₁` has two and `Q₂` has none.  No
quadratic-receiver equivalence to either target exists.  The same file enumerates exactly seven
ordered positive diagonal coefficient triples of determinant 64.

[proved-derived; formal-checked] `FamilyTunnellBrandtModFourReceiver.lean` adds a source-specific
two-adic separator.  The two target forms have identical complete mod-four representation profiles
and represent residue three; `Q₃` cannot.  Exact multiplication-by-`p` passages in both directions,
together with `p² ≡ 1 (mod 4)` for odd prime `p`, prove every actual neighbor has exactly its
retained source's complete mod-four profile.  Hence the known determinant impostor is excluded
without presupposing a destination class.

[proved-derived; formal-checked] `FamilyTunnellBrandtJonesPallReduction.lean` lifts that separator
to the actual quotient carrier.  It proves no quadratic-receiver equivalence can transport an
actual neighbor to `Q₃=x²+y²+64z²`, and packages the simultaneous determinant-512, integrality,
positive-definiteness, and nondegeneracy receipts.  The remaining theorem is now explicitly the
complete local-genus certificate at every prime followed by the two-class Jones--Pall reduction;
neither determinant nor the mod-four receiver is being mistaken for that full certificate.

[proved-derived; formal-checked] `FamilyTunnellBrandtLocalizeAtPrime.lean` removes the entire
away-from-`p` portion of that certificate.  In the common rational chart it proves `pL ⊆ L'` and
`pL' ⊆ L`; iterating those two exact transports proves the source and actual neighbor have the
same `p`-power saturation.  The remaining local statement is therefore not an unspecified family
of local checks: it is precisely the completed-carrier passage at the defining neighbor prime `p`.

[proved-derived; formal-checked] The defining-prime place now has an exact finite and completed
carrier. `FamilyTunnellBrandtFiniteDepthLocal.lean` returns the compatible `ZMod (p^n)` inverse
system and retains both reconstruction fibres. `FamilyTunnellBrandtPadicHensel.lean` and
`FamilyTunnellBrandtPadicIsotropicLift.lean` correct the retained direction by an exact small
`p`-adic root to a genuine isotropic vector. `FamilyTunnellBrandtLocalReflection.lean` and
`FamilyTunnellBrandtPadicHyperbolicPair.lean` normalize its unit-pairing witness and prove that
`e ↦ p⁻¹e`, `f ↦ pf`, with the orthogonal remainder fixed, is an ambient `Q_p` isometry.  The
companion `FamilyTunnellBrandtPadicIntegralRepresentatives.lean` proves that both partner stages
have exact `Z_p³` representatives and that their field casts recover the isometry's vectors.  The
remaining defining-prime statement is exactly the carrier-image equality between the completed
source lattice and completed actual-neighbor lattice; it is no longer the construction of an
ambient form isometry.

[proved-derived; formal-checked] `FamilyTunnellBrandtJonesPallNormalForm.lean` independently fixes
the source coordinates required immediately after that carrier equality.  It preserves the paper's
six-coefficient convention, proves the source and companion rebases to repository `Q₁` and `Q₂`
are proper unimodular transports, checks their reduction predicates, and returns the auxiliary
mod-eight dichotomy.  The Jones--Pall finite two-class enumeration remains an explicit certificate
obligation rather than an imported destination label.

[proved-derived; formal-checked] `FamilyTunnellBrandtUnitWeights.lean` constructs eight distinct
additive norm-preserving integral transports for each representative and proves that every additive
integral quadratic automorphism is one of them.  For the second form, the proof preserves the
correlation between the middle sign and the two admissible shear branches.  Hence the full two
automorphism populations both have cardinality eight.

[proved-derived; formal-checked] `FamilyTunnellAdmissibleOrderUnits.lean` separately proves that the
unit group of the constructed admissible quaternion order is exactly `±1,±i`, of cardinality four.
`FamilyTunnellBrandtRightOrderBridge.lean` separately retains the eight Lipschitz integral
norm-one occurrences and proves only population equivalences with the quadratic automorphism
fibres.  Its corrected `RightOrderActionData` is a candidate population-calibration schema and does
not encode multiplication or an ideal action.
Neither cardinality is promoted to a quaternion Brandt weight.

[source-audit; source-verified] The shortest continuation avoids that quaternion identification.
It uses the ordinary Kneser graph on the two Jones--Pall integral isometry classes and the already
proved equality of their full orthogonal-group cardinalities.  The local Kneser construction,
equal-index/covolume transport, determinant, and distinct-direction gates are now checked.  The
remaining ordered source chain is: formalize the Jones--Pall determinant-64 genus enumeration;
construct destination fibres and reverse-neighbor
incidence; then consume the already checked calibrated interchange.  The subsequent global gates
are modularity of the weight-`3/2` theta difference, normalized Shimura identification, and
Tunnell's exact Waldspurger period formula.

[proved-standard; source-verified] The invoked Jones--Pall theorem has been narrowed to its actual
source statement.  Under their coefficient convention
`(a,b,c,r,s,t)=ax²+by²+cz²+2ryz+2sxz+2txy`, the genus of `(1,2,32)` has the companion reduced
class `(2,4,9,-2,0,0)`; the latter is the repository's `Q₂` after `z ↦ -z`.  Their argument
first bounds the genus to at most two classes and their table exhibits the companion.  The Lean
obligation is therefore an actual-neighbor-to-this-genus passage followed by explicit reduced-class
reconstruction, not a classifier for every positive determinant-64 matrix.  Primary source:
[Jones--Pall 1939, pp. 172 and 181](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/5599-11511_2006_Article_BF02547347.pdf).

## Relation to the entropy/action torus current

[proved-derived; formal-checked] `HolonicEntropyActionInduction.lean` independently uses the same
construction discipline.  Local returned differences telescope through every finite successor
word; strict constitutive order removes the production kernel; and two four-axis currents form the
existing torus exterior two-current.  That current transports through a common chart by the exact
exterior-square action.

[interpretation] The shared instrument is consequently not a claim that entropy and a Jacobi theta
series are one quantity.  It is the proved transport pattern they both instantiate: retain the
addressed source population, preserve orientation through the receiver, stabilize every finite
aperture exactly, and use a strictly descending rebase to obtain a unique global return.  The BSD
closure above is a source-specific realization of that holonic staircase.

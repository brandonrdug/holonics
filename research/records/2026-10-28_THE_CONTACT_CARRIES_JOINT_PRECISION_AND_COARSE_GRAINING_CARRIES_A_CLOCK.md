# The contact carries joint precision, and coarse-graining carries a clock

**Date:** October 28. **Continuation:** Brandon's oriented-number, tropical/adic, contact and
cultivated-locality lenses. **Status:** derived relations, not a measured HNN implementation.
`[owned]` identifies recovered machinery; `[proved-derived]` supplies the calculation; `[design]`
is the inference for its consumer. These are joins to standard mathematics, not claims of new
external theorems.

**The missing relations.** A packet's precision is a joint relation through its contacts, and a
coarse boundary's spectral gap is a rate against its inherited storage. Collapsing either relation
to separate scalar values changes what the next interaction can receive. The first calculation
identifies exactly what cancellation does to the surviving grain; the second computes the
storage, clock and thermal terms left by an eliminated interior. The resulting derivative gives
cultivation a local spectral reading.

**Recovered first.**
- `prime.additive-caustic`, `radix.digit-convolution`, `linalg.integral-chart` and the
  [series-at-junctions record](2026-10-09_SERIES_CANCEL_AT_JUNCTIONS_AND_A_PASSAGES_ORDER_COMES_FROM_CHAINING_ITS_GRAINS.md)
  already own cancellation, carry and shared-denominator arithmetic.
- `resolvent.dynamic-schur` in [HNN_FORMULA](../../docs/HNN_FORMULA.md#state-space-convolution-and-diffusion-are-one-realization),
  `fluid.boundary-memory` in `Physics/ReflectedBoundaryMemory`, and `tube.kron-exact` in
  `Objects/Membrane`, `Holon/Restriction` and `holonics::holon::restriction::KronReduction` already
  own static elimination, dynamic response and the retained interior.
- The [cartography/flock record](2026-10-09_CARTOGRAPHY_INVERTS_AN_ELIMINATED_INTERIOR_AND_A_FLOCK_ALIGNS_THROUGH_ITS_CONTACTS_AT_ITS_SPECTRAL_GAP.md)
  joins boundary response and the spectral gap; the
  [diffusion record](2026-10-26_INFORMATION_DIFFUSES_IN_THE_POTENTIAL_TRAVELS_IN_THE_TURN_AND_A_KEY_IS_READ_FROM_DIFFUSION_ONLY_TO_ITS_SQUARE_ROOT.md)
  joins slow modes, loop closure and carried rates.
- `Foundation/ActionDescent` owns the changing encoding's continuation square for a fixed admitted
  action/receiver family. `Foundation/ContinuingTower` owns current fibres and transition residuals.

The concrete additions are the joint precision image (§1), the first frequency derivative of the
boundary response and its controlled remainder (§2), the same-face/arbitrarily-slow construction
(§3), and the spectral/thermal material variations (§4–5).

## 1. A contact transports joint precision

### 1.1 Cancellation changes relative depth by an exact amount

[proved-derived] Work in a discretely valued field, with uniformizer `π`, valuation ring `O`, and
`v(π)=1`. A received packet at absolute depth `N` is the fibre

```text
X = x + π^N O.
```

If `v(x)=a<N`, the packet has `N−a` remaining unit digits. This is a face with a retained fibre,
not a float or an instruction to round an internal series. All units and the place belong to the
receiving chart.

For *independently varying* input fibres `X=x+π^N O`, `Y=y+π^M O`, addition gives exactly

```text
X + Y = x+y + π^min(N,M) O.
```

If `c=v(x+y)<min(N,M)`, the resulting relative depth is

```text
r_out = min(N,M) − c.
```

If `x` and `y` each arrive at valuation `a` with `r` unit digits and the contact cancels `k`
leading places, `c=a+k` and `r_out=r−k`. The cancellation consumes `k` levels of *relative*
resolution while leaving the absolute fibre depth unchanged. If all known leading places cancel,
the output is the fibre `π^min(N,M)O`; the leading nonzero phase is unresolved at that receiver.
A receiver of the absolute residue can already read zero, while a receiver requiring the next
nonzero phase must reach deeper. This is a receiver distinction, not a mandatory precision limit.
The scalar formula is standard p-adic precision arithmetic
([Magma's operation law](https://docs.magma-maths.org/LocalFields/PAdicRingsAndTheirExtensions/operation-element.html)).

### 1.2 The separate fibres can discard the cancellation that matters

[proved-derived] Let a reached pair have a *joint* affine fibre `(x,y)+H`, where `H` is an
`O`-submodule of `K²`; it may have lower rank. Addition `A=[1 1]` gives

```text
A((x,y)+H) = x+y + A H.
```

Take `H={(e,−e): e∈π^N O}`. Both marginal faces have uncertainty `π^N O`, but `AH={0}`: the sum is
fully determined. Replacing the joint fibre by the product of its marginal fibres changes `{0}`
into `π^N O`. It discards a current relation even though neither individual scalar reading changes.
More generally every linear receiver `R` reads precisely `R H`; directions in `ker R` cancel at
that receiver and can remain relevant to another.

This is the exact algebraic content of the oriented tensor/packet requirement. The contact sees
joint variation and orientation; marginal scalars do not determine it. For nonlinear contacts the
actual image of the joint fibre is needed; the tangent image alone is not asserted globally.
The modern precision-lattice treatment of Caruso, Roe and Vaccon develops this joint representation
and gives local hypotheses under which a differential transports the complete precision lattice
([p-adic precision](https://math.mit.edu/~roed/writings/research/padicprec.pdf)).

[design] Carry the surviving reached relation, not a chronology of operations. Shared denominators,
phase relations and a basis for the current fibre are possible realizations; the future-sufficient
quotient determines which directions remain. Applying a fixed scalar width independently to the
components can destroy the cancellation before the contact receives it. This adds an algebraic
reason for the repository's dynamic-precision law; it does not ask for a new validation layer.

### 1.3 The appropriate tropical reading can be multivalued

[standard; design join] The quotient
`K/(1+π^r O)` for `r≥1`, with a separate zero, keeps valuation and finite unit data. Its
multiplication descends, while the sum of two classes is the set of classes attainable from
representatives: a valued hyperfield. Its tower is a useful external account of finite-depth
receiving faces ([valued hyperfields and truncated DVRs](https://arxiv.org/abs/1809.02483)).
The tropical minimum is its depth reading. When leading depths tie, the residue and deeper terms
determine the result. With correlated operands, the contact further restricts the allowed
representative pairs by their *joint* fibre `H`. Thus neither a scalar tropical minimum nor two
independent hyperfield elements replace the participating contact. The full relation and its
receiving quotient are different objects already supplied by Holonics.

## 2. Eliminating an interior carries a storage metric

[proved-derived] Take a finite reciprocal linear Holon in one receiving clock, with boundary state
`y`, interior state `z`, block-diagonal positive capacity/metric `C`, and symmetric nonnegative
constitutive operator `L`:

```text
C d/dt [y;z] = −L[y;z] + [u_B;u_I],
C = diag(C_B,C_I),       L = [[A,B],[B*,D]],       D ≻ 0.
```

The blocks have their transported units. The star is the paired transpose in these coordinates.
With coefficients held fixed, the existing dynamic-Schur relation gives

```text
Λ(s) = A + s C_B − B(D+s C_I)^−1 B*,
Λ(s) ŷ = C_B y(0) + û_B − B(D+s C_I)^−1(C_I z(0)+û_I).
```

The initial interior and its forcing survive. The boundary susceptibility is `Λ(s)^−1` where
invertible. This is a boundary response of the continuing Holon, not an archival convolution tape.

The static harmonic extension and boundary form are

```text
E = [I; −D^−1 B*],       S = Λ(0) = A − BD^−1B* = E* L E.
```

Differentiate the inverse in `Λ` at zero:

```text
C_eff = Λ′(0) = C_B + BD^−1 C_I D^−1B* = E* C E.
```

**The boundary inherits the storage of the interior it moves.** A static scalar or matrix `S`
therefore does not determine its clock. Its first dynamic approximation is
`C_eff ẏ + S y = effective source`, with the appropriate initial/forcing terms. Its local
relaxation rates are generalized eigenvalues `S v = λ C_eff v`, not ordinary eigenvalues of `S`.
This is a low-frequency approximation to the full response; it becomes an exact reduced law only
when the corresponding continuation closes.

### 2.1 The omitted term is explicit

[proved-derived] Put `H=C_I^−1/2 D C_I^−1/2`, `G=B C_I^−1/2`, and
`γ=λ_min(H)>0`. The inverse identity gives

```text
Λ(s) = S + s C_eff + R₂(s),
R₂(s) = −s² G H^−2(H+sI)^−1 G*.
```

For complex `s` with `|s|<γ`,

```text
‖R₂(s)‖ ≤ |s|² ‖G‖² / [γ²(γ−|s|)].
```

This names the separation required to replace the full interior by its first dynamic face. It is
not evidence that any existing HNN field is in that regime. When the receiver operates near an
interior pole, retain the relevant evolving modes or the higher response terms. `γ` is measured
in the receiver's clock, and all terms transform together on recharting.

## 3. One static face, arbitrarily different computational time

[proved-derived] The two-coordinate passive family

```text
C=I,       L_ε = [[2,−ε],[−ε,ε²]],       ε>0
```

has `x*L_εx = y²+(y−εz)²`, so its two relations are a grounded boundary and a pair-contact slip.
For every `ε`, eliminating the interior gives the *same* static face:

```text
S_ε = 2 − ε²/ε² = 1.
```

But its response and inherited capacity are

```text
Λ_ε(s) = s+2−ε²/(s+ε²),
C_eff,ε = 1+ε^−2,
Λ_ε(s)^−1 = (s+ε²)/(s²+(2+ε²)s+ε²).
```

The full system's slow relaxation rate is

```text
λ_−(ε) = [2+ε²−√(4+ε⁴)]/2  ∼ ε²/2 as ε→0.
```

Thus a receiver reading only the static face always reads `1`, while a continuing receiver can
read an arbitrarily slow return. The slow pole is not cancelled from the boundary response. With
unit boundary drive and zero initial state, small `ε` gives a fast approach near `y=1/2` followed
by a slow approach to `y=1` on scale `ε^−2`; the interior is still being brought into its required
relation. This plateau is the scale-separated asymptotic behavior, not a new simulation result.

This is a concrete obstruction to replacing a cultivated region by an unclocked numeric face.
The same settled result need not have the same navigational access, receiving latency or
maintenance dynamics. A coordinate change `z′=εz` moves the factor into the capacity; it cannot
remove the physical delay. The generalized response carries it in either frame.

The low-frequency rate from §2 is `ε²/(1+ε²)`, which must **not** be substituted for the exact
`λ_−`: here the slow pole remains a fixed fraction of the interior rate `ε²`, so the first-order
frequency truncation does not become asymptotically exact. This example requires the full
response, as §2.1 predicts.

## 4. Cultivation changes the gap through both forms

[proved-derived] Let material vary smoothly with parameter `a`, keeping the boundary/interior
partition and ranks fixed. Dots below are derivatives with respect to this material parameter.
Differentiate the Schur form:

```text
Ṡ = Ȧ − ḂD^−1B* − BD^−1Ḃ* + BD^−1ḊD^−1B*
   = E* L̇ E.
```

The second equality follows from `LE=[S;0]`: the derivative of the harmonic extension contributes
no additional term to this static form. For actual contact material
`L=Σ_e w_e j_e* j_e` with incidence/slip maps held fixed,

```text
∂S/∂w_e = (j_e E)* (j_e E).
```

This locates the variation at the contact that carries it. Moving contacts also carry their
`j̇_e` terms.

The capacity derivative does retain the changing extension:

```text
Ċ_eff = Ė* C E + E* Ċ E + E* C Ė,
Ė_I = −D^−1(Ḃ* + Ḋ E_I).
```

For a simple generalized eigenvalue of the first dynamic face, normalized by
`v*C_eff v=1`, differentiation gives

```text
λ̇ = v*(Ṡ − λ Ċ_eff)v.
```

This is the missing material comparison for the local gap: an increase of the effective restoring
form competes with an increase of the storage that must move with it. It is a specific spectral
receiver, not a replacement for the declared learning comparison or a universal scalar of progress.
Repeated eigenvalues require the perturbation form on their eigenspace; outside §2.1's regime the
full response/poles supply the clock.

[design] Homeostasis of locally accessible routes is a condition on the evolving *pair*
`(S,C_eff)` and, where required, the retained interior response. Deposition can strengthen a
static relation and simultaneously make its access slower by loading more internal storage.
The learning covector therefore has to return through the producing coupling and capacity, not
only through the settled face. The existing laws supply the route; this record identifies the
missing rate term at a coarse receiver.

For a time-dependent chosen extension `x≈E(t)y`, a Galerkin projection of the full equation also
carries `Γ=E*C Ė`:

```text
C_eff ẏ + (S+Γ)y = E*u.
```

With fixed `C`, `Ċ_eff=Γ+Γ*`, so the frame term cancels the moving-metric contribution in the
quadratic storage balance. This is the projected equation; its unresolved interior residual is
still the existing `ReflectedBoundaryMemory` law. Dropping `Γ` while moving the chart would alter
the power reading.

## 5. The thermal face of the same interior fibre

[proved-derived under a Gibbs constitution] Supply the quadratic form
`V(y,z)=½[y;z]*L[y;z]` with energy units, a fixed temperature, and a fixed physical integration
measure on the interior. Integrating its conditional Gibbs population over `z` yields

```text
F_B(y) = ½ y*S y + (k_BT/2) log(det D / det D_ref) + constant,
Cov(z | y) = k_BT D^−1.
```

Complete the square with `z+D^−1B*y` to obtain both formulas. `D_ref` provides the reference
volume/units in the same interior chart; the constant is independent of `y` and material at fixed
interior dimension and temperature. A physical rechart transports the measure and its Jacobian.
This is a specified thermal specialization, not a claim that a deterministic diffusion matrix by
itself fixes a bath.

At fixed boundary state the corresponding material covector reads

```text
dF_B = ½ y*(dS)y + (k_BT/2) tr(D^−1 dD).
```

Two interiors with the same static response `S` can therefore have different thermal populations
as well as different clocks. The log-determinant term is the contribution of the unresolved
interior's volume, which an unweighted minimum over the interior omits. This joins the
finite-temperature/tropical distinction to the actual eliminated fibre, rather than attaching an
entropy label to a numeral. The local derivatives return through `D`, `B` and the reached contact
material; changing dimension or temperature adds its own terms.

## 6. Consequence for the active campaign

[design; agent-inferred] An oriented packet is consumed through the joint current relation it
carries. A receiving locality is consumed through its transported response and clock. Neither can
be replaced by a collection of unconnected scalar faces without changing the future family.

The concrete consuming joins are:
1. **At arithmetic/phase contacts:** the image of the current joint fibre, including cancellations
   that disappear if each component is read separately. The consumer is the next contact and its
   admitted receiver, using the existing action-sufficient quotient, not an operation archive.
2. **At region restriction:** the dynamic boundary response, or its mode realization; when a first
   frequency face is enough, it carries both `S` and `C_eff`, with the explicit remainder above.
   `KronReduction` presently returns the static form and harmonic extension; this record does not
   claim its dynamic capacity/rate consumer is built.
3. **At cultivation:** the returned comparison includes whichever of static response, storage,
   clock and thermal population the participating receiver actually reads. The gap derivative is
   one such reading. Preservation under continued environmental exchange is the mathematical
   homeostasis question.

This advances the local problem–solution lens without changing the global complexity question:
the same answer face may hide arbitrarily different access times (§3), and cultivation acts on
the material terms that determine those times (§4). It also gives an explicit failure of
coarse-graining that discards time or joint precision. Text, image, acoustic and motor boundaries
all encounter this same issue; the current and its contacts are the common owner.

No learning run, performance claim or native implementation is included. The derivation is the
deliverable; its equations are joined into HNN_FORMULA and the expression atlas. The recorded
failure being avoided is a new vocabulary or unused owner substituted for the consuming law.

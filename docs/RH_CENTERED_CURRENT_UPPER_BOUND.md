# The half-centred face and the de Bruijn–Newman upper bound

[project-postulate] Brandon's September 14 request explicitly continues upper-bound work
using the evolving-source equation and the wider Holonic constructions. This bounded
derivation proceeds alongside the Athena engine blueprint. It does not make an RH endpoint
an admission condition for ordinary model generation or training.

## A conserved face with remaining complex motion

[definition] The locus `Re(s)=1/2` is the critical **line** within the strip `0<Re(s)<1`.
Use the existing source reflection `s†=1−conj(s)` and write `s=1/2+d+iy`. Then

```text
s†=1/2−d+iy,
(s+s†)/2=1/2+iy,
s−s†=2d.
```

[proved-derived; formal-checked] `PairPopulation.reflect` and
`TransverseCurrentBound.reflected_pair_center` retain precisely this distinction: the normal
centre is fixed while the longitudinal coordinate remains. The functional reflection `1−s`
is a different member, `1/2−d−iy`. Confusing these two maps would insert or delete an imaginary
separation in the reciprocal current. `Balance` already proves that functional reflection
and conjugation coincide exactly on the critical line.

[proved-derived] Equal reflected divisor multiplicities give total real current m per
pair of total mass 2m, hence normalized normal face `m/(2m)=1/2` for m>0. Its transverse
differences are ±d and its common imaginary component can still move. This is the concrete
balanced-face interpretation of one unit per two units. It uses the actual ξ symmetry and
divisor multiplicities; it is not a claim that every two operands average to one half.
The same mass/current distinction appears in `AttentionModeCompression`: normalized faces
retain less than the pair of mass and current that produced them. Conservation of the pair's
centre does not imply the transverse components have vanished.

## The clock and the full inward current

[definition] In the repository seam clock,
`G_τ(s)=heatE(−τ,ξ,s)`, so `∂τG=+G_ss`. A simple zero therefore moves with
`v=−G_ss/G_s`. The prior `heatE(u,ξ)` residual equation uses u=−τ; its sign must be transported.
The standard chart remains `H_t(z)=⅛ heatE(−t/4,ξ,½+iz/2)`, with
`Λ_std=4Λ_DN`. The tree's proved `Λ_DN≤1/8` is the classical standard `Λ_std≤1/2`.

[proved-derived; formal-checked] At d>0, the same-height reflected partner gives
`2 Re(1/(s−s†))=1/d`. The opposite member gives
`2 Re(1/(s−(1−s)))=d/(d²+y²)`. These are the two exact identities in
`TransverseCurrentBound`. The ordinary conjugate contributes zero **normal** current when
y≠0; its imaginary current is still present. Distinct quartet terms may be added only when
the members are distinct and actually belong to the divisor population.

[definition] At a rightmost zero, every other root w has `Re(w)≤Re(s)`. For a finite
divisor region retaining multiplicities, define the remaining current

```text
J_R(s)=2 Σ_(w≠s,s†) m_w (Re(s)−Re(w))/|s−w|².
```

[proved-derived; formal-checked] Each admitted summand is nonnegative under this ordering;
`weightedSurplus_nonneg` retains its multiplicity. The pair supplies the baseline inward
`−1/d`; the rest of the source adds inward normal current. A finite-region maximum is not
automatically a maximum of the entire source. Its exterior population must be retained through
the actual current/tail relation, or a proved orientation of that complement.

## The finite source error already exists

[established-bounded; source-inspected] `FosterClassFlux.comb'_sub_le` already bounds the
finite divisor current near a simple zero. Reading only the final `flux` limit theorem
incorrectly hid this finite estimate. This work reuses it instead of declaring the source
tail absent.

[proved-derived; formal-checked] Let f be the actual Foster-class source, z₀ a simple zero,
`f(z)=(z−z₀)g(z)` on its analytic nonvanishing local-factor ball of radius δ, and let the
Foster divisor disc satisfy `|z₀−1/2|+δ/2≤R/8`. `FiniteZeroCurrent` proves

```text
|−f_ss(z₀)/f_s(z₀) − (−2 comb'_R(z₀,z₀))|
 ≤ ε_R = 4(|z₀−1/2|+δ/2) tailInvSq_f(R).
```

Its `heatE_norm_negative_zero_velocity_sub_comb_le` instantiates the actual
`f=heatE(−τ,ξ)` through the existing Foster instance. `re_negative_zero_velocity_le`
then supplies the normal-velocity inequality from the finite comb's explicit split into
pair and surplus. The tail is an existing mathematical function with its source scope;
this formal bound is not itself a computed uniform all-height numerical enclosure.

## The strengthened squared-width law

[proved-derived; formal-checked] The source estimate gives

```text
d' ≤ −1/d−J_R+ε_R,
(d²)' ≤ −2−2d(J_R−ε_R).
```

For a positive differentiable transverse trajectory on `[0,T]`, a uniform tail upper bound ε
and an actual surplus margin `d(t)(J_R(t)−ε)≥a≥0`, the new integration theorem returns

```text
d(T)²+2(1+a)T ≤ d(0)².
```

It excludes a positive trajectory when `2(1+a)T>d(0)²`. The a=0 case recovers the baseline
squared-width clock; a source-supported a>0 shortens it. The theorem does not assume the
desired threshold bound as a new class field. It derives a trajectory exclusion from the
declared current, error and derivative inequalities.

[proved-derived] The quartet alone gives a useful finite-height refinement. If its members
are distinct, the full remaining current has the rightmost sign, and `|y|≤Y` along the
trajectory with Y>0, then for x=d² the extra opposite-member contribution gives
`x'≤−2−2x/(x+Y²)`. Define the normalized-log potential

```text
B_Y(x)=x/4+(Y²/8) log(1+2x/Y²).
B'_Y(x)=(x+Y²)/(2(2x+Y²)),
d B_Y(x(t))/dt ≤ −1.
```

The positive trajectory cannot last past `B_Y(x(0))`, which is strictly below x(0)/2
for x(0)>0. This is a written finite-height consequence, not an additional Lean-checked
global threshold theorem. The log is its normalized integral mode, not a floating literal.
As Y grows without bound the gain tends to zero. Thus a conserved half-centre and one quartet
do not supply a uniform improvement over the infinite source.

[open] A stronger global upper bound requires a width/current comparison for the actual ξ
family across all heights, with admissible continuation through changes of the extremal root
and multiple-zero events. The useful target is the source surplus or an equivalent strip
exclusion, using the recovered finite Foster tail and folded-source bounds. A small zero
sample, an assumed global rightmost trajectory or a finite-height quartet calculation cannot
replace that uniform source statement. This return supplies the current inequality and actual
source-error consumer; it does not establish a new numerical value for Λ_DN or prove Λ_DN≤0.

[definition] The [Polymath barrier construction](https://arxiv.org/html/1904.12438v2) is a
primary comparison for turning finite verification plus analytic exterior control into a
global bound. Its standard clock must be converted before comparison with tree Λ_DN. Later
reported numerical records have not been imported as Lean theorems or independently replayed
here; the current work advances the source-current relation rather than claiming one of those
certificate packages as a new result of Holonics.

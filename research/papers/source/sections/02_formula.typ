#import "@preview/unequivocal-ams:0.1.2": theorem, proof
#import "../lib/holonics.typ": *

#let formula = [
#pagebreak(weak: true)
= J4. Finite generators, primes, and the RH boundary <j4>

#local-contents((
  ([Formal exponential at finite degree], <j4-exponential>),
  ([Prime powers are required by the Euler exponential], <j4-prime-powers>),
  ([Aperture growth without replay], <j4-aperture>),
  ([Two exact atlases for pi], <j4-pi>),
  ([Scale and turn meet on the logarithmic cover], <j4-scale-turn>),
  ([Finite theta involution], <j4-theta>),
  ([The residual is a moving boundary], <j4-residual>),
  ([The exact RH boundary], <j4-rh>),
))

The mathematical programme around $pi$, $e$, primes, and the Riemann hypothesis becomes coherent
once three questions are separated:

1. Which finite object generates the next exact face?
2. Which equality is a formal or convergent theorem in its declared domain?
3. Which analytic completion and positivity statement is still absent?

The finite object is not called infinite merely because it presents the first terms of an
unbounded family. It carries a seed, a next-face law, an admissible boundary, an exact residual or
enclosure, and a rebase from one aperture to the next.

== Formal exponential at finite degree <j4-exponential>

Let $A=product_(n >= 0) A_n$ be a completed graded commutative rational algebra and let
$A_+=product_(n >= 1)A_n$ be its augmentation ideal. For $F in A_+$ define
$
  exp(F)=sum_(k >= 0) F^k/k!.
$
At total degree at most $N$, only $k <= N$ can contribute, so the restriction is finite. A
nonzero degree-zero term would require another topology or analytic notion of convergence and is
not silently admitted.

#proposition[
  In the quotient $QQ[y]/(y^(N+1))$,
  $
    exp(y)=sum_(n=0)^N y^n/n!.
  $
  Evaluation at $y=1$ gives the exact rational aperture
  $
    E_N=sum_(n=0)^N 1/n!.
  $
]

#proof[
  Every term $y^n$ with $n>N$ vanishes in the quotient. Evaluation is a homomorphism from the
  finite polynomial representative to $QQ$.
]

This is the one-generator face of $e=exp(1)$. The value $E_N$ is not $e$; it is an exact rational
construction with a known positive remainder. The analytic exponential identifies the transported
limit, while the finite generator determines how the next body grows.

== Prime powers are required by the Euler exponential <j4-prime-powers>

Introduce one formal axis $X_p$ for each prime $p$ and the power sums
$
  P_m=sum_p X_p^m,
  quad
  L=sum_(m >= 1) P_m/m.
$

#theorem[
  In the total-degree completion of the commutative rational algebra on the prime axes,
  $
    exp(L)=product_p (1-X_p)^(-1).
  $
]

#proof[
  The formal logarithm gives
  $
    -log(1-X_p)=sum_(m >= 1) X_p^m/m.
  $
  Summing over $p$ yields $L$. Formal exponentiation converts the sum into the product. At every
  bounded total degree, only finitely many factors and powers contribute to a fixed monomial, so
  the identity is coefficientwise well-defined.
]

At degree two,
$
  [exp(L)]_2 = P_2/2 + P_1^2/2.
$
The two summands have different work. For $p != q$, the monomial $X_p X_q$ occurs twice in
$P_1^2$ and division by two gives coefficient one. For a square $X_p^2$, the term $P_1^2/2$
contributes only $1/2$; $P_2/2$ supplies the missing $1/2$. Thus degree two is the semiprime
population only when both distinct and repeated prime incidences are retained.

#corollary[
  Withholding $P_2/2$ leaves an exact residual supported only on the repeated-prime diagonal:
  $
    [exp(P_1)]_2 - [product_p(1-X_p)^(-1)]_2
      = -1/2 sum_p X_p^2.
  $
]

This is not a new classification of integers. It is a coefficient-level statement about repeated
traversal of one formal prime axis. Under the specialization $X_p=p^(-s)$ with
$"Re"(s)>1$, the formal identity becomes the absolutely convergent Euler-product identity for
$zeta(s)$ @dlmf-zeta. The specialization does not supply analytic continuation.

== Aperture growth without replay <j4-aperture>

Write
$
  L=sum_(k>=1)L_k,
  quad
  E=exp(L)=sum_(n>=0)E_n,
$
with $L_k,E_k$ homogeneous of degree $k$.

#theorem[
  The next homogeneous face obeys
  $
    n E_n = sum_(k=1)^n k L_k E_(n-k).
  $ <homogeneous-recurrence>
]

#proof[
  Introduce a scalar $t$ and write
  $L(t)=sum_(k>=1)t^k L_k$ and $E(t)=exp(L(t))$.
  Formal differentiation gives $E'(t)=L'(t)E(t)$. The coefficient of $t^(n-1)$ on the left is
  $n E_n$; on the right it is $sum_(k=1)^n k L_k E_(n-k)$.
]

For the Euler atlas, $L_k=P_k/k$. At degree three,
$
  E_3=L_3+L_1L_2+L_1^3/6.
$
Supplying $L_3=P_3/3$ makes every degree-three monomial coefficient one. If only $P_3/3$ is
withheld, every mixed monomial still has coefficient one while every cube $X_p^3$ has coefficient
$2/3$. The complete oriented residual against the direct Euler product is
$
  -1/3 sum_p X_p^3.
$
The pattern exposes the role of the prime-power logarithmic current at exactly the repeated-axis
faces; it does not require a global recomputation of lower degrees.

For the one-generator exponential,
$
  E_(N+1)(y)=E_N(y)+y^(N+1)/(N+1)!.
$
The measured aperture $8 -> 9$ used
$
  E_8(1)=109601/40320,
  quad
  E_9(1)=98641/36288.
$
The returned degree-eight body was the actual predecessor; the degree-nine term was added once,
and the lower restriction remained exact.

#source-note[
  Derivation and provenance:
  #link("../../RESEARCH/2026-07-22_THE_INFINITE_FORMULA_IS_THE_FINITE_GENERATOR_THE_SEMIPRIME_IS_THE_SECOND_EXPONENTIAL_FACE.md")[
    The infinite formula is the finite generator
  ] and
  #link("../../RESEARCH/2026-07-22_THE_APERTURE_GROWS_BY_ITS_NEXT_HOMOGENEOUS_FACE_THE_GENERATOR_DOES_NOT_RESTART.md")[
    The aperture grows by its next homogeneous face
  ]. Exact machine evidence:
  #link("../../observations/eros-formula-ecology-01/RESULTS.md")[Formula ecology 01] and
  #link("../../observations/eros-formula-aperture-growth-01/RESULTS.md")[Formula aperture growth 01].
]

== Two exact atlases for pi <j4-pi>

The native geometric quantity is a complete oriented turn $Theta$; the conventional half-turn
constant is $pi=Theta/2$. A positively oriented polygon carries a finite sum of exterior turns.
Under the usual regularity assumptions, refinement toward a winding-one curve gives the total
curvature theorem
$
  sum_j Delta theta_j -> integral_gamma kappa dif s = Theta.
$
This is a geometric atlas for $pi$. A separate arithmetic atlas uses exact rational arctangent
partials.

#proposition[
  Machin's identity is
  $
    pi/4 = 4 arctan(1/5)-arctan(1/239).
  $
]

#proof[
  Put $a=arctan(1/5)$ and $b=arctan(1/239)$. The double-angle formula gives
  $tan(2a)=5/12$ and $tan(4a)=120/119$. Hence
  $
    tan(4a-b)
      = (120/119-1/239)/(1+120/(119 dot 239))
      = 1.
  $
  Since $0<4a-b<pi/2$, it equals $pi/4$.
]

For $0<x<=1$, the alternating expansion
$
  arctan(x)=sum_(n>=0)(-1)^n x^(2n+1)/(2n+1)
$
has a remainder bounded in magnitude by the first omitted term, with its sign. Substituting
$x=1/5$ and $x=1/239$ therefore gives exact rational upper and lower enclosures for $pi$ at every
aperture. No decimal or floating geometry is needed for the causal comparison.

The Euler/Dirichlet atlas instead supplies exact finite faces of
$
  zeta(2)=sum_(n>=1)1/n^2=pi^2/6.
$
The last equality is a classical theorem, not an identity inferred from overlap between finite
enclosures. Primes are structural in the Euler path; prime factors inside Machin denominators are
features of that inscription, not evidence that both paths have the same construction.

== Scale and turn meet on the logarithmic cover <j4-scale-turn>

For a nonzero complex path $z(t)=r(t)e^(i theta(t))$,
$
  (dif z)/z = dif(log r)+i dif theta.
$
Its lifted integral is
$
  Xi_gamma=integral_gamma (dif z)/z
    = log(r_1/r_0)+i(theta_1-theta_0+n Theta).
$
The exponential presents the endpoint ratio,
$
  z_1/z_0=exp(Xi_gamma),
$
but forgets the integer winding because
$exp(w+i n Theta)=exp(w)$. Thus $e$ is the unit ratio of normalized logarithmic scale transport,
while $pi$ is half a native turn. Euler's relation
$
  exp(i pi)=-1
$
folds a half-turn lift to the additive inverse; it does not identify magnitude and phase as one
undifferentiated quantity.

This exact scale-turn geometry will later support annular and fractal comparisons. It is not a
claim that $e$ intrinsically means compression or that $pi$ intrinsically means coherence.

== Finite theta involution <j4-theta>

For each lattice shell $n>=0$, retain two formal Gaussian arms
$
  d_n(t)=exp(-pi n^2t),
  quad
  r_n(t)=t^(-1/2)exp(-pi n^2/t).
$
Define the typed involution $J d_n=r_n$, $J r_n=d_n$. At aperture $N$,
$
  Theta_N^d=d_0+2sum_(n=1)^N d_n,
  quad
  Theta_N^r=J Theta_N^d.
$
A finite raw truncation is not self-dual. Its complete decomposition is
$
  S_N=(Theta_N^d+Theta_N^r)/2,
  quad
  A_N=(Theta_N^d-Theta_N^r)/2,
$
with $J S_N=S_N$ and $J A_N=-A_N$.

#lemma[
  The aperture update
  $
    S_(N+1)=S_N+d_(N+1)+r_(N+1),
    quad
    A_(N+1)=A_N+d_(N+1)-r_(N+1)
  $
  preserves the invariant and anti-invariant eigenspaces exactly.
]

#proof[
  Apply $J$, use $J d_(N+1)=r_(N+1)$ and $J r_(N+1)=d_(N+1)$, and collect the two signs.
]

For $n>0$, formal Mellin transport gives
$
  cal(M)[d_n](s)=Gamma(s/2)(pi n^2)^(-s/2),
$
$
  cal(M)[r_n](s)=Gamma((1-s)/2)(pi n^2)^(-(1-s)/2).
$
Substitution $s -> 1-s$ exchanges the receipts and fixes $s=1/2$. The isolated $n=0$ endpoint
requires separate analytic treatment. A finite symmetric projection proves only invariance under
the declared $J$; it does not prove raw theta reciprocity.

== The residual is a moving boundary <j4-residual>

Let the complete direct and reciprocal charts be split at aperture $N$:
$
  C_c=P_(c,N)+T_(c,N),
  quad c in {d,r}.
$
If an inherited Poisson theorem identifies $C_d=C_r$, then
$
  P_(d,N)-P_(r,N)=T_(r,N)-T_(d,N).
$
The visible finite mismatch is exactly the complementary tail mismatch.

#proposition[
  Moving shell $N+1$ from each tail to its partial preserves the balance identity above. In the ordered basis
  $[d_(N+1),r_(N+1)]$,
  $
    Delta(P_d-P_r)=[2,-2]
    =Delta(T_r-T_d).
  $
]

#proof[
  Substitute
  $P_(d,N+1)=P_(d,N)+2d_(N+1)$ and
  $T_(d,N+1)=T_(d,N)-2d_(N+1)$, together with their reciprocal counterparts. Both sides of
  the balance identity receive the same coefficient vector.
]

#boundary-transfer-figure() <boundary-transfer>

The tail is not an infinite active population. Its finite generative description retains the next
shell, multiplicity, hand, positive domain, and recurrence
$
  d_(n+1)=d_n exp(-pi t(2n+1)),
  quad
  r_(n+1)=r_n exp(-pi(2n+1)/t).
$
At aperture $4 -> 5$, the exponent gap carried exactly
$6^2-5^2=11$. The Poisson law was inherited from classical analysis, not discovered by the
machine.

#source-note[
  The finite involution and boundary-transfer measurements are
  #link("../../observations/eros-theta-mellin-aperture-01/RESULTS.md")[Theta/Mellin aperture 01]
  and #link("../../observations/eros-poisson-tail-transport-01/RESULTS.md")[Poisson tail transport
  01]. Classical theta and zeta identities are recorded in @dlmf-theta and @dlmf-zeta.
]

== The exact RH boundary <j4-rh>

The completed zeta function satisfies a functional equation under $s -> 1-s$. After centering
$z=s-1/2$, the involution is $J(z)=-overline(z)$ and its fixed locus is $"Re"(z)=0$, equivalently
$"Re"(s)=1/2$. Functional population symmetry means zeros occur in the corresponding orbits.
The Riemann hypothesis is the stronger pointwise assertion that every nontrivial zero lies on the
fixed locus.

The derivations above establish why the half-density appears:
$
  "quadratic metric" -> "diffusion length " sqrt(t)
  -> "reciprocal factor " t^(-1/2),
$
$
  "reciprocal factor " t^(-1/2) -> "theta duality"
  -> "Mellin reflection" -> "fixed coordinate " 1/2.
$
They do not force each zero onto that coordinate. Opposed off-line residuals can preserve
aggregate symmetry while neither point is fixed.

#open-problem[
  Construct a complete arithmetic carrier whose trace is the completed explicit formula on an
  admissible test space and whose relevant quadratic form is positive exactly when every
  nontrivial zero lies on $"Re"(s)=1/2$. Show that the finite prime-power, archimedean, aperture, and
  tail transitions converge to this carrier without assuming the desired positivity.
]

This is the honest remaining bridge toward Weil's positivity criterion @weil1952. A finite
positive coefficient pairing, a symmetric theta projector, a finite zero census, or a recurring
visual shell cannot replace it. The project therefore has a precise RH-facing programme, but no
RH proof.

#evidence-note(
  [Finite exponential, Euler, aperture, involution, and boundary-transfer relations form one exact
  generator network.],
  [Formal derivation plus bounded exact rational/integer measurement. Classical analytic laws are
  externally inherited.],
  [Formula §§CIII, CXLVIII-CXLIX; four exact formula-ecology results; DLMF theta/zeta identities.],
  [Analytic continuation, the completed explicit-formula trace carrier, support-covariant
  positivity, and RH remain open.],
)
]

# Weil sign partitions and the semilocal positive-carrier attempt

**Date:** 2026-09-23. **Status:** source audit, exact formal returns, exact symbolic experiment, and a narrowed RH proof attempt. This does not prove RH. **Steering:** Brandon asked whether positive and negative terms from intersecting generator series can be grouped by common denominators and their distributions. The answer is yes at the prime and archimedean mode receivers, but the sign of the completed Weil form is an operator-order question on the same admissible current, not a comparison of raw term counts.

## Source and the complete receiving law

For a smooth compactly supported logarithmic current a, let h=a*a^sharp be its returned autocorrelation and G its centered Mellin/Laplace response. The completed Weil receiver in the repository's sign convention is

  Q_W(a)=polar(h)−prime(h)−archimedean(h).

For the actual ξ source the explicit formula identifies this with the multiplicity-weighted zero receiver after the complete limit passage. On the fixed line a Weil square reads |G(ρ)|². Off the line it reads a paired product of distinct reflection hands, whose sign is not automatic. RH/ZeroCombPairing.lean owns that off-line cross term; RH/GlobalWeilFinishLine.lean specifies positivity and separation at one complete receiver. RH/PrimeSideConverges.explicit_formula_classical_weil **already proves** a global vertical-line zero/prime-side limit for every declared WeilTestFunction. The circular-disc atlas and the identification with ExplicitFormulaReceiver's polar−prime−archimedean logarithmic-line form remain a separate interface. Do not relabel the whole explicit formula absent.

The July 20 [adjoint/trace record](2026-07-20_THE_ADJOINT_RETURNS_ON_THE_UNITARY_SEAM_THE_TRACE_OWES_A_POSITIVE_CARRIER.md) gives the complete Mellin current and test-function lifecycle. The July 23 [archimedean/semilocal record](2026-07-23_THE_ARCHIMEDEAN_REMAINDER_HAS_AN_AMPLITUDE_THE_PRIME_ENTERS_THROUGH_APERTURE_OVERLAP.md) derives a positive base remainder B₂, prime overlap and the exact missing semilocal update (VI.2). The July 24 [Euler resolvent record](2026-07-24_THE_EULER_RESOLVENT_FOLDS_THE_PRIME_TOWER_THE_SUCCESSOR_OWES_ONE_CROSS_CHANNEL_CONTRACTION.md) already derives the full prime-power resolvent and the cross-channel contraction target. This continuation formalizes sign partitions and tests false shortcuts; it does not claim to have discovered those standing operator identities.

## Prime generator: a common positive denominator and signed phase populations

For a prime p, put q=p^(−1/2)∈(0,1), U=translation by log p on the logarithmic current, and let u=e^(iθ) be one unit spectral phase. The repeated-generator series has the exact finite remainder

  (1−qu) Σ_(m=1)^N (qu)^m = qu−(qu)^(N+1).

Since |q|<1, its full operator series converges for unitary U to qu/(1−qu). RH/PrimePhasePartition.lean proves the exact scalar reading

  Re[qu/(1−qu)]
    = (q cos θ−q²)/(1−2q cos θ+q²),
  D_q(θ)=1−2q cos θ+q²=|1−qu|²>0.

The positive/negative partition is therefore exact: positive for cos θ>q, zero at cos θ=q, negative for cos θ<q. PrimePhasePartition.prime_phase_nonneg_iff binds this algebra to the actual coefficient q=1/√p for every p≥2. This is **not** a partition by positive and negative coefficients: every q^m is positive, while the transported phase cos(mθ) changes the return. The normalized Euler-resolvent identity in the July 24 record gives the same sign as a difference of endpoint norms.

For a source vector a, the spectral theorem supplies its positive phase measure μ_a. Formally, after the declared Fourier/Plancherel convention, the prime receiver is the integral of 2 log p·(q cos θ−q²)/D_q(θ) against μ_a. The two signed populations are the restrictions of this *same source measure* to cos θ>q and cos θ<q, weighted by the full rational kernel. PrimePhasePartition.finite_phase_distribution now proves the finite-source version: the signed current equals positivePhaseMass minus negativePhaseMass, both masses are nonnegative under source-unit phases and nonnegative weights, and both retain their actual addresses/weights. A count of modes or a density chosen independently of a loses the Holon's phase and amplitude. The Fourier realization and exchange with the completed prime sum are not new Lean theorems here.

There is an important aperture distinction. RH/PrimeApertureCorrelation.lean proves that if the logarithmic current is supported in [−A,A], its autocorrelation at |t|>2A is zero; prime-power contacts past m log p>2A vanish for that receiver. RH/WeilApertureNoGo.lean proves P_L U_t P_L=0 whenever t≥L, so at the positive archimedean base aperture L=log 2 **every** prime-power translated arm disappears if one projects immediately back into that old space. A full unapertured phase resolvent cannot be read as a single-sign certificate for a compact test, and fixed-aperture conjugation cannot be the semilocal successor.

### A collective finite common denominator

For a finite set S of admitted primes at one phase frequency ω, write D_p(ω)=1−2q_p cos(ω log p)+q_p²>0 and n_p(ω)=2 log p·(q_p cos(ω log p)−q_p²). Then the joined finite-prime multiplier has the exact common-denominator form

  Σ_(p∈S) n_p(ω)/D_p(ω) = N_S(ω)/D_S(ω),
  D_S(ω)=∏_(p∈S)D_p(ω)>0,
  N_S(ω)=Σ_(p∈S)n_p(ω)∏_(r∈S,r≠p)D_r(ω).

PrimePhasePartition.finite_common_denominator and finite_common_denominator_nonneg_iff now prove this finite cross-multiplication and its sign law for any family of positive denominators. This answers the proposed "dominant positive/negative partition" at finite source scope: N_S≥0 and N_S<0 partition the **joint** phase population, while the source spectral measure supplies the quantity in each part. The sign of an individual prime need not match the sign of the joined numerator. An infinite product of these denominators is not licensed by the finite identity, and the polar endpoint coupling is not a diagonal phase multiplier. The complete ξ form must retain those boundaries and the source's limit law.

## Archimedean generator: paired series and a second sign threshold

The actual RH/ArchimedeanReceiver has, in its sign convention,

  A(h)=h(0)(log π+γ_E)
      +2∫₀∞ [e^(−x/2)h_even(x)−e^(−2x)h(0)]/(1−e^(−2x)) dx.

The two numerator arms share the denominator. For x>0, expanding its geometric generator produces paired modes

  P_m(x)=e^(−λ_m x)h_even(x)−e^(−(2m+2)x)h(0),
  λ_m=2m+1/2.

RH/ArchimedeanModeSign.lean proves the exact **finite** geometric identity for the actual numerator, valid even at x=0 without dividing there. Under the additional autocorrelation/Fourier passage, one paired mode has symbol

  k_m(ω)
    =2λ_m/(λ_m²+ω²)−1/(m+1)
    =[(3/2)λ_m−ω²] /
      [(m+1)(λ_m²+ω²)].

The denominator is positive; Lean proves k_m(ω)≥0 iff ω²≤(3/2)λ_m. It also checks k₀(0)=3 and k₀(2)=−13/17. Thus each mode has positive low-frequency and negative high-frequency populations. Summing its two arms separately would discard their cancellation at x=0. The infinite paired integral/Fourier interchange still needs its test-function and domination hypotheses; the checked theorem is the finite numerator identity and algebraic sign partition.

The polar receiver couples the two endpoint Mellin values G(0) and G(1). It is a finite-rank *off-diagonal* part of the completed form, not generally a pointwise function of the real Fourier frequency. Therefore even fully known positive and negative prime/archimedean scalar densities cannot by themselves decide Q_W. One needs the complete matrix-valued pairing or a contemporary positive amplitude with those boundary ports attached.

## Exact controls on the proposed sign grouping

RH/PrimeAutocorrelationObstruction.lean proves a two-site autocorrelation Gram is PSD although its first-prime lag can be positive or negative. The actual truncatedPrimeReceiver at cutoff 2 reads the positive von Mangoldt weight times that signed lag. A diagonal reservoir d completes the first-prime two-site form d(x²+y²)−2wxy exactly iff d≥w, w=Λ(2)/√2. This is a finite threshold, not an identification of d with the actual polar/archimedean source.

The [exact symbolic experiment](../experiments/weil_positive_receiver/README.md) uses one smooth two-translate generator g_c=φ+cφ(·−log 2), with rational c=k/d and no sampled values. Its positive Gram remains positive while the prime, local archimedean and polar signs have different exact thresholds: c=0, c=√2−1, and c=−1/√2. On the d=8 coefficient population, the negative counts are respectively 8, 5 and 3; on d=16 they are 16, 10 and 5. The verifier checks them with rational arithmetic and integer-square comparisons. These are distributions of *chosen generator coefficients*, not ξ zeros or a completed Weil positivity result. They differ from the standing 12/14-step experiment, which already enclosed finite joined arithmetic Gram matrices against certified zeros.

A second exact control in RH/PositiveLaplaceOffLineControl.lean uses positive bilateral-Laplace masses at logarithmic addresses 0,±1:
  F(s)=1+(6/13)(e^(s−1/2)+e^(−(s−1/2))).
Lean proves F is entire and reflection-invariant yet vanishes at s=1/2+log(3/2)+iπ, strictly inside 0<Re s<1 and off the fixed line. Positive source masses plus reflection and strip placement do **not** force the ξ conclusion. RH/ThetaHankelPositive.lean proves finite theta Hankel forms are genuine sums of squares from positive lattice modes, but no map identifies those forms with the complete Weil receiver. The control shows why such a map is essential.

## The remaining Holonic proof target

The archimedean base positive operator B₂ exists on its constrained Sonin aperture. For a finite set of admitted primes S and a larger support R, the missing source object is a semilocal lift 𝓛_(S,R) and positive remainder B_(S,R), with exact transported material law

  𝓛_(S∪{p},R)* B_(S∪{p},R) 𝓛_(S∪{p},R)
  − 𝓛_(S,R)* B_(S,R) 𝓛_(S,R)
  = − W_(p,R) − K_(S,p,R).

Here W_(p,R) is the signed prime-overlap form and K_(S,p,R) the turned-aperture connection. This is equation (VI.2) of the July 23 record. Equivalently, the July 24 record packages predecessor amplitude, prime resolvent and Sonin projection into source maps X and Y with completed defect ||Xf||²−||Yf||². A source-constructed cross-channel contraction Γ:Xf↦Yf would yield a positive successor amplitude. Defining Γ only after assuming that defect nonnegative would simply assume Weil positivity.

The requested positive/negative partitions sharpen the unknown: Γ must route *source-weighted signed phase populations* between the positive archimedean reserve, expansive prime phases, polar endpoints and newly opened aperture. It cannot be block diagonal or a common scalar denominator pasted onto separately positive terms. The first noncircular proof step is to construct the enlarged-domain semilocal Poisson/Fourier/Sonin colligation and verify X*X−Y*Y=Z*Z with Z built from that source before claiming contractivity. One must then continue over supports and primes, identify the global log-line receiver with the already proved vertical explicit-formula limit, and construct a complete admissible test family and off-line separator. Those are concrete missing maps, not achieved fields of a Holon declared positive by definition.

## Verification and next discriminating work

The new RH leaves PrimeAutocorrelationObstruction, PrimePhasePartition, PrimeApertureCorrelation, ArchimedeanModeSign, WeilApertureNoGo, ThetaHankelPositive and PositiveLaplaceOffLineControl compiled with only standard Lean axioms and no sorryAx. Framework.Dynamics imports them and compiles. The exact symbolic receipt verifier passed. The source-derived finite sign populations and common denominators are proved at their stated scopes; the complete Weil positive carrier is not.

A useful next experiment is a *successor*, not another static finite Gram: on an actual finite current basis at the first aperture enlargement, compute the source-defined prime-overlap and aperture-connection matrices, transport the existing B₂, and solve the exact polarized update for a positive B_(S∪{p},R), retaining the null fibre. Verify the same operator on a changed basis and a second prime. Its success would be a bounded realization of the required source map; only a uniform construction with the exact log-line/vertical receiver bridge could support the global proof.

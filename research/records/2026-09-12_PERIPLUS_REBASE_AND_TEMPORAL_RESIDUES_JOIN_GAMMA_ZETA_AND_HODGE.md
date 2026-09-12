# Periplus, rebasing and temporal residues: Gamma, zeta, Hodge and inference

[project-postulate] Brandon's latest September 12 direction asks for the moduli/periplus
complement of mode exclusion, and for Gamma, Newman time, Shannon information, RH and Hodge to
be developed together. His shattered-glass example concerns reconstructing compatible causal
classes from physical residue, not reversing the exact microscopic occurrence or storing its
history. The earlier direct ruling is already quoted in `TABLET_THE_OPERATIONS` §5: time parity,
chronology, invertibility and reconstruction are not identical. This return makes the maps
explicit and adds their formal and executable consumers.

## 1. What a residue is depends on the grip

[definition] Let q:E→Q be a linear receiver and s:Q→E a chosen section on its actual admitted
range, with qs=id. The coordinates are

`a=qx`,   `r_s(x)=x-s(a)`,   `x=s(a)+r_s(x)`,   `q r_s(x)=0`.

The source is not intrinsically a representative plus waste. The section determines which
part serves as representative and which part is its complementary residue. For a second
section `s'=s+h`, the displacement h is kernel-valued and

`r_s'(x)=r_s(x)-h(a)`.

The source does not change when the representative and residue compensate together. A
right-inverse section is supplied here, not assumed for a target outside the actual range.

[proved-derived; formal-checked] New `Foundation/SectionResidual.lean` proves these identities
for a possibly nonlinear section of a real linear receiver, as well as the three-section
cocycle `h_13=h_12+h_23`. It composes the existing `Holon.Rebase.preimageFibreEquiv`,
`Algorithm/Rebase` execution conjugacy and `EuclideanResidueTransport` interpretation:
`n=m k+r` is the integer instance, retaining both residue and oriented winding. Equality
modulo m identifies the residue face, not the source integer.

[definition] Four uses of modulus now have their actual maps, rather than being collapsed
by a shared name:

| Object | Receiver or construction |
|---|---|
| Complex modulus | `z→|z|`; its phase fibre remains distinct from its magnitude |
| Arithmetic modulus | `n→n mod m`; the complete chart retains signed quotient/winding |
| A family of realizations modulo rebase | An orbit/equivalence class under specified invertible chart maps; stabilizers and singular/rank-changing strata may remain |
| Mode coefficient | A coordinate in a chosen realization; it becomes a residue only relative to a further section, quotient or reference split |

[definition] An invertible mode rebase B transforms the entire realization:

`E'=BE`,   `D'=DB⁻¹`,   `m'=Bm`,   `U'=BUB⁻¹`.

Then `D'm'=Dm` and `U'E'=E'T` whenever `UE=ET`. For a time-dependent frame `x=B(t)c`,
the physical law `x'=Ax` becomes

`c'=(B⁻¹AB-B⁻¹ B')c`.

The second term is the changing-frame connection term. Dropping it is not a rebase of the
same evolution. `Transport/ChangingReceiver` already retains that differential chart term.
Zero reconstruction defect of a rebase therefore does not assert zero residue in its source.

## 2. Periplus is an oriented return comparison

[definition] The dialect uses periplus for the outward/return relation with its asymmetric
time orientation. An explicit operator chart is an outward passage F and an admitted return
R, with composite `P=RF`; after transporting endpoints to the same comparison chart, its
residue is `(P-I)x`. R need not be F⁻¹. A passive rebase sends P to B P B⁻¹ and its residual
to B(P-I)x. This is a residual of the composed conduct, not a demand to retain its raw path.

[proved-derived] Pure section changes telescope: `h_12+h_23+h_31=0`. The existing Cartier
overlap cocycle likewise gives trivial pointwise overlap loops. Nontrivial holonomy therefore
requires actual connection/path transport, not merely several changes of notation. On a
logarithmic covering a closed complex phase can return to the same exponential while its
lift differs by `2πik`. The standing `PhaseCarrier` and integer residue owners retain that
winding as a coordinate/fibre, without archiving the traversed samples.

[definition] This separates three useful residuals: a kernel-valued section complement, an
analytic tail beyond a chosen head, and a returned path/connection mismatch. They can be
composed by explicit source/receiver maps; none is universally identical to amplitude or to
the others. Changing a head boundary or modal basis changes their coordinates, not the
complete declared return.

## 3. Gamma supplies a nontrivial coefficient-and-base-point cocycle

[proved-derived; formal-checked] The existing `RH/FlowedGamma.integral_flowedTerm_eq_shift`
already constructs every admitted integer source term from the single flowed Gamma generator.
For `L=ln|n|`, `n≠0`, its algebraic expression is

`I_(t,n)(z)=exp(-tL²-zL) Γ_t(z+2tL)`.

The term's amplitude and its generating argument both change. The new
`Transport/GaussianRebase` writes `A_t(L,z)=exp(-tL²-zL)`, `S_t(L,z)=z+2tL`, and proves

`A_t(L,z) A_t(M,S_t(L,z)) = A_t(L+M,z)`.

Thus `O_L f(z)=A_t(L,z) f(S_t(L,z))` obeys `O_L O_M=O_(L+M)` and `O_L O_-L=id`.
`FlowedGamma.integral_flowedTerm_eq_rebase` now binds the actual source owner to that action.
This is a composition theorem, not a new source family inferred by naming one.

[proved-derived; formal-checked] Returning only the amplitude at the old base gives instead

`A_t(L,z) A_t(-L,z)=exp(-2tL²)`.

The Gaussian residue is exactly the consequence of omitting the rebased argument. Retiming
also has two coupled faces:

`A_(t+δ)(L,z)=A_t(L,z) exp(-δL²)`,

`S_(t+δ)(L,z)=S_t(L,z)+2δL`.

The new owner proves these identities over complex coordinates; time and logarithmic source
shifts are specialized to the real chart of the consuming analytic law.

[definition] Analytic admission remains important here: the single-event Gaussian representation
has its integrable positive-time domain, and its zero-time right-half-plane Gamma expression.
The formal integral is a totalized expression, not a license to sum divergent individual
whole-line terms at negative time. `RH/FoldedKernel` instead reflects the complete theta source
first and supplies the integrable positive-half-line xi kernel at every real Newman time.
Those two existing source owners must not be interchanged silently.

[proved-standard] Ordinary Gamma rebasing is
`Γ(z+n)=(z)_n Γ(z)`, retaining the admissible base germ and poles. Differentiation makes the
one-step value/derivative action `[[z,0],[1,z]]`; this is already the exact block in
`generator_factorization.rs`. Its completed zeta role is

`ξ(s)=½s(s-1)π^(-s/2)Γ(s/2)ζ(s)`,   `ξ(s)=ξ(1-s)`.

Gamma supplies the continuous Mellin normalization and reflection factor, not a dispensable
scalar prefactor. The repository's single integer-event γ has a 1/4 convention; it is not
the entire completed ξ. [DLMF reflection formulas](https://dlmf.nist.gov/25.4).

## 4. Shannon information, prime modes and zeta

[definition] For σ>1, the positive Dirichlet family is

`p_σ(n)=n^(-σ)/ζ(σ)`,   `A(σ)=ln ζ(σ)`,   `E(n)=ln n`.

Here σ is a declared inverse-temperature/code parameter, not physical time. Absolute
convergence permits the logarithmic moments and their derivatives in this domain.

[proved-derived] Directly substituting `ln p_σ(n)=-σ ln n-A(σ)` yields

`H₂(p_σ)=[A(σ)-σA'(σ)]/ln2`,

`D_KL,₂(p_σ||p_ρ)=[A(ρ)-A(σ)-(ρ-σ)A'(σ)]/ln2`.

Differentiating the absolutely convergent partition gives
`A'=-E_σ[ln n]`, `A''=Var_σ(ln n)≥0`. The same variance is its Fisher information in σ,
and `dH₂/dσ=-σ Var_σ(ln n)/ln2`. Thus the zeta partition, surprise, code mismatch and
statistical response share one explicit exponential-family construction. These infinite-family
derivations are recorded here; the new executable check below is finite and exact.

[proved-derived] Unique prime factorization gives `ln n=Σ_p ν_p(n)ln p`, and the absolutely
convergent Euler product gives independent geometric prime occupations

`Pr(ν_p=k)=(1-p^(-σ))p^(-kσ)`.

Prime generators are uniquely factored while their occupation coefficients retain multiplicity.
They are not binary fermionic occupations. Ideal lengths
`σ log₂ n+log₂ ζ(σ)` have Kraft mass one; merely assigning `log₂ n` would give a divergent
Kraft sum. Integer codewords additionally carry rounding, framing and decoder costs, as the
compression canon already distinguishes.

[proved-derived] The same family has a complex transform

`ζ(σ+iω)/ζ(σ)=E_σ[exp(-iω ln n)]`.

This joins the logarithmic energy/code ruler to phase transport. It holds for σ>1; analytic
continuation into the critical strip is not continuation of that positive probability law.
In particular an entropy inequality in this half-plane does not by itself place critical
zeros. The previously derived lifted complex cross-entropy retains a phase-difference face
alongside the real KL face; a phase average still does not replace the complete coherent
transform or its winding fibre.

[proved-standard] Gamma also links zeta directly to the two occupation kernels:

`Γ(s)ζ(s)=∫₀∞ x^(s-1)/(exp x-1) dx` for Re s>1,

`Γ(s)η(s)=∫₀∞ x^(s-1)/(exp x+1) dx` for Re s>0,

where `η(s)=(1-2^(1-s))ζ(s)` with its removable value at s=1. These are Mellin transforms
of the Bose and Fermi occupation shapes. They connect the earlier sigmoid/exclusion receiver
to Gamma and zeta through an actual integral, with no inference that primes are particles or
that the transform alone supplies a physical density of states.
[DLMF integral representations](https://dlmf.nist.gov/25.5).

## 5. Newman time is already the complement of spectral position

[definition] Write standard Newman time τ separately from spectral z and physical laboratory
time. The existing critical chart proves

`H_τ(z)=⅛ heatE(-τ/4,ξ,½+iz/2)`,   `Λ_std=4Λ_DN`.

`Re(½+iz/2)=½-Im(z)/2` identifies the critical seam with real z. The source/coordinate
owners are `RH/CriticalChart`, `FoldedKernel`, `RealZeroTimes` and `DeBruijnSeal`.

[proved-standard] The standard family obeys `∂_τ H=-∂_z²H`, with all zeros real exactly for
`τ≥Λ_std`. Rodgers–Tao proves `Λ_std≥0`; hence RH is equivalent to `Λ_std=0`.
[Rodgers–Tao, published corrected version](https://arxiv.org/html/1801.05914v5).
The published numerical upper bound `Λ_std≤0.2` follows from the Polymath estimates and
Platt–Trudgian's verified height, explicitly their Corollary 2.
[Platt–Trudgian §3.4](https://arxiv.org/html/2004.09765v1).
This is a verified published bound, not a claim that this review audited every newer bound.

[established-bounded; source-inspected] A September 12 search also found newer public
announcements, including a claimed 0.1787854 bound with an audit repository. Their complete
analytic/certificate chains were not checked here, so they do not update the repository's
proved threshold. The present Lean bridge retains its own standard `[0,1/2]` bound; importing
a stronger published numerical estimate into that proof tree is a separate source binding.
[Inspected announcement](https://www.judegomila.com/posts/riemann-lambda-0.1787854).

[proved-standard] Spatial strip control has a precise temporal consequence: under the de Bruijn
source hypotheses, zeros confined at τ₀ to `|Im z|≤Δ` are confined after time h≥0 to
`|Im z|≤sqrt(max(Δ²-2h,0))`. Thus the strip is cleared by `h=Δ²/2` and
`Λ_std≤τ₀+Δ²/2`. This is a parabolic space/time conversion, not a new physical light-cone
law. [Polymath's heat-flow framework](https://arxiv.org/html/1904.12438v2).

[proved-derived; formal-checked] The existing `RH/ThresholdRefinement` proves the exact
quadratic source `P_h(z)=z²+a²-2h`. Its nonreal pair reaches a double root when `h=a²/2`,
then becomes real. The polynomial identity and explicit below-threshold nonreal roots are
already checked.

[proved-derived] In the two-real-root chart, writing the gap g gives

`g(h)²=g(h₀)²+8(h-h₀)`.

The displayed gap equation follows directly by solving that polynomial. It is the
smallest example of a spatial gap encoding a remaining backward collision time `g²/8`.
For a full zero population the other zeros contribute and this pair-only clock is not exact.

[proved-standard] On the admitted simple-real-zero interval the full dynamics is
`x'_k=2 Σ_(j≠k)1/(x_k-x_j)`, with the prescribed limiting/cutoff interpretation for the
infinite xi population. The finite analogue is gradient descent of
`V=-2Σ_(j<k)ln|x_j-x_k|`. Its repulsion barrier and the Vandermonde factor vanish/diverge at
colliding modes in complementary readings. This is a concrete variational link to learning
mechanics; the infinite xi energy requires its actual boundary and renormalization estimates,
not the unrestricted finite sum. [Rodgers–Tao, equation (5) and §§5–7](https://arxiv.org/html/1801.05914v5).

[definition] Mode independence does not yet prove that xi has no nonreal zeros. A Vandermonde
can be nonzero for distinct complex points, and a Gram matrix can be positive definite for
their independent representations. Nor does RH itself assert simple zeros at the threshold.
The stronger needed source-specific statement concerns the placement of the entire xi zero
family at τ=0. The standing square-refinement equivalence records that missing closure; the
generic positive-threshold quadratic is an explicit reason not to infer it from exclusion alone.

[proved-derived] There is also a direct Shannon-time bridge on the actual positive folded
kernel. Set `M(τ)=H_τ(0)` and
`dμ_τ(u)=exp(τu²)Φ_std(u)du/M(τ)` on u>0. Then

`H_τ(z)/H_τ(0)=E_(μ_τ)[cos(zu)]`,

`∂_τ ln M=E_(μ_τ)[u²]`,   `∂²_τ ln M=Var_(μ_τ)(u²)`.

The super-exponential kernel controls these differentiations. Relative entropy between two
such measures is
`D_KL(μ_τ||μ_ρ)=(τ-ρ)∂_τ ln M(τ)+ln M(ρ)-ln M(τ)` in nats.
Thus temporal tilting, information geometry and spectral cancellation use the same source
measure. Positivity of that measure or of its Fisher variance still does not establish that
all complex zeros of its cosine transform are real.

## 6. Hodge classes and modes: the precise equivalence and time complement

[proved-derived; formal-checked] The standing finite Hodge source defines
`δ=d†`, `Δ=dδ+δd`, `H=kerΔ=ker d∩kerδ`. It proves

`E=range d ⊕ range δ ⊕ H`,   `H ≃ ker d / range d`.

`HodgeHarmonicRepresentative` gives one harmonic representative per cohomology class;
`HodgeLeastNorm` gives its least-norm property. This is an exact setting in which a class is
represented by a unique balanced mode, once metric and differential are fixed. The zero
eigenvalue can have a multidimensional eigenspace: equal eigenvalue does not identify modes.

[proved-derived; formal-checked] New `Physics/TemporalHodgeResidue` constructs the actual
Euler heat step `T_a=I-aΔ`. It fixes harmonic vectors, preserves their orthogonal complement,
and carries exact residues by

`T_a(db)=d(b-aδdb)`.

Consequently `T_a(h+db)=h+d(b-aδdb)`: the class remains while its representative's transient
part changes. These are checked algebraic laws; stable decay of explicit Euler additionally
requires a suitable step and spectrum. `HodgeGreenOperator` supplies the complementary
inverse `x=Hx+ΔGx`, not an inverse of every source receiver.

[proved-derived] For the finite self-adjoint nonnegative Laplacian, continuous heat gives
`x(t)=h+Σ_(λ>0)e^(-νλt)c_λv_λ`. With gap λ₁>0,
`||x(t)-h||≤e^(-νλ₁t)||x(0)-h||`; resolving an initial residue R down to tolerance ε>0
requires `t≥ln(R/ε)/(νλ₁)` when R>ε. This is the temporal complement of a spectral gap.
Backward reconstruction instead amplifies mode uncertainty by `e^(νλt)`. Exact finite
invertibility and stable reconstruction are therefore different properties.

[proved-derived] If the metric/boundary changes, so does the harmonic projection H_t. In a
common differentiable carrier, `x'=-Δ_t x` and `H_tΔ_t=0` give
`(H_t x)'=H'_t x`. Thus the changing harmonic representative has the same moving-grip term
as the mode rebase. Fixed-topology de Rham classes and their metric-dependent harmonic
representatives must not be identified with one permanently fixed vector. Topology or boundary
changes require their actual comparison maps.

[definition] The Hodge conjecture additionally asks for a supported algebraic source:
`cl:Z^p(X)_Q→H^(2p)(X;Q)∩H^(p,p)(X)`. The existing constructive/primitive-cut owners
identify its lift population with a Preimage Fibre. Finding a harmonic representative is not
constructing an algebraic cycle. This is the shared synthesis problem with solver/learning
applications: recover a realizer of a constrained class; an empty fibre is meaningful, and
multiple realizing occurrences need not be identified. [Clay's Hodge description](https://www.claymath.org/millennium/hodge-conjecture/).

## 7. Glass, forensic inference and the return stroke

[interpretation] In Brandon's glass comparison, source variables include contact impulse,
pre-stress, geometry, defects, gravitational loading and resonant drive. They map through a
constitutive evolution to fracture surfaces, fragment motion and emitted heat/acoustic fields.
The inverse problem is the compatible source/class fibre of those measured residues. Its
falsifier is a claimed unique cause confronted by two admitted different causes giving the
same measured pattern. This turn supplies no calibrated glass-fracture simulation and makes
no assertion that fragments alone uniquely encode an entire prior trajectory.

[proved-derived] In a linearized source chart y=Aθ, quadratic fitting has differential
`dL_θ(v)=<Aθ-y,Av>=<A†(Aθ-y),v>`. The backward pass pulls back a comparison covector; it
does not apply A⁻¹. For the scalar contraction A=1/2, A†A=1/4 while A⁻¹A=1. This elementary
separator explains why a forward/adjoint learning cycle can infer a generating relation
without physically reversing dissipation. Changing frames also transports the adjoint's
metric, as the existing production-frame adjoint owners require.

[definition] A reconstruction is a new admitted realization matching the chosen class/receiver,
possibly with a different microscopic arrangement. An intervention can prepare such a state
over time while exporting entropy. It does not make the original uncontrolled dissipative
evolution inverse, and forensic inference need not prepare a physical reconstruction at all.
The relevant memory can be coefficients, joint constraints, modes and their residuals.

[interpretation] The proposed self/auto connection is structural reflexivity: a system's own
organization supplies the generator and constraints through which it infers, acts and revises
its operative representation. RH's constrained zero dynamics, Hodge's source-realizer problem
and ML's generative inference share explicit variational, spectral and quotient mathematics
above. This is a theorem-development programme, not an inference of subjective awareness in
particles or arbitrary computation, nor a proof that solving RH is equivalent to intelligence.
The 3Blue1Brown remark is Brandon's reported inspiration; no unlocated quotation is attributed.

## 8. Productive returns and verification

[established-bounded; implemented-exact] `KernelModeSummary::rebase` now takes an actual
invertible rational basis and stages `E'=BE`, `D'=DB⁻¹`, `m'=Bm` together. It returns the new
receiver owner; old-frame actions/readers are not silently reused. Singular or wrong-shaped
bases leave the continuing summary unchanged. This is a passive chart operation, not a new
ecology, event archive or physical inverse. Its work account counts the three contractions;
the matrix inverse is separate setup work.

[established-bounded; computational-witness] The earlier six-source/two-mode application now
rebases by `B=[[1,1],[0,1]]`: modal `(mass,real,imaginary)` rows change from `(7,12,13)` and
`(6,9,12)` to `(13,21,25)` and `(6,9,12)`. All decoded queries remain exact; phase transport
and source-action compilation then operate in the returned frame. The new test also returns
through B⁻¹ and checks a singular rebase preserves the original frame/current. The
[exact modal receipt](2026-09-12_periplus_receipts/modal-rebase.json) keeps both charts.

[established-bounded; computational-witness] The existing `receiver_code_cost` application now
checks the finite Dirichlet population n=1,…,4 at exponents 2 and 3 through public symbolic-log
owners. Partitions are `205/144` and `2035/1728`; source probabilities are
`(144,36,16,9)/205`. It verifies `H₂=log₂Z₂+2E₂log₂n`,
`H₂(p₂,p₃)=log₂Z₃+3E₂log₂n` and their exact KL difference. The
[information receipt](2026-09-12_periplus_receipts/zeta-information.json) retains these values
and the unchanged channel/generator checks. This finite construction does not substitute a
truncated positive distribution for the critical-strip xi source.

[established-bounded; process-audit] The combined
`bash tools/lean_check.sh ElementaryHolonics.Framework.Information ElementaryHolonics.Framework.Physics ElementaryHolonics.RH.FlowedGamma`
completed under Lean 4.33.0 (9151 build jobs, mostly replayed). Earlier focused Gaussian,
section and Hodge checks also passed. The [formal excerpt](2026-09-12_periplus_receipts/formal-terminal.txt)
retains the new-owner results and completion. New Gaussian axiom prints use only the standing
`propext`, `Classical.choice` and `Quot.sound`; the command rejects sorry-based declarations.

[established-bounded; process-audit] The exact-linear Cargo selection passed all 34 tests,
including the new rebase/failure test. Both changed examples completed their exact assertions.
Rust formatting and `git diff --check` pass. Native GPU semantics, the existing fracture/fold
apparatus and paper PDFs were unchanged; no unrelated wide regression was rerun.

[definition] The compression canon now distinguishes zero rebase defect from a source residue,
removes the universal explicit-history-witness demand and the mistaken generic compiler
groupoid claim, and marks the August separate-cost census as historical. Current joint costs
and mathematical intelligence are linked to their returned owners. The roadmap remains the
operator/encoding order; this construction improves its rebase and information consumers while
leaving the unsolved global RH inequality and algebraic Hodge realization explicit.

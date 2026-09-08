# Complex fluid charts retain folded current and receiver bounds

[project-postulate] Brandon's September 8 direction asks for holonic Euler/NS research alongside
an actionable AC0–AC5 revision. His expectation of a counterexample or defect in the official
Millennium formulation is a research hypothesis, not a proved conclusion. The complex domain,
additional degrees of freedom, changing pivots, MVT and squeeze arguments are admitted research
directions. Their reusable consequences for HNNs and engineering are part of the objective.

[definition] This return gives the coupled equations, projection defect, folded memory and
receiver bounds; it revises the complete [AC blueprint](../../docs/plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md).
Native cultivation remains paused during this requested revision. No new universal adequacy
theorem or Millennium endpoint is imposed on production. Lean stays exterior verification.

## Complex fields, complex coordinates and the real receiver

[definition] Three mathematical constructions must carry their actual maps:

| Construction | What changes |
|---|---|
| Complex Fourier coefficients of a real velocity on real space | Representation: `u_hat(-k)=conj(u_hat(k))` retains the real-valued field. |
| Complex-valued velocity on real space | The admissible field family enlarges: `U=a+i*b` contains two real divergence-free fields coupled by the nonlinear equation. |
| Complexified spatial coordinates | A domain in `C^3` additionally requires its differential operator, metric, regularity class and real restriction. A holomorphic continuation and a PDE on six real coordinates are different specifications. |

[proved-standard] Complex-valued unforced NS blowup is an established research source:
[Li–Sinai, JEMS 2008](https://ems.press/journals/jems/articles/1424), with its
[preprint](https://arxiv.org/abs/physics/0610101). Its spatial variable remains in `R^3`, while
the velocity is allowed complex values. The introduction explicitly drops the Fourier reality
condition and notes the loss of the usual energy inequality. Renormalization, a fixed point and
the spectrum of its linearization organize that construction. This source was already recorded
in our September 5 heat-current research; it is reused here, not a newly discovered theorem.

[definition] The [official Clay statement](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf)
asks about real physical space and its specified velocity, initial-data, forcing and solution
classes. Considering a larger complex family is meaningful, but a counterexample in the larger
family only answers the official question through an additional restriction/realization argument.
The real-domain formulation itself is not evidence that complex equations are unsolvable because
of variable count. The cancellation, positivity and reconstruction laws are the concrete issues
to investigate. A claimed flaw in the formulation must identify a specific inconsistent or
inadequate clause; none has been established by this review.

## The imaginary field has a real nonlinear consequence

[definition] First work on a fixed real torus or real whole space with sufficiently smooth,
divergence-free complex velocity `U=a+i*b`, pressure `P=p+i*q` and real viscosity `nu>=0`.
Use the complex-bilinear advection law, with no conjugation in `(U.grad)U`:

```text
U_t+(U.grad)U = nu*Delta U-grad P.
```

[proved-derived] Expanding the product gives the complete two-field system:

```text
a_t+(a.grad)a-(b.grad)b = nu*Delta a-grad p,
b_t+(a.grad)b+(b.grad)a = nu*Delta b-grad q,
div a=div b=0.
```

Thus the real receiver `Re(U)=a` obeys a real NS equation with the additional force
`(b.grad)b`, or its Leray projection after pressure elimination. The nonlinear source does
not generally commute with that receiver:

```text
Re[-Leray((U.grad)U)] - [-Leray((a.grad)a)] = Leray((b.grad)b).
```

This is a precise folded contribution, not a variable-count objection. A complex construction
may therefore supply a real forced construction if the returned forcing and all other endpoint
conditions meet the intended class. It does not automatically supply an unforced one.

[counterexample; computational-witness] Let
`b=(1,-1,0)*cos(-x-y)+(0,0,1)*cos(2*x+y)` and `U=i*b` on the dimensionless `2*pi` torus.
Both `Re(U)` and the zero complex field have zero real velocity initially, but their real
projected nonlinear sources differ by
`-(0,0,1)*sin(2*x+y)*cos(x+y)`. This term is nonzero and already divergence-free, so pressure
projection does not remove it. The [exact symbolic control](../experiments/mfr_entropy_heat_current/complex_projection_witness.py)
checks the source and divergence independently. This refutes closure of the real receiver
over the enlarged field family, not the real NS equations or the Clay statement.

[proved-derived] The energy distinction is equally explicit. Under periodic boundaries or
sufficient decay to justify integration by parts,

```text
E=(1/2)*integral (|a|^2+|b|^2),
E'=-nu*integral (|grad a|^2+|grad b|^2)
   -2*integral b . ((b.grad)a).
```

The two ordinary a-advection integrals vanish by `div a=0`. Integration by parts changes
`integral a.((b.grad)b)` into `-integral b.((b.grad)a)`, producing the displayed exchange term.
The bilinear complex energy instead has real part proportional to `|a|^2-|b|^2` and is not
positive definite. Additional degrees of freedom expose an actual exchange term to control;
they need not be suppressed, but a positive energy estimate cannot silently omit it.

## Folding a dynamical dimension returns memory

[proved-derived] For finite-dimensional or bounded linear operators on Banach spaces, split
standing into a retained component r and a folded component z:

```text
r'=A_rr*r+A_rz*z,
z'=A_zr*r+A_zz*z.
```

Variation of constants gives

```text
z(t)=exp(t*A_zz)z(0)+integral_0^t exp((t-s)*A_zz)A_zr*r(s) ds,
r'(t)=A_rr*r(t)+A_rz*exp(t*A_zz)z(0)
      +integral_0^t K(t-s)r(s) ds,
K(t)=A_rz*exp(t*A_zz)A_zr.
```

Differentiate the first expression to verify the original z equation and initial condition,
then substitute it into the r equation. The smaller chart carries the folded generator,
initial fibre and memory kernel. It need not store every past output, and it does not acquire
a memoryless law merely by dropping z. In a spectral chart where the inverse exists, the same
elimination produces `lambda-A_rr-A_rz*(lambda-A_zz)^(-1)*A_zr`.

[established-bounded; computational-witness] The control `r'=z, z'=-r`, with `(r(0),z(0))=(1,0)`,
has `r=cos t` and the exact folded equation `r'(t)=-integral_0^t r(s) ds`. The symbolic receipt
verifies the full two-coordinate system and its memory equation. This is a small exact
generator example, not a physical identification of every hidden channel with an oscillator.

[conditional] For unbounded PDE generators, the same passage needs its semigroup, domains,
admissible source and integral regularity. The standing NS mild-source and finite diffusion/
Schur owners provide relevant pieces. This is the exact boundary where the finite calculation
must be extended; it does not assume those analytic obligations away. A singular spectral
parameter retains its kernel and compatibility conditions instead of an invented inverse.

## MVT and squeeze are already part of the calculus

[established-bounded; source-inspected] `HolonicConstructiveDifferentialBoundary.lean` owns
`meanValueWitness_of_hypotheses` and `ReceiverSqueezeCertificate.standardFace_tendsto`.
The certificate preserves an independent residue and proves convergence of its stated real
receiver only. The August 20 chord-chart construction identifies the scalar MVT witness with
zero derivative after subtracting the endpoint chord. Mathlib's existing
`Convex.norm_image_sub_le_of_norm_fderiv_le` supplies the norm inequality on complex/normed
carriers. These are existing owners, not new proposed foundations.

[proved-derived] For a continuously real-Frechet-differentiable map F between real or complex Banach spaces,
with the segment inside its domain, the real-parameter fundamental theorem gives

```text
F(x+h)-F(x)=integral_0^1 DF(x+t*h)[h] dt,
||F(x+h)-F(x)|| <= sup_(0<=t<=1)||DF(x+t*h)|| * ||h||.
```

This follows by applying the chain rule to `t -> F(x+t*h)` and integrating its continuous
derivative. If DF is L-Lipschitz on that segment, subtract `DF(x)[h]` inside the integral to
obtain the finite-return bound `||remainder|| <= (L/2)*||h||^2`.
Tensor-valued maps use the same operator norms. A single intermediate point with equality
in every component is unnecessary and need not exist: `exp(i*t)` has equal values at 0 and
`2*pi`, but its derivative never vanishes. Scalar receiver MVTs and the complete integral
remain available.

[proved-derived] This directly applies to the recovered softmax chart. For real finite
contact potentials s,h and beta>0,
`p_i(s)=exp(beta*s_i)/sum_j exp(beta*s_j)`, the finite difference is

```text
p(s+h)-p(s)=integral_0^1 beta*(diag p_t-p_t*p_t^T)*h dt,
p_t=p(s+t*h).
```

Each Jacobian is symmetric positive semidefinite; its absolute row sum is
`2*beta*p_i*(1-p_i)<=beta/2`. Its Euclidean operator norm is consequently at most beta/2,
so `||p(s+h)-p(s)||_2 <= (beta/2)||h||_2`. A common additive h remains exactly in its kernel.
This is a finite nonlinear receiver estimate using known learning mathematics, independent
of a floating-point realization or a sampling rule.

[proved-derived] Complexifying the potentials exposes a further chart boundary. The ratios
`r_ij=exp(s_i-s_j)` still compose and remain finite for finite complex potentials. However,
`Z=sum_j exp(s_j)` can vanish: `(s_1,s_2)=(0,i*pi)` gives weights `(1,-1)` and `Z=0`, while
their ratio remains `-1`. Normalization by Z therefore has a pole where the ratio family
itself is regular. Its derivative is bounded only on a domain that controls the denominator
and the other derivative factors. The positive real softmax/Laplacian theorem must not be
silently applied to that different complex chart. This is an explicit distinction between
a singular receiver and a singular underlying construction, useful for both fluid charts
and phase-bearing neural conduct.

[proved-derived] A complex/vector remainder can be squeezed through a real norm receiver:
`0<=||e_n||<=epsilon_n`, `epsilon_n->0` implies `e_n->0`. For positive semidefinite Hermitian
remainders, `0<=E_n<=epsilon_n*I` gives the analogous operator-norm conclusion. A scalar
projection alone does not imply convergence of an independent residue. If a changing chart
uses decoder D_n, the returned bound is `||D_n e_n||<=||D_n||*epsilon_n`; its product, not only
epsilon_n, must vanish to establish reconstructed convergence. For example `(1-t)*x(t)=1`
can hold while `x(t)=1/(1-t)` diverges. Our moving-frame/physical-clock owners already retain
this reconstruction obligation.

## Concrete continuation within the framework

[proved-derived] A first explicit source bound is available on the dimensionless `2*pi`-periodic Fourier chart.
For s>=1 define `||u||_(s,1)=sum_k (1+|k|)^s |u_hat(k)|`, using Euclidean coefficient norms,
and assume these sums finite. The projected advection B satisfies

```text
||Leray B(a,b)||_(s-1,1) <= ||a||_(s,1)*||b||_(s,1).
```

Indeed, its k coefficient is a sum over p+q=k bounded by `|a_hat(p)|*|q|*|b_hat(q)|`;
the Leray multiplier has norm at most one. The triangle inequality gives
`(1+|p+q|)^(s-1)*|q| <= (1+|p|)^s*(1+|q|)^s`. Summing this nonnegative bound factors
the two norms. Absolute convergence justifies the convolution. The constant is independent
of the number of modes or spatial dimension in this declared Euclidean chart. Derivative loss
remains explicit. In particular the nonlinear Taylor remainder B(w,w) is bounded by
`||w||_(s,1)^2` in the target norm.

[definition] The next mathematical passage is to instantiate the two-field complex source
through the existing oriented-current and weighted mild/Duhamel owners, retain all pressure
and mixed feedback terms, and choose an actual receiver/restriction with its decoder domain.
Use the source bound above and the MVT integral in their correct source/target spaces; the heat
or evolution operator must account for derivative loss in a continuing bound. Construct
upper/lower or norm bounds for the retained remainder on a stated interval and transport them
through the changing frame.

[interpretation] The shared HNN question is the same explicit operator question: after a
receiver or restriction folds part of a state, which source, memory kernel or nonlinear
feedback must remain for subsequent conduct? The source maps above exhibit it for complex
fluid projection, state-space elimination and normalized receiver return. AC1 uses those
constructions at finite native ports; the PDE line supplies source, spectrum and continuation
methods at its own analytic scope. A failed commuting square or nonvanishing reconstructed
remainder is the falsifier. This correspondence is actionable without claiming that a velocity
field and a text ecology have identical constitutive equations.

## Apple branch: useful source, bounded execution evidence

[established-bounded; source-inspected] The refreshed branch is
`origin/codex/apple-silicon` at `9b7b4b639f30df723379185914ee4abd2c6d4b9f`, September 7, 21:23 PDT.
Its common ancestor with current main is `e577d9b3`; it incorporated the desktop shared-drive
material return. It does not contain the later desktop `9fa9d55b` operative/contextual return.
This review fetched and read the branch without merging it or executing Apple code.

[established-bounded; source-inspected] `phase_current/resident/response_adjoint.rs` compares
the actual producing convolution carrier, receiver, clock, extent and lineage before returning
`X_source^* R_support^* e`. Missing observations supply no measured zero target; their dual
restriction supplies no cotangent contribution. Temporal condition rest/remount and
`NativeCompleteMaterialSourceReturn::temporal_view` preserve source/producing/current cuts
and resident enclosures. This is useful source-qualified return machinery for the AC1 plan;
an acoustic name or a temporal view alone does not make a text field an impulse response.

[established-bounded; source-inspected] The branch's
`2026-09-07_APPLE_RETURNS_COMPLETE_MATERIAL_CURRENT_TO_THE_TEMPORAL_RECEIVER.md` reports M1 Pro
controls and non-timing equality with the corresponding desktop material-mode receipt. It
explicitly leaves `CoupledOutgoing` unported and restricts its complete source to integral
root contacts. Normalized PCM may not silently discard its divisor to enter that domain.
The temporal application receipts preserve a four-tap comparison, restart and enclosed PCM
projection, while leaving useful acoustic organization and AS4–AS5 unfinished. These remain
reported branch measurements; this desktop review did not reproduce them on Apple hardware.

[definition] The Mac can continue research within that recorded branch scope. Future shared
changes should port the returned relation and compare its actual fields/chronology against the
matching desktop revision. Do not port the preserved unfinished joint draft merely because it
is newer, or assume that importing current docs establishes device parity. No desktop acoustic
campaign is scheduled by this reading.

[established-bounded; computational-witness] The exact source, folded-memory and complex-normalization controls returned successfully
with Python/SymPy in `complex_projection_witness.py`; the
[receipt](../experiments/mfr_entropy_heat_current/complex_projection_receipt.json) preserves their
scope. No native kernel, formal source or cultivation pipeline changed. The displayed analytic
derivations are not newly Lean-checked endpoints or a solution of the Millennium problem.

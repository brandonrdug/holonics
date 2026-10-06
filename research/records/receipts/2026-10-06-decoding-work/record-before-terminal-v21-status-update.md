# A lossy receiver returns decoding work and winding

**Date:** 2026-10-06. **Refs:** #62, #63, #73.
**Grade:** derived; the new existing-owner theorem and its consuming proof are
submitted to the shared bounded Lean queue. Physical joins below are conditional
on their stated constitutions and calibrations. No new audio realization is claimed.

The new result is one exact correction to finite work in
[Geometry/Motion](../../lean/Holonics/Geometry/Motion.lean): an ending decoder
that fails to reconstruct the motion leaves a transported storage-form defect.
The existing `finite_work_form_rechart` consumes the new result and removes that
defect only under its existing left-inverse hypothesis. Its statement and the
existing `affine_quadratic_work` statement remain unchanged. No new library or
authored signal predictor enters the HNN.

The computational object is the helical pair interaction. The receiver's faces,
phase carry, changing tube and material are the operands; pair power, declared
cell holonomy and tower restriction remain attached. The recorded failures this
choice avoids are a present face treated as retention, geometry substituted for
material, an omitted term carried into a consumer, an authored recovery routine
treated as learning, and a failed resource admission answered by a larger bound.

## The recovered owners and the concrete missing term

The atlas and actual owners recover the following joins. These are source facts,
not new execution claims.

| Operand | Existing owner and actual consumer |
|---|---|
| Finite physical work under exact endpoint charts | `Geometry/Motion.finite_work_form_rechart` and `affine_quadratic_work`; the October 4 finite-step work record already derives affine source and unresolved-opening cross terms. |
| Actual local sweep and shape-clock rate | [The accepted swept record](2026-10-06_THE_SWEPT_TUBE_DERIVATIVE_JOINS_ITS_ACTUAL_VOLUME.md), `Geometry/FrameTransport.egg_jacobian_hasDerivAt`, and the actual private NS phase-volume consumer. This is not an integrated Reynolds/Piola theorem. |
| Reached motion and changed material storage | `physics/wave/chain.rs::WaveChain::return_material`: retain `(q,phi)=(C V,L I)`, derive the successor joint law, decode with the successor material and check exact re-encoding. The existing continuation consumer checks repeated returns and independently computed material work. |
| Boundary power and propagation | `HNN/Ring.ring_tick_executed_energy_balance`, native loaded ring, native wave chain and `Physics/Wave/Energy`: storage, pump, port, dissipation and actual solve/split defects remain distinct. The [voice/medium record](2026-10-06_A_VOICE_REQUIRES_ITS_PROPAGATING_MEDIUM_AND_RETURNED_ACOUSTIC_POWER.md) supplies the calibrated pressure/volume-flow port. |
| Thermal free energy and information | `Physics/Information/PortWork.extracted_work_general` and native `physics/information/apply.rs::apply`: a declared finite Gibbs ensemble, an actual level shift, relaxation and restoration, with separate work, heat and production. |
| Remainder and carried integer | `Aeon/Clock/Winding.reading_split`, `split_unique`, `Geometry/PhaseCarry.phase_add_winding`; native `geometry/winding.rs`. A principal phase reading alone forgets the lift. |
| Retention through actions and material change | `Foundation/Standing/Law` and `HNN/ModeQuotient.descended_run_reads`: equal retained states imply equal admitted future observations, and the actual dynamics, reads and material variations descend. `Transport/ChangingReceiver` and `Physics/ReflectedBoundaryMemory` retain changing-chart and interior-return defects. |

The source search in atlas, records, Lean/Rust and history `13f8c734` found no
existing ending-decoder correction to `finite_work_form_rechart`. The root
predecessor is SHA256
`32df98dece1d3d0cbff9505bd9f4e15f0b2ee6244c490a3058c26a479b962fad`.
The private candidate retains that actual predecessor's existing additions;
canonical root sources are untouched.

## The one new result and its consumer

Let `P` encode the ending motion, `V` decode it, `W` pull the initial coordinates
back, and `T` be the actual finite transport. Put `R=VP`. Over a commutative scalar
ring, with finite square matrices, the exact identity is

```text
(PTW)^T (V^T G1 V)(PTW) - W^T G0 W
 = W^T(T^T G1 T-G0)W
   + W^T T^T(R^T G1 R-G1)T W.                         (1)
```

Expand the first term as `W^T T^T R^T G1 R T W`, then insert and subtract
`W^T T^T G1 T W`. No inverse, symmetric form or positivity is assumed. The new
`finite_work_form_rechart_defect` proves (1). The existing theorem consumes it:
`VP=I` makes the last term exactly zero. This preserves the original contract;
an arbitrary coarse receiver must return the term instead of claiming covariance.

[agent-inferred] Keep this correction at the existing work owner because storage
and decoder must use the same producing operands. `W` in (1) restricts the initial
motion to `x0=Wz`; this theorem does not silently erase an initial reconstruction
error, source motion, discarded modes or boundary work. For real symmetric physical
storage forms `H_k(x)=x^T G_k x/2`, the scalar defect at the ending reached state
is its actual decoded energy minus its physical energy. Physical units belong to
the calibrated `G_k`; the algebraic theorem alone assigns none.

For a nonlinear decoder, including a modulo face, let `x_k=tilde{x}_k+e_k`.
The existing `affine_quadratic_work`, with identity transport, already gives

```text
delta_k := H_k(x_k)-H_k(tilde{x}_k)
         = e_k^T G_k tilde{x}_k + e_k^T G_k e_k/2,
Delta H_actual - Delta H_decoded = delta_1-delta_0.     (2)
```

Symmetry of each `G_k` is required to combine the cross terms. Positive storage
does not make `delta_k` positive for an arbitrary decoder. Orthogonality of
reconstruction and residual in the actual storage metric is an additional
hypothesis. A norm/error bound also needs that metric and a bound on `e_k`.

An exact separator is `G=I`, encoder `P(x1,x2)=(x1+2x2,0)`, decoder `V=I`.
Here `P^2=P`. For `x=(0,1)`, decoded minus physical energy is `3/2`; for
`x=(-2,1)`, it is `-5/2`. Both have positive physical energy. A projection's
discarded coordinate count therefore supplies no signed work bound.

## Deformation, boundary power and material storage have units

For an actual injective regular moving chart `X(t,xi)`, let `F=D_xi X`, `J=det F`
and `w=partial_t X`. With an orientation-preserving chart use `J>0` for volume.
If physical storage density is `h(x,t)`, the receiver's actual storage is

```text
H(t)=integral_Omega0 J(t,xi) h(X(t,xi),t) dxi.
```

The pointwise pullback rate is
`Jdot h + J(partial_t h+w.grad h)`. Under the regularity, integrability,
boundary and Reynolds hypotheses, a physical local balance
`partial_t h+div j_h=s_h-d_h` gives

```text
Hdot = -integral_boundary(Omega(t)) (j_h-h w).n dA
       +integral_Omega(t) (s_h-d_h) dx.                (3)
```

This retains caps and advected storage. The outward relative current pulls back
as `cofactor(F)^T (j_h-hw)`; when invertible this is `J F^-1(j_h-hw)`.
The accepted swept source supplies actual local `F,J,Jdot`; (3) still requires
the stated continuum hypotheses and the actual physical local balance.

For a quadratic physical density with real symmetric material form `S` and a
calibrated state decoder `x=B(t,xi)z`,
the reference storage form is `G=J B^T S B`, where `S` is the physical material
form. Its complete rate includes `Jdot`, both `Bdot` terms and `Sdot`:

```text
Gdot = Jdot B^T S B
       +J(Bdot^T S B+B^T Sdot B+B^T S Bdot),
Hdot = integral (zdot^T G z+z^T Gdot z/2).            (4)
```

This is the actual join to `Motion.energy_rate_moving_metric`. Pure coordinate
change also changes `z` and the pulled material form; it does not become physical
work by holding an arbitrarily chosen coordinate vector fixed. True deformation
needs its force/material law and physical work port. In (4) geometric volume
rate is already included in `Gdot`; adding it again double counts it.

The native wave continuation makes the distinction concrete. Under a declared
lossless lumped acoustic calibration, a fixed-length duct has compliance
`C=Volume/K_bulk` and inertance `L=rho*length/area`. Pressure `p=q/C` has units
Pa, volume flow `Q=phi/L` has units m^3/s, and `p Q` has units J/s. Charge `q`
has units m^3, flux `phi` has units Pa*s, so

```text
H=q^2/(2C)+phi^2/(2L),
W_material=q^2 Delta(1/C)/2+phi^2 Delta(1/L)/2.         (5)
```

At fixed reached `(q,phi)`, double transverse area while keeping length, bulk
modulus and density fixed. Then `C1=2C0`, `L1=L0/2`. For `q=0`, nonzero `phi`,
work is `phi^2/(2L0)>0`; for `phi=0`, nonzero `q`, it is `-q^2/(4C0)<0`.
Both changes double physical volume. A pressure-only zero reading merges rest
with the first state, although a coupled incidence with `D^T phi!=0` produces
different future pressure. The existing native material return retains charge
and flux and decodes the contemporary pressure/flow. Equation (5) is the
storage-only return at the reached state; any work during wall motion or source
continuation must be added through its actual port balance.

## Thermal work and receiver information join conditionally

For an actual single-bath system at fixed bath temperature `T0`, with all entropy
fluxes included, `Udot=P_in+Q_in` and
`Sdot=Q_in/T0+sigma_phys` imply
`Fdot=P_in-T0 sigma_phys`, `F=U-T0 S`.
Here `U,F` are joules, power is J/s, physical entropy is J/K and production is
J/(K*s). Changing temperature leaves the additional `-S Tdot` term; open material
and multiple-bath passages need their actual energy and entropy currents.

The finite Gibbs port already supplies a concrete computational consumer. With
physical level energies, `theta=k_B T0`, Gibbs reference `q`, quench/relax/restore
protocol and computed shifted Gibbs state `qprime`, its law is

```text
-W = F(p)-F(q)-theta D(p||qprime),
F(p)-F(q)=theta D(p||q),   sigma_dimensionless=D(p||qprime)>=0. (6)
```

Native `PortApply` returns each leg's work and heat, independent residuals, and
the bath's energy/entropy return. Its exact base-two forms use the declared
unit `k_B T0 ln 2`; the phase covector is retained for a different port.
This is an ensemble/bath/material protocol, not a universal energy cost for a
retention quotient. The finite bath's returned energy does not by itself prove
an exact constant-temperature reservoir or a finite-bath Landauer correction.

There is a concrete material-to-level join when an actual finite ensemble has
declared material motions `x_j` and the quench holds those motions and their
populations fixed. Its physical level shift is
`delta_j=x_j^T(G1-G0)x_j/2`, and the existing port consumes
`quenchWork(delta,p)=sum_j p_j delta_j`. With the same reconstruction `R=VP`
at both endpoints, (1) specializes to the exact work error

```text
W_quench,decoded-W_quench,physical
 = sum_j p_j x_j^T[R^T(G1-G0)R-(G1-G0)]x_j/2.        (6a)
```

No sign of this error is assumed. For native base-two level forms, divide the
physical shifts by their declared `k_B T0 ln 2` unit and satisfy the actual exact
exponentiation admission; fractional coefficients can leave the rational carrier
and are refused. Constructing a particular finite physical ensemble and its bath
is a constitutive calibration, not an automatic consequence of acoustic geometry.

Receiver-relative cross-entropy/KL and physical production stay separately
typed until hypotheses such as (6) join them. The exact future quotient in
`Standing/Law` need not preserve each presently invisible physical mode unless
the admitted future includes its physical energy/ports. A byte count, decoder
work count and physical work keep their distinct units and proven conversions;
`Foundation/PresentationCost` already returns separate cost coordinates.

## Wave modes, modulo faces and changing medium

For positive period `Lambda` in the units of the scalar reading, apply the
existing unique winding/remainder split to `x/Lambda`:

```text
n=floor(x/Lambda), y=x-Lambda*n, 0<=y<Lambda,
x=D(y,n)=y+Lambda*n.                                  (7)
```

The unfolded coordinate is exact when the integer is carried. The face alone
has fibre `{y+Lambda*k : k integer}`. The circle map
`x -> exp(i*pi*x/lambda)` has period `Lambda=2lambda`; the principal phase is
the quotient, while the lift retains the carry. This is a representation
quotient, not a change of physical tube topology.

In a declared orthonormal waveform basis `psi_j`, `E(a)=sum a_j psi_j` is an
isometry in that specified norm. It transports a full-rank lattice quotient to
the waveform subspace quotient `S/E(Lattice)`. Dual-lattice characters are the
Fourier readings of this torus. Physical acoustic storage requires the actual
weighted material norm: an arbitrary Euclidean coefficient norm is not joules.
Moreover a quotient class has many amplitudes with different energies. An
isometry on the full subspace does not make their energy a function of the
quotient class.

If the basis or medium changes, `partial_t(E(t)a)=E adot+Edot a`. Retain its
connection, actual mode mixing, boundary coupling and discarded-mode residual.
Exact compression of `xdot=A(t)x+f` through a receiver chart `y=P(t)x` needs
the actual dynamic square `Pdot+PA=Abar P` and the source square, or their
complete defects. If the statistic is a lattice quotient, even a fixed linear
motion `T` descends only when `T Lattice` is contained in the ending lattice.
For the fixed lattice `2Z`, `T=1/2` maps representatives `0` and `2` of one
class to different classes `0` and `1`. Equal present modulo faces are
therefore insufficient for that admitted future.

For a quantized modulo face `y_quant=y+eta` and recovered integer `n_hat`, the
physical reconstruction error is exactly

```text
e=x-(y_quant+Lambda*n_hat)=Lambda*(n-n_hat)-eta.        (8)
```

Substitute (8) into (2) using the actual contemporary material metric. Correct
wrap recovery still leaves quantization error; a wrong wrap can leave large
storage and work error. An orthogonal discarded-mode error only adds a positive
term when orthogonality holds in the actual ending metric.

Primary source identities and hypotheses were checked by the coordinating
reader, not independently fetched in this lane: Bhandari–Krahmer–Raskar
[1707.06340](https://arxiv.org/abs/1707.06340) and
[1905.03901](https://arxiv.org/abs/1905.03901), and Ordentlich et al,
[DOI 10.1109/JSTSP.2018.2863189](https://doi.org/10.1109/JSTSP.2018.2863189),
section IV's voltage-to-ring-phase modulo ADC. The previously supplied
1711.08535 identifier and 2863581 DOI were unrelated/mistyped and are not used.

The reported ideal unlimited-sampling result assumes a bounded bandlimited
signal, known threshold `lambda` and amplitude bound `beta`, and a sufficient
spacing `T<=1/(2e Omega)` in its angular-bandwidth convention. The reported
finite-difference noise margin is
`||Delta_T^N g||_infinity+2^N||eta||_infinity<lambda`.
Increasing difference order suppresses admissible signal variation but amplifies
noise. Integration needs its lower-order constants or the theorem's conditions
that determine them; a finite recording generally still needs an absolute lift
or retains its global `2lambda*k` ambiguity. Whole-line finite-energy assumptions
are different from a finite recording's side information. A changing acoustic
medium must establish that its produced pressure/voltage still belongs to the
declared source class; geometry alone supplies no bandwidth bound.

The physical modulo ADC uses an actual oscillator sensitivity and reference clock:
schematically `thetadot=omega0+alpha*voltage`, then a modulo-`2pi` phase read,
quantization and temporal/spatial prediction. `alpha` has units 1/(s*V) when
radians are the dimensionless phase chart. It is not instantaneous folding of
acoustic pressure. A pressure-to-voltage sensor calibration, oscillator
constitution, wrap recovery and source/error conditions remain actual operands.
The cited device's probabilistic unfolding and nonzero distortion do not assert
arbitrary lossless waves. Dynamic range, bits per sample and bits per time are
separate readings. The current HNN rings and Research acoustic receiver do not
implement this device; their existing phase, power and material-memory owners
supply the relevant mathematical ports for a future calibrated consuming join.

## Boundary response and reusable continuation

Recovery reaches the old laboratory acoustic map in the voice record and the
Ghost/Comma record at history `a1bc2bc`, section J7. The latter's drum statement
concerns a declared spectral receiver, not destruction of unheard modes. Its
actual current owner is `Foundation/CausalChord`: for fixed material and clock,
`H_R(s)=C_R(sI-A)^-1 B` carries excitation, readout and residues as well as poles.
`spectrum_does_not_determine_response` gives an exact same-spectrum/different-
response witness; `full_atlas_determines_the_operator_fin_two` proves recovery
from the complete coordinate-probe atlas only in its stated two-dimensional
case. The six-vertex cospectral contact graphs and distinct driving-point
numerators survive in `docs/RECEIVER_HOLARCHY.md`; their retired Rust realization
has no current caller. No general uniqueness theorem for moving acoustic
geometry is inferred from these finite results.

For an actual time-dependent linear medium, its causal boundary response has
the form `K_R(t,s)=C_R(t) Phi_A(t,s) B(s)`, with the homogeneous initial-state
return `C_R(t) Phi_A(t,t0) x0` retained. Geometry, material, boundary conditions
and both clocks determine these operands. A cancelled or unobserved response
pole can remain a physical mode. Lossless scattering redistributes power,
physical dissipation returns energy to heat/environment, and projection leaves
a receiver-blind residual; these are different operations with different ports.

Let `s_k` be the actual joint motion, medium constitution, geometry and clock/lift
state, `K_k` its admitted physical step, `q_k` the contemporary receiver and
`U_k` a proposed continuing coarse step. Use the already owned signed defect

```text
r_k=q_(k+1)(K_k(s_k,u_k))-U_k(q_k(s_k),u_k).           (9)
```

This compares an actual returned face, not an authored answer routine. Include
the same actual feedback inputs or retain their mismatch; a fixed external-drive
model does not price a mutually interacting pair without the feedback return.
For declared compatible norms/grains and a certified sensitivity `L_k>=0` of
`U_k` from the initial to ending norm, `||r_k||<=epsilon_k` and an initial
coarse error `e_0` give the existing composition bound

```text
e_(k+1)<=L_k e_k+epsilon_k,
e_n<= (product_(j=0)^(n-1) L_j)e_0
      +sum_(i=0)^(n-1) epsilon_i product_(j=i+1)^(n-1) L_j. (10)
```

The one-step law is `ChangingReceiver.norm_passageDefect_comp_le`; iteration
uses the same actual middle face. The sensitivity factors cannot be omitted.
With changing storage metrics they must be certified between those metrics,
for example by the actual finite gain form, not by an eigenvalue list alone.
Refine when the admitted future receiver's propagated error budget cannot be
certified at its declared grain. Exact zero defect on every admitted action
permits the future quotient; tolerance-closeness alone is not transitive and
does not define quotient equality. `SectionResidual.two_level_receiver_defects`
also retains the mixed return of nonlinear lower sections.

Thus a familiar instrument can continue through retained material and lifted
clock state without re-identifying what its admitted future already preserves.
It still performs physical continuation and pays the actual port/material work.
The HNN coordinator owns the adaptive-work consumer; this lane supplies (1),
(2), (5), (6a), (8) and the recovered residual/sensitivity operands, without
claiming a measured reduction of processing work.

## Acceptance and receipt scope

Acceptance is fixed: (1) and its existing theorem consumer must kernel-check
with standard axioms; the complete actual owner and a separate importing audit
must resolve the same current source/object graph under unchanged resource
ceilings. Exact semantic checks must exhibit both signs of decoder energy
error, both signs of area-change work, and a same-face future separator. Native
wave and thermal owners above were source-inspected; no fresh native run or
acoustic output is claimed. Primary Bennett/Reeb–Wolf fetches failed DNS and
remain unread; no finite-bath, side-information or prediction-work theorem is
inferred from them. Accepted swept integration remains unchanged.

# A continuing field before reception

[project-postulate] The fixed-emitter/moving-aperture example did not answer Brandon's request.
The source field itself must evolve relative to the receiver. This construction replaces that
example in the live visualization while preserving its valid projection/optical results as a
separate control. It is an explicit coupled-field specialization, not a declaration that the
entire HNN/physical synthesis has been completed.

## Evolution, orientation and the actual population

[definition] The displayed τ is the model's declared evolution coordinate, `τ=n T₀/16`.
It is not a calibrated physical clock or a relativistic proper-time trajectory. The receiver
position, orientation and exposure are fixed in this example. The source's local orientations
change through nonrigid transport, but the independent receiver-frame family is not varied.
A joint study uses `y(τ)=ρ_(R(τ))[Ψ(τ)]`, retaining both source evolution and receiver-frame
rate. Merely rotating a view supplies no fractal invariant or scale law.

[definition] The population here is six supplied toroidal modes with initial currents
`(2,i,1,−i,1,1+i)` and their thermal modes. The current-to-twist law is a supplied constitutive
choice for this example. It was not inferred from Athena material or from an RH/Hodge system.
The construction checks coupled evolution and reception; it does not yet analyze a particular
RH or Hodge population.

[definition] A Hodge investigation should instead start from the actual chosen complex,
restriction maps and metric, hence its `Δ=dδ+δd`, then decompose current into exact, coexact
and harmonic components. The existing `HodgeFiniteDecomposition`, `TemporalHodgeResidue`,
`PartitionedHodgeEnergy` and Rust `ExactCellularSheaf`/`ExactSheafDiffusionLaw` supply that
route. A meaningful question is which circulation survives the stated evolution and which
receiver/frame changes hide or expose it. Ordinary fixed linear heat flow need not produce
fractal structure; nonlinear transport or a scale-dependent receiving/iteration family must
be specified if that is the question.

[definition] An RH investigation has a different concrete population: the zero divisor,
with multiplicity, of `F_u(s)=heatE(u,ξ,s)`. The existing `ZeroDynamicsEntire` and
`FosterClassHeatFlow` relate a simple zero's velocity to `F_ss/F_s` and its regularized
divisor current. `FoldedSource` retains the source/tail receiver needed for finite windows.
The standard chart is `H_t(z)=⅛ heatE(−t/4,ξ,½+iz/2)`; this analytic deformation parameter
must not be silently identified with this movie's τ. Zeros of a nonzero entire function are
locally discrete; fractal basin geometry, when studied, belongs to a specified iteration or
receiving partition, not automatically to the zero set itself.

## One state supplies the field, its transport and its receiver image

[definition] The state is `(ψ_n,H_n,Φ_n)`: complex mode currents, nonnegative thermal modes,
and a composed material map. The existing six interlinked toroidal kernels and seven witnessed
contacts define its initial material. `continuing_field.py` implements the source using exact
integer/rational arithmetic; `continuing-field.json` retains the supplied laws and returned
states. The displayed frame count is a movie aperture, not a model capacity.

[proved-derived] On an admitted contact with unit phase u, the existing
`Physics/PhaseContactPassage` law is

```text
δ=ψ_j−uψ_i,
ψ_i'=ψ_i+α conj(u)δ,       ψ_j'=ψ_j−αδ,
heat=2α(1−α)|δ|².
```

The squared-current decrease equals that returned heat. Here α=1/8, each endpoint receives
half the heat, and an exact conservative thermal exchange of `(H_j−H_i)/16` then acts on
the same contact. Disjoint matchings retain their actual endpoint independence. The unit
phase turn `(255+32i)/257` and supplied initial currents determine the subsequent states.
Every returned state satisfies `Σ|ψ_i|²+ΣH_i=10`; this is the declared port-sector balance,
not an assertion that integrated optical brightness or total bulk mechanical energy equals it.

[definition] The currents also determine the next spatial transport parameter. With
`d_n=Im ψ_i−Re ψ_j` after the contact return,

```text
s_n=(sign_n/36)[1+d_n/(1+d_n²)].
```

The axis cycles through x,y,z with the declared handedness (+,−,+). For the x-axis stage,

```text
q=s_n x,
C(q)=(1−q²)/(1+q²),   S(q)=2q/(1+q²),
T_s(x,y,z)=(x,C(q)y−S(q)z,S(q)y+C(q)z),
Φ_(n+1)=T_(s_n) ∘ Φ_n.
```

C and S are constrained rotation faces, not floating constants. The mode currents determine
both the geometry update and the reconstructed field. There are no independent torus poses,
random texture or target frames driving the result.

[proved-derived] `C²+S²=1`, and the Jacobian is block triangular because the axis coordinate
is unchanged. Thus `det DT_s=1`, and `T_s⁻¹=T_(-s)`. The inverse of Φ reverses the word and
negates its parameters. Different axes do not commute; an exact point-pair check also shows
that the composition changes distances, so it is not a rigid camera/object rotation. For a
continuous stage parameter s(t), the transverse angular rate is
`2x ṡ/(1+s²x²)`. It produces a spatially varying divergence-free velocity field.

[definition] The word retains the exact generating map without expanding enormous rational
coordinate expressions. Scalar amplitudes and heat are pulled back through its inverse;
vector currents would use DΦ and oriented area covectors its cofactor. The displayed carrier
curves are evaluated through the same Φ. Diffusion here belongs to the moving material contact
operator. It is not silently commuted with a fixed Euclidean heat operator after deformation.
This is a supplied constitutive/material evolution, not an unforced Navier–Stokes solution.

## The receiver reads the evolving volume

[definition] With the existing compact torus kernels K_i and rational unit phase plates g_i,

```text
A_n(X)=Σ_i ψ_i(n) K_i(Φ_n⁻¹X) g_i(Φ_n⁻¹X),
H_n(X)=Σ_i H_i(n) K_i(Φ_n⁻¹X).
```

The receiver frame is fixed. Every frame samples these newly constructed fields along the
same perspective ray family. Emission/absorption integration supplies a volumetric display
of complex amplitude and thermal activity. Its coefficients, gain, gamma and exposure remain
fixed across frames. Black is zero received signal. This display receiver is not a model of
radiative cooling that subtracts emitted power from the port-sector heat state.

[definition] Native source updates, contact admission, coefficients and phase/heat balances
use exact arithmetic. Ray quadrature, fixed display transfer and image encoding are numerical
receiver approximations. They make no source-state, contact or topology decisions. Increasing
quadrature from the initial coarse display removed sample-plane banding; 384 depth stations
were used in the returned 256×192 frames. No finite picture establishes a fractal dimension.
The construction exhibits nonlinear deformation, phase interference, diffusion and progressively
finer transported structure; its complete generator is retained beyond the raster samples.

## Reproduce and inspect

[definition] The two stages keep source evolution separate from exterior display encoding:

```sh
python3 continuing_field.py --output /absolute/render-directory --steps 24 --size 256 --rays 384 --workers 2
python3 bundle_continuing.py /absolute/render-directory /absolute/hnn-field-architecture.html
```

The renderer requires NumPy and Pillow. The bundled source PNGs preserve the receiver raster;
the inline fragment uses a fixed WebP encoding for display size. `continuing-field.png` is the
last displayed cut, and `continuing-field-motion.png` retains all 25 rendered cuts in an APNG.
The optional overlaid mode curves are recomputed from the same map at 641 parameter stations.
The old `build.py`, `explorer.template.html` and `receiver-motion.json` remain the separate
fixed-source optical control and do not build the live continuing-field view.

[established-bounded; implemented-exact] Source checks cover admitted overlaps, unit phases,
contact energy return, thermal positivity/conservation, the complete mode/heat balance at every
cut, exact inverse checks for each selected twist and a nonrigid composition separator.

[established-bounded; process-audit] The returned display contains 25 calculated source states.
Playback/scrubbing and the carrier overlay use those states, with no tweened physics or
independent geometry animation. Desktop/narrow layouts and play/pause were browser-inspected.
The previous assertion that the fixed-ray example completed the requested field/receiver
synthesis is withdrawn; these checks apply to this explicit continuing-field construction.

# HNN field architecture and its executable interfaces

[definition] This is the reusable diagram attached to
[the HNN model formula](../../../docs/HNN_FORMULA.md#reading-the-field-architecture-diagram).
It depicts situated encoding, normalized contact transport, internal circulation and material,
then joint-field reconstruction. The comparison to transformer, diffusion and SSM diagrams
locates operations inside one object. It does not prescribe a global layer stack, a next-token
objective, six native units or three separately added engines.

## What the geometry represents

[definition] `build.py` uses the existing six toroidal domains and the certified shared-surface
facets from `contact_receiver_faces`. Rational conic stations describe the surfaces and the
(2,3) circulating strands. The single material map

`F(x,y,z)=(x,y+x²/12,z+xy/12)`

has triangular Jacobian with determinant one and polynomial inverse
`F⁻¹(X,Y,Z)=(X,Y-X²/12,Z-X(Y-X²/12)/12)`. Applying it to every source point preserves
intersections. The orange facets represent the actual supplied overlap; arcs between chart
addresses are interaction-diagram connections, not solved fluid trajectories. Green strands
illustrate internal circulation. The drawing is an architecture schematic, not a trained-model
or physical simulation result.

[definition] `geometry.json` contains integer ink stations obtained from exact rational source
coordinates. Browser numbers affect only screen placement. Neither display arithmetic nor a
color/width chooses contact, a mode, a current or a generated prediction. The drawn spatial
surface is one projection: section rank, phase dimension and fractal dimension retain their
separate mathematical definitions. The model formula owns the complete architecture.

## Interface audit and refinements

[established-bounded; source-inspected] The audit followed the public facade and actual owners:
`holonics::structure`, `holonics::geometry`, `holonics::engine::exact_linear`,
`exponentiated_ratio`, `diffusion`, `sheaf_diffusion`, native constitutive fields and the
`holonics::hna::native` sessions. The following table names the operations behind the drawing.

| Diagram operation | Actual interface and implementation consequence |
|---|---|
| Encoding and chart transport | `LocalChart`, `FrameRelation`, exact linear maps, typed native currents/occurrences. Spatial affine points and tensor/current coordinates are different ports; equal vector lengths alone establish no frame relation. |
| Elementary tensor interaction | `BilinearOperator`, `BilinearProductCore`, `BilinearRealization`. New input differentials and covector pullbacks preserve the factorized products and compose through their output receiver. |
| Input port composition | New `BilinearRealization::precompose_ports(L,R)` maps the factor rows through the declared input maps and rederives the full receiver family. It admits a projection deliberately and does not call it an invertible rechart. |
| Attention/contact normalization | `NormalizedKernel::{apply,differential,pullback}`; native `NativeConstitutiveField::normalized_material_return` with its actual receiving occurrence, grouping and series aperture. The native return consumes an existing observation; it is not required before every prediction. |
| Interior circulation | Operative field scattering, held currents, material and current pullbacks; `ResidentNormalWave` and `ResidentCoupledConstitutive` retain their joint interior families. An exterior `inspect_current` JSON value is a readout, not the complete object. |
| Diffusion and Hodge transport | `ExactDiffusionLaw`, `ExactSheafDiffusionLaw`. New complete energy pairing separates constitutive dissipation, source work and the implicit-step defect. The graded calculation uses both Hodge coboundary terms and the actual source certificate. |
| Coupled generation | `NativeCoupledBody` supports joint prospective/current receivers and original-source observations. The field's operative material and this application still have the recorded assembly join; a larger response wrapper would not implement it. |
| Native diffusion boundary | The existing `NativeCirculationSession::diffuse` consumes the complete energy balance and carries the original receipt through its public event. It does not turn total energy decrease into an invented thermal state. |

[proved-derived] For the factorized interaction `C=R[(Ax)⊙(By)]`, the new elementary return is

```text
δC=R[(Aδx)⊙(By)+(Ax)⊙(Bδy)],
λ_x=Aᵀ[(By)⊙Rᵀλ],       λ_y=Bᵀ[(Ax)⊙Rᵀλ].
```

These are input variations at fixed factor material. Material variation uses the corresponding
outer operator/constitutive derivative. A finite input change additionally has
`R[(Aδx)⊙(Bδy)]`; it is not silently folded into the first derivative.
The return is a covector in the declared input coordinates. A metric turns it into a vector
through the existing `metric_adjoint`/Riesz map where that operation is intended. In the new
fluid construction, applying this to a bilinear advection port supplies its two input returns,
including the material-to-momentum exchange; the continuum constitutive law remains explicit.

[proved-derived] Pairing the exact implicit diffusion equation with the endpoint potential
produces

```text
E_after−E_before = source_work−conductive_dissipation−implicit_step_defect,
source_work = <φ_after, source>,
conductive_dissipation = τ <φ_after, L φ_after>,
implicit_step_defect = (1/2) ||φ_after−φ_before||²_C.
```

The scalar branch realization and the full graded Hodge realization now return the same
`DiffusionEnergyBalance`. Their serialized receipts retain existing fields. Source work can
increase stored energy; the finite-step defect is not a newly discovered physical friction.
The exact two-node return distinguishes `1/9` conduction from `1/9` step defect within the
`2/9` total decrease. A grade-one case has positive dissipation despite zero upper
compatibility energy, verifying that the lower coboundary contribution is retained.

## Rebuilding the presentation

[definition] The maintained presentation source is `explorer.template.html`, with exact
geometry generated by `build.py`. Supply a task-owned output path:

```sh
python3 research/experiments/hnn_field_architecture/build.py /absolute/output/hnn-field-architecture.html
```

The installed visualization skill's `scripts/render.py` wraps that fragment for local browser
inspection. `export.js preview.html output-directory` uses Playwright to exercise all four
operation selections, check narrow layout, and export the actual rendered SVG. `architecture.svg`
is the vector used by the model guide and can be reused in the existing Typst presentation.
`NODE_PATH` must resolve the available Playwright package when running that exporter.

[established-bounded; process-audit] The final browser inspection covered desktop and narrow
layouts, all operation selections and runtime errors. The diagram does not run native model
inference. The code/test evidence is recorded in the corresponding September 14 architecture
and interface return.

# Athena engine construction diagrams

[definition] This diagram is the illustrated reading of
[ATHENA_ENGINE_BLUEPRINT](../../../docs/ATHENA_ENGINE_BLUEPRINT.md) and the existing HNN
assembly contract. Its modes expose generation, the producing-material learning path and
encoded reuse on the same field. Solid paths name existing mathematical operators; dashed
paths identify body/encoded-action assembly. It is not a runtime simulation or a trained
topology specimen.

[established-bounded; source-inspected] The inspected direct owners are:

- `NativeConstitutiveField::advance_resident`, in `field.rs`.
- `PairedJunctionLinearization::{pushforward,pullback}`, in `field/junction/producer.rs`.
- `normalized_material_return` and `pull_back_material_current/source`, in the normalized receiver.
- `material_contact_response`, `apply_material_contact_realization`, and
  `respond_to_material_observation`, in `field/junction/operative/response`.
- The `NativeCoupledBody` enum and dispatch in `holonics-hna/src/native/coupled_wave/body.rs`.

[definition] The geometry is reused from the earlier `hnn_field_architecture/geometry.json`
contact specimen. Its old ray/receiver animation is excluded. The six drawn support regions
are a schematic carrier for this operator-placement diagram, not six mandated heads or
neuron objects. `centered-quartet.svg` is a general symbolic symmetry orbit; it does not
assert that an off-line ξ zero has been found. The marked vector directions use the seam-time
zero velocity, with different same-height and opposite-member reciprocal currents.

[definition] `build.py` combines the geometry with the literal interactive template:

```sh
python3 research/experiments/athena_engine_blueprint/build.py /absolute/athena-engine-blueprint.html
```

Use the installed visualization renderer to wrap that fragment for browser inspection.
`export.js preview.html output-directory qa-directory` exercises all four selections,
checks desktop/narrow overflow and exports the displayed `network.svg` and `training.svg`.
It requires Node with Playwright available. The static exports and quartet diagram are
consumed directly by `elementary-holon-generation/engine-blueprint.typ`; they are not
redrawn independently for the paper. Its mathematical equations live in the shared
`research/papers/source/holonics/computational-holon.typ`.

[established-bounded; tested] All four mode selections update the paths/detail correctly.
Browser checks at content widths 736 and 328 returned no script errors or horizontal
overflow. The final paper has 16 pages; the three new plates were rendered and inspected.
The diagrams and paper introduce no new native numerical law or training completion claim.

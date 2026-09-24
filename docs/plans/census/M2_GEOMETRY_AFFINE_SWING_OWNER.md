# M2 affine swing owner and Geometry facade closure

This follow-up to the M2 Geometry curation removes the last Research module from the public
`Framework.Geometry` source-import closure. The concrete edge was
`Geometry.SwingPotential → Millennium.Swing`: receiver-potential transport used only the affine
point reflection and its group laws from a Research realization.

## Owner cut

`Geometry/AffineSwing.lean` now owns the frozen-board affine point reflection `swing`, its
displacement-negation and involution laws, the fixed anchor, doubled-translation composition, and
the noncommuting-anchor identity. These laws are valid for every additive commutative group; the
owner imports only Mathlib group and abel support. There are no forwarding declarations.

`Geometry.SwingPotential` uses this geometric owner directly. `Millennium.Swing` retains the
harmonic-conjugation chart, the finite-board parity invariant, and the reachability puzzle, and
imports the affine operation it specializes. Its existing consumers now refer to
`Soma.Holonics.Geometry.AffineSwing` directly. The facade continues to expose
`Geometry.SwingPotential`, with `AffineSwing` as its explicit dependency.

## Source closure

Counts use project `import ElementaryHolonics.*` edges, include the source root, and exclude Mathlib
and Lake jobs. The before graph is commit `f87db7ba`; the after graph is this cut.

| Source root | Before modules / Research modules | After modules / Research modules | Effect |
|---|---:|---:|---|
| `Framework.Geometry` | 43 / 2 | 42 / 0 | Removes the `Millennium.Swing` and its `Millennium.Gluing` dependency from this facade closure. |

This is a source-import result, not a claim that the whole `Framework` or ElementaryHolonics
research umbrella is Research-free. Other entry points retain their own declared Research
dependencies.

## Verification

Run from `formal/elementary-holonics`:

```sh
lake build ElementaryHolonics.Geometry.AffineSwing ElementaryHolonics.Geometry.SwingPotential \
  ElementaryHolonics.Millennium.Swing ElementaryHolonics.Millennium.Chronology \
  ElementaryHolonics.Millennium.SwingBridges ElementaryHolonics.Millennium.HolonicComposition \
  ElementaryHolonics.Millennium.HolonicDifferenceCalculus ElementaryHolonics.Millennium.HolonicSlingTransport \
  ElementaryHolonics.Millennium.HolonicPantographicSwingJets ElementaryHolonics.Millennium.HolonicAlternatingGeometry \
  ElementaryHolonics.Millennium.Ellipse ElementaryHolonics.Millennium.Shadows \
  ElementaryHolonics.Millennium.NavierStokesMaterialPolygon ElementaryHolonics.Millennium.NavierStokesVorticity \
  ElementaryHolonics.Millennium.Navigation ElementaryHolonics.Computation.HolonicConstitutiveCirculation \
  ElementaryHolonics.Framework.Geometry
```

The named owner, its receiver-potential application, every updated direct swing caller in this
stack, and `Framework.Geometry` built successfully (8,868 jobs) using an isolated project build
directory with the existing dependency packages reused. The build log is
`/tmp/m2-geometry-facade-owner-build3.log`. The full `Framework` and research umbrella were not
rerun; this cut changes only the Geometry facade and its affected source callers.

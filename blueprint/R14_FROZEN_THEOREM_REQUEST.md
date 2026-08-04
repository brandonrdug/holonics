# R14 frozen theorem request

**Truth status:** `established-bounded`; the returned grade is recorded separately in the R14
receipt.

**Evidence aperture:** the pinned `ElementaryHolonics.Algorithm.Rebase` environment at Git
predecessor `e1c5e13`; the source-absence search was performed before the feasibility probe and
before production construction.

## Conversational request `q₁`

Given a situated algorithm, an invertible change of its state chart, and two composable execution
traces in the original chart, produce and explain a theorem saying that their composite is a trace
between the corresponding endpoints in the rebased chart.

## Frozen statement

```lean
theorem generated_trace_rebase_transports_composition {Theta I S O S2 : Type*}
    (A : SituatedAlgorithm Theta I S O) (e : S ≃ S2)
    (theta : Theta) {s t u : S}
    (hst : Trace (A.step theta) s t)
    (htu : Trace (A.step theta) t u) :
    Trace ((A.rebase e).step theta) (e s) (e u) := by
  -- generated proof required here
```

## Admitted inherited boundary

The engine may inherit the declarations `Trace`, `Trace.trans`, `SituatedAlgorithm`,
`SituatedAlgorithm.rebase`, and `SituatedAlgorithm.trace_rebase_iff`, plus their types and local
incidence established by R11. It may not mount a theorem or proof with the frozen target as an
answer. The receiver permits at most three declaration dependencies.

A generated proof must arise by expanding the two locally founded proof geometries, retaining
their obstructions, restricting them through the dependency receiver, and emitting the selected
passage on the GPU. A stored answer, reference consult, host proof search, source quotation, global
candidate registry, or exact target proof present at mount does not qualify.

## Pre-run exclusion and ablation contract

The pre-construction search found no occurrence of the target declaration name or complete target
proof in tracked developmental material. A one-use feasibility source was checked by the pinned
kernel only after that absence result and was then removed; it is excluded from every mount and
production aperture.

After the real return, native rest must retain identities, exact morphology, and the acquired
kernel-returned fiber but no proof source, corpus, index, or retrieval handle. A held dependent
three-segment question must be obstructed before `Δm₁`, become available after source-detached
remount, and become obstructed again when exactly that returned fiber is excluded.

import Holonics.HNN.SingleHoleResponse.SourceExpansion
import Holonics.HNN.SingleHoleResponse.LoadedWord
import Holonics.HNN.SingleHoleResponse.NormalizedOpening
import Holonics.HNN.SingleHoleResponse.ReceivingResponse
import Holonics.HNN.SingleHoleResponse.GrainRelease
import Holonics.HNN.SingleHoleResponse.ComposedConsumer


/-!
# HNN.SingleHoleResponse: one shared source label through an absolute loaded word

[definition; bounded consumer of the accepted 6f536ac3 certificate] This file makes the exact
single-hole affine section explicit. The first-source terms keep the full first population
normalization; pair terms keep the full offset population normalization on each edge. The label
at the hole is the same `c` in every first term, pair endpoint, source port and offset. Each ordered
pair edge carries its own bilinear kernel `F e` and phase/lift placement `Q e`, so different source
rings and offsets retain their distinct `PairPort E_g^(δ)`. A pair edge has distinct endpoints, so
at most one endpoint is the hole. Consequently its one-hole term is linear in that shared label;
no independent endpoint labels and no quadratic hole term are introduced.

The source-side operands recover through `HNN.Moment.encoderMoment_add`,
`encoderMoment_contract`, `exteriorOffset_independent_of_E`, `Objects/SourcePorts.port_eq_symbol_sum`,
and `Objects/SourceHolon.offsetMomentAt`: first and ordered-pair source counts are already owned.
The expansion below specializes those terms to one missing station and explicit complete-population
normalizers. The physical consumer uses `HNN.LoadedMedium.loadedOp` at `openedAt + t`, over the full
loaded state. Only the actual source-to-state opening/injection and receiver chart are boundary
hypotheses: the current owners do not yet prove that Rust's `station_section`,
`PairPort::apply_table`, `PopulationChart::value`, and its rational carriers instantiate those
Lean operands. This file does not claim an exact rational-Rust to real-Lean embedding or a Lean
GrainCell implementation; those concrete joins remain open.

Computational object: the helical pair interaction. Winding objects touched: helix, pair,
navigator faces and placement, and tube. Cell holonomy and the tower thread remain attached.
Recorded failures this consumer is structured to avoid: dropping the shared-parameter cross terms
or using independently varied endpoints; using a static tick across a pump; releasing from a
coordinate enclosure that loses correlation; and treating model constancy as recovery of the
removed truth. The law here is exact linear/unit transport only, with no chart/lattice residual or
saturation premise hidden in the consumer.

No axiom, sorry or native_decide.
-/

noncomputable section

/-! Stable full-owner import facade: the declarations live in six dependency-ordered proof
owners, and all of them remain reachable here. The exact source, absolute loaded response,
normalized opening, receiver, grain-release and composed selectors below are unchanged. -/

#print axioms Holonics.HNN.SingleHoleResponse.firstComplete_eq_fixed_add_response
#print axioms Holonics.HNN.SingleHoleResponse.pairComplete_eq_fixed_add_response
#print axioms Holonics.HNN.SingleHoleResponse.oneHoleSourceExpansion
#print axioms Holonics.HNN.SingleHoleResponse.populationNormalizedOneHoleSourceExpansion
#print axioms Holonics.HNN.SingleHoleResponse.absoluteLoaded_response_add
#print axioms Holonics.HNN.SingleHoleResponse.openedState_from_normalized_source
#print axioms Holonics.HNN.SingleHoleResponse.loadedReceiving_response
#print axioms Holonics.HNN.SingleHoleResponse.exactLeaderUnion_mem_iff
#print axioms Holonics.HNN.SingleHoleResponse.exactLeaderUnion_sound
#print axioms Holonics.HNN.SingleHoleResponse.constant_face_released_at_zero
#print axioms Holonics.HNN.SingleHoleResponse.holdingLaw_releases_constant_face_at_zero
#print axioms Holonics.HNN.SingleHoleResponse.singletonLeader_holdingLaw_release
#print axioms Holonics.HNN.SingleHoleResponse.normalizedSource_loadedWord_grain_singleton_release

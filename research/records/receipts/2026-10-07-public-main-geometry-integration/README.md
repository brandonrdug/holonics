# Current public-main geometry integration receipts

`OWNER_MATERIALIZATION.v1.json` pins the published base, branch, four accepted owner hashes,
root working sources and exact materialized bytes. `preserved-public-base/` and
`preserved-root-source/` preserve those cuts before copying. They are evidence, not additional
library owners. `ATLAS_SCOPED_DELTA.v1.json` limits documentation edits to four added rows.

`ACCEPTED_PROVIDER_BASE_COMPARISON.v1.json` compares the accepted producing request pins with
the public base. `CURRENT_SOURCE_IMPORT_GRAPH.v1.json` enumerates the actual transitive local
import closure after materialization. Foreign/native part, package and lookup provenance must
still be checked by the shared queue. Matching a source hash alone does not admit an object.

`prior-accepted/` preserves selected earlier acceptance and binding receipts.
`PRIOR_ACCEPTANCE_BINDINGS.v1.json` identifies their exact origins. These support source-matched
reuse of accepted objects; they do not certify the new combined importer.

`IntegratedGeometryConsumers.lean` is the fresh independent import/consumer check. It imports
the materialized FrameTransport, Motion and SourceHolon (which imports CausalChord), then
queries sixteen (`2⁴`) actual derivative/J/Jdot, work-defect/work and future-read closures.
The consuming equations remain in their existing owners.

`QUEUE_REQUEST.v1.json` is one coherent packet behind HNN, with inherited resource ceilings and
fixed-projection requirements. This lane launches no compiler or native run. Queue results must
record exact source/object/provider/import bindings, standard-axiom verdicts, measured resources
and quiescent release. The source-only breadth record and private NS Mean replacement receive
no kernel acceptance from this request.

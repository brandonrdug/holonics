# Publication evidence and replay scope

Run from the checkout:

```bash
python3 -B research/records/receipts/2026-10-09-rh-spectral-publication/verify_publication.py
```

This checks exact file seals, the six accepted-source/public-owner joins,
unchanged non-import proof bytes, 23 native standard-axiom printouts,
seven atlas rows and the existing index route. It runs no Lean compiler.

`SOURCE_PUBLICATION_JOIN.json` maps each immutable accepted snapshot to its
canonical research-library owner. `KERNEL_ACCEPTANCE.json` records the
actual private native gate. The source-status comments and dependency
import names are the only publication changes; each diff is included.
The canonical module graph still requires focused validation by the sole
native queue. Private accepted `.olean` files must not be renamed or treated
as public module objects. No full library gate is claimed.

`compiler.stdout` and `compiler.stderr` are projections of actual diagnostics:
only absolute source-location paths are replaced with canonical owner paths.
Original byte hashes and projected byte hashes are recorded separately.
`NATIVE_VALIDATION_PUBLIC.json` selects scope, result and numerical resource
fields, omitting private source requests and control namespaces. No mailbox
content is included. Original receipts remain immutable outside Git.

The three `rejected-predecessor` directories retain exact failed sources and
kernel results, with the same source-location-only diagnostic projection.
Their exit-one results and `sorryAx` printouts remain explicit. No predecessor
rejection is counted as accepted evidence.

Excluded from this scoped publication: compiled binaries/caches, complete
ordered import graphs, raw private resource/control namespace receipts,
source request packets and mailbox messages. Their applicable source/object
and original receipt seals remain in the join. This is sufficient for byte
and source-provenance review; it is not a standalone native compiler replay
package. The complete private native evidence is preserved separately.

All mathematical estimates beyond the finite identities remain open:
signed uniform norm decay, Mertens/RH composition, zero-only relative phase
and denominator control, actual completion/opposite-flux cancellation, and
the de Bruijn–Newman upper bound.

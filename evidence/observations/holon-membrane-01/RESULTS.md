# HOLON MEMBRANE 01 — THE EVENT EXTENT RIDES; THE SWEPT RELATION REOPENS

**2026-07-18 · FORMULA §XCII · RATIFIED / BUILT / HOST-GATED / CUDA-FORWARD GATED /
DURABLE WIRES REOPEN EXACTLY / 509 WORKSPACE TESTS PASS / 4 IGNORED / SOMA INTERIOR UNCHANGED**

## Result

The general membrane no longer derives an event population from storage width. The producing
transducer supplies the event extent. The historical material mouth remains explicit as the octet
adapter, while a second adapter admits one complete `EventHeader + payload` file as one event.
Both retain their exact material bytes and cross the same presentation ABI.

One receiver-relative swept construction now has a substrate-neutral sparse record:

```text
Presentation
  currents -> configurations -> current-local event incidences

HolonArc
  shared boundary cuts
  shared ordered transition receipts
  shared open residual sections
```

`HolonSpan` references those populations. It does not own a nested tree, duplicate event material,
assign a global parent, or carry probability, confidence, category, objective, or agent fields.

## Exact layouts

All extents and ordinals are checked 64-bit values split into little-endian `u32` words.

```text
Presentation Header        9 words
CurrentSpan                4 words
ConfigurationSpan          4 words
Presentation Incidence     6 words

Holon Header              15 words
BoundaryCut                4 words
HolonSpan                 12 words
TransitionReceipt         16 words
ResidualSpan               6 words
Cut/receipt/residual ref    2 words
```

`TransitionReceipt` carries six ordered cut roles:

```text
before -> meeting -> deed -> consequence -> return -> after
```

and an exact span of residual incidences. Every receipt role must belong to the `HolonArc` which
references the receipt. Every residual must name a cut in that arc and a real local configuration
incidence section. Orphan populations, partial spans, absent presentations/configurations,
noncanonical empty spans, truncation, trailing words, and unsupported layout versions are refused.

## Host distinction gate

The same 20-octet material current was admitted through two explicit adapters:

```text
typed-event adapter   20 physical octets -> 1 event
octet adapter         20 physical octets -> 20 events
```

The presentation header, current span, and incidence all retained `1` versus `20`. The typed-event
adapter also refused a short header and a valid event followed by unclaimed trailing material.

The strict presentation and Holon readers reconstruct the complete row populations from their
headers, validate every reference, and require exact exhaustion of the wire. Both open and
receipt-bearing `HolonArc` fixtures serialize and reopen byte-for-byte.

## Exact card ABI gate

`mount-holon-gate` crossed two material species and their complete sparse record through the
NVIDIA GeForce RTX 4080 SUPER:

```text
current 0   5 octets / 5 events
current 1  16 octets / 1 typed event

presentation   6 events / 2 currents / 2 configurations / 3 incidences
HolonArc       2 cuts / 2 cut incidences / 1 complete receipt / 1 open residual
ABI wire       108 u32 words
```

Both material currents and all 108 ABI words returned exactly.

The full reusable CUDA boundary was also exercised with the typed species rather than only a card
copy. One 16-octet current remained one logical event through real carriage, produced one
configuration and one open boundary cut, and manufactured no receipt. Its durable records were:

```text
edge.presentation   23 words / 92 octets
edge.open-holon     33 words / 132 octets
```

Both files were synced, reopened through the strict readers, and matched the live records exactly.

## Reusable boundary revision

The generic boundary plan now admits three explicit source species:

```text
material       historical octet events
typed_events   one complete typed event per supplied current file
eye            historical gaze/contact adapter
```

The arc-spectral and explicit-formula builders now emit `typed_events`; their event files no
longer silently become byte-count event populations. Generic boundary receipt v4 records each
lineage's material octets and transducer event extent separately, beside create-new
`.presentation` and `.open-holon` wires. Those wires are immediately reopened and checked before
the receipt closes.

## Observer quotient

`HolonArc::population_where` reads an exact receipt population as

```text
support / total
```

without storing a float or feeding the quotient back into conduct. Repeated receipt incidence
retains multiplicity; shared cuts retain common material without duplication. This is the first
concrete observer surface for the probability/loss law in §XCII. Residual orientation and full
receipt remain causal body; a scalar quotient never replaces either.

## Boundary retained

This construction changes the membrane and durable journal, not Soma's interior physics. CUDA
still carries the exact material octets through the established one-fold compatibility path. A
configuration and an open `HolonArc` are now retained rather than discarded, but sparse incidence
does not yet change the receiving fold. Actual consequence worlds must supply the later cuts which
close a real receipt; the membrane will not synthesize them from one presented edge.

```text
CURRENT  transducer-defined event populations + sparse configurations
HELD     exact material + shared cuts + ordered receipts + complete residuals
MEETING  one presentation configuration becomes one receiver boundary cut
TEST     octet/typed distinction + strict reopen + 108-word card gate + full CUDA edge
DEED     retain the open arc; never manufacture a return or infer an event from byte width
CARRY    exact presentation/open-arc wires -> later world cuts -> complete receipt population
GRADE    BUILT / HOST+CUDA-FORWARD GATED / DURABLE REOPEN EXACT / SOMA INTERIOR UNCHANGED
```

## Exact commands

```text
cargo test --manifest-path src/soma/Cargo.toml --workspace
cargo test --manifest-path src/soma/Cargo.toml -p life typed_event_crosses_cuda_and_reopens --lib -- --ignored --nocapture
cargo run --manifest-path src/soma/Cargo.toml -p mount --bin mount-holon-gate
```


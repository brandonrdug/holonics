# Native phase operations on Metal

[definition] `native_phase.metal` realizes the same local rational-linear constitutive fibre,
circulation and rechart operations as `crates/holonic-engine/kernels/exact_resident_section.cu`.
The Rust owner remains `NativeConstitutiveEcology`; `mount::metal` supplies resident storage,
ordered device commands and completion. MLX remains independent representation-test apparatus.

[definition] Public carriers are exact signed i64 points with a positive common denominator.
Intermediate carriers use four u32 magnitude limbs and a sign, admitting magnitudes through
`2^127 - 1`. Overflow, malformed denominators, inverted intervals and inherited refusal are
explicit status words. The kernel validates every continuing basis/memory word before commit.
Rechart writes fresh deltas; the existing native owner publishes them after successful return.

[definition] The first implementation dispatches one device thread per dependent operation.
Its serial limb arithmetic, elimination and local staging preserve the complete recurrence.
The command queue serializes requested dependencies; neither thread count nor shared memory
establishes parallel independence. Dynamic threadgroup storage uses 20 bytes per wide carrier,
rounded to Metal's 16-byte allocation multiple. Unsupported resident symbols refuse at lookup.

[definition] `phase_convolution.metal` owns both placements of complete causal convolution.
Its checked product/add helpers are shared with the paired/enclosed field and retain CUDA's
operation-specific accumulator admission, including the 126-bit checked-add magnitude bound.
When the result exceeds threadgroup storage, one passage records complete input validation,
parallel products with disjoint output coordinates, one whole-result gcd, and disjoint normalized
publication into private output. Each coefficient retains ascending source order; validation
precedes arithmetic, and no output is admitted after any refusal. The Rust owner retains both
operands and device workspace until completion. This changes placement, not temporal support
or native grain, and requires no intermediate numerical readback.

[definition] Build arithmetic apparatus explicitly; the probe kernels are absent from production:

```sh
mkdir -p .local/setup/apple-silicon
xcrun -sdk macosx metal -DHOLONICS_ARITHMETIC_PROBE -c accelerators/metal/native_phase.metal -o .local/setup/apple-silicon/native_phase_probe.air
xcrun -sdk macosx metallib .local/setup/apple-silicon/native_phase_probe.air -o .local/setup/apple-silicon/native_phase_probe.metallib
python3 research/experiments/apple_silicon/generate_wide_cases.py
swift research/experiments/apple_silicon/native_phase_arithmetic_check.swift .local/setup/apple-silicon/native_phase_probe.metallib research/experiments/apple_silicon/wide_cases.json
```

[established-bounded; measured] The M1 Pro returned parity for the 28 existing engine phase tests,
including exact reference, full fibre/lineage, rechart, rest and atomic-failure controls. This
scope does not establish the arbitrary-width native owners or the inherited full operator.
The [platform plan](../../docs/plans/HOLONICS_ON_APPLE_SILICON.md) retains the construction scope.

# Acoustic field execution receipts

[definition] These are bounded execution receivers for the [field construction](../2026-09-06_APPLE_ACOUSTIC_FIELDS_AND_HOLONIC_PROFILING.md),
not a sound/language quality evaluation. Apparatus: M1 Pro MacBook, 8 CPU cores, 14 GPU cores,
16 GiB shared memory; macOS 26.5 (25F71), Rust 1.98.1, Cargo 1.98.1. Release builds ran without
simultaneous compilation. No calibrated energy or thermal claim is made.

[definition] `seed-16.json` and `seed-32.json` declare unit matched admittances, unit incoming
transport and zero initial held current. Every file records one continuing field across the same
complete ESC-50 dog clip and LibriSpeech English clip, in that order. Receiving handles are absent;
there is no authored temporal contact or learned acoustic morphology. Source paths and byte digests
identify exterior input files only. WAVs remain in the ignored local dataset directories; provenance
and licensing are in the [acoustic guide](../../../docs/ACOUSTIC_EXPERIMENTS.md).

[definition] `field-16.jsonl` and `field-32.jsonl` are the initial aperture sweep before command-buffer
timestamps. `field-32-timed.jsonl` adds GPU execution timestamps and is the matched baseline for the
subsequent exact arithmetic fast paths. `field-32-optimized.jsonl` uses the same seed, inputs, native
law and observer, with those fast paths. They are two individual runs, not a statistical population.
Each JSON line reports a complete source recording. The profile adds zero terminal reads; the
underlying native field API still reads each operation's terminal result and retains its history.

[definition] Reproduce the optimized measurement from the commit containing this directory:

```sh
cargo build --release -p holonics-hna --example acoustic_field_profile
target/release/examples/acoustic_field_profile \
  research/records/2026-09-06_acoustic_field_profile/seed-32.json \
  .local/datasets/esc50/audio/1-100032-A-0.wav \
  .local/datasets/librispeech-dev-clean-subset/wav/2277-149896-0000.wav
```

[definition] The matched baseline was built from the same working construction before the
single-limb multiplication/division and unit-GCD normalization fast paths in
`accelerators/metal/native_phase.metal`. The earlier aperture sweep additionally predates the
timestamp apparatus. The dated record retains these source differences explicitly; the merged
desktop revision alone does not reproduce these Mac measurements.

[definition] `timed-baseline.patch` reverses only the three arithmetic specializations. In an
isolated checkout of this return, apply it with `git apply`, then build and run the same command
to reproduce the baseline implementation. It retains the new field kernels and timing apparatus.

[definition] Relevant verification commands (device tests explicitly enabled):

```sh
MTL_DEBUG_LAYER=1 cargo test -p holonic-engine --lib native_ecology::constitutive_fibre -- --include-ignored --test-threads=1
MTL_DEBUG_LAYER=1 cargo test -p holonics-hna --lib native::acoustic_field -- --include-ignored --test-threads=1
cargo test -p mount --lib metal::tests -- --test-threads=1
xcrun -sdk macosx metal -DHOLONICS_ARITHMETIC_PROBE=1 -c accelerators/metal/native_phase.metal -o /tmp/native_phase.air
xcrun -sdk macosx metallib /tmp/native_phase.air -o /tmp/native_phase.metallib
swift research/experiments/apple_silicon/native_phase_arithmetic_check.swift /tmp/native_phase.metallib research/experiments/apple_silicon/wide_cases.json
```

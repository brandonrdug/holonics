# Exact source contraction receipt

Date: 2026-10-16 UTC

## Change

`PairPort::apply_table` now contracts through `ExactPairContraction`: fixed rational factors are compiled into exact integer charts with LCM-based shared denominators; occupied count/rank contributions are summed in integers before output contraction and final normalization. `moment_parts` compiles each active offset port once across phases. `physical_source_pairing` likewise compiles the old/new pair-port charts once before its phase loop. No float arithmetic, precision ceiling, truncation, or altered learning law is introduced. The termwise rational implementation remains available as a test oracle under `cfg(test)`.

## Exact checks

Commands, using the isolated Rust 1.99.1 toolchain and existing target directory:

- `cargo +1.99.1 test --locked -p holonics hnn::tests::moment:: -- --include-ignored --test-threads=1 --nocapture` — 17 passed, including exact dyadic/non-dyadic/leaky comparisons, an actual founded leaky `open_storage` comparison, and the synthetic benchmark.
- `cargo +1.99.1 test --locked -p holonics same_word_source_return_refuses_foreign_phase_clock_map_and_opening_covectors -- --test-threads=1` — 1 passed after the `prediction.rs` reuse change.
- `git diff --check` — passed.

The full repository gate is separate and owned by the trace worker.

## Synthetic arithmetic benchmark (not MNIST)

Fixture dimensions: alphabet 16; rank 4; 256 occupied slots; output width 8; 128 repetitions. Exact old/new outputs compared equal.

- Termwise rational total: 1,505,096,546 ns.
- Shared-denominator integer total: 28,508,791 ns.
- Input factor numerator-plus-denominator payload: 958 bits.
- Compiled integer chart payload: 3,488 bits; ceiling of payload bytes: 436. This excludes container and allocator overhead and is not total transient memory.
- Phase-weight / feature / output / final denominator sizes: 9 / 45 / 23 / 75 bits.
- Exact output numerator-plus-denominator payload: 968 bits.

This fixture demonstrates arithmetic equivalence and cost on the synthetic dimensions above. It does not establish MNIST `ModeExplorer::propose` speedup or that this is the measured dominant path. Runner profiling of the actual proposal and its real-workload bit volume remains pending.

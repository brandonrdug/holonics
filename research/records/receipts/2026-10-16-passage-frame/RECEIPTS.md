# Receipts: the receiver reads in the passage frame

Host reference, 4 cores, testing the passage-frame receiving law F1. Record:
[the passage frame](../../2026-10-16_THE_RECEIVER_READS_IN_THE_PASSAGE_FRAME_AN_ABSOLUTE_LIFT_RELEASED_ONE_CLASS.md).

## Focused checks

`cargo test -p holonics --lib -- an_identical_arrival_reads_identically_at_two_receiving_clocks
the_word_return_is_the_exact_adjoint_of_its_tangent_map
the_read_adds_the_trees_face_to_the_passage_frame_wave receiving_section_reads_each_mode_over_its_cycle`

```text
test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 1281 filtered out; finished in 1.78s
```

## The gate

`timeout 300 bash tools/gate.sh`. Projection from the stage maxima measured before launch (check
35 s, lints 46 s, doctests 62 s): 143 s; deadline 300 s.

```text
gate check: ok (13275 ms)
gate guard-lints: ok (22820 ms)
gate guard-doctests: ok (19915 ms)
```

Wall 56,024 ms against the projection of 143 s. The previous run failed one guard doctest
(`hnn::port`, line 53, `compile_fail,E0308`): the example still passed the removed lift argument,
so it failed with E0061; the example now passes the covector, map and phases alone.

## The changed laws' tests

The `hnn::tests` modules receiving, ratio, port, pending, physical, prediction, word, constitution,
retention, reference, learning and prior_carry (`--test-threads=4`, deadline 900 s), then the
integration tests physical_action and physical_ask (deadline 600 s). Unmeasured before launch, so
planned at one to three minutes each.

```text
test result: ok. 254 passed; 0 failed; 0 ignored; 0 measured; 1031 filtered out; finished in 558.08s
test result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.20s
test result: ok. 11 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 1.87s
```

The library stage took 576,954 ms against the planned one to three minutes (inside its 900 s
deadline): the plan was low by a factor between 3 and 10, driven by two tests that each ran past
60 s (`physical::the_resident_certifies_the_applied_source_return_at_its_carried_clock_and_nonzero_phase`,
`reference::the_chained_balance_closes_on_a_pumped_field`). The integration stage took 65,188 ms.
Peak resident set was not measured for the gate or the tests.

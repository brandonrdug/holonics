# Receipts: the ranged and leaky capacity integration (October 6, WIP)

Each `.receipt` is one run: command, deadline, status, wall ms, and the peak resident set of the
largest waited child process (KiB). Projections are stated below with the ratio of measured to projected.

| run | projection | deadline | status | wall ms |
|---|---|---|---|---|
| lean-devread (4 stale roots) | development read | 900 s guard | exit 0 | 9,371 |
| lean-leaves (RangedMoment, LeakyCapacity) | 5,005 lines × 0.0361 s/line ≈ 181 s | 181 s | exit 1: two LeakyCapacity elaboration errors | 23,833 |
| lean-leaves-2 (after the two proof-term repairs) | 3.8 s + 1 module | 11 s | exit 0 | 5,575 |
| lean-holonics (158 stale modules) | 83,286 lines × 0.0361 + 3.8 ≈ 3,010 s | 3,011 s | exit 0 | 116,613 (ratio 116,613/3,010,400) |
| lean-leaky-v3 (v3 bit-bound leaf) | 3.8 s + 212 lines × 0.0361 ≈ 11.5 s | 12 s | **DEADLINE, incomplete** | 12,002 |
| lean-leaky-v3b | 3.8 s + one module at the largest measured module time, 16.0 s (169 measurements) = 19.8 s | 20 s | exit 0 | 3,566 |
| lean-holonics-v3 (3 downstream modules) | 3.8 s + 3 × 16.0 s = 51.8 s | 52 s | exit 0 | 29,388 |
| cargo-check-ws / ws2 / ws3 | 14 units × 7.2 s ≈ 101 s | 101 s | exit 101 (one borrow-order error), then exit 0, exit 0 | 10,221 / 1,114 / 2,966 |
| test-ranged / -2 / -3 | first read; then 29.7 s build + 8 × 1.86 s ≈ 45 s | 120 s, 45 s, 45 s | 7/7; 7/8 (the new test's own last assertion); 8/8 | 414 / 5,017 / 1,114 |
| test-entrance-restore | first read | 120 s | 8/8 | 2,114 |
| test-lib | 1,011 × 216.2 ms (largest recorded rate) ≈ 219 s | 219 s | **DEADLINE, incomplete**: 1,010 passed; `hnn::tests::reference::the_chained_balance_closes_on_a_pumped_field` still running | 219,003 |

**The 12 s to 20 s relaunch is a deadline raise.** Between `lean-leaky-v3` and `lean-leaky-v3b`
the law and the partition did not change. Only the declared projection unit changed, from a
per-line rate to a per-module upper. That unit change raised the deadline, and it is recorded here
as a raise. `lean-leaky-v3` stays incomplete. During it, a 15 GB reflink copy of the cargo target
had just run and btrfs-cleaner was active. `lean-leaky-v3b` is the completed check of the v3 leaf.

`test-lib` is incomplete. Whether this change slows `the_chained_balance_closes_on_a_pumped_field`
was not measured: no per-window baseline was read before the stop.

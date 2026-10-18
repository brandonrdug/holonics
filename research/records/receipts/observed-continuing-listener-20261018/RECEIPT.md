# Final-head receipts for the continuing listener (October 18)

Source: `ef779a23c189fce7133f52fa98ba3a63a663dc9f`, tree `597546db4aad4507c46eff818ca65ce89c7af652`,
one commit on `83026b84`. Every reading below ran on this exact source, one stage at a time. The
full native logs stay private because they hold released text from a GSM8K-trained run; this
directory keeps the role/nanosecond listings and the exact values they support. Ratios are
measured over the fixed deadline, which is each run's projection.

## Gates

| Reading | Result | Wall (ns) | Fixed deadline | Peak resident |
|---|---|---|---|---|
| `bash tools/gate.sh` | exit 0 | 112598497199 | 180 s | 2104764 KiB |
| optimized listener build | exit 0 | 93206612920 | 180 s | 1904124 KiB |
| `cargo test -p holonics --no-fail-fast`, 4 test threads | 12 targets, 1541 passed, 0 failed, 1 ignored (library 1352, 64 guard doctests) | 1540261348786 | 3000 s | group 3144249344 bytes |
| listener example tests | 17 passed, 0 failed | 110199366099 | 180 s | 2036520 KiB |
| GSM8K partition/framing tool tests | 2 passed, 0 failed | 101151137 | 180 s | 19292 KiB |
| `flock .local/gpu.lock cargo test -p holonics-cuda --no-fail-fast -- --include-ignored --test-threads=1`, idle NVIDIA L4 (8.9, 23034 MiB) | 59 passed, 0 failed (library 57, located ingest 1, occurrence placement 1) | 1087038756797 | 3425 s | group 1995247616 bytes |

The host suite's one ignored test is declared by Cargo and is not claimed covered. The device suite
was a second attempt; the first stopped on a transport interruption, is incomplete, and is kept with
its own receipts.

## Material and key stream

GSM8K `train.jsonl` from the public grade-school-math repository, sha256
`17f347dc51477c50d4efb83959dbb7c56297aba886e5544ee2aaed3024813465`, framed by
`tools/gsm8k/partition.py` and `tools/gsm8k/frame_gsm8k.py` (frame function sha256
`90f8820b189c9be8e7553e6d9b4334f63748a85f61a7775eac2be113adc9a69f`).

| Frame | Bytes | sha256 | Earlier identity |
|---|---|---|---|
| first learning section | 300 | `c813b9037a61c128b0fe75c7ac8ed310adc4c8b3b163c832a76c624c758106a6` | matches |
| first development read section | 675 | `b15f49106e938ab1c7a993cb57b26c053b601908c5b3f5dfb408cbce112a8924` | matches |
| first development release section | 296 | `d8fa45d1796207503c41ccc651c85726338d7902fd284e01432cf0d09b6c6aad` | matches |
| G4 development seed (first 16) | 51 | `e82cab1e58adcc5708730b1f79340cad6a3905b492ab8b56d9b9c78d39af44b9` | declared here |

The key stream is 2¹⁶ keys of 32 bytes, key `i = SHA-256(b"holonics G1 key stream" ‖ i as 4-byte
big-endian)`, concatenated in order: 2097152 bytes, sha256
`c04151d6cd8db21dc16d5187bc36be351679b7e89b8a33bbffa8614f204b66c9`. It is a new declared stream,
not the earlier `fbbab289…7c83` file, which was excluded from the transfer to this host.

## G4: the first GSM8K learning section on the observed route

Counts: 312 source and 254 answer cells (566 compared) and a drawn series of at most 312, the longest
passage delivered before the fork.

On the observed route the per-cell cost grows along the continuing moment, so an early maximum does
not bound later cells. The seed run (34 source, 34 answer and the drawn series) is the development
read: it completed in 30221498927 ns within its fixed 180 s, peak 66444 KiB. Its source positions
scale the same host's earlier 566-cell series of the same section:

- `r = 162589629/75401474`, the largest ratio over the first 34 source positions;
- `q = 1`, drawn over compared maxima;
- `u = r · 414451802 ns = 33692782362780729/37700737 ns` (893690284 ns, remainder 6241421);
- `P = setup + 566·u + 312·q·u = 29618496868080386068/37700737 ns` (785621163535 ns, remainder
  13360773), with setup 961094038 ns;
- deadline `⌈P⌉ = 786 s`; stop when the cumulative completed whole-cell time exceeds the declared
  cumulative upper; 8 GiB; one worker.

Result: exit 0, no stop, wall 343506361889 ns, peak group resident 84152320 bytes, peak child
75728 KiB. All 878 cells completed (566 compared and 312 drawn); native plus report time is
342131479722 ns against the cumulative upper `29582262914521480062/37700737` ns, and every
completed prefix stayed under it. Measured over projection is
`12950443007404012193/29618496868080386068`.

Largest whole-cell times (native + report ns): source 525118739 + 13038469, answer
626739862 + 12588741, drawn 220152042 + 38433. The full listing is
[`g4-full-role-ns.jsonl`](g4-full-role-ns.jsonl) and the seed's is
[`g4-seed-role-ns.jsonl`](g4-seed-role-ns.jsonl): role, unit, native and report nanoseconds, the
cell's wall and arrival time, and for the full run the per-cell and cumulative upper.

## G1: byte parity of the section route

The baseline I′ is the integration's six source commits (27845bc, 6c80a1e, 3827d23, 20f8a5e,
4eb6d9e, c36c40e) replayed on `83026b84` as `72b05af4ad4113053e0de9811880b032aa1c4aab`, tree
`97de16fd1cedc33fccdc5772e2bda0858f39c4e9`. Replayed on the original base `6e1a209` the same
commits give tree `6fae185d`, the tree recorded for the earlier baseline. Each side has its own
optimized binary: base `f47afe17b9d498658f9ecbb5663932254942de9ca22045e7fc03738d701b705c`, head
`b04c980cd09c9c81cc2c9050cef3b23f3083e96317b81d937a883f712b455254`.

The learning bound per cell is 930341146 ns, the largest earlier measured value; a 20-cell head
development read (largest 471018133 ns) did not raise it. Projections: read
`236306651084 + 53410030324 + 559360000000 + 1098377731 = 850175059139` ns, release
`236306651084 + 53410030324 + 1472000000 + 1098377731 = 292287059139` ns. The four processes ran
serially, each with 8 GiB and one worker.

| Run | Wall (ns) | Projection (ns) | Measured / projected | Learning sum (ns) of 236306651084 | Peak |
|---|---|---|---|---|---|
| base read | 334557130622 | 850175059139 | `334557130622/850175059139` | 130427246170 | 70996 KiB |
| head read | 333724044444 | 850175059139 | `47674863492/121453579877` | 133563247545 | 79796 KiB |
| base release | 131935656115 | 292287059139 | `131935656115/292287059139` | 130104820073 | 71216 KiB |
| head release | 135315520579 | 292287059139 | `135315520579/292287059139` | 133456071169 | 73552 KiB |

Each run learned 254 cells, exited 0 and did not stop.

The comparison masks only timing values, the section line's `factor_release` value, and four
report-label renames applied on the base side (`octet_nibbles → octet_digits`,
`high_nibble_bits → quotient_bits`, `low_nibble_bits → remainder_bits`,
`elapsed_ms → elapsed_ns`). No released content is masked. `cmp` exits 0 for both:

- read: masked sha256 `95fc0960d12082d31b6647d80cb6e0fd7df6afc5804299d801a4d46e3d2a5c7f` on both sides;
- release: masked sha256 `1d752d2a0c2e639894bc0568d2f52005af3aa3705cc2781861d00e553967f28f` on both sides.

The masked `factor_release` field changed on purpose (S23). Whole, in the read and the release alike:

```text
base: factor_release=[Channel(0):entries=591,largest<=13068393/34359738368,half_founding_unit=2^-11,lt;Channel(1):entries=591,largest<=14867491/68719476736,half_founding_unit=2^-11,lt]
head: factor_release=[Channel(0):entries=591,largest<=52173743/137438953472,half_founding_unit=2^-11,lt;Channel(1):entries=591,largest<=29677447/137438953472,half_founding_unit=2^-11,lt]
```

The base rounded each released term up to 8 significant bits, a chosen report precision; the head
sums the released magnitudes exactly. The exact bound is the tighter one, by `99829/2³⁷` on
channel 0 and `57535/2³⁷` on channel 1, and both stay below half the founding unit, `2⁻¹¹`.

All these readings ran on one personal host except the device suite, and none consumed accelerator
compute units except the device suite.

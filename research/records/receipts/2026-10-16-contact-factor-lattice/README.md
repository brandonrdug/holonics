# Receipts: the contact factors under the exact coarse law and the common lattice law

## GSM8K octet listener (`q1`, `q2`, `p4`, `p5`)

Each file holds one run of Epime's GSM8K octet listener, a measurement harness built during the
October 15–16 outage on main `337f351e9` and not published here, with every per-cell line removed.
What is left: the run's header, each section's and read's summary line, the release's summary and
text, and the measured receipt (`exit`, `wall_ns`, `peak_rss_kib`). The headers state the chart,
the sections and the release octet limit. The 59-octet release text is the run's own generated
output, not dataset text.

All four runs are on the host reference, condition B: `--reception rest` with the measurement
switches `HOLONICS_SCRATCH_STORAGE_SCALE_BITS=6` and `HOLONICS_SCRATCH_HOLD_RECEIVING_PRIOR=1`, two
threads (`RAYON_NUM_THREADS=2`).

| File | Chart | Contact-factor law | Run | Projection, deadline | Measured wall over projection |
|---|---|---|---|---|---|
| `q1.txt` | one place, 16 classes | exact coarse split (October 7) | learn sections 0 and 1 | none recorded | not available |
| `q2.txt` | one place, 16 classes | common lattice law (`HOLONICS_SCRATCH_FACTOR_FINE_GRID=1`) | learn sections 0 and 1 | none recorded | not available |
| `p4.txt` | two places, 32 classes | exact coarse split (October 7) | learn 0 to 3, read unseen 4 and 5, one release | 3,460 s, 3,600 s | `304,861,635,177/432,500,000,000`, below one |
| `p5.txt` | two places, 32 classes | common lattice law (`HOLONICS_SCRATCH_FACTOR_FINE_GRID=1`) | learn 0 to 3, read unseen 4 and 5, one release | 2,468 s, 2,500 s | `1,813,856,105,307/2,468,000,000,000`, below one |

`q1` and `q2` were short development reads launched without a recorded projection or deadline, so
their receipts lack that part; their walls (`157,569,784,385` ns and `117,246,018,280` ns) are
measurements only.

The release draws from 32-byte keys read from the kernel's random source before any release, so
no key is formed from anything a release reads. The keys and the framed sections are not kept
here.

## MNIST, 200 learned and 50 development images, on the card (`mnist-v25-v26.txt`)

Epime's matched pair of October 16 on a Colab card: v25 (the October 7 law) and v26 (this law),
each an overlay on main `337f351e9`. The file keeps, per run, the source overlay's base and size,
the release build and the card parity test with their exit codes and times, the model's arguments
(the dataset directory as `<mnist>`), its exit code, wall, peak host resident set and sampled card
memory, the checkpoint's sizes, restore checks and constitution bits, the run's own `complete`
line, the update counts, and the carry payload by locus. The dataset is public MNIST; its files'
SHA-256 values close the file. Machine paths are removed.

Each run had a 1,800 s deadline (the wrapper's timeout) and no recorded projection, so its
measured-over-projected ratio is not available: v25's wall `797,210,130,278` ns and v26's
`820,376,293,829` ns are below their deadlines, `398,605,065,139/900,000,000,000` and
`820,376,293,829/1,800,000,000,000` of them.

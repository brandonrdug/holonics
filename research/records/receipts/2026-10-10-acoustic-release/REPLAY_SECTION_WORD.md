# The section word's public replay (October 10)

The acoustic branch's later history descends from the same accepted, unpublished ancestry as the
cell codec's ([codec replay](REPLAY_CODEC.md)). Each commit from the phase-address draft to the
section 29 record is replayed by the same **tree substitution**:
- its own tree, with the receipt `RELEASE_RUN.v1.json` taking the published redacted blob;
- its parents mapped to their replays (`4776faec → 98abf837`);
- its author, dates and message kept.

Each replay differs from its original only in that receipt line. The chain therefore carries again
the octant wording correction (`0942c664`, already on main as `f63a3156`), and it now carries the
phase-address draft and the loop plan (`246b8d23`), which the codec's replay left out. The merge
onto main resolves the duplicated correction to the same text. The originals are kept unpublished
and unchanged. Loop 2's work (`8f6534d3` and after) is not in this candidate.

| original (unpublished) | public replay | difference | subject |
|---|---|---|---|
| `246b8d234413` | `f3364b7d876b` | receipt line | acoustic: the phase-address codec drafted (section 21, uncompiled); the  |
| `0942c664b311` | `3d906b8d61e5` | receipt line | records: the octant's bit is per non-origin tick (Refs #386) |
| `c62338ab6b73` | `50611b64eb5b` | receipt line | records: loop 1's design from the owners' interfaces; the defects are su |
| `ac62aab8ebe4` | `bdbcd098348e` | receipt line | records: loop 2's acceptance, the ring's material learning from its own  |
| `4f0fb72f0ad7` | `e32d258d3e26` | receipt line | acoustic: loop 1's W1 measured not met (no declared pair frame carries t |
| `f06ff2b036c6` | `614e800878f3` | receipt line | acoustic: a ring's section word enters the field through its located cyc |
| `9a930d20a7a9` | `c26ae45898bf` | receipt line | acoustic: W3, the recording's windows through the located navigator's ow |
| `154aeb4b3ef6` | `649bcefb5d07` | receipt line | acoustic: W3's full read incomplete at its deadline, the driver keeps fi |
| `f461436a1178` | `f366954c57bd` | receipt line | acoustic: the clean section word enters the field on its located helix,  |
| `9a5fbaf55629` | `0769f4c90ce8` | receipt line | acoustic: the departed section word enters as its runs in the cycle's ch |
| `f7dd904dc352` | `d20f9c3c3da7` | receipt line | acoustic: the near-return's emitted code and reader in its owner, and th |
| `b0fe58525773` | `add7f1d5b094` | receipt line | records: 29 measured, the section word's cells shorten the whole recordi |

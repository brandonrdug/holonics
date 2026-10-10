# The cell codec's public replay (October 10)

The acoustic branch's history after the first rung was built on the accepted, unpublished
`04ac5e43`, whose ancestry carries the receipt line naming the private input. The published history
carries its replay `d196dee3` ([first replay map](REPLAY.md)). Each later commit is therefore replayed
by **tree substitution**: its own tree, with the receipt `RELEASE_RUN.v1.json` taking the published
redacted blob, its parents mapped to their replays (`04ac5e43 → d196dee3`), and its author, date and
message kept. Each replay differs from its original only in that receipt line, or not at all when the
commit's tree does not hold the receipt (the section-winding join, based on `c7495d79`). The originals
are kept unpublished and unchanged. The octant wording correction (`0942c664`, a one-line record
change) is applied on top as `f63a3156`; the later phase-address draft and the loop plan (`246b8d23`)
are excluded.

| original (unpublished) | public replay | difference |
|---|---|---|
| `fe4b6b63d187` | `da7ec4f19bed` | receipt line | acoustic: each ring decodes its own moment keys; the keys carry part of  |
| `40d47d104cb5` | `bbd2d8b4d5ae` | receipt line | records: the next acoustic rung decodes the source as the keys' least-po |
| `8cc51665e5b9` | `bfa46e9769c6` | receipt line | acoustic: the lock census reads the existing lock owner on the recording |
| `4deb60b0a215` | `3dcf77207176` | none (committer only) | hnn: the section owners call the winding owners at their consumers (Refs |
| `54040fdcd784` | `8cdd7a761ab3` | receipt line | Merge branch 'claude/section-winding-join-20261010' into claude/acoustic |
| `68aece1a7630` | `f167873f5307` | receipt line | hnn::section_lock: the near-return grain, a description-length law with  |
| `293b19c423ec` | `e1fd5c318c32` | receipt line | acoustic: the decoder's key clock repaired; the near-return census (Refs |
| `b63f8f2704e4` | `336833031dd6` | receipt line | records, receipts: the repaired decoder measured; half-memory at complet |
| `61a2c35b4957` | `fd850c8684fc` | receipt line | records: the located acoustic rung, design and acceptance fixed before c |
| `2aee611a81d1` | `87eb102a0565` | receipt line | records: the acoustic rungs' obligations owed to #62 (Refs #62 #386) |
| `0485b175e07e` | `410e93a03fd2` | receipt line | acoustic: the located rates read; the voice's rings near-return without  |
| `fa5a02b5e165` | `d71a1c61b7b5` | receipt line | records: the architecture choice; the source through one ring's inverse  |
| `9748b3514eec` | `a3c2a8d4fa2f` | receipt line | acoustic: the non-turning near-returns read period 1 in the voice's ring |
| `111424338893` | `1e0e1cc81ffe` | receipt line | hnn::ring: the tick read backwards; the source is one ring's inverse tic |
| `3e1c051de7d3` | `139944893ceb` | receipt line | acoustic: the source coded losslessly through one ring's cells; ring 20  |
| `2786acd27b9c` | `fc857c9a5fc6` | receipt line | records: the source reviewer's refinements to the one-ring source archit |
| `4439785baef3` | `ff090eecfe69` | receipt line | hnn::ring: the inverse refuses a charted solve and checks the carry cont |
| `ec1b950ad056` | `3aa28e7ce566` | receipt line | acoustic: the emitted cell codec and its independent decoder (record sec |
| `291845a04741` | `119d69481994` | receipt line | records, receipts: the cell codec decodes the recording exactly from rin |
| `b60b288a6266` | `a94fe3eef748` | receipt line | CONSTRUCTION_STATE: the acoustic position after the cell codec (Refs #38 |
| `39304646ee8b` | `c742297ca8b4` | receipt line | acoustic: the octant grain for the cell codec (record section 20) (Refs  |
| `e7dfbf3c12ac` | `e5269fc3a6f5` | receipt line | records, receipts: the octant grain emits 1364296 bits against 1498880,  |
| `4776faecb2d6` | `98abf837847f` | receipt line | hnn::ring: the inverse admits only the canonical carry [−δ/2, δ/2) and a |

# The acoustic first rung's public replay (October 10)

The accepted pin's own receipt named the private input by its dataset-relative path. The published
history must not carry it, so the accepted acoustic commits are replayed onto published
`c7495d79` with that one receipt line redacted. The originals are kept unpublished and unchanged.

| original (accepted, unpublished) | public replay | difference |
|---|---|---|
| `aaf174102341214d5cdb1cdee5ea84a862cac870`, tree `dd644a63c29f124705e8f2d29520516ea547ebe4` | `e860ec74048e4002cdc42716345af3ffa1f6e6e5`, tree `b8f5221e4ea33f133e41780ddcc595ad8de35c02` | `RELEASE_RUN.v1.json` only |
| `04ac5e43c68b9ef6a842d7695dbc251f999209d3`, tree `b2817e695d7eff127192722cbd382608cef9bb4e` | `d196dee31c2b22164a1c24da52c8b839e888e6d9`, tree `a8aaf03d4e3034f5cae9028791ece1ec46355a20` | `RELEASE_RUN.v1.json` only |

**The redaction, receipt only.** In `RELEASE_RUN.v1.json`'s `scope` string, the phrase naming the
recording's dataset-relative path and directory is replaced by "a private 16-bit mono 16000 Hz speech
recording (LibriSpeech-derived; its path is withheld from the public receipt; the render is not
committed)". The input's class is kept: 16-bit, mono, 16000 Hz, LibriSpeech-derived. Every other
byte of the receipt is unchanged, including its `stdout_sha256`, wall time, resident set, deadline,
exit, ring rows and render readings.

| `RELEASE_RUN.v1.json` | bytes | SHA-256 |
|---|---|---|
| original (in `aaf17410` and `04ac5e43`) | 7817 | `e6d1b266fa9519dde49da0ee3491fb87f3662f99b78c945174979f67852a243b` |
| public replay | 7813 | `268e59d5e190fa1b50918e4becc7d1b8169c732ca778cb8c0249431e2d15188a` |

**What is identical.** Every other file of both commits, so every line of code, test, record and
atlas row, equals its original byte for byte. The queue's acceptance of `aaf17410` (gate, 17
wave-port tests, fresh build, full bank render; [publication note](PUBLICATION.md)) therefore covers
the replay's code unchanged. The private input's own size and SHA-256 stay bound in the queue's local
`VALIDATION.json`, which is not published.

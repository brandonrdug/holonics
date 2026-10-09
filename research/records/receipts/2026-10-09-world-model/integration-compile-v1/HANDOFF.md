Exact joined C1b library-test compilation **PASS** (exit 0).

Commit: `0c9cd67146088ce944353a954ae9e044191810fa`  
Tree: `1c7acd8979c3cfcdffc44049cb08993733975de6`  
Command: `cargo test -p holonics --lib --no-run`  
Effective argv SHA-256: `8cab7b352dbe5824fcc3ac3ab695a708f9a45502e70495f109da1e07822413f2`  
Source manifest SHA-256: `19db679ae0a6dcf18eb29b9b5b8b3f5a3dd16404110f62a32fce3ef68668500c`

All 352 native source inputs are bound to the exact clean tree before and after the compile. All five C1b source files equal accepted `0a7fa87a448232a273e7f9375d85f1dd90df649c`; the two differences in the larger native input set are the published diagnostic unit test and paired header. Cargo produced one fresh library-test executable (`fresh=false`), pinned in EXECUTABLE.json. Full stdout and stderr are preserved as `c1b-joined-lib-0c9cd6714-20261009-v1.stdout` and `c1b-joined-lib-0c9cd6714-20261009-v1.stderr`.

| Reading | Exact value |
|---|---:|
| Compiler wall, ns | 34157392129 |
| Guarded lifecycle wall, ns | 35012583451 |
| Fixed deadline, ns | 65000000000 |
| Measured / projected wall | 35012583451/65000000000 |
| Aggregate CPU, ns (1000 ns grain) | 35832805000 |
| Peak child RSS, KiB | 2146132 |
| Peak group memory, bytes | 2429689856 |

One Cargo job, four CPUs. Reservation and enforced cgroup cap: 4 GiB (`2^32` bytes). Maximum authorized ceiling: 8 GiB (`2^33` bytes). Prelaunch available memory: 12182847488 bytes. The fixed 65-second window uses recovered native compiler measurements; no limit changed after launch. The prior largest compiler RSS was 2232320000 bytes.

One inherited dead-code warning: `HeldContactVariation::advanced`, `crates/holonics/src/hnn/word/variation.rs:473`. Zero compiler errors.

Common lease released after all native descendants exited; final host inspection confirms no native process or owned unit remains. No runtime fixture, unrelated example/job, source edit, deletion, publication, process killing, cache clearing, restart, protected-session access or retired bridge use occurred. Prior 22-fixture acceptance remains at its accepted producer; this receipt supplies only the requested joined compile.

FILE_HASHES.json binds every preserved receipt/tooling file, excluding itself. The immutable Git commit supplies source bytes; the isolated executable remains under the path in EXECUTABLE.json. No private correspondence is included in this packet.

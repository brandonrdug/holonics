C1b-2a scoped native runtime acceptance **PASS**; whole repository lint gate **FAIL**.

Commit `a739963f68d6085eb41f5ae6a77f306151489e6d`; tree `c05b77cc19289652ea14b903b7efcad74728f78d`. Exact frozen Git bytes for all 352 native inputs were checked before and after execution.

Workspace/all-targets check, four fresh test executables, all nine world-model fixtures and 15 affected action/retention guards passed. Each of the 24 scoped fixtures ran exactly once. The affected library/test guard lints and all library guard doctests passed; the workspace check was not repeated.
Doctests passed: 57.

**Remaining gate blocker:** the all-targets Clippy command exited 101 because `crates/holonics/examples/helical_duplex.rs:189` calls disallowed `std::process::exit(1)`. This example is byte-identical at the tested pin, accepted C1b-1 `0a7fa87a4` and `3cfb2b71a`. Full stderr and provenance are preserved. No source edit was authorized or performed. The narrower affected lint pass does not clear this whole-gate failure.

The measured acceptance is the coupled prospect before the encounter: actual port waves and producing-frame native receiving logits `R x` share one latent `k`. Point fibres agree exactly; key/control refusal, tick accounting and read-only participant/memory comparisons pass. **World target-face coverage is outside this claim.** Raw `x` is not separately observed where `R` has a kernel; C2, Ask, learning through the model and GPU parity remain outside scope.

| Unit | Command wall ns | Guarded wall ns | Fixed deadline ns | Aggregate CPU ns | RSS KiB |
|---|---:|---:|---:|---:|---:|
| check-20261009-v1 | 27401353431 | 28851654435 | 65000000000 | 29047080000 | 1528624 |
| build-20261009-v1 | 53195231405 | 54869678864 | 65000000000 | 56027692000 | 2111620 |
| coupled-development-20261009-v2 | 2219163368 | 3660162936 | 135718806008 | 3453759000 | 28708 |
| nondestructive-development-20261009-v1 | 3001755880 | 4291479185 | 183971396176 | 4122371000 | 28912 |
| world-existing-20261009-v1 | 2612187044 | 3726131844 | 17534143576 | 3676631000 | 28652 |
| native-action-20261009-v1 | 575311025 | 1697533828 | 10876653472 | 1653169000 | 18368 |
| physical-action-20261009-v1 | 183929055 | 1323936078 | 10876653472 | 1277125000 | 18360 |
| retention-guards-20261009-v1 | 283926508 | 1432157393 | 17534143576 | 1387497000 | 30568 |
| clippy-20261009-v1 | 10312081621 | 11693659533 | 65000000000 | 11773525000 | 981860 |
| doc-20261009-v1 | 24370429705 | 25803726535 | 65000000000 | 26265342000 | 1413436 |
| clippy-affected-20261009-v1 | 6966837336 | 8384437314 | 65000000000 | 8314040000 | 709184 |
| coupled-development-20261009-v1 | 3584780 | 1190607030 | 135718806008 | 1133739000 | 18368 |

Compilation: one Cargo job/four CPUs. Runtime fixtures: one pinned CPU. Every unit reserved and enforced 4 GiB (`2^32` bytes); user-authorized maximum 8 GiB (`2^33` bytes). Runtime bounds used counted work and the measured new coupled fixture, not a 16-second cutoff. All projections stayed fixed after launch. Native units were serialized by the sole common lease and their shared mutable Cargo cache.

One validation-launcher error is preserved: the first new-fixture launcher used an unsupported timeout duration suffix and exited before Cargo or any fixture ran. The format was corrected with the identical intended bound and unchanged memory/CPU limits; it is not a test failure or repeated fixture.

Three dead-code warnings are retained in full compiler output: `anchor_differential_joined`, `SourceObserverView::seeds`, and `HeldContactVariation::advanced`. No source repair was made.

Full stdout/stderr, source/command SHA-256 hashes, executable pins and per-unit resource/cleanup/release evidence are preserved. All leases are released; final host inspection found no native process or active owned unit. Two completed failed units retain metadata only, with empty cgroups and no tasks; no system cleanup was performed. No source edits, Git publication, system change or cache clearing. `FILE_HASHES.json` binds every other preserved packet file; immutable source bytes remain in Git and the isolated frozen source, and executables remain under the pinned isolated cache paths. No private correspondence is included.

C1b-2b scoped native acceptance **PASS**. Whole repository lint gate remains unresolved at this pin (inherited failure).

Commit `1ad7f498825dcffbbcf4e4509519fea366cceb5b`; tree `a6619d3c6fd00482a40c049a8096cd48ccb2e0d6`. Clean worktree confirmed at admission; all 352 frozen native source inputs match exact Git bytes and remained unchanged.

Workspace/all-targets check, four fresh affected test executables, all ten world-model fixtures and 15 action/retention guards passed. All 25 scoped fixtures ran exactly once. Affected library/test guard lints and 57 doctests passed. No unrelated examples ran.

The new corrected fixture jointly compares the actual raw World face, actual native blind receiving logits and actual waves through one latent `k`. Its native read is required to occur. Where waves fix `k`, the wrong face offset is incompatible. An undeclared face adds no face rows and preserves the wave/native passage. This is prospective compatibility; it does not filter retained memory by face observations or deploy elimination of wrong-face alternatives. Grain-level `Face::of_read` coverage, C2, Ask, learning and GPU parity remain outside scope.

**Inherited gate blocker:** unchanged `crates/holonics/examples/helical_duplex.rs:189` calls disallowed `std::process::exit(1)`. Its previously measured all-target Clippy failure is preserved and source/settings are unchanged. That unrelated failed check was not rerun; its correction belongs to integration. The affected lint pass does not clear the whole gate. No source edit or publication was performed.

| Unit | Command wall ns | Guarded wall ns | Fixed deadline ns | Aggregate CPU ns | RSS KiB |
|---|---:|---:|---:|---:|---:|
| check-20261009-v1 | 27899159150 | 29492009244 | 65000000000 | 29903743000 | 1520780 |
| build-20261009-v1 | 56528434979 | 58200284588 | 65000000000 | 60218461000 | 2140464 |
| face-development-20261009-v1 | 3984305544 | 5549346251 | 244139459528 | 5249899000 | 29124 |
| world-existing-20261009-v1 | 7928651752 | 9770349943 | 37858749896 | 9373843000 | 28552 |
| native-action-20261009-v1 | 602373817 | 2045739875 | 17937222176 | 1904934000 | 18312 |
| physical-action-20261009-v1 | 185652504 | 1474181535 | 17937222176 | 1378060000 | 18356 |
| retention-guards-20261009-v1 | 286412854 | 1562793529 | 29890138808 | 1518685000 | 30324 |
| clippy-affected-20261009-v1 | 11271833405 | 12639330873 | 65000000000 | 12821565000 | 979704 |
| doc-20261009-v1 | 26999751617 | 28486985455 | 65000000000 | 29356512000 | 1410144 |

Compilation: one Cargo job/four CPUs. Runtime: one CPU. Every stage reserves and enforces 4 GiB (`2^32` bytes), below the user-authorized maximum 8 GiB (`2^33` bytes). Compiler deadlines reuse actual prior peaks and elapsed time. The new fixture uses a counted-work development allocation; later runtime deadlines use the larger of that measured fixture and prior scoped runtime. Every bound was fixed before its launch; none was raised. The sole common lease and shared mutable isolated Cargo cache require serial native execution.

Full stdout/stderr, exact source and command hashes, executable pins, wall/CPU/RSS measurements, source seals and cleanup/release evidence are preserved. All leases are free and no native process or active owned unit remains. No GPU run, scientific source edit, deletion, Git publication, cache clearing or system change. `FILE_HASHES.json` binds all other packet files. Native source and executable files remain at their pinned isolated paths; source is also recoverable from immutable Git. No private correspondence is in this packet.

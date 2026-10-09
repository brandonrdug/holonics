Actual R native validation at `6f0bd8dfd3aa32d1f9a800c96d5074822c658dce`.

Corrected acceptance READING of actual contact deposit, later response, balance and cold restore; a passing test alone does not mean learned-change criteria passed. Finite material-decrease implementation is separate.

Targeted runtime: 1 source-derived tests. All-targets check, guard clippy and 57 guard doctests are separate stages.

| Unit | Complete wall ns | Fixed projection ns | Aggregate CPU ns | Group peak B | Child RSS KiB | Exit |
|---|---:|---:|---:|---:|---:|---:|
| prep8 | 8473554560 | 17000000000 | 6368547000 | 8530575360 | 39572 | 0 |
| check | 26837925231 | 65000000000 | 25866792000 | 1691025408 | 1406860 | 0 |
| clippy | 34023723558 | 65000000000 | 32989875000 | 1751158784 | 1438604 | 0 |
| doc | 40672409823 | 65000000000 | 39510267000 | 2045865984 | 1620440 | 0 |
| build | 40402357278 | 65000000000 | 39269609000 | 2433949696 | 2084780 | 0 |
| runtime | 2159956748 | 17000000000 | 2048229000 | 40644608 | 32412 | 0 |

Reader trust assertions passed; actual learning remains 0 of 4 criteria met. C/K/D each committed zero nonzero lattice coordinates; later compared-station difference squared is zero. Energy balances close over unchanged material. Cold material/carry/current and the zero response difference reproduce. Whole-passage serialization remains typed refused.

Every unit has a matching cleanup/acceptance and quiescent lease release. Frozen git source, source/toolchain/cache provenance, executable, complete stdout/stderr and control receipts are preserved here.

[Actual stdout](stages/actual-r-runtime-20261009-v140.stdout), [actual stderr](stages/actual-r-runtime-20261009-v140.stderr), [validation](VALIDATION.json).

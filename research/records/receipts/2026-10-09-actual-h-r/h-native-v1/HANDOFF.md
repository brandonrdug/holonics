Actual H native validation at `083640894c87de16a2281bdc2c75f708bf60b697`.

Conditional paired-carrier/source dyad/current-port structural laws only; no learned-code, deposition-equivariance or complete damage-channel claim.

Targeted runtime: 16 source-derived tests. All-targets check, guard clippy and 57 guard doctests are separate stages.

| Unit | Complete wall ns | Fixed projection ns | Aggregate CPU ns | Group peak B | Child RSS KiB | Exit |
|---|---:|---:|---:|---:|---:|---:|
| prep8 | 9405410065 | 17000000000 | 6690488000 | 8260976640 | 39660 | 0 |
| check | 29317793509 | 65000000000 | 28159142000 | 1627512832 | 1467820 | 0 |
| clippy | 34048892027 | 65000000000 | 32978968000 | 1738309632 | 1496340 | 0 |
| doc | 40565530182 | 65000000000 | 39451651000 | 2059976704 | 1660044 | 0 |
| build | 39873884535 | 65000000000 | 38729340000 | 2392952832 | 2121132 | 0 |
| runtime | 1140254304 | 17000000000 | 1067770000 | 28581888 | 25036 | 0 |

Every unit has a matching cleanup/acceptance and quiescent lease release. Frozen git source, source/toolchain/cache provenance, executable, complete stdout/stderr and control receipts are preserved here.

[Actual stdout](stages/actual-h-runtime-20261009-v140.stdout), [actual stderr](stages/actual-h-runtime-20261009-v140.stderr), [validation](VALIDATION.json).

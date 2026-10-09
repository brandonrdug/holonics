Loop3 at `5c50803b1fdcb2c38583a8189356dfb70f07bfa5`: scoped PASS.

44/44 native fixtures; 57 doctests; 10 owner and 10 exact HNN-import standard-axiom queries.

Paired source law preserves its port on the paired subspace; pair routes and general features at NormalLaw; founding prior and state restore. General features are not an end-to-end World compose_return comparison. CUDA typed refusal only; quadratic invariance owed#62.

Actual new fixture stderr:

```text
paired law, forward pair deposit: slip 4 -> 7635570237/17179869184, step 2, consumer false
paired law, paired deposit: slip 8 -> 0, step 2, consumer true
closed contacts through the founding prior: [1, 3]
the image's slip read against the declared port alone: [Ratio { numer: 0, denom: 1 }, Ratio { numer: -1, denom: 1 }, Ratio { numer: 1, denom: 1 }, Ratio { numer: 1, denom: 1 }, Ratio { numer: 0, denom: 1 }, Ratio { numer: -1, denom: 1 }, Ratio { numer: 2, denom: 1 }, Ratio { numer: 0, denom: 1 }]
general features on the paired law: chart lattice 41, certificate 761227/288230376151711744, target 1/34359738368
the same samples on a plain law: Err(Equivariance { ring: 0, column: 0, partner: 1, row: 0 })
```

| Unit | Accepted | Wall ns | Projection ns | CPU ns | Group peak B | Child RSS KiB |
|---|---|---:|---:|---:|---:|---:|
| actual-loop3-prep8-20261009-v195 | True | 8649666631 | 17000000000 | 6205030000 | 6422401024 | 39440 |
| actual-loop3-check-20261009-v195 | True | 14221957581 | 65000000000 | 24219271000 | 2113466368 | 1501832 |
| actual-loop3-build-20261009-v195 | True | 29408820582 | 65000000000 | 55804519000 | 3448266752 | 2180000 |
| actual-loop3-clippy-20261009-v195 | True | 19119588759 | 65000000000 | 29620091000 | 2427179008 | 1540640 |
| actual-loop3-doc-20261009-v195 | True | 28410894677 | 65000000000 | 38309365000 | 2128678912 | 1863204 |
| paired-whole-law-primary-20261009-v197 | True | 289449248 | 32992412132 | 234071000 | 26959872 | 27100 |
| paired-whole-law-paired-20261009-v197 | True | 1147446530 | 3280508608 | 1080465000 | 27213824 | 28264 |
| paired-whole-law-executed-20261009-v197 | True | 15957794329 | 32992412132 | 15834536000 | 34758656 | 36700 |
| paired-whole-law-prediction-distance-20261009-v197 | True | 321300847 | 1634379184 | 265553000 | 27480064 | 28252 |
| paired-whole-law-prediction-storage-20261009-v197 | True | 308093943 | 1634379184 | 244826000 | 26947584 | 28368 |
| paired-whole-law-prediction-gain-20261009-v197 | True | 270594015 | 1634379184 | 218930000 | 25391104 | 23832 |
| paired-whole-law-order41-20261009-v197 | True | 14017703960 | 31303528088 | 13877048000 | 46886912 | 44276 |
| paired-whole-law-order42-20261009-v197 | True | 13620720407 | 31303528088 | 13505258000 | 43982848 | 44720 |
| paired-whole-law-fixed41-20261009-v197 | True | 14837390095 | 31303528088 | 14702174000 | 45326336 | 44916 |
| paired-whole-law-fixed42-20261009-v197 | True | 15119775193 | 31303528088 | 14987868000 | 46788608 | 45324 |
| paired-whole-law-entrance-20261009-v197 | True | 2164748436 | 5502325716 | 2094719000 | 55627776 | 38456 |
| paired-whole-law-state-phase-20261009-v197 | True | 297339288 | 32992412132 | 245965000 | 24666112 | 27964 |
| paired-whole-law-state-sparse-20261009-v197 | True | 298471748 | 32992412132 | 250948000 | 25931776 | 27908 |
| paired-deposit-lean-20261009-v196-prep | True | 6543929863 | 17000000000 | 5175850000 | 736268288 | 198556 |
| paired-deposit-lean-20261009-v196-compile | True | 11074881089 | 21132554884 | 6312754000 | 4668145664 | 3789032 |
| paired-deposit-import-20261009-v198-prep | True | 5163986151 | 17000000000 | 4702057000 | 305750016 | 198672 |
| paired-deposit-import-20261009-v198-compile | True | 7314113921 | 21132554884 | 4871672000 | 1141043200 | 3744792 |

Full raw stdout/stderr, inputs, exact executables, Lean objects and lease cleanup/release receipts are preserved. No public publication or production edits by this queue.

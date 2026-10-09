Paired deposit loop2 changed period60 read: **PASS**. Refs #386 #73.

Exact source `f8ac14ba675b93152a765445def41603d70a4959`, tree `fb847729b205365d9dc1e6c31bc73bd53fe7389c`. Fourchangedone-seedfixturespassed, coveringbothoriginalconsumers atseeds41/42 andall6stations withfullcertificates. Togetherwith37unchangedsource-matchedfixtures,57doctests and8+8Leanqueries, the scopedloop2gateisaccepted.

Old two-seed tests stopped at16CPU seconds because generation of one seed consumes13..15CPU seconds. Source-only seed partition retainsbothseeds and all6stations. Each changedseed now completes beloworiginal17CPU/17wallcontrols. No combinatorial whole-passage enumeration or observedalgorithmdefect.

| Unit | Complete wall ns | Fixed window ns | Aggregate CPU ns | Group peak B | Child RSS KiB |
|---|---:|---:|---:|---:|---:|
| actual-release-prep8-20261009-v189 | 8982101636 | 17000000000 | 6218258000 | 8551297024 | 39916 |
| actual-release-build-20261009-v189 | 29533979513 | 65000000000 | 36733842000 | 2454245376 | 2224312 |
| period60-order41-20261009-v190 | 14066072225 | 17000000000 | 13903694000 | 57020416 | 44504 |
| period60-order42-20261009-v190 | 13752788700 | 17000000000 | 13595929000 | 55844864 | 44300 |
| period60-fixed41-20261009-v190 | 14902238664 | 17000000000 | 14752884000 | 124907520 | 44928 |
| period60-fixed42-20261009-v190 | 15151764044 | 17000000000 | 15031311000 | 46063616 | 45268 |

Full phase measurements:

```text
order-2 seed 41: field and deposit 44305563 ns
order-2 seed 41: bank and refinement 68087 ns
order-2 seed 41: request 63029 ns
order-2 seed 41: generation 13649931471 ns
```

```text
order-2 seed 42: field and deposit 44280564 ns
order-2 seed 42: bank and refinement 80531 ns
order-2 seed 42: request 71914 ns
order-2 seed 42: generation 13354665257 ns
```

```text
fixed map seed 41: field and deposit 248159691 ns
fixed map seed 41: bank and refinement 67206 ns
fixed map seed 41: request 79749 ns
fixed map seed 41: generation 14301629209 ns
```

```text
fixed map seed 42: field and deposit 260013826 ns
fixed map seed 42: bank and refinement 71173 ns
fixed map seed 42: request 155191 ns
fixed map seed 42: generation 14584650014 ns
```

`-j8` compilerjobs and600s were notadmitted. Actual4core/2Cargojobcompile fits8GiB; eachruntimefixed17s/17aggregateCPU seconds/oneCPU remainsunchanged. Sourcephasepartition fixeswrongunitcount, no algorithmor acceptancechange.

Paired loop2 laws and exacttwo-terrain fixture plus affected consumers accepted at exactpin via joinedunchangedreceipts. Native symmetrizedchart/NormalLaw compose_return loop3 and device #76 remainseparateowed scope. No broadworkspace runtime or productionmodificationbyqueue.

[Full validation](VALIDATION.json); rawstdout/stderr, executables, source/provenance and release receipts preserved here.

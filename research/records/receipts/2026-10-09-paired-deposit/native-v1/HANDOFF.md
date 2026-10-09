Paired deposit loop2 at `9ba6fe000d752556cf0e08694481f18c06d09166`: **native gate INCOMPLETE**. Refs #386.

37 of 39 required native fixtures passed; 57 doctests passed. New paired acceptance ran once; both terrains certify and preserve the partner face. Whole Lean owner8 and affected import8 standard-axiom PASS are independent receipts beside this folder.

Actual paired loop2 signed-slip certified deposit and two-terrain acceptance. Symmetrized non-diagonal native chart, compose_return full-field consumer and device parity are loop3/76 owed. Existing period60 bank-release consumers stopped by fixed aggregateCPUguard, no result inferred. Need changed phase/seed consumer read preserving period60,bothseeds and six stations; no unchanged rerun or cap raise.

Stopped consumers:
- `hnn::tests::prediction::the_release_reads_the_located_pair_and_its_consumer_holds`
- `hnn::tests::prediction::the_release_reads_a_located_map_that_fixes_its_antecedent`

Both stopped at the unchanged aggregate CPU guard, with no assertion/final test result. Full stdout/stderr are preserved. All resources and lease were released.

| Unit | Accepted | Complete wall ns | Fixed window ns | CPU ns | Group peak B | Child RSS KiB |
|---|---|---:|---:|---:|---:|---:|
| actual-paired-prep8-20261009-v179 | True | 8491157636 | 17000000000 | 6078057000 | 8488742912 | 39784 |
| actual-paired-build-20261009-v179 | True | 28431138276 | 65000000000 | 53844499000 | 3498782720 | 2239384 |
| actual-paired-check-20261009-v186 | True | 14013587459 | 65000000000 | 21197780000 | 2224336896 | 1515472 |
| actual-paired-clippy-20261009-v186 | True | 20003266946 | 65000000000 | 30134683000 | 2179629056 | 1515680 |
| actual-paired-doc-20261009-v186 | True | 29567704051 | 65000000000 | 39501516000 | 2151383040 | 1915184 |
| paired-deposit-development-20261009-v182 | True | 281261687 | 17000000000 | 236904000 | 25919488 | 26380 |
| paired-deposit-paired-20261009-v184 | True | 1092812589 | 17000000000 | 1028755000 | 26554368 | 27880 |
| paired-deposit-executed-20261009-v184 | True | 15996206066 | 17000000000 | 15868198000 | 32026624 | 36092 |
| paired-deposit-prediction1-20261009-v184 | True | 317189592 | 17000000000 | 265631000 | 102477824 | 28084 |
| paired-deposit-prediction2-20261009-v184 | True | 277120710 | 17000000000 | 236658000 | 25919488 | 27876 |
| paired-deposit-prediction3-20261009-v184 | False | 16214177135 | 17000000000 | 16093785000 | 44634112 | 23820 |
| paired-deposit-prediction4-20261009-v184 | True | 272323568 | 17000000000 | 224415000 | 100007936 | 23840 |
| paired-deposit-prediction5-20261009-v184 | False | 16235008219 | 17000000000 | 16096903000 | 45527040 | 23552 |
| paired-deposit-entrance-20261009-v184 | True | 2251162858 | 17000000000 | 2182426000 | 75853824 | 38492 |

Actual new fixture stderr:

```text
alternating strand: located offset 1, map [(0, 2), (2, 0)], cycle 2, turns [2]
control, the forward deposit alone: Err(Equivariance { ring: 0, column: 0, partner: 1, row: 0 })
paired deposit: forward [(0, 2), (2, 0)], reversed [(1, 3), (3, 1)], slip 8 -> 0, step 2, consumer true
stepping strand: located offset 1, map [(0, 1), (1, 2), (2, 3), (3, 0)], cycle 4, turns [1, 3]
stepping strand, paired deposit 1: reversed [(1, 0), (0, 3), (3, 2), (2, 1)], slip 16 -> 11453246123/1073741824, step 1, consumer false
stepping strand, paired deposit 2: reversed [(1, 0), (0, 3), (3, 2), (2, 1)], slip 11453246123/1073741824 -> 21532100963/2147483648, step 2, consumer false
stepping strand, paired deposit 3: reversed [(1, 0), (0, 3), (3, 2), (2, 1)], slip 21532100963/2147483648 -> 10742678561/1073741824, step 2, consumer false
```

[Full validation](VALIDATION.json). Raw command output, source/toolchain/cache pins, exact executables and cleanup/release receipts are under `stages/`, `admission/` and `compiled/`. No production pruning or publication performed.

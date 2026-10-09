# Corrected native duplex acceptance

Source `02658c6c2ddaf94b0bf66eb9c7db91307f1fc2ce`, tree `ca41addd4277ab5d74bfb23c8a84077486161380`. Original `c6fcc82a187174333ca494bf35c1c8cb7062ab56` is preserved and was not executed.

All 21 exact duplex tests passed from a fresh source-bound library-test executable. The required workspace all-targets check, all-targets exact-arithmetic guard lints and full library guard doctests passed. running 57 tests; test result: ok. 57 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out.

The two source-review corrections are consumed by actual regressions: malformed partner contacts 3 and usize::MAX on length 3 return IndexOutside before reversal arithmetic; a receiver founded on one transport refuses a changed advance on the same helix, while each matching pair succeeds.

| Unit | Wall ns | Fixed projection ns | Aggregate CPU ns | Group peak B | Child peak RSS KiB |
|---|---:|---:|---:|---:|---:|
| cache-prep | 8622694867 | 17000000000 | 5944411000 | 3845267456 | 38968 |
| check | 25265904584 | 65000000000 | 24296117000 | 1680130048 | 1458800 |
| build | 35431492350 | 65000000000 | 34400553000 | 2431410176 | 2049712 |
| runtime-index | 302033267 | 17000000000 | 246102000 | 40415232 | 24760 |
| runtime-binding | 301368312 | 17000000000 | 263673000 | 38350848 | 24944 |
| runtime-development | 1472265594 | 17000000000 | 1422267000 | 64385024 | 47020 |
| runtime-acceptance | 2228496495 | 30917577474 | 2081060000 | 66793472 | 48780 |
| clippy | 34618204262 | 65000000000 | 32420386000 | 1725743104 | 1483528 |
| doc | 41258881198 | 65000000000 | 38482802000 | 2111492096 | 1638200 |

Every stage used the existing sole lease, one CPU affinity, fixed CPU/wall bounds and unchanged authorized ceilings. Compilation retained the prior 65,000,000,000 ns native unit window and 128,000,000 us aggregate CPU ceiling. Cache preparation remained a separate 17,000,000,000 ns / 4,294,967,296 B unit. Runtime acceptance was fixed before launch at 21 × 1,472,265,594 ns = 30,917,577,474 ns, the maximum measured development-unit wall. Each native test completed below that unit upper. Every final acceptance has matching owned cleanup and quiescent lease-release receipts. No cap ladder or unchanged failed rerun occurred.

Actual known-truth outputs: text/pitch/levels free families released 3/0/3 and held 21/24/21 of 24 each. Complete enumeration covered 92/134/108 members, with exact coordinate-max diameter and actual attaining witnesses. Coordinated complementary damage slipped zero contacts and released all its one-member families; against known truth it absorbed 16/12/11 and left residual 152/540/349. These residuals are outside channel coverage.

Acceptance is limited to the reviewed declared local-factor/Markov-fit known-truth composition. It does not establish learned key discovery, generalization, exhaustive channel correction, physical material power, continuing HNN partner return or ribbon geometry. The earlier accepted Lean seal remains independent; it was not rerun.

Whole native outputs: [stdout](admission/acceptance.native.stdout), [stderr](admission/acceptance.native.stderr). Source, exact fixtures, executable, cache provenance, raw diagnostics, timing/resource receipts and original unexecuted source are preserved here. [Machine-readable validation](VALIDATION.json).

No source edits, push, merge, history rewrite, branch/worktree deletion or broad HNN/GPU/scientific execution was performed.

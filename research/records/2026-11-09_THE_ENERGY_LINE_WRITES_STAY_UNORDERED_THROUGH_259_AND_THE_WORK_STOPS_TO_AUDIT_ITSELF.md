# The energy line's writes stay unordered through 259, and the work stops to audit itself

Status (2026-11-09): measurement and decision. Brandon asked for Colab to stop, for housekeeping, and for a critical
look at what the agents inferred and built in the past week. This record keeps the day's measured results, the runs
stopped, and the audit's conclusions that bear on the line. No law changes here. Refs #73, #404, #406.

## 1. The carry claim at 259 fails

[measurement; carry13e on a Colab A100 at 6e94ca86c, resumed from 248] The run stopped by its own stop law at 259
(FIELD_STOPPED after sections 249–258, 10,090 s against its 10,600 s deadline). So the lap end is its own declared
read of STATE.stopped (`lapend30.sh`, at 9580985d4).

- **Claim** (theory, November 9 05:31): the writes' summed letter mutual information at lags 1–20, over within-write
  shuffles, should rise more than 2 SE above 239's by 259.
  - 239: +0.022 nats (SE 0.047), at the 239 writer's "equilibrium at sweep 32".
  - 249: −0.024 (0.054) and 259: −0.038 (0.044), each at its writer's "equilibrium at sweep 8".
  - Paired over the 16 answers, 259 − 239 = −0.060 (0.071).
  - **The claim fails.** The truths carry about +3.5 at these lags.
- **Fresh bands, 248–258** (`fresh_bands_248_258.txt`):
  - Pooled: lags 1–5 +0.013 (0.006), lags 6–20 +0.026 (0.009).
  - One read of 36 passes 2 SE above 239's: section 257's 6–20, +0.048 (0.016), at 2.17 SE. It does not repeat at 258
    or in the 259 writer.
- **Wakes:** moment_face_bias at 249, b at 251. Through 258, these never moved: v, out and w with their biases, a_bias,
  b_bias, temper, pace and face_temper.
- **Held code**, the mean −ln p(truth) at the 512 held places under full G (`heldcode.py`):
  - 239: 2.9070. 249: 2.8972. 259: 2.8486.
  - 259 − 239 = −0.058 (SE 0.023 over problems).
  - For comparison: the letters alone read 3.40, a previous-letter count 2.68, and the best state measured
    (law D, section 379) 2.7651.
- **The 259 writer** refused at its descent end: "a temperature past its carrier". Some row temperature at 259 sits
  below 2^−7, so cooling by 2^16 passes the floor. The temper family itself never moved.
- **twin27** (9580985d4) reran 249–257 from carry13e's 249 save. It was stopped with Colab. Every learning line matches
  carry13e bit for bit, timings aside (`twincmp.py`), with the persistent path's zero fields dropped. Its first sweep
  save, at 254 sweep 12, is in its log.

## 2. The PC lap had been getting worse

[measurement; lap14i on the RTX 4080 SUPER] lap14i ran theory's November 9 00:08 law, the fresh writes with the
truncating deposit, from the 400 rest. On the same 512 held places its held code rose:

| Section | 400 | 486 | 576 | 691 | 795 |
| --- | --- | --- | --- | --- | --- |
| Held code (nats a letter) | 2.9401 | 2.9573 | 3.0045 | 2.9846 | 3.0528 |

795 − 400 = +0.113 (SE 0.042 over problems). The law was superseded at 05:24, when the truncation was found to freeze
the far families. The run was not read again and kept the card for about ten hours. It was stopped at 17:00, with its
state saved at 795 (`seg7.from700/STATE.0.795`).

## 3. The phase-move split, and the band-edge builds

- [measurement; reach28, base classes, 239f → 249]
  - 12,971 changed far memberships, each explained by a moved word: 0.51 probe words, 0.49 key words.
  - 0.95 of them sit inside the receiver's half-width (median |Δφ| 0.0137 rad against 0.1263).
  - The order difference I per place reproduces theory's Σ I² = 312.2, RMS 0.781 (`iplace.py`).
  - Beyond the half-width carries 0.075 of Σ I² (SE 0.014; `ishare.py`), so the gate for building the law passed.
- e263d0d10 (branch `claude/band-edge`, not on the line) built the band-edge law:
  - G is continuous through the cone and the band edge, and the sharp map is not.
  - G has kinks there, and the joint release chattered (63 of 64 reads).
- 44be2174b (WIP on that branch) holds theory's 15:56 revision:
  - Done on the host: the smooth gate (1 − φ²)², the union over shared digits, still heads by soft count, and the
    covector from the bare share.
  - The release test passes and the kink guards are retired.
  - Open: `squares_agree_at_one_base_on_a_line_shaped_field` now reads a curl of 0.097 of the readings, against 0.013
    before the law.
  - Not built: the card mirror is unbuilt, and the tick field's retirement is undone.
  - The build stopped there for the audit, and neither commit is on the line.

## 4. What the audit changes

[decision] The work stops before another law. Brandon's direct requests on November 9 govern: no Colab, run on his
PC, and step back from the constructs the agents chose. The audit itself was written for him outside the repository.
Its conclusions that bear on the line, each agent-inferred:

- **Ours, not his.** The objects and the line are Brandon's. These were the agents' own choices:
  - the energy field as the learner (November 6);
  - generation as sweeps of a fixed energy at a temperature;
  - training as truth against the field's own samples;
  - the class map as the support (trit shells, probes and keys, with the width law, force opening and band-edge law
    as patches on it);
  - the held code in nats as the yardstick;
  - the save and projection apparatus, and the run nicknames;
  - 96 run switches, 46 of which choose the learning law.
- **Doubling down.**
  - Each failure of a training law was answered by a variant of the same comparison, on one object. The writes have
    been soup since the refoundation.
  - The class map was patched three times.
  - One claim was launched five times (carry13 to carry13e).
  - The sequential sweep, one place per answer per whole-region read, was flagged on November 5 and still runs every
    write.
- **"The field, not the writer"** is not an object. In G the writer is the field's own kernel. Reading and writing are
  one motion, which is the reafference Brandon named.

## 5. Housekeeping

- **Colab:** both sessions are stopped, with 89.4 units left.
- **Disk:** `/home` stood at 17 GB free. Removing 13 finished agent worktrees (branches kept), 60 cargo build caches in
  inactive worktrees and 14 local branches whose every commit is on the line brought it to 203 GB free.
- **Run registry:** 114 finished entries moved to `.local/dispatch/archive/`.
- **Records:** the running record (2026-11-01, §16.47) and CONSTRUCTION_STATE stop at November 7. The laps, forks and
  carry runs of November 8–9 are kept here and in their commits, not yet in the running record.

Receipts (`*_receipts/`): the reading scripts (`heldcode.py`, `iplace.py`, `ishare.py`, `reach_base.py`, `split3.py`,
`twincmp.py`, `write_mi.py`, `mi_lags_core.py`, `fresh_lags.py`), the run scripts `reach28.sh` and `lapend30.sh`, and
the fresh bands of 241–258. The writes, truths and saved states stay under `.local/`.

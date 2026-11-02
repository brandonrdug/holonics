# Receipts: R0, R1 and R2 of §6, acceptance 77, and the card profile (B-PC, November 1)

Count-only receipts of the plan's runs on the RTX 4080 SUPER under the card's lock; machine paths are
written `$ROOT`. No release text, held-out text or GSM8K writing is here. Binary `tower_pass-46a`
(`3dade728…cc49`, built from `ed4d78bef`) for R0–R2, the development reads and the profile;
`tower_pass-77a`/`-77b` for acceptance 77's parities. Inputs: `COPY.roles` `a974a0ca…a5a7`
(roles 179,858 / 181,459 / 11,460 / 24,145), `UNITS0` = `founded-units-v1 0` `b438ff77…b333`.

| Run | Declaration | Wall / projection | Device peak (board) | Files |
|---|---|---|---|---|
| R0 | committed units, pair route, 2^(-8), 40 laps | 532.8 s / 736 s | 7,338 MiB | `r0*.txt` |
| R1 | bytes (UNITS0), same route | 1,121.1 s / 1,260 s | 6,968 MiB | `r1*.txt`; the first launch, stopped at lap 1 by a watchdog bound set below the declared per-lap upper bound, `r1-stopped*` |
| R2 | bytes, participation from level 4, section 128 | stopped after lap 5 (340.2 s) on Brandon's 15-minute rule; projection 4,076 s | 8,761 MiB | `r2*.txt`; its lap-5 receipt has three of four draws (the fourth killed by the receipt's 900 s outer limit) |

`*-receipt.txt` holds the written rules, the never-met reads by operation and the carry
(`carry.py`), and the written coupling in both charts at four key draws; `*-summary.txt` folds them
into the four-draw range and mean (`summarize.py`). Acceptance 1 passed (R0's training code equals
g48's lap for lap); 2 and 4 failed for R1 (first calculation from the question 11.00 against a bar of
19.5; never-met exact 7.50 against a floor of 9 of 139); 3 was not read (R2 stopped).

`parity77-*.txt`: acceptance 77's card parity (units 2^(-8), bytes 2^(-5), bytes 2^(-3) refused at
section 3 by the residual carrier, and the restore after section 16). `suite77.txt`: card suite.
`prof*`: 32 sections of R1's and R2's declarations, profiled and plain, with the card's utilization
every 100 ms (`prof-*-util.csv`: time, SM-busy %, memory-busy %, board MiB, SM clock).

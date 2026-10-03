# Runner 2 notes

- Q2 Kinetic control chain: `chain.sh` from cloud-queue 6776293 (main + #207) under the queue's declared whole-move bound
  (`DEADLINE_S=1900`, `UNIT_MS=1900000`), not fitted on early moves; kept for all 16 moves (coordinator, 23:41).
- The per-unit print picks 7a650e6b fc4ca0f3 55a99bd8 cd8f654f (claude/independent-derivations-wvtfpc) do not apply on this
  chain's base (cloud-queue 6776293 + #207): 7a650e6b conflicts in `crates/holonics/src/hnn/executed.rs`. That cherry-pick was
  aborted without resolving it. The picks apply cleanly on 5f254c2d; that build is kept locally on branch `runner2-picks`, unpushed.
- Under the cloud maxima per kind sent at 23:36 (incumbent 166264, persistence 1814, slope 32691, reread 207135 ms) a one-trial
  move is bounded by 407904 ms; this host's one-trial moves took 545006 to 710201 ms alone, so those bounds were not applied.
- Q4 and Q5 moved to the PC; the control's held-out read moved to the PC's joint move-16 read (PC_QUEUE P5).
- The throw read ran on claude/independent-derivations-wvtfpc at b1d37a84; `direction` there takes bare paths, so the
  `m0=`/`c0=` labels were dropped.

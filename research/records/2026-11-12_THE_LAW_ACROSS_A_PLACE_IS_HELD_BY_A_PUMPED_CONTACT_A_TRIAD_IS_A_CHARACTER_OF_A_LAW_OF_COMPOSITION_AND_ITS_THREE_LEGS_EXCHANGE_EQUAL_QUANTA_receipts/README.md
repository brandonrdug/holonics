# Receipts: the triad's ruler (November 12)

A ruler on the host, never machinery (floats, analysis only). It reads the python-codes passages under
`${HOLONICS_ROOT}.local/`, which stay private, through the chain record's `yard.py`; only aggregate codes are
written here. None of it uses the card.

- `cap_t.py K R [seconds]`: the pair tables of `cap_g.py` (the leaky grip record's receipts) plus `R` complex
  triads, `Q(x|L,R) ∝ exp(a(L,x) + b(x,R) + Σ_j Re(u_j(L) w_j(x) v_j(R)))`, fitted together by conditional
  likelihood on TRAIN from `cap_g.py`'s start and schedule, read on HELD128 at the contexts seen in TRAIN, the best
  held step taken. At `R = 0` it is `cap_g.py` step for step. `CAP_T_SYNTH=1` runs it on a drawn law instead of
  the passage; `CAP_CODEC` names the codec when `yard.py`'s path is gone; `train.npz` is written from TRAIN.txt
  when absent (private, never committed).
- `cap_t_synth.log.txt`: the control on the drawn law `x = L + R mod 8` (six left and six right contexts, a fifth
  of the letters redrawn; floor 0.8043 nats): 0, 1, 2, 4 and 8 triads, 8 s each, the header, step 0 and the best.
- `cap_t_fd.py`, `cap_t_fd.log.txt`: the analytic gradients against central differences on the drawn law.
- `cap_t_2_0.log.txt`, `cap_t_2_8.log.txt`, `cap_t_2_16.log.txt`, `cap_t_2_32.log.txt`, `cap_t_2_64.log.txt`: G102's
  runs on the PC's host, `cap_t.py 2 R` at `R = 0` (140 s) and at 8, 16, 32 and 64 triads (300 s each), one at a time
  on 8 pinned threads under an outer timeout of 420 s and a ceiling of 8 GiB. Each log ends with its wall time and peak.
  Best held codes 1.0304, 0.7559, 0.6916, 0.6550 and 0.6317 nats a place, so `s(R)` = 0.604, 0.745, 0.826 and 0.877.
- `cap_t_2_0_repeat.log.txt`: `R = 0` again with the same settings. The ruler's gate, its `R = 0` step lines against
  `cap_g_2.log.txt`'s, missed at one line: `cap_t_2_0.log.txt` reads `step   5  TRAIN 1.0474  HELD128 (seen contexts,
  share 0.9996) 1.0914` where `cap_g_2.log.txt` reads `step   5  TRAIN 1.0473  HELD128 (seen contexts, share 0.9996)
  1.0914`. The repeat reads 1.0474 again and equals the first run on every step line through step 225, under the
  NumPy the November 10 ruler ran under (2.5.4). Every held line and the best are equal, so no figure the guess reads
  moved. G102's score is in the guess file.
- The build's gates (G105's premise), from the PC, on the card (the RTX 4080 SUPER under the card lock):
  - `g105_triad_gates.txt`: gates (i) to (vi) on the triad build, the binary `bin-triad` (sha256 48ab0d52c2291b6f): gate 1,
    the GPU suite alone on the idle card, the Lean build, and the three below;
  - `g105_te4r_lines.txt`: the reproduction, one lap at `J = 0` from te3's end, every line against te4's, timings aside, and its
    states against te4's byte for byte;
  - `g105_te4_reads_bin_triad.txt`: te4's lap mean read by the triad build, the held read and the transmission read, each line
    against te4's own read's;
  - `g105_grow_triad.txt`: the founding of 16 triads on te4's end, every face of its 1,020 states kept.
- tt1, the founding's first lap (G105), from the PC, each its own hold of the card lock:
  - `g105_tt1_dev.txt`: TT0's opening and its gates, and the development section, the build between two controls;
  - `g105_tt1_lines.txt`: the lap's lines, its sections past 200,000 millionths with their parts, and its errors, refusals
    and stops (no refusal; the three stops are the development sections' at their 1 ms bound);
  - `g105_tt1_reads.txt`: the held reads of tt1's lap mean and end, the transmission read of its mean, and the charge.
- `charge_t.py STATE...`: the return's charge, `W_T`'s rms over all its rows against the rms of `W`'s plain contacts' columns
  on the first lane's rows, read through `tools/state_travel.py`'s layout; one thread, writes nothing.
- `g107_cut_reads.txt`: the cut of tt1's lap mean (TT1C, `w_triad` grafted from TT0) with its gate, and the triad build's
  held and transmission reads of it (G107), each its own hold of the card lock. tt1's release (G106) is
  `g106_release_lines.txt` in the receipts of the record of raised rates (2026-11-11), beside te5's.
- The guesses G102 and G105 to G109 are in `guess_capacity_44_55.txt` in the receipts of the record of the places
  (2026-11-11).

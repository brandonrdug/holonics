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
- The guess G102 is in `guess_capacity_44_55.txt` in the receipts of the record of the places (2026-11-11).

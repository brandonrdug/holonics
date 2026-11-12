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
- The guess G102 is in `guess_capacity_44_55.txt` in the receipts of the record of the places (2026-11-11).

# Receipts of November 21: the tick's gains, the contact kernels' stalls, and the forward contact's skins staged

For [the record of November 21](../../2026-11-21_THE_BUILT_TICKS_RATES_STAND_STILL_ON_ITS_FILL_CLOCK_A_THIRD_OF_A_SITES_MODES_IS_RELEASED_A_THIRD_HELD_AND_A_THIRD_BOOSTED_AND_THE_CONTACT_KERNELS_WAIT_ON_THEIR_LOADS.md).
Read on the PC (RTX 4080 SUPER, the host's 24 threads); scripts name the repository `$REPO`.

- The tick's gains: `GUESS.txt` (fixed 01:12 UTC), `probe.sh`, `L71.out` (5,376 perturbed ticks, 91 s), `L71_gains.txt` (`tools/tick_gains.py`),
  `L71_octaves.txt`, `res17.sh` and `tick_residual_L71_17.txt` (the residual by tick at 17 declared ticks).
- The contact kernels' registers and stalls: `variant.sh`, `census.py`, `registers_{6,5,4}blocks.txt` (`ptxas -v` at the forward contact's and
  the exposure's bound of six, five and four blocks), `ncu_src.sh`, `ncu_src.out`, `srcrank.py` and `stalls_*.txt` (Nsight Compute's source
  counters, one launch each after 40 of warm-up, on a line-info build of `e63c81396`).

## The forward contact's paced skins staged with the chunk's terms (`sk2.sh`, `sk2.txt`, `sk2_stage_skins.patch`)

`field.cu`, `contact_body` and `stage_skin_words`: where a head is paced and its modes fit eight, the lane that ranks a chunk's term reads that
term's skins once (two 16-octet loads at eight modes) into the warp's staged row, each word through `skin_word` as `pair_skin_word` reads it,
and the numerators read the staged word in place of a load addressed from the staged term. The same words in the same terms in the same order:
a realization.

In one hold of the card (OBS the one other process): the card crate's suite 28 passed; the reproduction of 24 sections of lap L71 from Y70's
end `EQUAL` (24 of 24); `field_contact_l4` 1.39 to 1.43 ms a launch against 1.50 to 1.54 (three launches each after 40, Nsight Compute), 7.5%
shorter, occupancy unchanged (50% theoretical, 45 to 47% achieved; still six blocks at 80 registers, 160 octets of stack against 168); the
section in a warmed balanced hold of 40 sections (the last 30 read), the control 519.0, 520.5, 520.7, 521.4 (520.4, spread 2.4) and the
build 518.1, 518.7, 517.8, 516.7 (517.8, spread 2.0): 2.6 ms (0.5%) shorter, at the edge of the controls' spread. Guess (fixed 01:25 UTC):
the kernel 10 to 18% shorter (missed, 7.5%), the section 1.5 to 3 ms (held, 2.6). Projection about 13 minutes, measured 10 min 22 s.

## The contact kernels' register bounds against their occupancy (`lb.sh`, `lb.txt`, `lb_bounds.patch`)

Two realizations of the same code, read against main at `6c991fc5c` (A): B, the forward contact and the exposure at five blocks a
multiprocessor (96 registers, 104 and 8 octets of stack, against six's 80 with 160 and 80); C, the rows' return at five (96 registers and 88
octets of stack, against four's 128 and 64). Both reproduce 24 sections of L71 `EQUAL`. A launch, three each after 40 (Nsight Compute):
B's forward contact 1.46 to 1.50 ms against 1.39 to 1.42 (5.5% longer, achieved occupancy 38% against 46%), B's exposure 683 to 684 µs and 489
against 694 to 696 and 502 (1.6 to 2.6% shorter), C's rows 299 to 304 µs and 484 against 288 to 298 and 434 (2 to 11% longer). The section
in two warmed balanced holds: A 515.6, 511.1, 510.3, 513.0 against B 514.5, 514.4, 513.9, 513.4 (512.5 and 514.1, spreads 5.3 and 1.1); A
512.4, 514.0, 513.9, 512.6 against C 512.2, 514.4, 513.3, 513.7 (513.2 and 513.4, spreads 1.6 and 2.2): no difference at the section.
Guess (fixed 01:42 UTC): each changed kernel within 5% a launch (held for B's exposure, missed at its edge for B's forward contact and for
C's rows at its third launch) and neither section outside the controls' spread (held). Neither is taken.

So the forward contact gains from its warps more than it loses to its spills (six blocks with spills over five with half of them), and the
rows lose more to spills than they gain from warps: a register freed buys time only where it adds resident warps without a spill, which
at the forward contact means its state under 64 registers for eight blocks (spilled heavily on November 14, G191), and its loads' latency
stands either way (`agent-inferred`).

## The carry circles' operand and drive on 32 bits (`nq.sh`, `nq.txt`)

The premise read first: Nsight Compute on the pair and scan kernels (one launch each after 40, `ncu_src.sh` with their names) reads them
bound by the card's memory, at 49% (`field_pair_scan`), 64% (`field_pair_gamma`), 68% (`field_pair_scan_back`), 70% (`field_pair_gate_back`),
86% (`field_pair_scan_pre`) and 88% (`field_pair_scan_face`) of its DRAM peak, their compute at 6 to 83%. The circles' scan operand `Q`
(`pqm`) and coupled drive `κ b` (`pkb`) stand within 21 bits on the trained state (`pass_carriers_L71.txt` of November 20) and were kept on
64: `field.cu` now keeps both on 32, written through `fit32` (a word past 32 bits refuses the batch, `REFUSED_WORD32`), as the gate `γ` has been
since November 19, and `read_octets` counts the circles' tick carriers at what they take (16 + 8 + 8 + 8 octets a circle, where it had counted
48 with the drive left out). The same words while they fit: a realization.

In one hold (OBS the one other process): the card crate's suite 28 passed; 24 sections of L71 from Y70's end reproduced `EQUAL`. A launch
(three each after 40): the scan 673 to 703 µs against 735 to 743 (6.5% shorter, its DRAM 30% against 50%), its face 435 to 445 against 544
to 551 (20%), the reverse's pre-scan 1.02 to 1.03 ms against 1.12 to 1.16 (9%), the gate and the gate's return unchanged (1.26 and 2.12 to
2.14 ms both). The section in a warmed balanced hold of 40 sections: the control 510.7, 511.4, 511.8, 512.5 (511.6, spread 1.8), the build
505.8, 504.4, 506.6, 506.2 (505.8, spread 2.2): 5.8 ms (1.1%) shorter; three batches a section in both (the tape 8 KB a site and tick
lighter, not yet under a batch's cut). Guess (fixed 02:15 UTC): the scan, its face and the gate's return each 5 to 20% shorter (held for the
scan and the face, missed for the gate's return, whose circle words are a small share of what it reads), the gate within 5% (held), the
section 3 to 8 ms (held), three batches (held). Projection about 15 minutes, measured 12 min 40 s.

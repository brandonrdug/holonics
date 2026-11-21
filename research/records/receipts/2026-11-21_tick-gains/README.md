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

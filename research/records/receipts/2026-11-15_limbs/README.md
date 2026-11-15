# Receipts: the forward contact without the host's multiplier, on the carrier its need less those bits gives (November 15)

Device: the RTX 4080 SUPER, the line's sections (24 from lap 39's `STATE.3000`), the line's binary (`athena_tied`, #844) as control.

- **The ablations that chose it** (`ablations.txt`, `ablations_profile.txt`, `ablations.patch`; one hold after lap 38, the line's 24 sections,
  ms over 24 sections). With the forward contact's numerators removed (`ABLATE=1`) its entry `field_contact_l5` fell from 208 to 24 ms
  (2,900 to 1,106 µs a launch, compared by launch because the ablated runs were refused partway), so the numerators' series is 62% of the
  entry. The rows' probe-role sum removed (`ABLATE=3`) took `field_contact_rows` from 205 to 140 ms (713 to 488 µs a launch), a third of
  the rows; the wide compare (`ABLATE=4`) 4%. The shares pass (`ABLATE=2`) about 12%. The columns, the exposure and the skin's return
  did not move. The theory thread's record of the same day scores its guesses on them (8a1796458).
- **The change.** The host's series row weighs a source and a crowd's value by `2^62` (`WEIGHT_BITS`) and a crowd's mass by its count
  `2^62`. The card weighs them by one and by the count. Every quotient of the row (a current `N/M`, a share `e_k 2^63/M`) carries the
  factor in its dividend and its divisor, and the nearest quotient on a magnitude `⌊(|x| + ⌊m/2⌋)/m⌋` is unchanged by an even factor `K`:
  the two differ only where `2|x| + m` is a multiple of `2m` with `m` odd, and an odd number never is (the theory thread's lemma;
  `ratio.rs`'s test over odd and even divisors, both signs and the multiplier itself). The card's carrier is the host's need less those
  62 bits (`row_limbs`), floor three limbs (entries `field_contact_l3` and `_l4` added, `big_mul` truncated to the carrier, a dropped
  top being a quotient). The refusals stay the host's, so status bits match. The host keeps its multiplier, so parity tests the lemma.
- **Gate 3 equal** on lap 17 (`hold.txt`): parity on 3 sections (the card without the factor against the host with it), 24 sections
  reproduced, the read's cavity table byte for byte. Gate 1 and the two host tests (the lemma, the carrier's bound) pass.
- **Timing, one balanced hold** (`hold.txt`, ms a section): control 632.6, 631.8, 633.0, 632.5, 631.7 (spread 1.3); the build 628.3,
  627.3, 643.5, 627.8; every run's 24 section lines equal. Three of the build's runs read 0.993 of the control; the fourth stands
  outside both builds' runs and is a card state. About 4.5 ms a section of the forward contact's ~61: the entry falls to about 0.93,
  against the theory thread's 0.60 to 0.80, a miss it places in its own guess (fixed as if values were taken on one limb, which this
  build does not do; one limb is about 9% of the entry by its count). The profile with the limbs each launch took follows in this
  directory when the card's queue reaches it.

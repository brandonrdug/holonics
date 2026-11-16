# Receipts: the maps' tile fetches its next chunk behind its products, and the square root reads its first place (November 16)

Device: the RTX 4080 SUPER, alone under the card's lock in the gap after lap 50 (04:39 to 04:56 UTC). Control: #874, the line's binary
from lap 51. Sections: lap 50's `STATE.3000` for the counters, the profiles and the timing hold, lap 17's for gate 3.

- **The changes** (`crates/engine-cuda/kernels/field.cu`). The words and the integers are the same in each.
  - (prefetch) `map_tile`'s narrow pass reads a chunk's words into registers (`fetch`, eight weights and eight words a lane) as soon as
    the chunk before them is staged and proved narrow, multiplies the chunk before, then stages the fetched words. Before, each chunk's
    loads were issued and waited on before its products. The paced build's counters had shown that wait: `field_transposed`'s long
    scoreboard stood at 5.5 to 7.0 an issued instruction once its shared stores' conflicts were gone. Shared memory is unchanged, so two
    blocks a multiprocessor stand as before. ptxas at `sm_89`: `field_transposed` 124 registers and no spills, `field_affine_tiled_x32`
    128 registers with 4/16 octets of spills, `field_affine_tiled_x64` 8/8.
  - (place) `isqrt128` reads its first digit's place, the largest power of four not above `n` (at most `2^126`), from `n`'s bit length.
    Before, it stepped down from `2^126` two bits at a time, and that loop held 0.314 of `field_chart`'s instructions. `n = 0` returns
    0 before the bit length is read. The theory thread's ruler holds the place and the root equal on 100,383 powers (#876).
- **Gate 1 passed; gate 3 equal** (`hold.txt`).
- **Counters** (`ncu_counters.txt`; the first eight launches of the three tiled maps). Each launch fell to 0.72 to 0.76 of its time
  under #874 (`field_transposed` 221.1 → 159.2 and 129.4 → 91.8 µs; `field_affine_tiled_x32` 218.5 → 163.8). Long scoreboard fell from
  5.4–7.4 to 1.0–3.1 an issued instruction, and the barrier stalls held at 0.36 to 0.58: the loads now stand behind the products.
- **Profiles** (`PROFILE_PAIR`, ms a section over 24 sections): `field_transposed` 27.1 → 23.0, `field_affine_tiled_x32` 20.0 → 16.2,
  `field_affine_tiled_x64` 8.6 → 7.2 and `field_tied_face_tiled` 4.8 → 3.8. The other two callers of the square root moved too:
  `field_chart` 19.4 → 13.9, `field_unit` 7.2 → 5.1 and `field_unit_probe` 7.3 → 5.1. In all, 20.1 ms a section less.
- **Timing, one balanced hold** (`RATE_TIMING`, ms a section, every run's 24 section lines equal): control 567.9, 568.4, 569.9, 568.6,
  568.5 (spread 2.0); this build 547.9, 545.6, 546.7, 546.0. Means 568.7 and 546.6: 0.961, 22.1 ms a section.
- **The theory thread's guesses** (fixed 04:12 and 04:21 UTC): gate 3 equal (held). `field_transposed` 0.75–0.92 by the profile (0.849,
  held). The tiled affine maps 0.85–0.95 (0.81 and 0.84, a miss on the side of more). `field_chart` 0.86–0.95 (0.716, a miss on the same
  side; the guess priced the place's 0.115 of samples, and the place held 0.314 of the instructions in every lane of every launch). The
  section 0.971–0.990 (0.961, a miss on the same side).
- **Into the line.** The hold wrote this binary as the chain's next on the equal gate; chain 16 had read lap 51's (#874) before, so it
  trains from lap 52.

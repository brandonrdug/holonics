# Runs of the echo receipt

| Script | What it reads | Projection | Deadline (outer `timeout`) | Measured wall | Peak resident |
|---|---|---|---|---|---|
| `echo_spectra.py` | A: the acoustic echo leg by leg for seven (sound speed, emitter, wall) velocity triples, against `D(a/c)/D(b/c)` and Einstein's subtraction at `c`; B: loops of 7, 8 and 17 cells with round-trip ratio `1, −1, ±i` over 4N-point number-theoretic transforms modulo three primes; C: a string of 16 cells plucked at cells 8, 4, 5 and 3; D: a plasma wall below and above cutoff, four mass-shell triples and the LC ladder's pass band; E: the sum of all round trips for `g = 1/2, 7/8, 99/100` at six phases, twelve trips each, with the Fabry–Pérot transmission; F: four round trips along and across a wind | under 1 s, from a development run (0.1 s) | 60 s | 0.1 s | 11,684 KiB |

`echo_spectra.py`: exit 0, `fail []`. Output `echo_spectra.txt` (7 lines, one per part, each with its elapsed
milliseconds), SHA-256 `dae7a3536f37f9997df11bc35d69602e354849eca517a4e9ff05f2b8e43292a5`; script SHA-256
`7802161d7affe04a5701967356cec262fbe78b618f8e68c30435e1906a43c8dd`. Rationals (`fractions.Fraction`), rational
complex pairs and residues modulo the three primes only, no float anywhere. The elapsed milliseconds differ between
runs; every other field is deterministic. No private data.

Development, before this run:
- B first failed for `ρ = ±i`: the class was written `m ≡ r (mod 4)`. The transform is nonzero only where
  `w^(mN) = ρ⁻¹`, so the class is `m ≡ −r` when `w^N` is the chosen fourth root of unity; the script now derives it.
- B first required every bin of the class to sound. The excitation can silence one (N = 17, `ρ = −1`: 16 of 17), which
  is part C's point, so B now requires every bin outside the class to vanish and at least one inside to sound.
- D first checked `|Γ| = 1` through a quotient that was 1 by construction; it now divides `(1 − iκ)/(1 + iκ)` over
  `ℚ(i)` and reads the modulus.
- Each part was then broken on purpose in a scratch copy (the return leg's factor inverted in A, `k` shifted in E, the
  silence rule changed in C, the boost's square changed in D), and each broken copy failed its part.

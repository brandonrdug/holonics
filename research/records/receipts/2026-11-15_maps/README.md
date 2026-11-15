# Receipts: the site maps' second loop (Brandon, November 15 15:19: "40 minutes a lap is a lot")

Device: the RTX 4080 SUPER. The maps (the forward map, the transposed map and the outer sum) held about 140 ms of a ~700 ms section in lap
31's profile, at about a fifth of the card's measured product rate (`p50_step0.txt`, the tile yardstick).

- What bound them, read at source and in the compiled code: each tile read every word once before staging any (the proof `k · a · b < 2^63`
  and the forward map's refusal), and the narrow and wide sums stood live together, so a thread held 156 to 170 registers and a
  multiprocessor one block of 256 threads. The outer sum added its partials atomically every 64 sites.
- The change, every bit kept: each chunk's largest words are read as the chunk is staged, the narrow sums go on while the chunks' bound
  `Σ len · a · b` stands under `2^63` (every partial then stands under it), and a tile whose chunk breaks it begins again in the wide form;
  the two forms' registers stand in separate scopes, so two blocks fit a multiprocessor (128 registers); the forward map's refusal is read
  only by the wide form, since a narrow tile's inputs under `2^31` cannot reach `2^126` with any 32-bit weight bound; the outer sum's walk is
  read by the host for one wave of two blocks a multiprocessor (64 to 512 sites).
- Parity: the maps' test at every shape the line launches, 96 cases equal; a new test of the outer sum's long walks (walks of 256 and 512,
  a walk that turns wide mid-walk, a bound that passes `2^63` at the eighth chunk, masks), 18 cases equal.
- The bench at the line's shapes (`the_site_maps_timed_at_the_lines_shapes`, 20,298 sites, run beside a lap of the line, the least of 100
  interleaved rounds): the forward and transposed maps 0.62 to 0.76 of the earlier form, the outer sums 0.36 to 0.43 (walks 256 and 512
  against 64; 1,024 read slower).
- Gate 3 on lap 17 equal (`lines.txt`): parity on 3 sections, 24 sections reproduced, the read's cavity table byte for byte.
- Timing, one balanced hold on 24 of the line's sections from lap 34's `STATE.3000`, the card alone after lap 34's reads: the control
  (`athena_rate2`) 648.6 to 668.3 ms a section, the build 595.2 to 628.5; every run's 24 section lines equal the first's. The build reads
  0.94 of the control (0.92 in the hold's first pair, 0.965 in its second): about 40 ms a section, the maps' share the bench forecast.
- The line takes the build from lap 36 (`next_bin`; lap 35 had read its binary before the hold).

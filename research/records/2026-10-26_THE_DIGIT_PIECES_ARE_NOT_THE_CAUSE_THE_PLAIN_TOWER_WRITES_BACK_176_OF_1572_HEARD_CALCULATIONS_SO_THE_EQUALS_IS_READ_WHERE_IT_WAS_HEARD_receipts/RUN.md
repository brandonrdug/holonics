# The cause test's trainings and reads, and the slice of the next read

## The cause test on Brandon's PC

At `d26e16daf46ab2d311d94b967f6da61e9ab162a0`, in a fresh worktree whose own target directory built
the example (`Compiling holonics` from the worktree). Every run went under the run directory's
`wait4` wrapper (`RUN_RECEIPT`), with `RAYON_NUM_THREADS=8` and an 8 GiB memory scope
(`memory.max` 8,589,934,592, `swap.max` 0), with nothing else heavy on the host.

- Binary `examples/solenoidal_alpha`, SHA-256 `04232e3d2c4785866fe285a6cf9d84ba422b94ae5e316a3dd655180f0eda70b5`.
- Founding key stream `keys_tower.bin`: `fcaadc56deeb837ce9e46f2c0d52269022c576bae30facaacea74756a71e9593`.
- Inputs checked by SHA-256: the committed units `d0973c39…782a`, the foil `186b82ed…d0b4`, the
  training text `050b94f3…3b95`, the held-out text `e5bffe0e…3153`, its roles `a7d7ccdc…c9c1`, the
  development slice `173c9ac3…f0d0`, and the `lapD8` read's key file `bbe735d7…c243`.
- `DIGIT_UNITS founded=1062 kept=949 removed=113`.

| run | projection | deadline | measured wall | ratio | peak resident |
|---|---|---|---|---|---|
| build | 126 s | 180 s | 122.9 s | 0.975 | 3,365,664 KiB |
| development pass `C`, first 800 training problems | unmeasured | 180 s | 14.4 s | — | 206,332 KiB |
| development pass `F`, first 800 training problems | unmeasured | 180 s | 15.1 s | — | 196,252 KiB |
| training `C`, three passes | 354.7 s | 360 s | 285.5 s | 0.805 | 240,544 KiB |
| training `F`, three passes | 345.0 s | 350 s | 307.7 s | 0.892 | 234,488 KiB |
| read `C`, 747 problems | 27.7 s | 30 s | 12.9 s | 0.466 | 41,124 KiB |
| read `F`, 747 problems | 29.5 s | 30 s | 13.6 s | 0.461 | 42,608 KiB |

The trainings' projections are the record's upper ends, `3·(S·1.12·w + h) + 1 s`.
- `C`: `w` = 78.1875 ms (its first window, 2,502 ms over 32 sections; the others 68.7 to 70.9 ms a
  section), `h` = 3,092 ms, window bound 2,802.2 ms. Largest window over the three passes: 2,342 ms
  (pass 2, section 256), of 123.
- `F`: `w` = 66.375 ms, `h` = 3,219 ms, window bound 2,378.9 ms. Largest window: 2,256 ms (pass 0,
  section 1,408), of 141.
- A pass's first window is counted from that pass's start, so the held-out read is not in it.

The reads' first 64 problems took 1,193 and 1,238 ms, against a stop line of 3,300 ms.

```text
UNIT_READ units=1318 train_bytes=3528168 train_units=1342760 dev_bytes=397669 dev_units=151684
TOWER_TRAIN material=277542 streams=8 section=128 sections_a_pass=1311 train_bytes=3528168 dev_bytes=397669
TOWER_PASS pass=0 train_bits_a_byte=2.173 dev_bits_a_byte=1.984 dev_regions Q=1.523 P=2.593 N=0.870 M=1.990 deposits=1311/1311 pass_ms=94363 elapsed_ms=94366 train_code=8037223663024 dev_code=827211273484 grain_bits=20
TOWER_PASS pass=1 train_bits_a_byte=1.914 dev_bits_a_byte=1.906 dev_regions Q=1.407 P=2.515 N=0.695 M=1.913 deposits=1311/1311 pass_ms=95118 elapsed_ms=189485 train_code=7078380619281 dev_code=794924858380 grain_bits=20
TOWER_PASS pass=2 train_bits_a_byte=1.851 dev_bits_a_byte=1.869 dev_regions Q=1.318 P=2.390 N=0.608 M=1.878 deposits=1311/1311 pass_ms=95568 elapsed_ms=285053 train_code=6846808079124 dev_code=779508401907 grain_bits=20
TOWER_DONE state_bytes=9249896 state_sha256=84e2bacfc6ea56c49181e4048f21ac32ad502ce67a94a001cd1d2ad9dd1678b4 elapsed_ms=285111
RUN_RECEIPT exit=0 wall_s=285.5 peak_rss_kib=240544 user_s=1686.2

UNIT_READ units=1205 train_bytes=3528168 train_units=1535797 dev_bytes=397669 dev_units=173650
TOWER_TRAIN material=262965 streams=8 section=128 sections_a_pass=1499 train_bytes=3528168 dev_bytes=397669
TOWER_PASS pass=0 train_bits_a_byte=2.148 dev_bits_a_byte=1.974 dev_regions Q=2.962 P=3.477 N=1.788 M=1.961 deposits=1499/1499 pass_ms=103933 elapsed_ms=103936 train_code=7943812264068 dev_code=822892436856 grain_bits=20
TOWER_PASS pass=1 train_bits_a_byte=1.882 dev_bits_a_byte=1.881 dev_regions Q=2.952 P=3.598 N=1.427 M=1.868 deposits=1499/1499 pass_ms=104258 elapsed_ms=208195 train_code=6957746229993 dev_code=784370877819 grain_bits=20
TOWER_PASS pass=2 train_bits_a_byte=1.813 dev_bits_a_byte=1.837 dev_regions Q=2.882 P=3.477 N=1.544 M=1.824 deposits=1499/1499 pass_ms=99144 elapsed_ms=307340 train_code=6704577384966 dev_code=765754436194 grain_bits=20
TOWER_DONE state_bytes=8931974 state_sha256=a03eb86f2afee212e85f7267de87724b69f364e144a1a5ba58996507654fa5e7 elapsed_ms=307391
RUN_RECEIPT exit=0 wall_s=307.7 peak_rss_kib=234488 user_s=1819.5

TOWER_WRITTEN problems=747 calculations=2448 free_bytes=299731 prompt_units=468588 released_units=116253 most_units_a_problem=4692 agree=1 mark_agree=64 mark_cap=8 elapsed_ms=12900
TOWER_WRITTEN_FILES free_sha256=889d1f9b2c434b43d0e9ad404811507120011adc3dc732e13449f6bbfea4a098 marks_sha256=f738c4c3d31e809233bc1271215d064adc7b6d50ee1a6d6a13bb8ed967f30599
RUN_RECEIPT exit=0 wall_s=12.9 peak_rss_kib=41124 user_s=100.5

TOWER_WRITTEN problems=747 calculations=2448 free_bytes=299772 prompt_units=518610 released_units=128587 most_units_a_problem=4988 agree=1 mark_agree=64 mark_cap=8 elapsed_ms=13560
TOWER_WRITTEN_FILES free_sha256=8a4672f890e5d8c9dd308006f5479d125820d73cf727cb9dca6c19abb96ee40c marks_sha256=d04e84f9e471c419c772264a06670cbee0f8bee92a6e1928565c320661371a0b
RUN_RECEIPT exit=0 wall_s=13.6 peak_rss_kib=42608 user_s=105.7
```

The rules, with `TypeError` read as no value (the one-line change in this commit; the first run
stopped on `F`'s `<<8(2/3)=15>>` after printing `C`'s line, which the changed rules print
byte-identically):

```text
WRITTEN dir=C problems=747 a_on_problem=47 b_free_calculations=1219 b_free_right=53 c_first_calculations=637 c_from_question=25 b_equals=190/2448 met=176/1572 never_met=14/876 binary +=14/470 -=21/388 *=114/897 /=29/343
WRITTEN dir=F problems=747 a_on_problem=38 b_free_calculations=1227 b_free_right=61 c_first_calculations=618 c_from_question=49 b_equals=156/2448 met=131/1572 never_met=25/876 binary +=14/470 -=14/388 *=91/897 /=20/343
PAIRED met_only_a=158 met_only_b=113 met_both=18 never_only_a=14 never_only_b=25 never_both=0
```

The free releases and the marks are written from GSM8K prompts and stay out of the repository.

## The next read's slice

Cut in the container from the training text `050b94f3…3b95`:

```python
chunks = [p for p in train.split(b"\n\n") if p.strip(b"\n")]   # 6,730 problems
slice = b"\n\n".join(chunks[0::9]) + b"\n\n"                  # 748 problems, 392,606 bytes
```

SHA-256 `b9a2236637730ef450d69816edd7c64f744e21f2331c683bc9f3651e95ef04b2`; 2,344 calculations;
prompt bytes 1,190,596 (the held-out text: 747 problems, 2,448 calculations, 1,256,521).

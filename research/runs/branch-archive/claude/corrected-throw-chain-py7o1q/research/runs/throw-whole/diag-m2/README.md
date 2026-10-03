# Diagnostic of m2 from m1 (not the chain's m2)

The corrected throw chain (`5f254c2d`, whole-move release test) stopped at m2: no line before its
1350 s deadline (`../m2/`). This diagnostic reruns m2 from m1's state and flight to find where the
time goes. Build `5f254c2d` + `7a650e6b` (print-only unit lines on stderr; cherry-picked locally as
`5f59550`), 4 threads, outer timeout 4049 s, no per-move deadline. `gdb -batch -p` backtraces every
~115 s are in `stacks/` (each attach pauses the process briefly, so a gap holding a sample is on the
long side). `stderr.stamped` carries each unit line's wall arrival; process start (`/proc`, 10 ms
ticks) is in `process_start.txt`. `first-unprinted/` is an earlier 236 s run on the plain `5f254c2d`
binary, stopped for the rebuild; its two samples agree.

Wall-stamped gaps (ms), with the printed ms beside them:

| unit | gap | printed |
|---|---|---|
| incumbent (from process start) | 166264 | 165832 |
| proposal and persistence | 1814 | 1812 |
| returns, slope, first step, whole-move power | 32691 | 32691 |
| trial η 4 (refused, OwnNotBelow) | 155229 | 151812 |
| trial η 2 (refused) | 207135 | 203871 |
| trial η 1 (refused) | 206605 | 203396 |
| trial η 1/2 (refused) | 209825 | 206634 |
| trial η 1/4 (refused) | 206763 | 203392 |
| trial η 1/8 (refused) | 155897 | 152599 |
| trial η 1/16 (adopted) | 208749 | 205464 |

Every sample from 235 s to 1503 s has the main thread in `executed_move_flown → ladder`, in the
rayon map over requests (a trial's reread). Each gap holds exactly one trial: seven trials, seven
reread lines. The move completed: process wall about 1551030 ms (`listing.txt` written 23:43:55.332).

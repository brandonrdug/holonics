# Audit: waiting, deadlines and concurrency. The workers blocked on their own runs

**Date.** September 30. **Issues.** #63. **Grade.** [measured] from the transcripts; [project-postulate]
for the standard.

**Occasion.** Brandon: "can you audit the timeout patterns that agents have been engaging in during
workflows? I get the impression they're wasting a ton of time waiting repeatedly and we need standards
for this so that they don't freely keep raising the limit and wasting time."

**Sources.** Every Claude Code transcript of this repository since the reset (September 24), main
sessions and subagents (542 transcripts), and 382 Codex session files over the same window. The
analysis scripts read shell calls, their wall times from call to result, their commands, their tool
timeouts and the turns' token usage. Nothing private is reproduced here.

## 1. What the Claude workers did

- **Calls.** 32,387 shell calls, of which 706 ran in the background, and 376 Monitor calls.
- **Waiting.** Foreground shell wall time was 194,986 s, and **87,780 s of it was wait loops**
  (`until …; do sleep …; done`, `sleep N; cat …`, `while … sleep`): 493 calls.
- **Poll chains.** 42 chains of at least three consecutive waits with gaps under 120 s, holding 231
  calls; the longest ran 20 calls in a row. The chains exist because the shell tool caps a call at
  600 s, so a worker blocking on a two-hour run re-enters every ten minutes.
- **Blocked sleeps.** 97 foreground `sleep N; …` calls, in 85 transcripts, were refused by the
  harness and returned nothing.
- **Wait durations.** 275 under 60 s, 74 from 60 to 300 s, 113 from 300 to 600 s, and 31 from 600 to
  1,200 s. The inner sleep intervals were mostly 5, 10 and 60 s.
- **What was awaited.** 233 waits grepped a log for an exit or progress line, 63 watched a process
  and 9 waited for a file. The rest were other conditions.
- **The heaviest waiters were today's step-1 workers.**

  | Worker | Span | Waiting |
  |---|---|---|
  | Stage-2 executed comparison | 20,823 s | 12,087 s in 38 waits |
  | Step 1a | 11,633 s | 9,058 s in 21 waits |
  | Modulus | 12,723 s | 8,292 s in 18 waits |

- **Raised limits.** 9 runs relaunched with a larger outer `timeout N`, for example 600 → 900,
  2,400 → 3,000 and 7,200 → 9,000. 20 repeated commands were relaunched with a larger tool timeout.
  Tool timeouts of 900,000, 1,200,000, 1,800,000 and 3,600,000 ms were requested 1,773 times, above
  the tool's own 600,000 ms bound.
- **Serial schedules.** The modulus loop ran its independent terrains one at a time. Its order-2,
  alternation and line pipelines took about 7,800 s in series. Run together, the longest of them
  takes about 4,300 s: the host has 24 cores and 32,746,147,840 bytes of memory.
  - Step 1a ran its terrains together on 8 threads each.
  - Step 1a's projection for trained-constitution reads was about 3.5 times too low. Two validation
    reads passed their deadline and were reported incomplete, not rerun: lesson 9 held.
- **Shared scratch.** Two workers overwrote each other's files under shared scratch names
  (`pinned_runs.sh`, `tests_before.txt`).
- **What it did not cost.** Tokens. The turns that issued a wait read 266,655,280 input tokens, about
  one per cent of the 14,382,700,044 read across all tool turns. The cost is wall time and the
  orchestrator's blocked schedule.

## 2. What Codex did

382 session files, 2,288 function calls: no wait loops, and tool timeouts of 10,000 to 60,000 ms
(30,000 ms on 312 calls). Codex's runs in this window were short, and it does not block on long ones.

## 3. The causes

1. **Blocking instead of launching.** The workers ran their long jobs in the foreground or polled
   them, though the harness re-invokes an agent when a background command exits.
2. **No per-unit early stop.** A run whose first moves already exceeded the projected rate was waited
   out to its deadline.
3. **Limits treated as adjustable.** Raising a deadline or a tool timeout was the routine response
   to a slow run. Lesson 9 names it, but it was not stated as an operational rule.
4. **Serial schedules by default** on a 24-core host.
5. **Projections from too little.** 1a projected trained reads from untrained ones.

## 4. The standard

Stated in CLAUDE.md and AGENTS.md, "Waiting, deadlines and concurrency", and supplied with every
brief:
- launch, do not block;
- progress is an event, not a poll;
- project, then fix the deadline once;
- stop early on evidence;
- never raise a limit;
- run independent work together within declared thread budgets;
- isolate scratch;
- receipts carry time;
- the orchestrator waits on notifications.

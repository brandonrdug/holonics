#!/usr/bin/env -S python3 -I
"""Controls of runs.py's failure lines (host text only; no run is dispatched, read or stopped).

A log line reports a failure when a failure word stands outside the counts that read zero: every FIELD_LAP line prints
next_refused=0, and the watch flagged each lap line of the P8 laps (November 11) until counts at zero were set aside.
A count above zero, an error, a panic, a kill, a traceback and a busy lock still read as failures.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import runs  # noqa: E402

CASES = {
    "FIELD_LAP lap=1 section=12 own=1.72 next_refused=0 halvings=0 ms=3401": False,
    "FIELD_SECTION refused=00 next_refused=0": False,
    "refused=0 error_count=0.000 panics=0": False,
    "FIELD_LAP lap=1 section=12 next_refused=3": True,
    "next_refused=0.5": True,
    "error: the card refused the field: a sum outgrew its 128-bit carrier": True,
    "thread 'main' panicked at src/lib.rs": True,
    "Killed": True,
    "Traceback (most recent call last):": True,
    "LOCK_BUSY .local/gpu.lock": True,
}


def main():
    wrong = [(text, want) for text, want in CASES.items() if runs.failure(text) != want]
    assert not wrong, wrong
    print(f"runs failure lines: {len(CASES)} lines, the controls hold")


if __name__ == "__main__":
    main()

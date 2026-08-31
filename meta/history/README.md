# Historical manifest snapshots

[definition] Files in this directory are immutable evidence snapshots of ignored return populations
which no longer exist in the working tree. They do not describe the live `output/` directory and
are never inputs to a current release gate.

[historical; measured] Brandon authorized removal of `output/` on 2026-08-30. The pre-clean output
manifest records 263 roots, 23,252 files, and 103,829,498,632 apparent bytes. Its paired closure
manifest preserves the producer/source-closure testimony available before deletion, including
explicit `ORPHAN` rows. The limitations of that older closure calculation are retained as evidence;
the live closure owner is corrected separately.

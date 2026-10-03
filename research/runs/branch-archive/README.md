# Run outputs archived from branches (October 3)

Before this directory, 52 of the 103 earlier states that `research/runs/u6/LEGACY_STATES.txt`
lists, and four states that `research/runs/u6/PC_QUEUE.md` names, existed only on run branches.
Deleting a branch would have taken them with it. Every run output that was on a run branch and in
no commit of main is copied here byte for byte, so that the branches can be retired with nothing
cited left behind. The branch inventory and the classification of each branch are in the audit
`branches_2026-10-03.md` (the project's audits folder).

## Layout

- `claude/<branch>/<path on that branch>`: one file per run output (states, flights, stamps, timing
  and section receipts, the drivers that produced them). The path below the branch name is the
  file's path on the branch, so a manifest line `claude/<branch>:<path>` becomes
  `research/runs/branch-archive/claude/<branch>/<path>` on main.
  - Run branches copied: `cloud-runs-2-5aw27d` (68 files), `cloud-runs-pfo084` (22),
    `corrected-throw-chain-py7o1q` (54), `pc-receipts` (52), `throw-control-chain-847j2f` (39),
    `u6-local-archive` (45). That is 280 files.
  - `independent-derivations-wvtfpc` (65 files) is the head of the held PR #240. Its
    `2026-10-02_THE_THROW_receipts/` directory is copied because the manifest cites six of its
    states; it stays a duplicate if #240 merges.
- `bundles/<branch>.bundle`: every commit on the branch beyond main `0a155865`, whole, for 11
  branches. These keep what the plain copies leave out: the code, Lean and record versions the
  runs were made with, and the unmerged derivations on `cell-units-aifrqz`, `chart-mirror-aifrqz`,
  `lattice-floor-aifrqz`, `reading-curvature-aifrqz` and `window-chain-archive`. Each bundle's
  head is the branch's tip commit, so every commit hash a record cites stays recoverable.
- `SOURCES.tsv`: for every file, its sha256, its size in bytes, its archive path, its branch, the
  branch's tip commit and its path on the branch. 345 copied files (3071633 bytes), 11 bundles
  (935315 bytes) and two files kept only inside `bundles/pc-receipts.bundle`: the card suite logs
  `gpu259/gate3_c3e6d21.txt` (5703079 bytes) and `gpu259/gate3_mergebase_3515ed4a.txt`
  (5703078 bytes), which no record cites and which were the stale-kernel runs.

## Checking and restoring

```bash
cd research/runs/branch-archive
awk -F'\t' 'NR>1 && $3 !~ /^\(/ {print $1"  "$3}' SOURCES.tsv | sha256sum -c --quiet

# a branch, whole, with its original name (main must be present):
git fetch research/runs/branch-archive/bundles/pc-receipts.bundle \
  'refs/heads/claude/pc-receipts:refs/heads/claude/pc-receipts'
```

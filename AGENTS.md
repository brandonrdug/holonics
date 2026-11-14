# Holonics — Codex operating guide

This is Codex's guide. The repository's laws and practice are stated once, in
[CLAUDE.md](CLAUDE.md), and they bind Codex as they bind Claude. Read that guide whole before any
work, with the four documents it names (THE_MACHINE, the elementary objects, CONSTRUCTION_STATE and
THE_REBUILD), and keep what you have read. This file holds only what is Codex's own.

[project-postulate] **Why this file is short** (November 14;
[the consolidation](docs/plans/THE_CONSOLIDATION.md), decision D8). Until then this file and
CLAUDE.md were the same 85.7 KB but for about forty lines, and every rule was edited twice. A law
stated twice drifts, and a reader cannot tell which copy governs. So the laws live in CLAUDE.md
alone. Where that guide says what Claude does (its delegation rule, its mailbox id, its permission
on the PC), the paragraphs below say what Codex does. Everything else there applies to Codex as
written. The last full copy of this file is at
[`ba180139`](https://github.com/brandonrdug/holonics/blob/ba180139/AGENTS.md).

[project-postulate] **Whose repository this is** (Brandon, November 10). Brandon asked that Claude
hold the repository as its own, with complete authority over its structure, guides, plans,
branches and technical decisions. Claude leads and decides; Codex executes and reviews. An agent
here does not leave a defect it has seen for someone else: Codex repairs what its order covers and
writes the rest to the mailbox.

[project-postulate] **Working with Claude** (Brandon, October 5 and 8, November 8 and 10). Claude
decides the theory, the plan, the acceptance and the fixed guesses. Codex (GPT-6; also called Epime
and Astra) executes bounded work from Claude's written orders, and reviews.
- An order names its object, its equations, its consumer, its acceptance and the guess fixed before
  the read. Codex carries it out as written and reports the measurement against the guess, a miss
  included.
- Where an order is silent, Codex stops at that point and writes the question to the mailbox. It
  does not extend the plan, change a law, an acceptance or a fixed guess, add a run switch, or
  choose between laws by running them. Reason: the method rules of CLAUDE.md, and a plan extended
  by its executor is a second plan.
- A review or letter from Codex is for thinking together: predictions, hypotheses,
  counterexamples. It is never a gate, and nothing waits on it (November 8).
- An author merges its own pull request when the gates of its change pass (the trunk contract in
  CLAUDE.md).
- The two coordinate through the repository mailbox (`python3 tools/agent_mailbox.py`;
  [its protocol](tools/agent_mailbox.md)); Codex's sender id is `codex`.
- A statement relayed as Brandon's is read in his own message before it governs (Evidence, in
  CLAUDE.md).
- Brandon's exports of the Epime room, kept outside the repository, are evidence with the same
  handling as `tools/human_messages.py` output: never committed or published.

[project-postulate] **Delegation.** Codex delegates to **GPT-6 Luna workers only**, for bounded
independent work with explicit owned paths, mathematical operands, source records and consuming
calls. Use fewer workers when the work does not split. Every brief supplies what CLAUDE.md's
delegation rule lists (the lessons records, the guide, the paths and owners, the equations, the
consumer, the receipts, the device line and the waiting standard). The primary inspects source and
integrates the returns; worker measurements are receipts. Honour a request to work without agents.

[project-postulate] **The census on the PC.** The allow rule for `python3 tools/repo_census.py` in
the repository's `.claude/settings.json` is Brandon's grant to Claude's sessions (November 10). A
run with `--push-local` asks him, because it publishes commits that never left the PC. No agent
adds a permission rule of its own.

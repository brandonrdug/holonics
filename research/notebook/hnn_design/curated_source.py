"""The curated conversation source (THE_REBUILD campaign 5's input; HNN_FORMULA, "The source and
release contract"; #73, #148).

An exterior codec step, stdlib only, run once. It reads the private conversation exposure
(`.local/datasets/athena-alpha-exposure-2026-09-06.jsonl`, schema
`holonics.conversation-exposure.v1`) and writes a structured source, its incidence, a pinned cut and
the same bytes as a flat stream into `.local/cuts/` (mode 0700), each file created mode 0600
(`standing_cut.private_write`: private from creation, never widened and narrowed after). Nothing it
writes is published, and it prints counts and hashes only, never any text.

The contract's items, as this source meets them:

1. **A terrain chart.** The cells are the UTF-8 bytes of each visible part's text (codes 0..255),
   and the section letters are twelve more codes, 256 + 3k + c, for kind k in (open, switch, turn,
   part) and channel c in (human, agent, tool). So the declared alphabet is 268, and a section is a
   coded cell, never side information: a channel's change costs the bits of its letter.
2. **Channels as ports** (the mapping, by value name; agent-inferred from the data rules at
   `13f8c734:docs/CONVERSATION_DATA.md`):
   - human: part kinds `human-text` and `human-command` (a command explicitly attributed to a
     human), under `author_class` `human` (record kinds `user`, `response_item`);
   - agent: part kind `agent-text`, under `author_class` `agent-visible` (record kinds `assistant`,
     `response_item`);
   - tool: part kinds `tool-call` and `tool-result`. The port is declared, and this exposure has no
     part of either kind (tool material is in the refined package's tool ports, not the exposure);
   - harness: a view flagged `control-surface` (a control block), every captured view after a
     family's first (a presentation mirror of the same declared record), and every nonvisible
     reference of kind `harness-text`. The harness is a port of references only: its bytes are
     counted and never enter the stream.
   A part whose text is absent (`human-material`) stays a reference on its author's port. The flag
   `container-has-copied-session-meta` marks the container, not the view's text (the exposure
   already keeps the first container origin), so a flagged view stays on its author's port.
3. **Sections follow the declared turn.** Before each visible part with cells, one letter, read
   against the previous emitted occurrence: `open` when the occurrence is the first of its
   conversation (`session_id`) in the stream, an aeon opening; `switch` when its conversation is
   another than the previous emitted occurrence's (sessions interleave in the declared order);
   `part` when it lies in the previous emitted occurrence's declared turn (the provider's
   `turn_id`, in the same conversation), or is a further part of the same record; `turn`
   otherwise: a new declared turn or, where the provider declares no `turn_id`, the record boundary
   (the fallback: one declared occurrence is one turn). So turns are epochs and conversations are
   aeons. The manifest counts the letters by path (`turn_id` declared, the record boundary, a
   further part within a record). [agent-inferred] A return into a conversation whose declared
   turn continues is a `switch`: the letter must mark the aeon change, and the four kinds carry one
   section, not two; the manifest counts those returns, and a declared turn re-entered after
   another turn of its conversation.
4. **Incidence** (the incidence file, one record per development occurrence, ordinals and capture
   coordinates only): the occurrence's port and its parts' cell ranges; its declared parent (the
   provider's `parent_id`, its `provider-parent` link) and its relations (`comparison-request`,
   `later-human-after-agent`), each resolved to an earlier occurrence of the stream or kept
   unresolved (`outside`: no development occurrence holds it; `later`: it lies after this one).
   `previous_record` is the capture predecessor (it is `event - 1` in every development view): it is
   carried as a coordinate and never as a parent, since adjacency never manufactures an edge.
5. **Separation**: the harness above. Equal text never merges occurrences: every occurrence is
   emitted in the dataset's declared order, whatever its text. A mirror is harness only when it
   is one: every mirror view's visible parts (kinds and text) are compared by hash with its
   family's first view's, and every development family's `conflicts` must be empty. A family
   failing either is **refused** (deferred): never emitted and never resolved, its events a
   relation's `refused` state, the refusals counted in the manifest's `checks`.
6. **Counts under a certified partition**: the manifest's counts; the pinned cut below declares
   its population `n*`.
8. **A pinned partition.** Only the `development` partition is read into the source. The
   `evaluation` and `deferred` families are parsed for their partition label alone (and hashed with
   the whole file); none of their fields enter anything.

The pinned cut: the development stream's tail of at most `population` cells (a power of two,
`2^20` as the wide cut), beginning at its first section letter at or after `len - population`, so
the cut opens a part. Its final eighth (`cells // 8`) is held out, as the wide cut's. The flat cut
is the same bytes with every letter removed, its held-out cells the bytes of the curated held-out
cells, so the two are measured on identical cells.

    HOLONICS_ROOT=<main checkout> python3 research/notebook/hnn_design/curated_source.py 1048576

For F4, F1, F2 or F5, after `development_families.py` has pinned the private membership, the optional
second argument `choosing` or `validation` emits only that role's development families under
`curated-<item>-<role>-*` names (`F4` is the default item; pass `F1`, `F2` or `F5` as a third argument). It does
not decode evaluation or deferred records. A relation across roles is unheld, never supplied by
adjacency.

Outputs in `.local/cuts/`:
- `curated-source.bin`: the whole development stream, one little-endian u16 code a cell;
- `curated-source.incidence.jsonl`: the occurrences' ports, cell ranges and incidence;
- `curated-source.json`: the manifest (counts and hashes only);
- `curated-cut.bin` (+ `.json`): the pinned cut, u16 codes;
- `curated-flat-cut.bin` (+ `.json`): the same bytes, one byte a cell, in the standing cut's
  manifest format (`exterior::read_cut` reads it).
"""

import hashlib
import json
import os
import sys
from array import array

from development_families import PARTITION, assignment
from standing_cut import ROOT, SOURCE, private_directory, private_write

CHANNELS = ("human", "agent", "tool")
KINDS = ("open", "switch", "turn", "part")
BYTES = 256
ALPHABET = BYTES + len(KINDS) * len(CHANNELS)
PART_CHANNEL = {
    "human-text": "human",
    "human-command": "human",
    "human-material": "human",
    "agent-text": "agent",
    "tool-call": "tool",
    "tool-result": "tool",
}
AUTHOR = {"human": "human", "agent-visible": "agent"}
HARNESS_FLAG = "control-surface"
RELATIONS = ("provider-parent", "comparison-request", "later-human-after-agent")


def letter(kind, channel):
    return BYTES + len(CHANNELS) * KINDS.index(kind) + CHANNELS.index(channel)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def visible(view):
    """A view's visible parts, kinds and text, as one hash (compared, never printed)."""
    digest = hashlib.sha256()
    for part in view["visible_parts"]:
        digest.update(json.dumps([part["kind"], part.get("text")]).encode("utf-8"))
    return digest.digest()


def u16(codes):
    packed = array("H", codes)
    if sys.byteorder != "little":
        packed.byteswap()
    return packed.tobytes()


def count(table, *keys):
    for key in keys[:-1]:
        table = table.setdefault(key, {})
    table[keys[-1]] = table.get(keys[-1], 0) + 1


def main():
    arguments = sys.argv[1:]
    if len(arguments) not in (1, 2, 3) or (len(arguments) >= 2 and arguments[1] not in ("choosing", "validation")) or (len(arguments) == 3 and arguments[2] not in ("F1", "F2", "F5")):
        sys.exit(__doc__)
    population = int(arguments[0])
    assert population > 0 and population & (population - 1) == 0, "a power of two"
    role = arguments[1] if len(arguments) >= 2 else None
    item = arguments[2] if len(arguments) == 3 else "F4"
    name = "curated" if role is None else f"curated-{item.lower()}-{role}"
    if role is not None:
        with open(os.path.join(ROOT, ".local", "cuts", f"development-families-{item.lower()}.json"), "rb") as handle:
            split = json.load(handle)
        assert split["seed"] == f"holonics-{item.lower()}-development-families-2026-09-27-v1"
        expected = {entry["family_sha256"]: entry["role"] for entry in split["members"]}
        assert len(expected) == len(split["members"])

    stream = []  # the curated codes, bytes and letters
    occurrences = []  # the incidence records
    event_to_occurrence = {}
    families = {"development": 0, "evaluation": 0, "deferred": 0}
    channel_counts = {c: {"parts": 0, "cells": 0, "empty_parts": 0, "material_references": 0} for c in CHANNELS}
    harness = {"control_views": 0, "control_parts": 0, "control_bytes": 0, "mirror_views": 0,
               "mirror_parts": 0, "mirror_bytes": 0, "harness_text_references": 0,
               "other_nonvisible_references": 0}
    letters = {kind: {channel: 0 for channel in CHANNELS} for kind in KINDS}
    paths = {path: {kind: {channel: 0 for channel in CHANNELS} for kind in KINDS}
             for path in ("turn_id", "record_boundary", "within_record")}
    returns = {"switch_into_its_conversations_continuing_turn": 0, "declared_turn_reentered": 0}
    checks = {"families_conflicts_empty": 0, "families_conflicts_declared": 0,
              "mirror_views_equal_first_view": 0, "mirror_views_differing": 0, "families_refused": 0}
    refused_events = set()
    flags = {}
    sequence_order = {"increasing": 0, "not_increasing": 0}
    capture = {"previous_record_is_event_minus_one": 0, "otherwise": 0}
    sessions = {}
    aeons = set()  # the conversations whose aeon the stream has opened
    turns = {}  # each conversation's declared turns: the one its last emitted occurrence lies in, and all
    source_hash = hashlib.sha256()
    last_sequence = None
    last_session = None
    last_turn = None  # the previous emitted occurrence's declared turn (None: none declared)

    with open(SOURCE, "rb") as handle:
        for line in handle:
            source_hash.update(line)
            prefix = line[:line.find(b'"views"')] if b'"views"' in line[:1024] else line[:1024]
            match = PARTITION.search(prefix)
            if match is None:
                continue
            partition = match.group(1).decode("ascii")
            families[partition] += 1
            if partition != "development":
                continue
            record = json.loads(line)
            assert record["kind"] == "occurrence-family" and record["partition"] == partition
            if role is not None:
                assigned, family_hash = assignment(record["family"], split["seed"])
                assert expected[family_hash] == assigned
                if assigned != role:
                    continue
            sequence = record["sequence"]
            count(sequence_order, "increasing" if last_sequence is None or sequence > last_sequence
                  else "not_increasing")
            last_sequence = sequence
            view, mirrors = record["views"][0], record["views"][1:]
            first = visible(view)
            differing = sum(1 for mirror in mirrors if visible(mirror) != first)
            checks["mirror_views_differing"] += differing
            checks["mirror_views_equal_first_view"] += len(mirrors) - differing
            checks["families_conflicts_declared" if record["conflicts"] else "families_conflicts_empty"] += 1
            if record["conflicts"] or differing:
                checks["families_refused"] += 1
                refused_events.update(captured["event"] for captured in record["views"])
                continue
            index = len(occurrences)
            for captured in record["views"]:
                event_to_occurrence[captured["event"]] = index
            for mirror in mirrors:
                harness["mirror_views"] += 1
                for part in mirror["visible_parts"]:
                    harness["mirror_parts"] += 1
                    harness["mirror_bytes"] += len((part.get("text") or "").encode("utf-8"))
            for flag in view["flags"]:
                count(flags, flag)
            capture["previous_record_is_event_minus_one" if view["previous_record"] == view["event"] - 1
                    else "otherwise"] += 1
            for reference in view["nonvisible_part_references"]:
                harness["harness_text_references" if reference["kind"] == "harness-text"
                        else "other_nonvisible_references"] += 1
            author = AUTHOR[view["author_class"]]
            conversation = sessions.setdefault(view["session_id"], len(sessions))
            entry = {
                "occurrence": index,
                "conversation": conversation,
                "port": "harness" if HARNESS_FLAG in view["flags"] else author,
                "capture_predecessor_event": view["previous_record"],
                "event": view["event"],
                "parts": [],
                "links": [(link["kind"], link["target_event"]) for link in view["links"]],
            }
            occurrences.append(entry)
            if entry["port"] == "harness":
                harness["control_views"] += 1
                for part in view["visible_parts"]:
                    harness["control_parts"] += 1
                    harness["control_bytes"] += len((part.get("text") or "").encode("utf-8"))
                continue
            opened = False
            declared = view["turn_id"]
            known = turns.setdefault(conversation, {"last": None, "all": set()})
            for part in view["visible_parts"]:
                channel = PART_CHANNEL[part["kind"]]
                assert channel == author or channel == "tool", "a part's kind agrees with its author"
                text = part.get("text")
                if text is None:
                    channel_counts[channel]["material_references"] += 1
                    entry["parts"].append({"channel": channel, "reference": part["kind"]})
                    continue
                cells = text.encode("utf-8")
                if not cells:
                    channel_counts[channel]["empty_parts"] += 1
                    entry["parts"].append({"channel": channel, "cells": [len(stream), len(stream)]})
                    continue
                if opened:
                    kind, path = "part", "within_record"
                else:
                    path = "record_boundary" if declared is None else "turn_id"
                    if conversation not in aeons:
                        kind = "open"
                        aeons.add(conversation)
                    elif view["session_id"] != last_session:
                        kind = "switch"
                    elif declared is not None and declared == last_turn:
                        kind = "part"
                    else:
                        kind = "turn"
                    if declared is not None:
                        if kind == "switch" and declared == known["last"]:
                            returns["switch_into_its_conversations_continuing_turn"] += 1
                        elif declared != known["last"] and declared in known["all"]:
                            returns["declared_turn_reentered"] += 1
                        known["all"].add(declared)
                    known["last"] = declared
                    last_session, last_turn = view["session_id"], declared
                opened = True
                stream.append(letter(kind, channel))
                letters[kind][channel] += 1
                paths[path][kind][channel] += 1
                start = len(stream)
                stream.extend(cells)
                channel_counts[channel]["parts"] += 1
                channel_counts[channel]["cells"] += len(cells)
                entry["parts"].append({"channel": channel, "letter": kind, "cells": [start, len(stream)]})

    # incidence, resolved against the stream's occurrences
    incidence = {}
    for entry in occurrences:
        resolved = []
        for kind, target in entry.pop("links"):
            at = event_to_occurrence.get(target)
            if at is None:
                state = "refused" if target in refused_events else "outside"
            elif at < entry["occurrence"]:
                state = "earlier"
            else:
                state = "later"
            count(incidence, kind, state)
            resolved.append({"kind": kind, "state": state,
                             **({"occurrence": at} if state == "earlier" else {"event": target})})
        if not any(link["kind"] == "provider-parent" for link in resolved):
            count(incidence, "provider-parent", "none declared")
        entry["relations"] = resolved

    # the flat stream and the pinned cut
    flat = bytes(code for code in stream if code < BYTES)
    curated = u16(stream)
    start = max(0, len(stream) - population)
    while stream[start] < BYTES:
        start += 1
    cut = stream[start:]
    cells = len(cut)
    held_start = cells - cells // 8
    flat_cut = bytes(code for code in cut if code < BYTES)
    flat_held_start = sum(1 for code in cut[:held_start] if code < BYTES)
    cut_letters = {kind: {channel: 0 for channel in CHANNELS} for kind in KINDS}
    for code in cut:
        if code >= BYTES:
            k, c = divmod(code - BYTES, len(CHANNELS))
            cut_letters[KINDS[k]][CHANNELS[c]] += 1

    incidence_bytes = "".join(json.dumps(entry, separators=(",", ":")) + "\n"
                              for entry in occurrences).encode("utf-8")
    private_directory()
    private_write(name + "-source.bin", curated)
    private_write(name + "-source.incidence.jsonl", incidence_bytes)
    private_write(name + "-cut.bin", u16(cut))
    private_write(name + "-flat-cut.bin", flat_cut)
    manifest = {
        "schema": "holonics.curated-source.v1",
        "source": os.path.relpath(SOURCE, ROOT),
        "source_sha256": source_hash.hexdigest(),
        "families": families,
        "development_role": role,
        "development_role_families": len(occurrences),
        "split_membership_sha256": split["membership_sha256"] if role is not None else None,
        "declared_order": sequence_order,
        "chart": {"cells": "UTF-8 bytes 0..255", "alphabet": ALPHABET,
                  "letters": {f"{kind}:{channel}": letter(kind, channel)
                              for kind in KINDS for channel in CHANNELS}},
        "ports": {"channels": channel_counts, "harness": harness, "flags": flags},
        "checks": checks,
        "sections": {"rule": "open: the conversation's first occurrence in the stream; switch: another "
                             "conversation than the previous emitted occurrence's; part: the previous "
                             "emitted occurrence's declared turn (turn_id) in the same conversation, or a "
                             "further part of the same record; turn: otherwise (a new declared turn, or "
                             "the record boundary where turn_id is absent)",
                     "letters": letters, "paths": paths, **returns,
                     "declared_turns": sum(len(known["all"]) for known in turns.values()),
                     "conversations": len(sessions),
                     "occurrences": len(occurrences),
                     "occurrences_with_cells": sum(1 for o in occurrences
                                                   if any("letter" in p for p in o["parts"]))},
        "incidence": {"relations": incidence, "capture_predecessor": capture},
        "development_stream_cells": len(stream),
        "development_stream_sha256": sha(curated),
        "flat_stream_cells": len(flat),
        "flat_stream_sha256": sha(flat),
        "incidence_sha256": sha(incidence_bytes),
        "cut": {"from": "development stream tail, beginning at its first section letter at or after len - population",
                "stream_start": start, "cells": cells, "population": population,
                "held_out_start": held_start, "held_out_rule": "the cut's final eighth, cells // 8 (as the wide cut)",
                "letters": cut_letters,
                "cut_sha256": sha(u16(cut)), "development_sha256": sha(u16(cut[:held_start])),
                "held_out_sha256": sha(u16(cut[held_start:])),
                "flat_cells": len(flat_cut), "flat_held_out_start": flat_held_start,
                "flat_cut_sha256": sha(flat_cut), "flat_development_sha256": sha(flat_cut[:flat_held_start]),
                "flat_held_out_sha256": sha(flat_cut[flat_held_start:])},
    }
    if role is not None:
        assert manifest["source_sha256"] == split["source_sha256"]
    private_write(name + "-source.json", json.dumps(manifest, indent=2).encode("utf-8"))
    private_write(name + "-cut.json", json.dumps({
        "schema": "holonics.curated-cut.v1", "encoding": "u16 little-endian, one code a cell",
        "alphabet": ALPHABET, "population": population, "cells": cells,
        "held_out_start": held_start, "cut_sha256": manifest["cut"]["cut_sha256"]}, indent=2).encode("utf-8"))
    private_write(name + "-flat-cut.json", json.dumps({
        "schema": "holonics.standing-cut.v2",
        "from": "the curated cut's bytes, its section letters removed; held out: the curated held-out cells' bytes",
        "population": len(flat_cut), "declared_population": population,
        "held_out_range": [flat_held_start, len(flat_cut)],
        "cut_sha256": manifest["cut"]["flat_cut_sha256"]}, indent=2).encode("utf-8"))
    print(json.dumps({key: manifest[key] for key in (
        "families", "development_role", "development_role_families", "split_membership_sha256",
        "declared_order", "checks", "ports", "sections", "incidence", "development_stream_cells",
        "development_stream_sha256", "flat_stream_cells", "flat_stream_sha256", "cut")}, indent=1))


if __name__ == "__main__":
    main()

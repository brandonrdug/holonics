"""The development split by conversation, the aeon, with a reserve that nothing reads (THE_REBUILD U6,
restated September 29; the audit record
`research/records/2026-09-29_THE_TEXT_CHART_AUDITED_ONE_PREDICTOR_SEEN_CONVERSATIONS_AND_NO_ARITHMETIC.md`,
§4 item 1; #73, #148, #63).

The source's evaluation and deferred records are inspected only for their partition label. Keys and
assignments stay in an owner-only file; stdout holds counts and hashes only.

    HOLONICS_ROOT=<checkout with private data> python3 development_families.py [U6]

**The unit is the conversation** (from U6 on). A conversation is the provider's `session_id` of a
family's first view, as `curated_source.py` reads it (its `open` and `switch` letters mark the same
aeons). Every message of a conversation (a development family, the pair `(provider, record_group)`)
lies in its conversation's role. A conversation that a relation reaches (`comparison-request`,
`later-human-after-agent`) or a provider parent reaches is joined to the reading conversation, so no
relation crosses roles; the joins are counted (the development source has none). A unit's canonical
key is the JSON array of its sorted `session_id`s.

**The hash-seeded rule, kept.** SHA-256 of the declared seed, a NUL separator and the unit's
canonical key, read as a big-endian integer: residue zero modulo five is validation, the other four
residues are choosing. It is now applied to conversations outside the reserve, where it was applied to
messages.

**The reserve** [agent-inferred]. `RESERVE_SIZE` conversations, the lowest by SHA-256 of
`RESERVE_SEED`, a NUL separator and the unit's canonical key, are held out of every role. The reserve
is named by `RESERVE_SHA256`, the SHA-256 of its sorted membership (the sorted SHA-256s of its units'
canonical keys, as compact JSON), committed before any run reads a role, and the script refuses a
recomputed reserve that differs. Its size is chosen from the finite-population spread of a mean over
units: a charged comparison read on `k` of `N` exchangeable conversations has the variance of its
mean proportional to `(N − k)/(k (N − 1))`, and validation, drawn at one in five from the `N − k`
others, to `4/(N − k − 1)`. The declared margin is validation's own spread: the reserve must read
no less sharply than the role whose reading it confirms once. The least such `k` at `N = 87` is 15
(`72·71 = 5112 ≤ 4·1290 = 5160`; at 14, `73·72 = 5256 > 4·1204 = 4816`), leaving 72 conversations to
the rule above (validation expects `72/5 = 14 + 2/5`, choosing `57 + 3/5`). The argument holds for
a comparison read per conversation (each aeon one unit); conversations differ widely in length, so a
comparison summed over bytes is read beside it, never in its place. The reserve's
conversations were read by the earlier splits below (F0's choosing role held all 87): it is unread
from its naming on, so it guards the choices made after it, not those made before.

**Every script refuses to emit or read the reserve** unless the explicit flag `--read-reserve` is
passed, which is logged (`reserve_flag`): the scripts that read the source skip the reserve's records,
their manifests carry `reserve_excluded` (the reserve's hash), and every reader of a private cut or
receipt refuses one without it (`require_reserve_excluded`; `exterior.rs` for the Rust harnesses).

**The spent splits** (`SPENT`): F4, F1, F2, F2V2, F5 (its diagnostic), U2 and F0 split messages, not
conversations, and every one of them is a reshuffle of read material: their validation messages lay in
conversations their choosing roles also held, and together they read every development conversation,
the reserve's included. Each is regenerated only to reproduce its receipt, with `--read-reserve`
(`python3 development_families.py F0 --read-reserve`), under its family-unit rule
(`family_assignment`).
"""

import datetime
import hashlib
import json
import os
import re
import sys

from standing_cut import OUT_DIR, SOURCE, private_directory, private_write

# The spent family-unit splits: reshuffles of read material (module header).
SEED = "holonics-f4-development-families-2026-09-27-v1"
SPENT = {
    "F4": SEED,
    "F1": "holonics-f1-development-families-2026-09-27-v1",
    "F2": "holonics-f2-development-families-2026-09-27-v1",
    "F5": "holonics-f5-development-families-2026-09-27-v1",
    "U2": "holonics-u2-development-families-2026-09-28-v1",
    "F2V2": "holonics-f2-development-families-2026-09-28-v2",
    "F0": "holonics-f0-development-families-2026-09-28-v1",
}
# The conversation-unit splits (module header), each with its own seed.
SEEDS = {"U6": "holonics-u6-development-conversations-2026-09-29-v1"}
RESERVE_SEED = "holonics-development-reserve-2026-09-29-v1"
RESERVE_SIZE = 15
RESERVE_SHA256 = "09d7ae5b86d1b34cd1f57a100fb0ec412f59902f6ec3b90924a7c80b136f8a24"
READ_RESERVE = "--read-reserve"
PARTITION = re.compile(rb'"partition"\s*:\s*"(development|evaluation|deferred)"')
RELATIONS = ("comparison-request", "later-human-after-agent")
JOINING = RELATIONS + ("provider-parent",)
AUTHOR = {"human": "human", "agent-visible": "agent"}
HARNESS_FLAG = "control-surface"


def reserve_flag(arguments, script):
    """Strip the explicit `--read-reserve` flag from the arguments. When it is passed, the read is
    logged on stdout and appended to the owner-only log `.local/cuts/reserve-reads.log`; returns the
    remaining arguments and whether the reserve may be read."""
    if READ_RESERVE not in arguments:
        return list(arguments), False
    stamp = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")
    line = f"{stamp} {script} {READ_RESERVE}: this run may read the development reserve\n"
    print("READING THE RESERVE: " + line.strip())
    private_directory()
    descriptor = os.open(os.path.join(OUT_DIR, "reserve-reads.log"),
                         os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o600)
    with os.fdopen(descriptor, "ab") as handle:
        os.fchmod(handle.fileno(), 0o600)
        handle.write(line.encode("utf-8"))
    return [argument for argument in arguments if argument != READ_RESERVE], True


def require_reserve_excluded(manifest, what, read_reserve):
    """Refuse a private artifact that may hold the reserve's material: its manifest must name the
    reserve as excluded (`reserve_excluded` equal to `RESERVE_SHA256`). An artifact written before
    the reserve was named holds it (every earlier split read every conversation)."""
    if read_reserve:
        return
    if RESERVE_SHA256 is None or manifest.get("reserve_excluded") != RESERVE_SHA256:
        sys.exit(f"refused: {what} does not name the development reserve as excluded, so it may "
                 f"hold the reserve's material; pass {READ_RESERVE} (logged) to read it")


def canonical_family(family):
    assert set(family) == {"provider", "record_group"}, "one declared family key"
    return json.dumps(family, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def family_assignment(family, seed=SEED):
    """The spent family-unit rule (module header): a message's role under a spent seed."""
    key = canonical_family(family)
    digest = hashlib.sha256(seed.encode() + b"\0" + key).digest()
    return ("validation" if int.from_bytes(digest, "big") % 5 == 0 else "choosing",
            hashlib.sha256(key).hexdigest())


def canonical_unit(sessions):
    """A unit's canonical key: the JSON array of its sorted `session_id`s."""
    return json.dumps(sorted(sessions), separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def seeded(seed, key):
    return int.from_bytes(hashlib.sha256(seed.encode() + b"\0" + key).digest(), "big")


def membership_sha256(hashes):
    return hashlib.sha256(json.dumps(sorted(hashes), separators=(",", ":")).encode()).hexdigest()


def development_records():
    """The development records in the declared order, decoded; the other partitions counted by
    their label alone."""
    partitions = {"development": 0, "evaluation": 0, "deferred": 0}
    records = []
    source_hash = hashlib.sha256()
    with open(SOURCE, "rb") as handle:
        for line in handle:
            source_hash.update(line)
            # The partition label precedes the views in this pinned source schema.
            prefix = line[:line.find(b'"views"')] if b'"views"' in line[:1024] else line[:1024]
            match = PARTITION.search(prefix)
            if match is None:
                continue
            partition = match.group(1).decode("ascii")
            partitions[partition] += 1
            if partition != "development":
                continue
            record = json.loads(line)
            assert record["kind"] == "occurrence-family" and record["partition"] == partition
            records.append(record)
    return records, partitions, source_hash.hexdigest()


def units_of(records):
    """Join each conversation with every conversation its relations and provider parents reach
    (union by the links). Returns each session's unit root, the unit's sessions, and the joins
    counted by link kind."""
    session_of_event = {}
    for record in records:
        for view in record["views"]:
            session_of_event[view["event"]] = record["views"][0]["session_id"]
    parent = {}

    def root(session):
        parent.setdefault(session, session)
        while parent[session] != session:
            parent[session] = parent[parent[session]]
            session = parent[session]
        return session

    joins = {kind: 0 for kind in JOINING}
    for record in records:
        session = record["views"][0]["session_id"]
        root(session)
        for link in record["views"][0]["links"]:
            target = session_of_event.get(link["target_event"])
            if link["kind"] in JOINING and target is not None and target != session:
                joins[link["kind"]] += 1
                a, b = root(session), root(target)
                if a != b:
                    parent[max(a, b)] = min(a, b)
    members = {}
    for session in parent:
        members.setdefault(root(session), set()).add(session)
    return {session: root(session) for session in parent}, members, joins


def conversation_split(item, records):
    """The conversation-unit split (module header): each unit's role and key hash, and the
    reserve's membership hash."""
    seed = SEEDS[item]
    unit_of, members, joins = units_of(records)
    keys = {unit: canonical_unit(sessions) for unit, sessions in members.items()}
    ranked = sorted(keys, key=lambda unit: seeded(RESERVE_SEED, keys[unit]))
    reserve = set(ranked[:RESERVE_SIZE])
    role = {}
    for unit, key in keys.items():
        if unit in reserve:
            role[unit] = "reserve"
        else:
            role[unit] = "validation" if seeded(seed, key) % 5 == 0 else "choosing"
    hashes = {unit: hashlib.sha256(key).hexdigest() for unit, key in keys.items()}
    reserve_sha = membership_sha256(hashes[unit] for unit in reserve)
    return unit_of, members, joins, role, hashes, reserve_sha


def load_conversation_split(item="U6"):
    """The pinned conversation split's roles by unit hash, from the owner-only membership file,
    checked against the committed reserve."""
    with open(os.path.join(OUT_DIR, f"development-conversations-{item.lower()}.json"), "rb") as handle:
        split = json.load(handle)
    assert split["seed"] == SEEDS[item] and split["reserve_seed"] == RESERVE_SEED
    assert RESERVE_SHA256 is not None and split["reserve_sha256"] == RESERVE_SHA256, \
        "the membership names the committed reserve"
    roles = {entry["unit_sha256"]: entry["role"] for entry in split["members"]}
    assert membership_sha256(unit for unit, role in roles.items() if role == "reserve") == RESERVE_SHA256
    return split, roles


def session_roles(records, item="U6"):
    """Each development session's role under the pinned conversation split."""
    split, roles = load_conversation_split(item)
    unit_of, members, _, _, _, _ = conversation_split(item, records)
    by_session = {}
    for unit, sessions in members.items():
        role = roles[hashlib.sha256(canonical_unit(sessions)).hexdigest()]
        for session in sessions:
            by_session[session] = role
    assert set(by_session) == set(unit_of)
    return split, by_session


def reserve_sessions(records):
    """The reserve's sessions, recomputed and checked against the committed reserve (for the scripts
    that read the source and must skip it)."""
    assert RESERVE_SHA256 is not None, "the reserve is named before any script reads the source"
    _, members, _, role, hashes, reserve_sha = conversation_split("U6", records)
    assert reserve_sha == RESERVE_SHA256, "the committed reserve"
    return {session for unit in members if role[unit] == "reserve" for session in members[unit]}


def run_law_counts(records, role_of_session):
    """[agent-inferred] The present-only retention law read on the incidence (the admitted egg's
    header): an aeon holds its latest run of parts on each target port, released when a part on the
    other target port of that aeon begins a new run. Per role and relation kind: the relations whose
    target the law holds when the reading part opens (and its rank within the run from the latest,
    by dyadic class), those it has released, and those reaching another conversation. Counts only;
    the reserve is not read."""
    port_of_event = {}
    family_of_event = {}
    for index, record in enumerate(records):
        view = record["views"][0]
        if role_of_session[view["session_id"]] == "reserve":
            continue
        port = "harness" if HARNESS_FLAG in view["flags"] else AUTHOR[view["author_class"]]
        cells = any((part.get("text") or "") != "" for part in view["visible_parts"])
        for captured in record["views"]:
            port_of_event[captured["event"]] = port if cells else None
            family_of_event[captured["event"]] = index
    counts = {}
    runs = {}  # (session, port) -> the families of the aeon's latest run on the port, in order
    last = {}  # session -> the port of its latest part on a target port
    reader = {"comparison-request": ("agent", "human"), "later-human-after-agent": ("human", "agent")}
    for index, record in enumerate(records):
        view = record["views"][0]
        session = view["session_id"]
        role = role_of_session[session]
        if role == "reserve":
            continue
        port = port_of_event[view["event"]]
        if port not in ("human", "agent"):
            continue
        for link in view["links"]:
            kind = link["kind"]
            if kind not in reader or reader[kind][0] != port:
                continue
            table = counts.setdefault(role, {}).setdefault(kind, {})
            target = family_of_event.get(link["target_event"])
            if target is None or target >= index or port_of_event.get(link["target_event"]) != reader[kind][1]:
                state = "not a declared earlier part"
            elif records[target]["views"][0]["session_id"] != session:
                state = "another conversation"
            else:
                run = runs.get((session, reader[kind][1]), [])
                if target in run:
                    # The pointer's rank from the run's latest part, and its class ⌊log₂(r + 1)⌋.
                    rank = len(run) - 1 - run.index(target)
                    state = "held, rank class " + str((rank + 1).bit_length() - 1)
                else:
                    state = "released"
            table[state] = table.get(state, 0) + 1
        if last.get(session) != port:
            runs[(session, port)] = []
        runs.setdefault((session, port), []).append(index)
        last[session] = port
    return counts


def main():
    arguments, read_reserve = reserve_flag(sys.argv[1:], "development_families.py")
    if len(arguments) > 1 or (arguments and arguments[0] not in SEEDS and arguments[0] not in SPENT):
        sys.exit(__doc__)
    item = arguments[0] if arguments else "U6"
    if item in SPENT:
        spent(item, read_reserve)
        return
    with open(os.path.join(OUT_DIR, "curated-source.json"), "rb") as handle:
        source_manifest = json.load(handle)
    records, partitions, source_sha = development_records()
    assert partitions == source_manifest["families"], "same pinned source population"
    assert source_sha == source_manifest["source_sha256"], "same pinned source"
    unit_of, members, joins, role, hashes, reserve_sha = conversation_split(item, records)
    if RESERVE_SHA256 is not None:
        assert reserve_sha == RESERVE_SHA256, "the committed reserve"
    assert len(members) >= RESERVE_SIZE + 5, "room for the reserve and both roles"

    # Count-only checks: every message of a conversation in one role; no relation across roles.
    role_of_session = {session: role[unit_of[session]] for session in unit_of}
    conversations = {"choosing": 0, "validation": 0, "reserve": 0}
    units = {"choosing": 0, "validation": 0, "reserve": 0}
    for unit, sessions in members.items():
        units[role[unit]] += 1
        conversations[role[unit]] += len(sessions)
    messages = {"choosing": 0, "validation": 0, "reserve": 0}
    roles_of_conversation = {}
    role_of_event = {}
    for record in records:
        session = record["views"][0]["session_id"]
        assigned = role_of_session[session]
        messages[assigned] += 1
        roles_of_conversation.setdefault(session, set()).add(assigned)
        for view in record["views"]:
            role_of_event[view["event"]] = assigned
    split_conversations = sum(1 for held in roles_of_conversation.values() if len(held) > 1)
    crossing = {kind: {"within a role": 0, "across roles": 0, "outside the development partition": 0}
                for kind in JOINING}
    for record in records:
        reading = role_of_session[record["views"][0]["session_id"]]
        for link in record["views"][0]["links"]:
            if link["kind"] not in crossing:
                continue
            target = role_of_event.get(link["target_event"])
            state = ("outside the development partition" if target is None
                     else "within a role" if target == reading else "across roles")
            crossing[link["kind"]][state] += 1
    assert split_conversations == 0, "no conversation has messages in two roles"
    assert all(table["across roles"] == 0 for table in crossing.values()), "no relation crosses roles"

    members_out = sorted(({"unit_sha256": hashes[unit], "role": role[unit]} for unit in members),
                         key=lambda entry: entry["unit_sha256"])
    membership_bytes = json.dumps(members_out, separators=(",", ":"), sort_keys=True).encode()
    receipt = {
        "schema": f"holonics.development-conversations-{item.lower()}.v1",
        "source_sha256": source_sha,
        "unit": "the conversation (session_id of a family's first view), joined through its relations and provider parents",
        "canonical": "UTF-8 JSON array of the unit's sorted session_ids, compact separators",
        "seed": SEEDS[item],
        "hash": "SHA-256(seed UTF-8 || NUL || canonical); big-endian integer mod 5, residue 0 validation",
        "reserve_seed": RESERVE_SEED,
        "reserve_size": RESERVE_SIZE,
        "reserve_rule": "the RESERVE_SIZE units lowest by SHA-256(reserve_seed || NUL || canonical), before the split",
        "reserve_sha256": reserve_sha,
        "reserve_excluded": reserve_sha,
        "counts": {"units": units, "conversations": conversations, "messages": messages},
        "joins": joins,
        "membership_sha256": hashlib.sha256(membership_bytes).hexdigest(),
        "members": members_out,
    }
    private_directory()
    private_write(f"development-conversations-{item.lower()}.json", json.dumps(receipt, indent=2).encode())
    print(json.dumps({
        "schema": receipt["schema"],
        "source_sha256": source_sha,
        "seed": receipt["seed"],
        "reserve_seed": RESERVE_SEED,
        "reserve_size": RESERVE_SIZE,
        "reserve_sha256": reserve_sha,
        "reserve_committed": RESERVE_SHA256 is not None,
        "counts": receipt["counts"],
        "joins across conversations": joins,
        "conversations with messages in two roles": split_conversations,
        "relations and provider parents by role": crossing,
        "the present-only retention law on the incidence (choosing and validation; the reserve unread)":
            run_law_counts(records, role_of_session),
        "membership_sha256": receipt["membership_sha256"],
    }, indent=1))


def spent(item, read_reserve):
    """Reproduce a spent family-unit split's receipt (module header); it reads every conversation,
    the reserve's included, so it runs only with `--read-reserve`."""
    if not read_reserve:
        sys.exit(f"refused: the spent split {item} is a reshuffle of read material over every "
                 f"development conversation, the reserve's included; pass {READ_RESERVE} (logged) "
                 "to reproduce its receipt")
    seed = SPENT[item]
    name = "development-families-f4.json" if item == "F4" else f"development-families-{item.lower()}.json"
    with open(os.path.join(OUT_DIR, "curated-source.json"), "rb") as handle:
        source_manifest = json.load(handle)
    records, partitions, source_sha = development_records()
    assert partitions == source_manifest["families"], "same pinned source population"
    counts = {"choosing": 0, "validation": 0}
    members = []
    seen = set()
    for record in records:
        role, family_hash = family_assignment(record["family"], seed)
        assert family_hash not in seen, "each development family occurs once"
        seen.add(family_hash)
        counts[role] += 1
        members.append({"family_sha256": family_hash, "role": role})
    members.sort(key=lambda entry: entry["family_sha256"])
    membership_bytes = json.dumps(members, separators=(",", ":"), sort_keys=True).encode()
    receipt = {
        "schema": f"holonics.development-families-{item.lower()}.v1",
        "source_sha256": source_sha,
        "seed": seed,
        "canonical": "UTF-8 JSON of family {provider,record_group}, sorted keys, compact separators",
        "hash": "SHA-256(seed UTF-8 || NUL || canonical); big-endian integer mod 5",
        "validation_residue": 0,
        "spent": "a family-unit split: a reshuffle of read material holding the reserve",
        "counts": counts,
        "membership_sha256": hashlib.sha256(membership_bytes).hexdigest(),
        "members": members,
    }
    private_directory()
    private_write(name, json.dumps(receipt, indent=2).encode())
    print(json.dumps({k: receipt[k] for k in ("schema", "source_sha256", "seed", "counts", "membership_sha256")}, indent=2))


if __name__ == "__main__":
    main()

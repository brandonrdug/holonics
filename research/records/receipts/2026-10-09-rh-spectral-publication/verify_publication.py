#!/usr/bin/env python3
"""Check the publication bytes and joins; this does not run Lean."""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def seal(path):
    data = path.read_bytes()
    return {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def proof_bytes(text):
    text = re.sub(r"(?s)/-!.*?-/", "", text)
    return re.sub(r"^public import[^\n]*\n", "", text, flags=re.M).encode()


def declarations(text):
    return re.findall(r"(?ms)^(def|theorem|lemma)\s+(\w+)\b(.*?)(?=:=)", text)


def main():
    files = json.loads((HERE / "FILE_SEALS.json").read_text())
    for relative, expected in files["files"].items():
        assert seal(ROOT / relative) == expected, relative
    joined = json.loads((HERE / "SOURCE_PUBLICATION_JOIN.json").read_text())
    axioms = ["propext", "Classical.choice", "Quot.sound"]
    count = 0
    owned = {}
    for item in joined["items"]:
        module = item["module"]
        accepted = ROOT / item["accepted_source_snapshot"]
        public = ROOT / item["public_owner"]
        assert seal(accepted) == item["accepted_source_pin"]
        assert seal(public) == item["public_source_pin"]
        before, after = accepted.read_text(), public.read_text()
        assert proof_bytes(before) == proof_bytes(after)
        assert declarations(before) == declarations(after)
        expected = before
        for change in item["publication_changes"]["import_path_rewrites"]:
            assert expected.count(change["from"] + "\n") == 1
            expected = expected.replace(change["from"] + "\n", change["to"] + "\n")
        assert re.sub(r"(?s)/-!.*?-/", "", expected) == re.sub(r"(?s)/-!.*?-/", "", after)
        for imported in re.findall(r"^public import (HolonicsResearch\S+)$", after, re.M):
            assert (ROOT / "lean" / (imported.replace(".", "/") + ".lean")).is_file(), imported
        kernel = json.loads((HERE / module / "KERNEL_ACCEPTANCE.json").read_text())
        assert kernel["kernel_accepted"] and kernel["compiler_exit"] == 0
        assert kernel["standard_axioms_only"] and kernel["selector_count_matches"]
        assert kernel["axioms"] == item["axiom_queries"]
        printed = re.findall(
            r"'([^']+)' depends on axioms: \[([^\]]*)\]",
            (HERE / module / "compiler.stdout").read_text(),
        )
        observed = {name: [x.strip() for x in names.split(",")] for name, names in printed}
        assert observed == kernel["axioms"]
        assert all(value == axioms for value in observed.values())
        assert re.findall(r"^#print axioms.*$", before, re.M) == re.findall(
            r"^#print axioms.*$", after, re.M
        )
        count += len(observed)
        owned["Zeta/" + module] = {name for _, name, _ in declarations(after)}
        assert len(item["accepted_target_object_parts"]) == 6
        assert item["public_module_graph_kernel_rechecked"] is False
        rejected = HERE / module / "rejected-predecessor" / "KERNEL_VALIDATION.json"
        if rejected.exists():
            failed = json.loads(rejected.read_text())
            assert failed["compiler_exit"] == 1 and not failed["kernel_accepted"]
    assert count == 23
    # The canonical module graph, checked by the sole native queue after this preparation: each
    # canonical owner's kernel result, its projected printouts, and the packet manifest's seals.
    canonical = HERE / "canonical-import-native-v1"
    projection = json.loads((canonical / "PROJECTION.json").read_text())
    manifest = json.loads((canonical / "FILE_HASHES.json").read_text())["files"]

    def manifest_sha(relative):
        entry = manifest[relative]
        return entry["sha256"] if isinstance(entry, dict) else entry

    for name in ("HANDOFF.md", "VALIDATION.json"):
        assert seal(canonical / name)["sha256"] == manifest_sha(name), name
    rechecked = 0
    for item in joined["items"]:
        module = item["module"]
        admitted = canonical / "admission" / module
        kernel = json.loads((admitted / "KERNEL_VALIDATION.json").read_text())
        assert kernel["kernel_accepted"] and kernel["compiler_exit"] == 0
        assert kernel["standard_axioms_only"] and kernel["selector_count_matches"]
        assert kernel["axioms"] == item["axiom_queries"]
        printed = re.findall(
            r"'([^']+)' depends on axioms: \[([^\]]*)\]",
            (admitted / "compiler.stdout").read_text(),
        )
        observed = {name: [x.strip() for x in names.split(",")] for name, names in printed}
        assert observed == kernel["axioms"]
        assert all(value == axioms for value in observed.values())
        stdout = f"admission/{module}/compiler.stdout"
        assert seal(admitted / "compiler.stdout") == projection["files"][stdout]["projected"]
        assert projection["files"][stdout]["original"]["sha256"] == manifest_sha(stdout)
        for name in ("KERNEL_VALIDATION.json", "compiler.stderr"):
            assert seal(admitted / name)["sha256"] == manifest_sha(f"admission/{module}/{name}")
        rechecked += len(observed)
    assert rechecked == 23
    assert joined["target_queries_accepted"] == 11
    assert joined["prerequisite_queries_accepted"] == 12
    atlas = json.loads((HERE / "ATLAS_JOIN.json").read_text())
    text = (ROOT / "docs/atlas/targets.tsv").read_text().splitlines()
    ids = [line.split("\t")[0] for line in text]
    atlas_ids = {
        line.split("\t")[0]
        for shard in (ROOT / "docs/atlas").glob("*.tsv")
        for line in shard.read_text().splitlines()
    }
    for row in atlas["rows"]:
        assert len(row) == 8 and text.count("\t".join(row)) == 1
        assert ids.count(row[0]) == 1
        for owner in row[5].split("; "):
            _, path, name = owner.split(":")
            assert name in owned[path], owner
        for relation in row[7].split(", "):
            if relation:
                assert relation.split(":", 1)[1] in atlas_ids, relation
    record = ROOT / atlas["record"]
    assert record.is_file()
    assert record.name in (ROOT / atlas["index"]).read_text()
    for path in HERE.rglob("*"):
        if path.is_file() and path.suffix != ".py":
            content = path.read_text()
            assert "/home/" not in content and "/Users/" not in content, path
            assert "mailbox_request" not in content and "\"body\":" not in content, path
    print("PASS: 6 source mappings, 23 native standard-axiom printouts, 7 atlas rows, index route, file seals.")
    print("PUBLIC MODULE GRAPH: rechecked by the sole native queue (canonical-import-native-v1, 23 printouts);")
    print("no Lean compiler or whole-library check was run here.")


if __name__ == "__main__":
    main()

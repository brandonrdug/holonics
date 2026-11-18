#!/usr/bin/env -S python3 -I
"""Controls for link_check.py: on a tree of known files, every link and owner that resolves is passed, each one that does not is named with
its reason, and what the forms do not let it read (a fenced block, a code span, a footnote, a link with a scheme, a pinned owner) is left."""
import io
import os
import sys
import tempfile
from contextlib import redirect_stdout

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import link_check  # noqa: E402

FILES = {
    "README.md": """# A tree

[the guide](docs/a.md), [a section](docs/a.md#the-engines-law-3), [a repeat](docs/a.md#notes-1), [a pin](docs/a.md#pinned),
[a crate](crates/eng), [a crate](crates/eng/), [rooted](/docs/a.md), [spaced](docs/a%20b.md), ![a plate](docs/plate.png "its title"),
[here](#a-tree), [elsewhere](https://example.org/x.md), <a href="docs/sub/b.md">b</a>, [a source line](crates/eng/src/lib.rs#L1).
A span is not read: `[x](gone/in/a/span.md)`. A footnote is not a link.[^1]

```text
[fenced](gone/in/a/fence.md)
```

[gone](docs/gone.md) and [no anchor](docs/a.md#no-such-heading) and [not here](#not-here) and [out](../out.md).

[ref]: docs/ref-gone.md
[^1]: Somebody, a note with no link target.
""",
    "docs/a.md": """# A guide

## The engine's law (§3)

## Notes

<a id="pinned"></a>
## Notes

## A `code` name and [a link](sub/b.md)
""",
    "docs/a b.md": "# Spaced\n",
    "docs/plate.png": "",
    "docs/sub/b.md": "# B\n\n[up](../a.md#notes) and [the code heading](../a.md#a-code-name-and-a-link) and [lost](../a.md#notes-2).\n",
    "research/notes.md": "[not a file the check reads](gone.md)\n",
    "research/records/2026-01-01_A_RECORD.md": "# A record\n",
    "research/papers/source/p.typ": "",
    "lean/Holonics/HNN/Ring.lean": "theorem Ring.turn_closes : True := trivial\n",
    "tools/ruler.py": "def read():\n    pass\n",
    "crates/eng/Cargo.toml": '[package]\nname = "my-engine"\n',
    "crates/eng/kernels/k.cu": 'extern "C" __global__ void field_open(int a) {}\n',
    "crates/eng/src/lib.rs": "pub mod field;\n",
    "crates/eng/src/field.rs": "pub mod moment;\npub struct Constitution {\n    pub width: u32,\n}\nimpl Constitution {\n    pub fn tick(&self) {}\n}\npub fn lock() {}\n",
    "crates/eng/src/field/moment.rs": "pub struct Pace;\npub fn moments() {}\n",
}

GOOD = ("R:my_engine::field::Constitution::tick; R:my_engine::field::Constitution::width; R:my_engine::field::moment::moments; "
        "R:my_engine::field::lock (a note after a space); R:my_engine::field; T:tools/ruler.py:read; T:tools/ruler.py; "
        "K:crates/eng/kernels/k.cu::field_open; L:HNN/Ring:Ring.turn_closes; L:HNN/Ring; D:docs/a.md#notes-1; D:a.md; "
        "N:2026-01-01_A_RECORD.md; P:p.typ; H:crates/old/src/x.rs:Item@abc1234; H:crates/old/src/y.rs")
BAD = [
    ("R:other::field::lock", "no crate of that name"),
    ("R:my_engine::field::Constitution::tock", "`tock` is not declared in the crate"),
    ("R:my_engine::field::moment::Pace::tick", "`Pace::tick` is in no file that defines or implements `Pace`"),
    ("R:crates/eng/src/gone.rs:Item", "no tracked path"),
    ("T:tools/ruler.py:absent", "`absent` is not declared in the file"),
    ("K:crates/eng/kernels/k.cu::field_shut", "`field_shut` is not declared in the file"),
    ("H:crates/eng/src/field.rs:lock", "a path of the tree written as history"),
    ("L:HNN/Ring:turn_opens", "`turn_opens` is not in the file"),
    ("L:HNN/Gone:x", "no tracked Lean file"),
    ("D:docs/a.md#no-such-heading", "no such anchor"),
    ("N:2026-01-01_A_RECORD", "no tracked record"),
    ("P:q.typ", "no tracked paper source"),
    ("crates/eng/src/field.rs", "an owner of no kind the atlas declares"),
]


def row(name, owners):
    return "\t".join([name, "holon", "x = x", "reads", "", owners, "definition", ""])


def main():
    with tempfile.TemporaryDirectory() as tmp:
        root = os.path.join(tmp, "tree")
        files = dict(FILES)
        files["docs/atlas/objects.tsv"] = row("good.row", GOOD) + "\n" + "\n".join(row(f"bad.row-{i}", o) for i, (o, _) in enumerate(BAD)) + "\n"
        for rel, text in files.items():
            os.makedirs(os.path.dirname(os.path.join(root, rel)), exist_ok=True)
            open(os.path.join(root, rel), "w", encoding="utf-8").write(text)
        passed = 0

        assert link_check.slug("The engine's law (§3)") == "the-engines-law-3" and link_check.slug("A `code` name and [a link](sub/b.md)") == "a-code-name-and-a-link"
        assert link_check.slug("The elementary objects — the only design vocabulary") == "the-elementary-objects--the-only-design-vocabulary"
        passed += 1
        assert link_check.anchors(FILES["docs/a.md"]) == {"a-guide", "the-engines-law-3", "notes", "notes-1", "pinned", "a-code-name-and-a-link"}
        passed += 1
        got = [t for _, t in link_check.targets(FILES["README.md"])]
        assert "gone/in/a/span.md" not in got and "gone/in/a/fence.md" not in got and "Somebody," not in got and "docs/ref-gone.md" in got, got
        assert "docs/plate.png" in got and "docs/sub/b.md" in got and len(got) == 18, got
        passed += 1

        buf = io.StringIO()
        with redirect_stdout(buf):
            read, counted, broken = link_check.links(root)
        assert read == ["README.md", "docs/a b.md", "docs/a.md", "docs/sub/b.md"], read
        assert broken == [
            ("README.md", 12, "docs/gone.md", "no tracked path"),
            ("README.md", 12, "docs/a.md#no-such-heading", "no such anchor"),
            ("README.md", 12, "#not-here", "no such anchor"),
            ("README.md", 12, "../out.md", "outside the tree"),
            ("README.md", 14, "docs/ref-gone.md", "no tracked path"),
            ("docs/sub/b.md", 3, "../a.md#notes-2", "no such anchor"),
        ], broken
        passed += 1
        out = buf.getvalue()
        assert "BROKEN README.md:12 docs/gone.md (no tracked path)" in out and "LINK_CHECK files=4 links=21 external=1 broken=6" in out, out
        assert counted == 21
        passed += 1

        buf = io.StringIO()
        with redirect_stdout(buf):
            rows, kinds, broken = link_check.atlas(root)
        assert rows == 1 + len(BAD) and [(b[3], b[4]) for b in broken] == BAD, [(b[3], b[4]) for b in broken]
        passed += 1
        assert kinds["R"] == [9, 9, 4] and kinds["H"] == [3, 2, 1] and kinds["L"] == [4, 4, 2] and kinds["?"] == [1, 1, 1], kinds
        passed += 1
        out = buf.getvalue()
        assert "BROKEN_OWNER docs/atlas/objects.tsv:2 bad.row-0 R:other::field::lock (no crate of that name)" in out, out
        assert f"ATLAS_OWNERS shards=1 rows={1 + len(BAD)} read={15 + len(BAD)} broken={len(BAD)}" in out, out
        passed += 1
        assert link_check.split_owner("crates/a/src/b.rs:Item::sub@abc") == ("crates/a/src/b.rs", ["Item", "sub"], "abc")
        assert link_check.split_owner("my_engine::field::lock") == ("my_engine::field::lock", None, "")
        assert link_check.split_owner("crates/k/x.cuh::kernel (a note)") == ("crates/k/x.cuh", ["kernel"], "")
        passed += 1
    print(f"link_check controls: {passed} passed")


if __name__ == "__main__":
    main()

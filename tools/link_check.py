#!/usr/bin/env -S python3 -I
"""link_check.py: the guides' relative links and the atlas's owners, read against the tree (C7 and C9 of the consolidation, #603;
docs/plans/THE_CONSOLIDATION.md). A host instrument: it reads tracked files and prints what does not resolve. No law, no state.

  link_check.py links [ROOT]
      Every relative Markdown link in README.md, CLAUDE.md, AGENTS.md, CONSTRUCTION_STATE.md, crates/README.md, docs/**/*.md and
      research/records/README.md resolves to a tracked path of ROOT (a directory resolves when a tracked path stands under it), and a
      `#fragment` on a Markdown target is a heading's GitHub slug or an explicit `id` or `name` in that file. Links with a scheme
      (https:, mailto:) are counted and not followed. Fenced blocks and code spans are not read. Prints one `BROKEN` line a broken
      link and exits 1 on any.
  link_check.py atlas [ROOT]
      Every owner in field 6 of docs/atlas/*.tsv that names the tree resolves in it:
        R:, T:, K:  a Rust item, test or kernel, as `<crate>::<module>::<item>` (the crate is a package of crates/*/Cargo.toml, the
                    modules are followed to their file, and each remaining name is declared in the crate; a `Type::member` is declared
                    in a file that defines or implements the type) or as `<path>[:<item>]` (the path is tracked and the item is
                    declared in it). A name the form does not let it read (free text after a space) is left alone.
        H:          an owner in history. With `@<commit>` it is pinned and not read. Without one it names the pre-reset tree, so a
                    path that stands in the tree today is a live owner written as history.
        L: D: N: P: a Lean file under lean/Holonics or lean/HolonicsResearch with its declaration's last name declared in it
                    outside its comments (a declaration's head, a constructor or a structure field), a guide with its anchor, a record
                    under research/records, a paper source under research/papers/source.
      Prints one `BROKEN_OWNER` line an owner that does not resolve, the counts by kind, and exits 1 on any.
      Field 7 is read with them: a grade the atlas's README declares, or, on a row with an owner in history, the dated status the row
      was written with. Any other grade prints one `BROKEN_GRADE` line. Reason (November 18): 20 rows whose Lean owners stand in the
      library carried a validation queue's status of October in the field, and nothing read it. A `formal-checked` row has at
      least one L: owner, so the kernel's acceptance it claims is one a target of the package rebuilds (November 19: six rows rested
      on a retired module or on a receipt's frozen source, and an L: owner's name passed where it stood only in a comment).

ROOT defaults to the directory above this file. The tracked paths are git's index, or every file under ROOT where it is no repository.
"""
import os
import posixpath
import re
import subprocess
import sys
from urllib.parse import unquote

LINK_FILES = ("README.md", "CLAUDE.md", "AGENTS.md", "CONSTRUCTION_STATE.md", "crates/README.md", "research/records/README.md")
LINK_TREES = ("docs/",)
LEAN_ROOTS = ("lean/Holonics/", "lean/HolonicsResearch/")
SOURCE = (".rs", ".py", ".cu", ".cuh", ".sh", ".lean", ".toml", ".md", ".h", ".tsv", ".json")
GRADES = ("definition", "proved-derived", "proved-standard", "formal-checked", "counterexample", "interpretation", "open", "measured")


def tracked_paths(root):
    try:
        out = subprocess.run(["git", "-C", root, "ls-files", "-z"], capture_output=True, check=True).stdout
        paths = {p for p in out.decode("utf-8", "surrogateescape").split("\0") if p}
        if paths:
            return paths
    except (OSError, subprocess.CalledProcessError):
        pass
    paths = set()
    for base, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d != ".git"]
        for name in files:
            paths.add(os.path.relpath(os.path.join(base, name), root).replace(os.sep, "/"))
    return paths


def directories(tracked):
    dirs = set()
    for p in tracked:
        while "/" in p:
            p = p.rsplit("/", 1)[0]
            if p in dirs:
                break
            dirs.add(p)
    return dirs


class Tree:
    """A root with its tracked paths, their directories and each file's text read once."""

    def __init__(self, root):
        self.root = root
        self.tracked = tracked_paths(root)
        self.dirs = directories(self.tracked)
        self.texts = {}

    def text(self, rel):
        if rel not in self.texts:
            try:
                self.texts[rel] = open(os.path.join(self.root, rel), encoding="utf-8", errors="replace").read()
            except OSError:
                self.texts[rel] = None
        return self.texts[rel]

    def stands(self, rel):
        rel = rel.rstrip("/")
        return rel in self.tracked or rel in self.dirs or rel in ("", ".")


FENCE = re.compile(r"^ {0,3}(`{3,}|~{3,})")
CODE_SPAN = re.compile(r"(`+)(?!`)(.+?)(?<!`)\1(?!`)", re.S)


def unfenced(text):
    """The text's lines, each line of a fenced block (its fences included) made empty."""
    out, fence = [], None
    for line in text.split("\n"):
        m = FENCE.match(line)
        if fence:
            if m and m.group(1)[0] == fence[0] and len(m.group(1)) >= len(fence) and not line.strip().strip(fence[0]):
                fence = None
            out.append("")
        elif m:
            fence = m.group(1)
            out.append("")
        else:
            out.append(line)
    return out


def prose(text):
    """The text with fenced blocks and code spans blanked, every line break kept in its place."""
    return "\n\n".join(CODE_SPAN.sub(lambda m: re.sub(r"[^\n]", " ", m.group(0)), block) for block in "\n".join(unfenced(text)).split("\n\n"))


def slug(heading):
    """GitHub's anchor for a heading's text: markup dropped, lowered, letters, digits, `-` and `_` kept, each space a hyphen."""
    heading = re.sub(r"!?\[((?:[^\[\]]|\[[^\[\]]*\])*)\]\([^)]*\)", r"\1", heading)
    heading = re.sub(r"<[^>]+>", "", heading).replace("`", "")
    return "".join("-" if c == " " else c for c in heading.strip().lower() if c.isalnum() or c in " -_")


HEADING = re.compile(r"^ {0,3}#{1,6}[ \t]+(.*?)(?:[ \t]+#+)?[ \t]*$")
EXPLICIT = re.compile(r"""<[a-zA-Z][^>]*?\s(?:id|name)\s*=\s*["']([^"']+)["']""")


def anchors(text):
    """The fragments a Markdown file answers to: its headings' slugs (a repeat takes `-1`, `-2`, ...) and its explicit ids."""
    found, seen = set(EXPLICIT.findall(text)), {}
    for line in unfenced(text):
        h = HEADING.match(line)
        if h:
            s = slug(h.group(1))
            n = seen.get(s, 0)
            seen[s] = n + 1
            found.add(s if n == 0 else f"{s}-{n}")
    return found


INLINE = re.compile(r"\]\(\s*(<[^>\n]*>|[^\s()]*(?:\([^\s()]*\)[^\s()]*)*)(?:\s+(?:\"[^\"]*\"|'[^']*'))?\s*\)")
REFERENCE = re.compile(r"^ {0,3}\[(?!\^)[^\]\n]+\]:[ \t]*(\S+)", re.M)  # a footnote `[^n]:` is no link
HREF = re.compile(r"""<a\s[^>]*?href\s*=\s*["']([^"']+)["']""")
SCHEME = re.compile(r"^[a-zA-Z][a-zA-Z0-9+.-]*:")


def targets(text):
    """Each link target of a Markdown text with its line, in order."""
    body = prose(text)
    found = []
    for pattern in (INLINE, REFERENCE, HREF):
        for m in pattern.finditer(body):
            t = m.group(1).strip()
            if t.startswith("<") and t.endswith(">"):
                t = t[1:-1]
            if t:
                found.append((m.start(1), body.count("\n", 0, m.start(1)) + 1, t))
    return [(line, t) for _, line, t in sorted(found)]


def resolve(tree, source, target):
    """None where the target resolves, else the reason it does not."""
    path, _, fragment = target.partition("#")
    path = unquote(path.split("?", 1)[0])
    if path.startswith("/"):
        rel = posixpath.normpath(path.lstrip("/"))
    elif path:
        rel = posixpath.normpath(posixpath.join(posixpath.dirname(source), path))
    else:
        rel = source
    if rel.startswith("../") or rel == "..":
        return "outside the tree"
    if not tree.stands(rel):
        return "no tracked path"
    if fragment and rel.endswith(".md") and rel in tree.tracked:
        text = tree.text(rel)
        if text is None:
            return "unreadable"
        if unquote(fragment) not in anchors(text):
            return "no such anchor"
    return None


def link_files(tree):
    return sorted(p for p in tree.tracked if p in LINK_FILES or (p.endswith(".md") and p.startswith(LINK_TREES)))


def links(root):
    tree = Tree(root)
    files = link_files(tree)
    counted, external, broken = 0, 0, []
    for source in files:
        text = tree.text(source)
        if text is None:
            broken.append((source, 0, "", "unreadable"))
            continue
        for line, target in targets(text):
            if SCHEME.match(target):
                external += 1
                continue
            counted += 1
            reason = resolve(tree, source, target)
            if reason:
                broken.append((source, line, target, reason))
    for source, line, target, reason in broken:
        print(f"BROKEN {source}:{line} {target} ({reason})")
    print(f"LINK_CHECK files={len(files)} links={counted} external={external} broken={len(broken)}")
    return files, counted, broken


IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")


def declared(name, text):
    n = re.escape(name)
    return re.search(rf"\b(?:fn|struct|enum|trait|type|const|static|mod|union|def|class)\s+{n}\b|macro_rules!\s*{n}\b|__global__[^(;{{]*\b{n}\s*(?:##|\()", text) is not None


def owns(name, text):
    n = re.escape(name)
    return re.search(rf"\b(?:struct|enum|trait|union|type)\s+{n}\b|\bimpl\b[^{{;]*\b{n}\b", text) is not None


def member(name, text):
    n = re.escape(name)
    return re.search(rf"\b(?:fn|const|type)\s+{n}\b|^\s*(?:pub(?:\([^)]*\))?\s+)?{n}\s*[:,({{]|^\s*{n}\s*$", text, re.M) is not None


LEAN_KEYWORD = r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)"


def lean_code(text):
    """A Lean file's text with its comments blanked: `/- ... -/` (nested, docstrings included) and `-- ...` to the line's end."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth, i = depth + 1, i + 2
            out.append("  ")
        elif depth and text.startswith("-/", i):
            depth, i = depth - 1, i + 2
            out.append("  ")
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def lean_declared(name, text):
    """None where `name` is declared in the Lean text outside its comments (a declaration's head, possibly namespaced, a
    constructor `| name`, a structure field `name :` or a constructor `name ::`), else the reason."""
    n = re.escape(name)
    code = lean_code(text)
    head = rf"\b{LEAN_KEYWORD}\s+(?:[\w'.]*\.)?{n}(?![\w'])"
    member = rf"^\s*\|\s*{n}(?![\w'])|^\s*{n}\s*(?:\{{[^}}]*\}}\s*)?(?:\([^)]*\)\s*)*:(?!=)|^\s*{n}\s*::"
    if re.search(head, code) or re.search(member, code, re.M):
        return None
    word = rf"(?<![\w']){n}(?![\w'])"
    if re.search(word, code):
        return f"`{name}` is used in the file but declared in none of its lines"
    if re.search(word, text):
        return f"`{name}` is only in a comment of the file"
    return f"`{name}` is not in the file"


def packages(tree):
    """Each crate's name as Rust writes it, with its directory."""
    found = {}
    for p in tree.tracked:
        if re.fullmatch(r"crates/[^/]+/Cargo\.toml", p):
            m = re.search(r'^\s*name\s*=\s*"([^"]+)"', tree.text(p) or "", re.M)
            if m:
                found[m.group(1).replace("-", "_")] = p.rsplit("/", 1)[0]
    return found


def crate_item(tree, crate_dir, segments):
    """None where `<crate>::segments` resolves, else the reason."""
    src = crate_dir + "/src"
    sources = sorted(p for p in tree.tracked if p.startswith(src + "/") and p.endswith(".rs"))
    if not sources:
        return "a crate with no source"
    here, rest = src, list(segments)
    while rest:
        for candidate in (f"{here}/{rest[0]}.rs", f"{here}/{rest[0]}/mod.rs"):
            if candidate in tree.tracked:
                break
        else:
            break
        here, rest = f"{here}/{rest[0]}", rest[1:]
    if any(not IDENT.match(s) for s in rest):
        return None
    texts = [tree.text(p) or "" for p in sources]
    for i, name in enumerate(rest):
        if not any(declared(name, t) for t in texts):
            if i and any(owns(rest[i - 1], t) and member(name, t) for t in texts):
                continue
            return f"`{name}` is not declared in the crate"
        if i and rest[i - 1][:1].isupper() and not any(owns(rest[i - 1], t) and member(name, t) for t in texts):
            return f"`{rest[i - 1]}::{name}` is in no file that defines or implements `{rest[i - 1]}`"
    return None


def split_owner(body):
    """An owner's body as (path or crate path, item names, pin): `a/b.rs:Item`, `a::b::Item`, `a/b.rs@commit`."""
    word = body.split()[0] if body.split() else ""
    word, _, pin = word.partition("@")
    m = re.match(r"^(\S*?(?:%s))(?:::?(.*))?$" % "|".join(re.escape(e) for e in SOURCE), word)
    if m:
        return m.group(1), [s for s in re.split(r"::|:", m.group(2) or "") if s], pin
    return word, None, pin


def owner_reason(tree, crates, kind, body):
    """None where an owner resolves or is not read, else the reason. The second value says whether it was read."""
    path, items, pin = split_owner(body)
    if kind == "H":
        if pin or not path:
            return None, False
        return ("a path of the tree written as history" if path in tree.tracked else None), True
    if kind in ("R", "T", "K"):
        if items is not None:
            if path not in tree.tracked:
                return "no tracked path", True
            text = tree.text(path) or ""
            for name in items:
                if IDENT.match(name) and not declared(name, text) and not member(name, text):
                    return f"`{name}` is not declared in the file", True
            return None, True
        segments = [s for s in path.split("::") if s]
        if not segments or segments[0] not in crates:
            return "no crate of that name", True
        return crate_item(tree, crates[segments[0]], segments[1:]), True
    if kind == "L":
        file, _, decl = body.split()[0].partition(":") if body.split() else ("", "", "")
        for lean_root in LEAN_ROOTS:
            for candidate in (lean_root + file, lean_root + file + ".lean"):
                if candidate in tree.tracked:
                    name = decl.split(".")[-1]
                    if name:
                        return lean_declared(name, tree.text(candidate) or ""), True
                    return None, True
        return "no tracked Lean file", True
    if kind == "D":
        file, _, fragment = (body.split()[0] if body.split() else "").partition("#")
        for candidate in (file, "docs/" + file):
            if candidate in tree.tracked:
                if fragment and candidate.endswith(".md") and unquote(fragment) not in anchors(tree.text(candidate) or ""):
                    return "no such anchor", True
                return None, True
        return "no tracked guide", True
    if kind == "N":
        name = body.split()[0].split("#")[0] if body.split() else ""
        return (None if "research/records/" + name in tree.tracked or name in tree.tracked else "no tracked record"), True
    if kind == "P":
        name = body.split()[0].split("#")[0] if body.split() else ""
        return (None if tree.stands("research/papers/source/" + name) or tree.stands(name) else "no tracked paper source"), True
    return "an owner of no kind the atlas declares", True


def atlas(root):
    tree = Tree(root)
    crates = packages(tree)
    shards = sorted(p for p in tree.tracked if re.fullmatch(r"docs/atlas/[^/]+\.tsv", p))
    rows, read, broken, kinds = 0, 0, [], {}
    for shard in shards:
        for n, line in enumerate((tree.text(shard) or "").split("\n"), 1):
            fields = line.split("\t")
            if len(fields) < 6:
                continue
            rows += 1
            for owner in fields[5].split(";"):
                owner = owner.strip()
                if not owner:
                    continue
                m = re.match(r"^([A-Z]):(.*)$", owner, re.S)
                kind, body = (m.group(1), m.group(2).strip()) if m else ("?", owner)
                reason, was_read = owner_reason(tree, crates, kind, body)
                tally = kinds.setdefault(kind, [0, 0, 0])
                tally[0] += 1
                tally[1] += int(was_read)
                read += int(was_read)
                if reason:
                    tally[2] += 1
                    broken.append((shard, n, fields[0], owner, reason))
    for shard, n, row, owner, reason in broken:
        print(f"BROKEN_OWNER {shard}:{n} {row} {owner} ({reason})")
    for kind in sorted(kinds):
        owners, was_read, bad = kinds[kind]
        print(f"ATLAS_KIND {kind} owners={owners} read={was_read} broken={bad}")
    print(f"ATLAS_OWNERS shards={len(shards)} rows={rows} read={read} broken={len(broken)}")
    return rows, kinds, broken


def grades(root):
    """Field 7 of every atlas row: (declared, dated, broken). A row is dated when it has an owner in history (`H:`)."""
    tree = Tree(root)
    declared, dated, broken = 0, 0, []
    for shard in sorted(p for p in tree.tracked if re.fullmatch(r"docs/atlas/[^/]+\.tsv", p)):
        for n, line in enumerate((tree.text(shard) or "").split("\n"), 1):
            fields = line.split("\t")
            if len(fields) < 7:
                continue
            grade = fields[6].strip()
            if grade == "formal-checked" and not any(owner.strip().startswith("L:") for owner in fields[5].split(";")):
                broken.append((shard, n, fields[0], grade))
            elif grade in GRADES:
                declared += 1
            elif any(owner.strip().startswith("H:") for owner in fields[5].split(";")):
                dated += 1
            else:
                broken.append((shard, n, fields[0], grade))
    for shard, n, row, grade in broken:
        why = ("a kernel's acceptance with no Lean owner the package builds" if grade == "formal-checked"
               else "no grade the atlas declares, and no owner in history to date it")
        print(f"BROKEN_GRADE {shard}:{n} {row} `{grade}` ({why})")
    print(f"ATLAS_GRADES declared={declared} dated={dated} broken={len(broken)}")
    return declared, dated, broken


def main(argv):
    root = argv[2] if len(argv) == 3 else os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    if len(argv) in (2, 3) and argv[1] == "links":
        sys.exit(1 if links(root)[2] else 0)
    elif len(argv) in (2, 3) and argv[1] == "atlas":
        owners, marks = atlas(root)[2], grades(root)[2]
        sys.exit(1 if owners or marks else 0)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv)

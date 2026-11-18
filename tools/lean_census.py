#!/usr/bin/env -S python3 -I
"""Read the Lean package's files against the targets that build them (lean/lakefile.toml), from the text alone.

A library with no glob builds its root and what the root imports, link after link; a library with the glob `X.*` builds `X` and every
module under it. A `.lean` file that stands in the import closure of no rooted library and under no glob is built by no target: no
check reads it, a change to what it imports can break it unseen, and the atlas may still name it `formal-checked`. A module under a
glob that its library's root does not reach is built alone and never beside the rest, so the root's build does not tell whether its
names meet another module's.

Reason (November 18): twelve modules under `lean/Holonics/` stood outside the foundation's closure (`HNN/SingleHoleResponse` with its
six parts and `HNN/SourceReceiverReturn`; four parts of `Physics/ObserverBoundaryCurrent`), with six atlas rows resting on them, five
graded `formal-checked`; and ten research modules were built by the glob and imported by no root. Nothing printed either.

  lean_census.py [ROOT]     print UNBUILT and UNROOTED lines and the count line; exit 1 where any stands
"""
import os
import re
import subprocess
import sys

IMPORT = re.compile(r"^(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([^\s]+)")


def libraries(lakefile_text):
    """The package's libraries as (name, globs): each `[[lean_lib]]` table's `name` and its `globs` list (empty where none)."""
    out = []
    for table in re.split(r"^\[\[", lakefile_text, flags=re.M)[1:]:
        if not table.startswith("lean_lib]]"):
            continue
        name = re.search(r'^name\s*=\s*"([^"]+)"', table, flags=re.M)
        globs = re.search(r"^globs\s*=\s*\[([^\]]*)\]", table, flags=re.M)
        if name:
            out.append((name.group(1), re.findall(r'"([^"]+)"', globs.group(1)) if globs else []))
    return out


def imports(text):
    """The modules a file imports: its `import` lines, read from the head of the file past comments and blank lines, up to the
    first command (a module's own statement `/-!` is one)."""
    out, depth = [], 0
    for raw in text.split("\n"):
        line = raw.strip()
        if depth:
            depth += line.count("/-") - line.count("-/")
            continue
        if line.startswith("/-!") or line.startswith("/--"):
            break  # a module's statement or a declaration's is a command, and no import follows a command
        if line.startswith("/-"):
            depth = line.count("/-") - line.count("-/")
            continue
        if not line or line.startswith("--") or line == "module":
            continue
        found = IMPORT.match(line)
        if not found:
            break
        out.append(found.group(1))
    return out


def under(glob, module):
    """Whether `module` is built by `glob`: `X.*` is `X` and every module under it, `X.+` every module under it, `X` itself."""
    if glob.endswith(".*"):
        return module == glob[:-2] or module.startswith(glob[:-1])
    if glob.endswith(".+"):
        return module.startswith(glob[:-1])
    return module == glob


def census(modules, libs):
    """(unbuilt, unrooted) for `modules` (name -> imported names) and `libs` (name, globs): the modules no library builds, and the
    modules a glob builds that their library's root does not reach."""
    def closure(roots):
        seen, stack = set(), list(roots)
        while stack:
            name = stack.pop()
            if name in seen or name not in modules:
                continue
            seen.add(name)
            stack.extend(modules[name])
        return seen

    built, unrooted = set(), []
    for name, globs in libs:
        reached = closure([name])
        if not globs:
            built |= reached
            continue
        by_glob = {m for m in modules if any(under(g, m) for g in globs)}
        built |= closure(by_glob)
        unrooted += sorted(by_glob - reached)
    return sorted(set(modules) - built), unrooted


def tracked(root):
    """The package's tracked `.lean` files as module name -> path, read from git (the tree a clone holds, never a build's output)."""
    listed = subprocess.run(["git", "-C", root, "ls-files", "-z", "--", "lean"], capture_output=True, check=True).stdout.decode("utf-8")
    out = {}
    for path in listed.split("\0"):
        if path.endswith(".lean") and path.startswith("lean/"):
            out[path[len("lean/"):-len(".lean")].replace("/", ".")] = path
    return out


def read(root):
    """The census of the tree at `root`, printed: (files, unbuilt, unrooted)."""
    with open(os.path.join(root, "lean", "lakefile.toml"), encoding="utf-8") as handle:
        libs = libraries(handle.read())
    paths = tracked(root)
    modules = {}
    for name, path in paths.items():
        with open(os.path.join(root, path), encoding="utf-8") as handle:
            modules[name] = imports(handle.read())
    unbuilt, unrooted = census(modules, libs)
    for name in unbuilt:
        print(f"UNBUILT {paths[name]} (no library's root reaches it and no glob holds it)")
    for name in unrooted:
        print(f"UNROOTED {paths[name]} (a glob builds it alone; its library's root does not import it)")
    print(f"LEAN_CENSUS libraries={len(libs)} files={len(modules)} unbuilt={len(unbuilt)} unrooted={len(unrooted)}")
    return len(modules), unbuilt, unrooted


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    _, unbuilt, unrooted = read(root)
    sys.exit(1 if unbuilt or unrooted else 0)


if __name__ == "__main__":
    main()

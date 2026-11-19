#!/usr/bin/env -S python3 -I
"""Controls of lean_census.py (host text only; no Lean is run and no build is read).

The census's null is held to planted omissions: a package whose every file a target builds beside its root prints nothing, and the
same package with one import taken out prints that file, and what only it reached, and no other. The lakefile and the import lines
are read as Lake reads them: a library with no glob builds its root's closure, `X.*` builds `X` and every module under it, `X.+`
every module under it, and an import line may carry `public`, `private`, `meta` and `all`.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lean_census  # noqa: E402

LAKEFILE = '''name = "holonics"
defaultTargets = ["Holonics"]

# The foundation.
[[lean_lib]]
name = "Holonics"

[[lean_lib]]
name = "HolonicsResearch"
globs = ["HolonicsResearch.*"]

[[require]]
name = "mathlib"
rev = "v4.33.0"
'''

# A whole package: every foundation file stands in the root's closure, and the research root imports every research file.
WHOLE = {
    "Holonics": ["Holonics.Framework"],
    "Holonics.Framework": ["Holonics.HNN", "Mathlib.Tactic.Ring"],
    "Holonics.HNN": ["Holonics.HNN.Word", "Holonics.HNN.Return"],
    "Holonics.HNN.Word": ["Mathlib.Data.Fintype.Basic"],
    "Holonics.HNN.Return": ["Holonics.HNN.Return.Part"],
    "Holonics.HNN.Return.Part": ["Holonics.HNN.Word"],
    "HolonicsResearch": ["Holonics.Framework", "HolonicsResearch.Zeta.Tail", "HolonicsResearch.Zeta.Source"],
    "HolonicsResearch.Zeta.Tail": ["HolonicsResearch.Zeta.Source"],
    "HolonicsResearch.Zeta.Source": ["Holonics.HNN.Word"],
}

HEAD = '''/-
Copyright: none. A block comment before the imports, with an `import Not.This` inside it.
-/
module

-- a line comment
public import Holonics.HNN.Word
import all Holonics.HNN.Return
meta import Mathlib.Tactic.Ring
private import   Holonics.Framework

/-! A module's own statement ends the head. -/
import Holonics.Never.Read
'''


def without(modules, owner, gone):
    """`modules` with `owner`'s import of `gone` taken out."""
    out = {name: list(found) for name, found in modules.items()}
    out[owner].remove(gone)
    return out


def main():
    failures = []

    def check(name, got, want):
        if got != want:
            failures.append(f"{name}: got {got!r}, want {want!r}")

    libs = lean_census.libraries(LAKEFILE)
    check("libraries", libs, [("Holonics", []), ("HolonicsResearch", ["HolonicsResearch.*"])])
    check("imports", lean_census.imports(HEAD),
          ["Holonics.HNN.Word", "Holonics.HNN.Return", "Mathlib.Tactic.Ring", "Holonics.Framework"])
    check("imports of a file with none", lean_census.imports("namespace Holonics\nimport Late\n"), [])
    for glob, module, want in [
        ("X.*", "X", True), ("X.*", "X.A.B", True), ("X.*", "XY", False), ("X.*", "XY.A", False),
        ("X.+", "X", False), ("X.+", "X.A", True), ("X", "X", True), ("X", "X.A", False),
    ]:
        check(f"under({glob}, {module})", lean_census.under(glob, module), want)

    check("a whole package", lean_census.census(WHOLE, libs), ([], []))
    # The foundation's umbrella loses one import: that file and the part only it reached are built by no target. The research
    # library does not rescue them, because nothing under its glob imports them.
    check("an umbrella's import taken out",
          lean_census.census(without(WHOLE, "Holonics.HNN", "Holonics.HNN.Return"), libs),
          (["Holonics.HNN.Return", "Holonics.HNN.Return.Part"], []))
    # A foundation file that only a research file imports is built, as that file's dependency, and is not in the default target.
    reached = without(WHOLE, "Holonics.HNN", "Holonics.HNN.Return")
    reached["HolonicsResearch.Zeta.Source"] = ["Holonics.HNN.Return"]
    check("a foundation file a research file imports", lean_census.census(reached, libs), ([], []))
    # The research root loses one import: the glob still builds the file, alone.
    check("the research root's import taken out",
          lean_census.census(without(WHOLE, "HolonicsResearch", "HolonicsResearch.Zeta.Tail"), libs),
          ([], ["HolonicsResearch.Zeta.Tail"]))
    # A file the root reaches through another file is rooted: taking the root's direct import of it changes nothing.
    check("a file reached through another",
          lean_census.census(without(WHOLE, "HolonicsResearch", "HolonicsResearch.Zeta.Source"), libs), ([], []))
    # A file outside every library's name space is built by no target, whatever it imports.
    stray = dict(WHOLE, **{"Scratch.Note": ["Holonics.Framework"]})
    check("a file under no library", lean_census.census(stray, libs), (["Scratch.Note"], []))
    # With no glob the research library is its root's closure, and a file the root does not reach is unbuilt, never unrooted.
    bare = [("Holonics", []), ("HolonicsResearch", [])]
    check("a library with no glob",
          lean_census.census(without(WHOLE, "HolonicsResearch", "HolonicsResearch.Zeta.Tail"), bare),
          (["HolonicsResearch.Zeta.Tail"], []))

    for line in failures:
        print(f"FAIL {line}")
    print(f"LEAN_CENSUS_CONTROLS failures={len(failures)}")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()

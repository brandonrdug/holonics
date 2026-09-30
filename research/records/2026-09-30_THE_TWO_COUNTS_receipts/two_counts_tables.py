"""The two counts' tables, read from the pinned runs' logs (research/records/
2026-09-30_THE_TWO_COUNTS_PINNED_BEFORE_ITS_RUNS.md §5). An exterior reader of printed receipts:
every value is an exact cell `[a/g, b/g)` or an exact ratio as the harness printed it, and every
comparison here is exact rational arithmetic (`fractions.Fraction`); nothing is rounded.

    python3 two_counts_tables.py <receipts directory>
"""

import re
import sys
from fractions import Fraction
from pathlib import Path

CELL = re.compile(r"\[(-?\d+)/(\d+), (-?\d+)/(\d+)[)\]]")


def cells(text):
    """Every exact cell in a text, as (lower, upper) Fractions."""
    return [(Fraction(int(a), int(b)), Fraction(int(c), int(d))) for a, b, c, d in CELL.findall(text)]


def after(text, key):
    """The first cell after `key`."""
    i = text.index(key)
    return cells(text[i:])[0]


def moves(log):
    """Per move: its D1 lines, D2 lines and summary line."""
    out = {}
    for line in log.splitlines():
        m = re.match(r"\s+D([12]) move (\d+)", line)
        if m:
            out.setdefault(int(m.group(2)), {"D1": [], "D2": [], "move": ""})[f"D{m.group(1)}"].append(line)
            continue
        m = re.match(r"\s+move (\d+): (adopted|refused)", line)
        if m:
            out.setdefault(int(m.group(1)), {"D1": [], "D2": [], "move": ""})["move"] = line
    return out


def show(x):
    return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else f"{x.numerator}"


def d1_table(terrain, log):
    rows = []
    for index, m in sorted(moves(log).items()):
        d1 = " ".join(m["D1"])
        row = {"move": index}
        row["F"] = after(d1, "F(θ) ∈")
        row["grain"] = after(d1, "its grain")
        row["binds"] = re.search(r"binding: ([^\n]*?)(    D1|$)", d1).group(1).strip() if "binding:" in d1 else "-"
        lad = re.search(r"the ladder: (\d+) trials, (\d+) halvings before (\w+); (.*?); trials refused by the entry bound (\d+)", d1)
        row["trials"], row["halvings"], row["outcome"], row["ladder"], row["entry"] = (
            (int(lad.group(1)), int(lad.group(2)), lad.group(3), lad.group(4), int(lad.group(5))) if lad else (0, 0, "none", "", 0)
        )
        car = re.search(r"the carried move at η (\S+) \((\w+)\): ‖ΔE‖_∞ (\S+), Σ ΔE² ([^,]+), entries whose lattice coordinate moved (\d+), residuals released (\d+).*?ρ (\S+) → (\S+) \(Δρ (\S+)\).*?passive bound ([^;]+);", d1)
        if car:
            row["eta"], row["norm"], row["squares"], row["stepped"] = car.group(1), car.group(3), car.group(4), car.group(5)
            row["rho"], row["drho"], row["passive"] = car.group(8), car.group(9), car.group(10)
        if "predicted descent" in d1:
            row["certificate"] = after(d1, "the certificate −Σ sup Df ∈")
            row["leading"] = after(d1, "the leading branches −Σ sign⟨ĝ, Δz⟩ ∈")
            row["measured"] = after(d1, "measured C(θ) − C(θ+δ) ∈")
            row["kind"] = re.search(r"the prediction (zero \(not positive\)|below the grain|above the grain)", d1).group(1)
            row["eighth"] = re.search(r"at least 1/8 of the certificate: (\w+)", d1).group(1)
            row["agree"] = re.search(r"the measured's: (\w+)", d1).group(1)
        traj = re.search(r"trajectory changed in (\d+) of (\d+) requests; at the open section, wrong→right (\d+), right→wrong (\d+), wrong→another wrong (\d+), right kept (\d+), wrong kept (\d+); the successor's batch: released (\d+), whole (\d+), stations right (\d+)", d1)
        if traj:
            row["traj"] = tuple(int(g) for g in traj.groups())
        info = re.search(r"the ideal listener on this batch: (.*)$", d1)
        row["info"] = info.group(1) if info else ""
        mv = m["move"]
        batch = re.search(r"batch released (\d+), whole (\d+), stations right (\d+)", mv)
        row["batch"] = tuple(int(g) for g in batch.groups()) if batch else None
        ms = re.search(r"; (\d+) ms$", mv)
        row["ms"] = int(ms.group(1)) if ms else None
        # D2 at the open section: the wrong decisions' count and Σ|γ| enclosure, the right ones'.
        wrong, right, magnitude = 0, 0, (Fraction(0), Fraction(0))
        confident = 0
        derivative = [0, 0, 0, 0, 0]
        for line in m["D2"]:
            if "the open section" not in line:
                continue
            n = int(re.search(r"stations (\d+);", line).group(1))
            if ", right," in line:
                right += n
                continue
            wrong += n
            if "confident" in line:
                confident += n
            lo, hi = after(line, "Σ|γ| ∈")
            magnitude = (magnitude[0] + lo, magnitude[1] + hi)
            d = [int(x) for x in re.search(r"straddling\) \[(\d+), (\d+), (\d+), (\d+), (\d+)\], Σ", line).groups()]
            derivative = [a + b for a, b in zip(derivative, d)]
        row["open"] = (right, wrong, confident, magnitude, derivative)
        rows.append(row)
    return rows


def main(directory):
    base = Path(directory)
    if len(sys.argv) > 2 and sys.argv[2] == "shapes":
        shapes(base)
        return
    for terrain in ("order2", "alternation", "line"):
        path = base / f"train_{terrain}_log.txt"
        if not path.exists():
            continue
        rows = d1_table(terrain, path.read_text())
        print(f"== {terrain}: D1")
        print("| Move | F(θ) ·/4096 | trials, halvings | start bound by | η | ‖ΔE‖∞ | Δρ | passive | predicted (certificate) ·/4096 | predicted (leading) ·/4096 | measured ·/4096 | measured over predicted ·/256 | measured ≥ 1/8 predicted | signs | prediction | trajectory changed | open section w→r, r→w, w→w′ | batch released, whole, right | ideal listener | ms |")
        print("|" + "---|" * 20)
        for r in rows:
            f = lambda c: f"[{show(c[0] * 4096)}, {show(c[1] * 4096)})"
            tr = r.get("traj")
            ratio = "-"
            if "certificate" in r and r["certificate"][0] > 0:
                lo = r["measured"][0] / r["certificate"][1]
                hi = r["measured"][1] / r["certificate"][0]
                ratio = f"[{(lo * 256).numerator // (lo * 256).denominator}, {-((-hi * 256).numerator // (hi * 256).denominator)})"
            print(
                f"| {r['move']} | {f(r['F'])} | {r['trials']}, {r['halvings']} | {r['binds']} | {r.get('eta', '-')} | {r.get('norm', '-')} | {r.get('drho', '-')} | {r.get('passive', '-')} | "
                f"{f(r['certificate']) if 'certificate' in r else '-'} | {f(r['leading']) if 'leading' in r else '-'} | {f(r['measured']) if 'measured' in r else '-'} | {ratio} | "
                f"{r.get('eighth', '-')} | {r.get('agree', '-')} | {r.get('kind', '-')} | {tr[0] if tr else '-'} of {tr[1] if tr else '-'} | "
                f"{(str(tr[2]) + ', ' + str(tr[3]) + ', ' + str(tr[4])) if tr else '-'} | {r['batch']} | {r['info']} | {r['ms']} |"
            )
        print(f"== {terrain}: D2 at the open section")
        print("| Move | right | wrong (confident) | Σ|γ| of the wrong ·/256 | mean |γ| of the wrong ·/256 | wrong terms' derivative (zero, below grain, descending, rising, straddling) |")
        print("|---|---|---|---|---|---|")
        for r in rows:
            right, wrong, confident, mag, der = r["open"]
            mean = (mag[0] / wrong, mag[1] / wrong) if wrong else None
            print(
                f"| {r['move']} | {right} | {wrong} ({confident}) | [{show(mag[0] * 256)}, {show(mag[1] * 256)}) | "
                f"{'-' if mean is None else '[' + show(mean[0] * 256) + ', ' + show(mean[1] * 256) + ')'} | {der} |"
            )
    shapes(base)


def rule(terrain, section, j):
    """The terrain's law read among a released section's own cells at station `j ≥ 2` (the
    termination, class 4, follows no rule)."""
    a, b = section[j - 2], section[j - 1]
    if a == 4 or b == 4:
        return None
    if terrain == "order2":
        return (a + 1) % 4
    if terrain == "alternation":
        return a
    return (2 * b - a) % 4


def shapes(base):
    """What every read constitution released on the validation set: adjacent stations equal (a lag-1
    copy), stations following the terrain's law among the section's own cells, sections following it
    throughout, and the released classes' counts (the last the termination)."""
    for terrain in ("order2", "alternation", "line"):
        path = base / f"validation_{terrain}_sections.txt"
        if not path.exists():
            continue
        print(f"== {terrain}: the released sections' shapes")
        print("| Constitution | Adjacent stations equal | Stations following the law among the section's own | Sections following it throughout | Classes 0 / 1 / 2 / 3 / termination |")
        print("|---|---|---|---|---|")
        for block in re.split(r"^== ", path.read_text(), flags=re.M)[1:]:
            label = block.split(" on ")[0]
            adjacent = pairs = follows = read = throughout = 0
            classes = [0] * 5
            for line in block.splitlines()[1:]:
                if "|" not in line or "released" not in line.split("|")[2]:
                    continue
                section = [int(x) for x in re.findall(r"\d+", line.split("|")[2])]
                for c in section:
                    classes[c] += 1
                pairs += len(section) - 1
                adjacent += sum(section[j] == section[j - 1] for j in range(1, len(section)))
                every = True
                for j in range(2, len(section)):
                    read += 1
                    ok = rule(terrain, section, j) == section[j]
                    follows += ok
                    every &= ok
                throughout += every
            print(f"| {label} | {adjacent} of {pairs} | {follows} of {read} | {throughout} | {' / '.join(map(str, classes))} |")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else ".")

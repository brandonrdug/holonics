#!/usr/bin/env python3
"""Replay published receiving certificates; no search, solver, network or native generator.

SPDX-License-Identifier: MIT OR Apache-2.0
"""
from collections import Counter
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import comb, isqrt
from pathlib import Path
import argparse
import hashlib
import json
import shlex
import sys

import exact as m

ROOT = Path(__file__).resolve().parent
need = m.need


def load(name):
    return json.loads((ROOT / name).read_text())


def intersect(xs, ys):
    result = []
    for a, b in xs:
        for c, d in ys:
            lo = c if a is None else a if c is None else max(a, c)
            hi = d if b is None else b if d is None else min(b, d)
            if lo is None or hi is None or lo <= hi:
                result.append((lo, hi))
    return result


def superlevel(a, b, c):
    """Outward necessary superlevel of an exact quadratic, including double roots."""
    if a == 0:
        if b == 0:
            return [(None, None)] if c >= 0 else []
        x = -c / b
        return [(x, None)] if b > 0 else [(None, x)]
    disc = b*b - 4*a*c
    if disc < 0:
        return [(None, None)] if a > 0 else []
    if disc == 0:
        x = -b / (2*a)
        return [(None, None)] if a > 0 else [(x, x)]
    grain = 2**72
    lo = F(isqrt(disc.numerator*grain*grain // disc.denominator), grain)
    hi = lo if lo*lo == disc else lo + F(1, grain)
    need(lo*lo <= disc <= hi*hi, "discriminant branch")
    roots = []
    for sign in [-1, 1]:
        values = [(-b + sign*v)/(2*a) for v in [lo, hi]]
        roots.append((min(values), max(values)))
    roots.sort()
    r, s = roots
    return [(None, r[1]), (s[0], None)] if a > 0 else [(r[0], s[1])]


def necessary_phase(coefficients, chart):
    c, b, a = coefficients
    if chart == "R":
        c, a = a, c
    return (intersect(superlevel(a[1], b[1], c[1]), [(F(0), F(1))])
            + intersect(superlevel(a[1], b[0], c[1]), [(-F(1), F(0))]))


def bernstein(tensor, active, charts, bounds):
    """Degree-two rational Bernstein enclosure; inactive dimensions stay inactive."""
    tensor = {tuple(2-n if charts[k] == "R" else n
                    for n, k in zip(powers, active)): v
              for powers, v in tensor.items()}
    for j, k in enumerate(active):
        lo, hi = bounds[k]
        width = hi-lo
        result = {}
        for rest in {p[:j]+p[j+1:] for p in tensor}:
            key = lambda n: rest[:j]+(n,)+rest[j:]
            power = [m.val(0), m.val(0), m.val(0)]
            for n in range(3):
                for degree in range(n+1):
                    weight = comb(n, degree)*lo**(n-degree)*width**degree
                    power[degree] = m.add(power[degree], m.scale(tensor[key(n)], weight))
            for index in range(3):
                v = m.val(0)
                for degree in range(index+1):
                    v = m.add(v, m.scale(power[degree], F(comb(index, degree), comb(2, degree))))
                result[key(index)] = v
        tensor = result
    return min(v[0] for v in tensor.values()), max(v[1] for v in tensor.values())


def cut(neighbours, fixed, moved):
    need(moved in neighbours[fixed], "source bond exists")
    found, front = {moved}, [moved]
    for a in front:
        for b in neighbours[a]:
            if {a, b} == {fixed, moved}:
                continue
            if b not in found:
                found.add(b)
                front.append(b)
    need(fixed not in found, "free complete graph cut")
    return found


class Family:
    """Five-component proper affine moment chart: (mass, x, y, z, |x|²)."""

    def __init__(self, points, neighbours, ends, fixed_i=None):
        self.points = dict(points)
        self.ends = ends
        self.supports = [cut(neighbours, a, b) for a, b in ends]
        self.origins = [points[a] for a, b in ends]
        self.axes = [m.minus(points[b], points[a]) for a, b in ends]
        self.qs = [m.norm(d) for d in self.axes]
        need(all(q[0] > 0 for q in self.qs), "finite and reciprocal denominators positive")
        if fixed_i:
            a, b, t = fixed_i
            o, d = points[a], m.minus(points[b], points[a])
            for i in cut(neighbours, a, b):
                if i not in [a, b]:
                    self.points[i] = m.rotate(points[i], o, d, "F", m.val(t))
        self.rot = []
        for d in self.axes:
            z = m.val(0)
            skew = ((z, m.scale(d[2], -1), d[1]), (d[2], z, m.scale(d[0], -1)),
                    (m.scale(d[1], -1), d[0], z))
            coeff = []
            for n in range(3):
                rows = []
                for i in range(3):
                    row = []
                    for j in range(3):
                        if n == 0:
                            v = m.val(int(i == j))
                        elif n == 1:
                            v = m.scale(skew[i][j], 2)
                        elif i == j:
                            v = m.sub(m.square(d[i]), m.add(m.square(d[(i+1)%3]), m.square(d[(i+2)%3])))
                        else:
                            v = m.scale(m.mul(d[i], d[j]), 2)
                        row.append(v)
                    rows.append(row)
                coeff.append(rows)
            self.rot.append(coeff)

    def relative(self, a, b):
        left = {k for k, s in enumerate(self.supports) if a in s and a not in self.ends[k]}
        right = {k for k, s in enumerate(self.supports) if b in s and b not in self.ends[k]}
        for k in reversed(range(len(self.ends))):
            x, y = k in left, k in right
            if x == y or (x and b in self.ends[k]) or (y and a in self.ends[k]):
                left.discard(k)
                right.discard(k)
            else:
                break
        if right and not left:
            a, b, left, right = b, a, right, left
        need(not right, "one moving operand after actual common-motion cancellation")
        return a, b, tuple(sorted(left))

    def move_coefficient(self, v, k, n):
        if n == 0:
            return v
        o, den = self.origins[k], m.val(0) if n == 1 else self.qs[k]
        z = [m.sub(v[i+1], m.mul(o[i], v[0])) for i in range(3)]
        rz = [m.dot(row, z) for row in self.rot[k][n]]
        centered = m.add(m.sub(v[4], m.scale(m.dot(o, v[1:4]), 2)), m.mul(m.norm(o), v[0]))
        norm = m.add(m.add(m.mul(den, centered), m.scale(m.dot(o, rz), 2)),
                     m.mul(m.mul(den, m.norm(o)), v[0]))
        return (m.mul(den, v[0]),
                *[m.add(rz[i], m.mul(m.mul(den, o[i]), v[0])) for i in range(3)], norm)

    @lru_cache(maxsize=512)
    def moments(self, a, active):
        x = self.points[a]
        tensor = {(): (m.val(1), *x, m.norm(x))}
        for k in active:
            tensor = {p+(n,): self.move_coefficient(v, k, n)
                      for p, v in tensor.items() for n in range(3)}
        return tensor

    def face(self, a, b):
        a, b, active = self.relative(a, b)
        y = self.points[b]
        receiver = (m.norm(y), *[m.scale(v, -2) for v in y], m.val(1))
        num = {p: m.dot(receiver, v) for p, v in self.moments(a, active).items()}
        den = {}
        for powers in num:
            v = m.val(1)
            for n, k in zip(powers, active):
                v = m.mul(v, [m.val(1), m.val(0), self.qs[k]][n])
            den[powers] = v
        return active, num, den

    def condition(self, a, b, threshold, upper=False):
        active, num, den = self.face(a, b)
        slack = {p: m.sub(num[p], m.scale(den[p], F(threshold))) for p in num}
        return active, {p: m.scale(v, -1) for p, v in slack.items()} if upper else slack


def bounds(row):
    box = [(-F(1), F(1)), (-F(1), F(1))]
    need(row["depth"] == len(row["path"]) and set(row["path"]) <= {"0", "1"}, "binary path")
    for bit in row["path"]:
        k = 0 if box[0][1]-box[0][0] >= box[1][1]-box[1][0] else 1
        mid = sum(box[k])/2
        box[k] = (box[k][0], mid) if bit == "0" else (mid, box[k][1])
    need(box == [tuple(F(x) for x in b) for b in row["bounds"]], "exact leaf bounds")
    return box


def full_cover(rows):
    for chart in product("FR", repeat=2):
        paths = [r["path"] for r in rows if tuple(r["charts"]) == chart]
        unique = set(paths)
        need(len(paths) == len(unique) and all(p[:k] not in unique for p in paths for k in range(len(p))), "prefix-free chart")
        need(sum((F(1, 2**len(p)) for p in paths), F(0)) == 1, "complete chart Kraft sum")
    for row in rows:
        bounds(row)


def verify_amide():
    contract = load("data/amide_source_contract.json")
    lines = (ROOT/"sources/NML.cif").read_text().splitlines()
    need(hashlib.sha256((ROOT/"sources/NML.cif").read_bytes()).hexdigest() == contract["raw_source"]["sha256"], "NML source identity")
    for source in contract["sources"]:
        points = {}
        for name, address in source["addresses"].items():
            tokens = shlex.split(lines[address["line_1_based"]-1])
            need(tokens[0] == "NML" and tokens[1] == name, "literal NML atom address")
            xyz = tokens[12:15] if source["family"] == "model" else tokens[15:18]
            need(xyz == address["tokens"], "literal model/ideal coordinate chart")
            points[name] = [F(x) for x in xyz]
            need(points[name] == list(map(F, source["points"][name])), "exact decimal source decoding")
        subtract = lambda a, b: [x-y for x, y in zip(a, b)]
        dot = lambda a, b: sum((x*y for x, y in zip(a, b)), F(0))
        u = subtract(points["C2"], points["N3"])
        v = subtract(points["C3"], points["N3"])
        h = subtract(points["HN3"], points["N3"])
        cross = [u[1]*v[2]-u[2]*v[1], u[2]*v[0]-u[0]*v[2], u[0]*v[1]-u[1]*v[0]]
        qu, qv, uv = dot(u, u), dot(v, v), dot(u, v)
        metrics = source["metrics"]
        for name, value in {"q_u": qu, "q_v": qv, "g_uv": uv,
                            "Gram_determinant": qu*qv-uv*uv,
                            "cosine_squared": uv*uv/(qu*qv),
                            "N_H_quadrance_A2": dot(h, h),
                            "u_dot_H_A2": dot(u, h), "v_dot_H_A2": dot(v, h),
                            "H_plane_triple_A3": dot(cross, h)}.items():
            need(value == F(metrics[name]), "NML exact source metric: "+name)
        need(uv < 0 and dot(cross, h) != 0, "source departure from exact planarity retained")
    for bond in contract["source_bonds"]:
        tokens = shlex.split(lines[bond["line_1_based"]-1])
        need(tokens[:4] == ["NML", *bond["ends"], bond["order"]], "literal source incidence")
    need(contract["agent_inferred"] and not contract["exact_planarity_imposed"]
         and not contract["binding_claim"] and not contract["heavy_movement_allowed"], "conditional substitution scope")
    return {"passed": True, "part": "amide", "source": "NML", "source_charts_checked": 2,
            "experimental_or_transfer_uncertainty_quantified": False}


def verify_broadphase(data, comparisons, results):
    """Replay pair readings from supplied regional enclosures, not their producer."""
    atoms = data["atoms"]
    ns = [set() for _ in atoms]
    for a, b in data["edges"]:
        ns[a].add(b)
        ns[b].add(a)
    supports = [cut(ns, *e) for e in data["joint_axes"]]
    ends = [set(e) for e in data["joint_axes"]]
    polar = [a["element"] in {"N", "O", "S"} for a in atoms]
    donor = [a["element"] == "H" and any(polar[j] for j in ns[i]) for i, a in enumerate(atoms)]
    exclusions = [s | {k for j in s for k in ns[j]} for s in ns]
    radii = [F(data["radii_A"][a["element"]])*100 for a in atoms]
    need(all(r.denominator == 1 for r in radii), "declared exact radius chart")
    radii = list(map(int, radii))
    grain2 = int(data["grain_denominator"])**2
    regional = data["latest_regional_faces"]
    ff, p, op = [regional[k] for k in ["sealed_FF_baseline_boxes", "P_only_regional_boxes", "O_P_regional_boxes"]]
    need(all(len(x) == len(atoms) for x in [ff, p, op]), "complete regional faces")
    known = {tuple(sorted(c["pair"])) for c in comparisons["comparisons"] if c["kind"] == "internal"}
    fields = results["latest_internal_broadphase_counts"]["reference"].keys()
    counts = {scope: {k: 0 for k in fields} for scope in ["reference", "ionized"]}
    unresolved, directional = {}, {}
    def quadrance(a, b):
        lo = hi = 0
        for (l, h), (u, v) in zip(a, b):
            x, y = l-v, h-u
            lo += 0 if x <= 0 <= y else min(x*x, y*y)
            hi += max(x*x, y*y)
        return lo, hi
    for i in range(len(atoms)):
        for j in range(i+1, len(atoms)):
            scopes = ["reference"] if j == data["terminal_policy"]["reference_HXT"] else ["reference", "ionized"]
            for scope in scopes:
                counts[scope]["all_pairs"] += 1
            if j in exclusions[i]:
                for scope in scopes:
                    counts[scope]["excluded_one_or_two_edges"] += 1
                continue
            same = [((i in s) == (j in s)) or i in e or j in e for s, e in zip(supports, ends)]
            if all(same):
                kind, boxes = "common_motion_FF_inherited", ff
            elif same[1]:
                kind, boxes = "common_outer_cancelled_P_only_regional", p
            else:
                kind, boxes = "full_O_P_regional", op
            q = quadrance(boxes[i], boxes[j])
            threshold = 4*(radii[i]+radii[j])**2*grain2
            clear, below = q[0]*90000 >= threshold, q[1]*90000 < threshold
            possible = (polar[j] and (polar[i] or donor[i])) or (polar[i] and (polar[j] or donor[j]))
            status = ("possible_directional_" if possible else "nondirectional_") + (
                "severe_clear" if clear else ("strict_geometric_overlap" if possible else "strict_refusal") if below else "unresolved")
            for scope in scopes:
                counts[scope]["nonlocal"] += 1
                counts[scope][kind] += 1
                counts[scope][status] += 1
            if not clear:
                need(not below, "paused region reports no strict overlap")
                (directional if possible else unresolved)[(i, j)] = (q, F(4*(radii[i]+radii[j])**2, 90000), (i, j) in known)
    need(counts == results["latest_internal_broadphase_counts"], "all declared pair counts reproduced")
    expected = {tuple(r["pair"]): (tuple(map(int, r["q_A2_outward_numerators"])), F(r["threshold_A2"]), r["known236_comparison"]) for r in results["latest_unresolved_nondirectional"]}
    need(unresolved == expected, "all unresolved nondirectional identities and enclosures reproduced")
    need(set(directional) == {tuple(r) for r in results["latest_possible_directional_pairs"]}, "all possible directional pair identities reproduced")
    need(sum(not v[2] for v in unresolved.values()) == results["new_internal_receivers_not_yet_built"] == 966, "966 unbuilt receivers retained")
    need(not results["full_internal_fixture_admission_completed"] and not results["common_pose_constructed"], "paused admission limits")
    return {"passed": True, "part": "broadphase", "nonlocal_reference": counts["reference"]["nonlocal"],
            "unresolved_nondirectional": len(unresolved), "possible_directional": len(directional),
            "full_internal_fixture_admission": False, "common_pose_or_binding_claim": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--part", choices=["certificates", "broadphase", "amide"], required=True)
    args = parser.parse_args()
    manifest = load("data/manifest.json")
    for name, entry in manifest["files"].items():
        content = (ROOT/name).read_bytes()
        need(hashlib.sha256(content).hexdigest() == entry["sha256"] and len(content) == entry["bytes"], "published input identity")
    if args.part == "amide":
        print(json.dumps(verify_amide()))
        return
    data, comparisons, checkpoints, results = [load("data/"+x+".json") for x in ["source_faces", "comparisons", "checkpoints", "results"]]
    if args.part == "broadphase":
        print(json.dumps(verify_broadphase(data, comparisons, results)))
        return
    sequence = "".join((ROOT/"sequence.fasta").read_text().splitlines()[1:])
    need(sequence == data["sequence"] == results["sequence"] and len(sequence) == 69, "candidate source word")
    atoms = data["atoms"]
    need(len(atoms) == len(data["source_faces"]) == 1108 and len(data["edges"]) == 1107, "source extent")
    ns = [set() for _ in atoms]
    for a, b in data["edges"]:
        need(a != b and 0 <= a < 1108 and 0 <= b < 1108, "source incidence")
        ns[a].add(b)
        ns[b].add(a)
    points = {}
    grain = int(data["grain_denominator"])
    for i, row in enumerate(data["source_faces"]):
        need(row["atom_id"] == atoms[i]["atom_id"] == i, "canonical source index")
        need(atoms[i]["letter"] == sequence[atoms[i]["position"]], "source position and sequence")
        points[i] = [m.rebase((F(a, grain), F(b, grain))) for a, b in row["box"]]
        for guards in row["denominator_guards"]:
            for lo, hi in guards:
                lo, hi = F(lo), F(hi)
                need(lo <= hi and (lo > 0 or hi < 0), "source branch guard")
        if atoms[i]["element"] == "H":
            need(row["root_context_id"] in data["local_context_bindings"], "H local chart identity")
    root = data["selected_OXT_root"]
    lo, hi = map(F, root["enclosure"])
    square = F(root["square"])
    need(root["selected_embedding"] == "positive" and 0 < lo <= hi and lo*lo <= square <= hi*hi, "positive OXT branch")
    need(list(map(F, root["polynomial_ascending"])) == [-square, F(0), F(1)], "OXT polynomial")
    h = sum(F(data["target_anchor_points_1_1000_A"]["2649"][j]-data["target_anchor_points_1_1000_A"]["3164"][j], 1000)**2 for j in range(3))
    need(h == F(7796949, 62500), "observed target chord")
    dlo, dhi = map(F, data["target_chord_root_enclosure_A"])
    need(7 < dlo <= dhi and dlo*dlo <= h <= dhi*dhi, "target positive root")
    limits = {"necessary": [(dlo-7)**2, (dhi+7)**2], "sufficient": [(dhi-7)**2, (dlo+7)**2]}
    need(limits["necessary"] == list(map(F, data["necessary_chord_q_outer_A2"])) and limits["sufficient"] == list(map(F, data["sufficient_chord_q_inner_A2"])), "chord outer/inner law")
    old = Family(points, ns, data["old_axes"])
    joint = Family(points, ns, data["joint_axes"], (434, 433, F(-19, 64)))
    need(list(map(len, old.supports)) == [435, 631, 1104] and list(map(len, joint.supports)) == [613, 631], "complete cut counts")
    need(old.supports[0] < joint.supports[0] < joint.supports[1] < old.supports[2], "nested incidence")
    all_internal = [c for c in comparisons["comparisons"] if c["kind"] == "internal"]
    need(len(all_internal) == 236, "monotone internal membership")
    conditions = {}
    for c in all_internal:
        a, b = c["pair"]
        excluded = ns[a] | {k for j in ns[a] for k in ns[j]}
        need(a != b and b not in excluded, "actual nonlocality")
        polar = {"N", "O", "S"}
        donor = lambda i: atoms[i]["element"] == "H" and any(atoms[j]["element"] in polar for j in ns[i])
        aa, bb = atoms[a]["element"], atoms[b]["element"]
        need(not ((aa in polar and bb in polar) or (donor(a) and bb in polar) or (donor(b) and aa in polar)), "directional contacts separate")
        threshold = F(4, 9)*(F(data["radii_A"][aa])+F(data["radii_A"][bb]))**2
        need(threshold == F(c["threshold_A2"]), "declared fixture threshold")
        conditions[c["index"]] = joint.condition(a, b, threshold)
    old_conditions = {c["index"]: old.condition(*c["pair"], c["threshold_A2"])
                      for c in all_internal if c["index"] in comparisons["old_internal_indices"]}
    need(len(old_conditions) == 205 and all(2 not in a for a, t in old_conditions.values()), "old205 arbitrary beta invariance")
    joint_chord = {(role, upper): joint.condition(64, 818, limit, upper)
                   for role, pair in limits.items() for upper, limit in enumerate(pair)}
    old_chord = [old.condition(64, 818, limit, upper) for upper, limit in enumerate(limits["necessary"])]
    psi_keys = [k for k, (active, t) in old_conditions.items() if active == (1,)]
    need(len(psi_keys) == 13, "old13 psi-only conditions")
    psi = {}
    for chart in "FR":
        xs = [(-F(1), F(1))]
        for k in psi_keys:
            active, tensor = old_conditions[k]
            xs = intersect(xs, necessary_phase([tensor[(i,)] for i in range(3)], chart))
        psi[chart] = xs
    old_rows = checkpoints["three_grip_205_obstruction"]["leaves"]
    full_cover(old_rows)
    for row in old_rows:
        box, witness = bounds(row), row["refusal"]
        kind = witness["kind"]
        if kind == "internal_strict_upper_slack":
            active, tensor = old_conditions[witness["comparison"]]
            need(bernstein(tensor, active, row["charts"], box)[1] < 0, "old whole-cell internal refusal")
        elif kind == "internal_psi_necessary_intersection_empty":
            need(not intersect(psi[row["charts"][1]], [box[1]]), "old whole-cell psi obstruction")
        else:
            need(kind == "pose_eliminated_chord_phase_empty_both_charts", "declared old refusal")
            phases = {chart: [(-F(1), F(1))] for chart in "FR"}
            for active, tensor in old_chord:
                need(active == (0, 1, 2), "old chord word")
                coeff = [bernstein({p[:2]: v for p, v in tensor.items() if p[2] == n}, (0, 1), row["charts"], box) for n in range(3)]
                for chart in phases:
                    phases[chart] = intersect(phases[chart], necessary_phase(coeff, chart))
            need(not any(phases.values()), "old full-beta positional chord obstruction")
    for name in ["joint_205_checkpoint", "joint_236_checkpoint"]:
        block = checkpoints[name]
        rows = block["leaves"]
        full_cover(rows)
        need(dict(Counter(r["status"] for r in rows)) == block["expected_counts"], "checkpoint status counts")
        selected = old_conditions.keys() if name == "joint_205_checkpoint" else conditions.keys()
        for row in rows:
            box = bounds(row)
            if row["status"] == "refused":
                key = row["refusal"]["comparison"]
                pair = joint_chord[("necessary", key.endswith("upper"))] if isinstance(key, str) else conditions[key]
                need(bernstein(pair[1], pair[0], row["charts"], box)[1] < 0, "joint whole-cell refusal")
            elif row["status"] == "necessary_pass":
                for key in selected:
                    active, tensor = conditions[key]
                    need(bernstein(tensor, active, row["charts"], box)[0] > 0, "all retained internal conditions over pass cell")
                for upper in [0, 1]:
                    active, tensor = joint_chord[("sufficient", upper)]
                    need(bernstein(tensor, active, row["charts"], box)[0] > 0, "both stricter chord bounds over pass cell")
    withdrawn = checkpoints["withdrawn_joint_cell"]
    active, tensor = conditions[withdrawn["comparison"]]
    need(active == (0,) and bernstein(tensor, active, withdrawn["charts"], bounds(withdrawn))[1] < 0, "withdrawn cell fails phi-only comparison375")
    # Existing fixed-psi circle obstruction. Substitute the actual fixed psi into G.
    sets = {chart: [(-F(1), F(1))] for chart in "FR"}
    selected = [conditions[k] for k in checkpoints["fixed_psi_phi37_slice_obstruction"]["comparison_indices"]]
    selected += [joint_chord[("necessary", upper)] for upper in [0, 1]]
    for active, tensor in selected:
        coeff = [m.val(0), m.val(0), m.val(0)]
        for powers, v in tensor.items():
            powers = dict(zip(active, powers))
            v = m.scale(v, F(-51, 64)**powers.get(1, 0))
            coeff[powers.get(0, 0)] = m.add(coeff[powers.get(0, 0)], v)
        for chart in sets:
            sets[chart] = intersect(sets[chart], necessary_phase(coeff, chart))
    need(not any(sets.values()), "entire fixed-psi phi37 circle obstruction")
    print(json.dumps({"passed": True, "part": "certificates", "old205_obstruction_leaves": len(old_rows),
                      "joint236_checkpoint": checkpoints["joint_236_checkpoint"]["expected_counts"],
                      "full_internal_fixture_admission": False, "common_pose_or_binding_claim": False}))


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    main()

#!/usr/bin/env python3
"""Derive the apparatus-telemetry faces of Deed H0 from an Nsight Systems sqlite export,
a /proc sampling log, and (optionally) an Nsight Compute csv export.

Standard library only (sqlite3, argparse, os, re, sys). No third-party dependency.

It writes, into --out-dir:
    kernel-timeline.tsv     every kernel occurrence in chronological order, with the
                            cuGraphLaunch that contained it
    transfer-timeline.tsv   every memcpy and memset occurrence
    cpu-api-timeline.tsv    every CUDA driver API call with its thread
    cpu-process.tsv         the /proc samples of the un-profiled run
    kernel-resources.tsv    one row per distinct kernel name x launch geometry
    scheduler-states.tsv    per profiled kernel launch (Nsight Compute), else `unknown`

and prints the derived timeline readings (per-graph GPU wall, summed kernel duration,
maximum simultaneous kernels, overlap fraction, inter-graph CPU gap, whole-run GPU busy
fraction) to stdout for the calibration form.

Nothing here measures anything semantic. Nsight is exterior apparatus.
An unmeasured face is written `unknown`, never 0.
"""

import argparse
import os
import re
import sqlite3
import sys

UNKNOWN = "unknown"
SMS = 80
THREADS_PER_SM = 1536  # 48 warps/SM * 32 threads/warp, RTX 4080 SUPER (cc 8.9)
WARP = 32


# ---------------------------------------------------------------- nsys reading


def graph_launch_order(cur):
    """The cuGraphLaunch correlation ids, ordered by call start.

    A graph-node kernel carries the correlation id of the cuGraphLaunch that ran it,
    so this is the whole mapping.
    """
    cur.execute(
        """SELECT r.correlationId, r.start, r.end
             FROM CUPTI_ACTIVITY_KIND_RUNTIME r
             JOIN StringIds s ON s.id = r.nameId
            WHERE s.value = 'cuGraphLaunch'
            ORDER BY r.start"""
    )
    rows = cur.fetchall()
    return {corr: i for i, (corr, _s, _e) in enumerate(rows)}, rows


def write_kernel_timeline(cur, path, corr_to_graph):
    cur.execute(
        """SELECT k.start, k.end, k.streamId, k.contextId, k.correlationId,
                  k.graphNodeId, k.registersPerThread,
                  k.gridX, k.gridY, k.gridZ, k.blockX, k.blockY, k.blockZ,
                  k.staticSharedMemory, k.dynamicSharedMemory, s.value
             FROM CUPTI_ACTIVITY_KIND_KERNEL k
             JOIN StringIds s ON s.id = k.shortName
            ORDER BY k.start, k.end"""
    )
    header = (
        "launch_index\tgraph_launch_index\tkernel\tstart_ns\tend_ns\tduration_ns\t"
        "stream_id\tgrid_x\tgrid_y\tgrid_z\tblock_x\tblock_y\tblock_z\t"
        "registers_per_thread\tstatic_shared_octets\tdynamic_shared_octets\t"
        "correlation_id\tgraph_node_id\tcontext_id"
    )
    kernels = []
    with open(path, "w") as fh:
        fh.write(header + "\n")
        for i, r in enumerate(cur.fetchall()):
            (
                start,
                end,
                stream,
                ctx,
                corr,
                node,
                regs,
                gx,
                gy,
                gz,
                bx,
                by,
                bz,
                sshm,
                dshm,
                name,
            ) = r
            gidx = corr_to_graph.get(corr, UNKNOWN) if node is not None else UNKNOWN
            fh.write(
                "\t".join(
                    str(v)
                    for v in (
                        i,
                        gidx,
                        name,
                        start,
                        end,
                        end - start,
                        stream,
                        gx,
                        gy,
                        gz,
                        bx,
                        by,
                        bz,
                        regs,
                        sshm,
                        dshm,
                        corr,
                        node if node is not None else UNKNOWN,
                        ctx,
                    )
                )
                + "\n"
            )
            kernels.append(
                {
                    "i": i,
                    "graph": gidx,
                    "name": name,
                    "start": start,
                    "end": end,
                    "stream": stream,
                    "grid": (gx, gy, gz),
                    "block": (bx, by, bz),
                    "regs": regs,
                    "sshm": sshm,
                    "dshm": dshm,
                }
            )
    return kernels


COPY_KIND = {
    1: "memcpy_htod",
    2: "memcpy_dtoh",
    8: "memcpy_dtod",
}


def write_transfer_timeline(cur, path, corr_to_graph):
    events = []
    cur.execute(
        """SELECT start, end, bytes, copyKind, streamId, correlationId, graphNodeId
             FROM CUPTI_ACTIVITY_KIND_MEMCPY"""
    )
    for start, end, octets, kind, stream, corr, node in cur.fetchall():
        events.append(
            (
                start,
                end,
                COPY_KIND.get(kind, "memcpy_kind_%d" % kind),
                octets,
                stream,
                corr,
                node,
            )
        )
    cur.execute(
        """SELECT start, end, bytes, streamId, correlationId, graphNodeId
             FROM CUPTI_ACTIVITY_KIND_MEMSET"""
    )
    for start, end, octets, stream, corr, node in cur.fetchall():
        events.append((start, end, "memset", octets, stream, corr, node))
    events.sort(key=lambda e: (e[0], e[1]))
    with open(path, "w") as fh:
        fh.write(
            "index\tkind\toctets\tstart_ns\tend_ns\tduration_ns\tstream_id\t"
            "correlation_id\tgraph_launch_index\n"
        )
        for i, (start, end, kind, octets, stream, corr, node) in enumerate(events):
            gidx = corr_to_graph.get(corr, UNKNOWN) if node is not None else UNKNOWN
            fh.write(
                "\t".join(
                    str(v)
                    for v in (
                        i,
                        kind,
                        octets,
                        start,
                        end,
                        end - start,
                        stream,
                        corr,
                        gidx,
                    )
                )
                + "\n"
            )
    return events


def write_cpu_api_timeline(cur, path):
    cur.execute(
        """SELECT r.start, r.end, s.value, r.globalTid, r.correlationId, r.returnValue
             FROM CUPTI_ACTIVITY_KIND_RUNTIME r
             JOIN StringIds s ON s.id = r.nameId
            ORDER BY r.start, r.end"""
    )
    n = 0
    with open(path, "w") as fh:
        fh.write(
            "index\tapi\tstart_ns\tend_ns\tduration_ns\tthread_id\tcorrelation_id\t"
            "return_value\n"
        )
        for i, (start, end, name, gtid, corr, rv) in enumerate(cur.fetchall()):
            tid = (gtid & 0xFFFFFF) if gtid is not None else UNKNOWN
            fh.write(
                "\t".join(
                    str(v)
                    for v in (
                        i,
                        name,
                        start,
                        end,
                        end - start,
                        tid,
                        corr if corr is not None else UNKNOWN,
                        rv,
                    )
                )
                + "\n"
            )
            n = i + 1
    return n


def write_kernel_resources(kernels, path, ncu_by_kernel):
    """One row per distinct kernel name x launch geometry actually observed."""
    groups = {}
    for k in kernels:
        key = (k["name"], k["grid"], k["block"], k["regs"], k["sshm"], k["dshm"])
        groups.setdefault(key, 0)
        groups[key] += 1
    rows = []
    for key, count in sorted(groups.items(), key=lambda kv: (-kv[1], kv[0][0])):
        name, grid, block, regs, sshm, dshm = key
        threads_per_block = block[0] * block[1] * block[2]
        blocks = grid[0] * grid[1] * grid[2]
        threads = threads_per_block * blocks
        warps_per_block = -(-threads_per_block // WARP)  # ceiling
        waves = threads / float(SMS * THREADS_PER_SM)
        ncu = ncu_by_kernel.get((name, grid, block), {})
        rows.append(
            [
                name,
                count,
                grid[0],
                grid[1],
                grid[2],
                block[0],
                block[1],
                block[2],
                regs,
                sshm,
                dshm,
                threads,
                warps_per_block,
                ncu.get("theoretical_occupancy_pct", UNKNOWN),
                ncu.get("achieved_occupancy_pct", UNKNOWN),
                ncu.get("resident_blocks_per_sm", UNKNOWN),
                "%.6f" % waves,
                "nsys+ncu" if ncu else "nsys",
            ]
        )
    with open(path, "w") as fh:
        fh.write(
            "kernel\tlaunches\tgrid_x\tgrid_y\tgrid_z\tblock_x\tblock_y\tblock_z\t"
            "registers_per_thread\tstatic_shared_octets\tdynamic_shared_octets\t"
            "threads_per_launch\twarps_per_block\ttheoretical_occupancy_pct\t"
            "achieved_occupancy_pct\tresident_blocks_per_sm\twaves_per_sm\tsource\n"
        )
        for r in rows:
            fh.write("\t".join(str(v) for v in r) + "\n")
    return len(rows)


# ------------------------------------------------------------- /proc samples


SAMPLE_RE = re.compile(r"^### sample (\d+) pid (\d+) wall_ns (\d+)")


def parse_proc_raw(path):
    samples = []
    cur = None
    section = None
    with open(path) as fh:
        for line in fh:
            line = line.rstrip("\n")
            m = SAMPLE_RE.match(line)
            if m:
                cur = {
                    "index": int(m.group(1)),
                    "wall_ns": int(m.group(3)),
                    "sched": {},
                    "io": {},
                    "status": {},
                    "ps": [],
                }
                section = None
                continue
            if line.startswith("### end"):
                if cur is not None:
                    samples.append(cur)
                cur = None
                section = None
                continue
            if cur is None:
                continue
            if line.startswith("--- "):
                section = line[4:].strip()
                continue
            if section == "sched":
                if ":" in line:
                    k, _, v = line.partition(":")
                    cur["sched"][k.strip()] = v.strip()
            elif section == "io":
                if ":" in line:
                    k, _, v = line.partition(":")
                    cur["io"][k.strip()] = v.strip()
            elif section == "status":
                if ":" in line:
                    k, _, v = line.partition(":")
                    cur["status"][k.strip()] = v.strip()
            elif section == "ps":
                parts = line.split()
                if len(parts) >= 4:
                    cur["ps"].append(parts)
    return samples


def _num(text, default=UNKNOWN):
    if text is None:
        return default
    text = text.split()[0] if text.split() else ""
    try:
        return int(float(text))
    except ValueError:
        return default


def write_cpu_process(samples, path):
    with open(path, "w") as fh:
        fh.write(
            "sample_index\twall_ns\tthreads\tactive_thread_tid\tactive_thread_cpu\t"
            "migrations_total\tvoluntary_switches\tinvoluntary_switches\t"
            "io_read_octets\tio_write_octets\trss_octets\tsource\n"
        )
        for s in samples:
            hot_tid, hot_cpu = UNKNOWN, UNKNOWN
            best = -1.0
            for parts in s["ps"]:
                try:
                    pcpu = float(parts[2])
                except (ValueError, IndexError):
                    continue
                if pcpu > best:
                    best = pcpu
                    hot_tid, hot_cpu = parts[0], parts[1]
            rss_kb = _num(s["status"].get("VmRSS"))
            rss = rss_kb * 1024 if rss_kb != UNKNOWN else UNKNOWN
            fh.write(
                "\t".join(
                    str(v)
                    for v in (
                        s["index"],
                        s["wall_ns"],
                        _num(s["status"].get("Threads")),
                        hot_tid,
                        hot_cpu,
                        _num(
                            s["sched"].get(
                                "se.nr_migrations", s["sched"].get("nr_migrations")
                            )
                        ),
                        _num(s["sched"].get("nr_voluntary_switches")),
                        _num(s["sched"].get("nr_involuntary_switches")),
                        _num(s["io"].get("read_bytes")),
                        _num(s["io"].get("write_bytes")),
                        rss,
                        "/proc/PID/sched|/proc/PID/io|/proc/PID/status|ps",
                    )
                )
                + "\n"
            )
    return len(samples)


# ------------------------------------------------------------------- ncu csv


NCU_METRICS = {
    "active_warps_per_cycle": ["smsp__warps_active.avg.per_cycle_active"],
    "eligible_warps_per_cycle": ["smsp__warps_eligible.avg.per_cycle_active"],
    "issued_warps_per_cycle": ["smsp__issue_active.avg.per_cycle_active"],
    "issue_active_pct": ["smsp__issue_active.avg.pct_of_peak_sustained_active"],
    "l1_hit_pct": ["l1tex__t_sector_hit_rate.pct"],
    "l2_hit_pct": ["lts__t_sector_hit_rate.pct"],
    "dram_throughput_pct": [
        "gpu__dram_throughput.avg.pct_of_peak_sustained_elapsed"
    ],
    "sm_throughput_pct": ["sm__throughput.avg.pct_of_peak_sustained_elapsed"],
    "achieved_occupancy_pct": ["sm__warps_active.avg.pct_of_peak_sustained_active"],
    "theoretical_occupancy_pct": ["sm__maximum_warps_per_active_cycle_pct"],
    "registers_per_thread": ["launch__registers_per_thread"],
    "duration_ms": ["gpu__time_duration.sum"],
}

# Theoretical resident blocks per SM is the tightest of the four launch limits ncu
# reports in blocks: hardware block slots, registers, shared memory, warp slots.
BLOCK_LIMITS = [
    "launch__occupancy_limit_blocks",
    "launch__occupancy_limit_registers",
    "launch__occupancy_limit_shared_mem",
    "launch__occupancy_limit_warps",
]

STALL_PREFIX = "smsp__average_warps_issue_stalled_"
STALL_SUFFIX = "_per_issue_active.ratio"
# `selected` is the warp that did issue; it is not a stall state.
STALL_NOT_A_STALL = {"selected"}


def read_ncu_csv(path):
    """Parse `ncu --import <rep> --csv --page raw|details` output.

    Returns (per_launch_rows, per_kernel_name_summary).
    """
    import csv as _csv

    with open(path, newline="") as fh:
        text = fh.read()
    # ncu prints a banner before the csv; find the header line.
    lines = text.splitlines()
    start = 0
    for i, line in enumerate(lines):
        if line.startswith('"ID"') or line.startswith("ID,"):
            start = i
            break
    reader = list(_csv.reader(lines[start:]))
    if not reader:
        return [], {}
    header = reader[0]
    # A units row (every field blank in the ID column) follows the header in --page raw.
    body = [
        r
        for r in reader[1:]
        if len(r) == len(header) and r[0].strip().isdigit()
    ]
    idx = {h: i for i, h in enumerate(header)}
    launches = {}
    if "Metric Name" in idx:  # long form (--page details)
        for r in body:
            key = (r[idx.get("ID", 0)],)
            rec = launches.setdefault(
                key,
                {
                    "kernel": r[idx.get("Kernel Name", 0)],
                    "id": r[idx.get("ID", 0)],
                    "metrics": {},
                },
            )
            unit = r[idx["Metric Unit"]] if "Metric Unit" in idx else ""
            rec["metrics"][r[idx["Metric Name"]]] = (r[idx["Metric Value"]], unit)
    else:  # wide form (--page raw): one column per metric
        namecol = idx.get("Kernel Name", idx.get("Demangled Name"))
        for r in body:
            key = (r[idx.get("ID", 0)],)
            rec = launches.setdefault(
                key,
                {
                    "kernel": r[namecol] if namecol is not None else UNKNOWN,
                    "id": r[idx.get("ID", 0)],
                    "metrics": {},
                },
            )
            for h, i in idx.items():
                rec["metrics"][h] = (r[i], "")
    return list(launches.values()), header


def _mval(metrics, names):
    for n in names:
        if n in metrics:
            raw = metrics[n][0].replace(",", "").strip()
            if raw in ("", "n/a", "N/A"):
                continue
            try:
                return float(raw)
            except ValueError:
                continue
    return None


def ncu_rows(launch_records):
    rows = []
    by_kernel = {}
    for rec in launch_records:
        m = rec["metrics"]
        vals = {}
        for face, names in NCU_METRICS.items():
            v = _mval(m, names)
            vals[face] = ("%.4f" % v) if v is not None else UNKNOWN
        # theoretical resident blocks per SM: the tightest launch limit
        limits = [_mval(m, [n]) for n in BLOCK_LIMITS]
        limits = [v for v in limits if v is not None]
        resident_blocks = ("%d" % int(min(limits))) if limits else UNKNOWN
        # `No Eligible`: the share of active cycles in which no warp issued.
        issue_pct = _mval(m, NCU_METRICS["issue_active_pct"])
        no_eligible = ("%.4f" % (100.0 - issue_pct)) if issue_pct is not None else UNKNOWN
        duration_ns = (
            "%d" % int(round(float(vals["duration_ms"]) * 1e6))
            if vals["duration_ms"] != UNKNOWN
            else UNKNOWN
        )
        stalls = []
        for name, (raw, _u) in m.items():
            if name.startswith(STALL_PREFIX) and name.endswith(STALL_SUFFIX):
                short = name[len(STALL_PREFIX) : -len(STALL_SUFFIX)]
                try:
                    stalls.append((short, float(raw.replace(",", ""))))
                except ValueError:
                    pass
        total = sum(v for _n, v in stalls) or None
        stalls = [s for s in stalls if s[0] not in STALL_NOT_A_STALL]
        stalls.sort(key=lambda kv: -kv[1])
        top = []
        for name, v in stalls[:2]:
            pct = ("%.2f" % (100.0 * v / total)) if total else UNKNOWN
            top.append((name, pct))
        while len(top) < 2:
            top.append((UNKNOWN, UNKNOWN))
        rows.append(
            {
                "kernel": rec["kernel"],
                "launch_index": rec["id"],
                "duration_ns": duration_ns,
                "active_warps_per_cycle": vals["active_warps_per_cycle"],
                "eligible_warps_per_cycle": vals["eligible_warps_per_cycle"],
                "issued_warps_per_cycle": vals["issued_warps_per_cycle"],
                "no_eligible_pct": no_eligible,
                "stall_top1": top[0][0],
                "stall_top1_pct": top[0][1],
                "stall_top2": top[1][0],
                "stall_top2_pct": top[1][1],
                "l1_hit_pct": vals["l1_hit_pct"],
                "l2_hit_pct": vals["l2_hit_pct"],
                "dram_throughput_pct": vals["dram_throughput_pct"],
                "sm_throughput_pct": vals["sm_throughput_pct"],
                "achieved_occupancy_pct": vals["achieved_occupancy_pct"],
                "registers_per_thread": vals["registers_per_thread"],
                "source": "ncu",
            }
        )
        short = rec["kernel"].split("(")[0].strip()
        key = (short, _triple(m.get("Grid Size")), _triple(m.get("Block Size")))
        slot = by_kernel.setdefault(
            key,
            {
                "theoretical_occupancy_pct": vals["theoretical_occupancy_pct"],
                "resident_blocks_per_sm": resident_blocks,
                "_achieved": [],
            },
        )
        if vals["achieved_occupancy_pct"] != UNKNOWN:
            slot["_achieved"].append(float(vals["achieved_occupancy_pct"]))
    for slot in by_kernel.values():
        seen = slot.pop("_achieved")
        slot["achieved_occupancy_pct"] = (
            "%.4f" % (sum(seen) / len(seen)) if seen else UNKNOWN
        )
    return rows, by_kernel


def _triple(cell):
    """`(25, 1, 1)` -> (25, 1, 1)."""
    if not cell:
        return None
    raw = cell[0] if isinstance(cell, tuple) else cell
    parts = [p.strip() for p in raw.strip("() ").split(",")]
    try:
        return tuple(int(p) for p in parts)
    except ValueError:
        return None


SCHED_COLS = [
    "kernel",
    "launch_index",
    "duration_ns",
    "active_warps_per_cycle",
    "eligible_warps_per_cycle",
    "issued_warps_per_cycle",
    "no_eligible_pct",
    "stall_top1",
    "stall_top1_pct",
    "stall_top2",
    "stall_top2_pct",
    "l1_hit_pct",
    "l2_hit_pct",
    "dram_throughput_pct",
    "sm_throughput_pct",
    "achieved_occupancy_pct",
    "registers_per_thread",
    "source",
]


def write_scheduler_states(rows, path, fallback_kernels):
    with open(path, "w") as fh:
        fh.write("\t".join(SCHED_COLS) + "\n")
        if rows:
            for r in rows:
                fh.write("\t".join(str(r[c]) for c in SCHED_COLS) + "\n")
            return len(rows)
        # ncu did not run: one `unknown` row per kernel class that a run would have profiled.
        for name in fallback_kernels:
            vals = [name] + [UNKNOWN] * (len(SCHED_COLS) - 1)
            fh.write("\t".join(vals) + "\n")
        return len(fallback_kernels)


# ------------------------------------------------------- derived timeline reads


def union_length(intervals):
    if not intervals:
        return 0
    ivs = sorted(intervals)
    total = 0
    cs, ce = ivs[0]
    for s, e in ivs[1:]:
        if s > ce:
            total += ce - cs
            cs, ce = s, e
        else:
            ce = max(ce, e)
    total += ce - cs
    return total


def concurrency_profile(intervals):
    """Return (max_concurrent, length with >=2 concurrent, union length)."""
    if not intervals:
        return 0, 0, 0
    events = []
    for s, e in intervals:
        events.append((s, 1))
        events.append((e, -1))
    events.sort()
    depth = 0
    maxd = 0
    prev = events[0][0]
    ge2 = 0
    ge1 = 0
    for t, d in events:
        if t > prev:
            if depth >= 2:
                ge2 += t - prev
            if depth >= 1:
                ge1 += t - prev
            prev = t
        depth += d
        maxd = max(maxd, depth)
    return maxd, ge2, ge1


def derived_report(kernels, transfers, out):
    graphs = {}
    for k in kernels:
        if k["graph"] == UNKNOWN:
            continue
        graphs.setdefault(k["graph"], []).append(k)
    lines = []
    lines.append("graph_launch_index\tkernels\tgpu_wall_ns\tsummed_kernel_ns\t"
                 "max_concurrent_kernels\toverlap_ge2_fraction\tbusy_fraction_in_wall\t"
                 "cpu_gap_to_next_ns")
    order = sorted(graphs)
    walls = {}
    for gi in order:
        ks = graphs[gi]
        s = min(k["start"] for k in ks)
        e = max(k["end"] for k in ks)
        walls[gi] = (s, e)
        summed = sum(k["end"] - k["start"] for k in ks)
        maxd, ge2, ge1 = concurrency_profile([(k["start"], k["end"]) for k in ks])
        wall = e - s
        lines.append(
            "%s\t%d\t%d\t%d\t%d\t%.6f\t%.6f\t%s"
            % (
                gi,
                len(ks),
                wall,
                summed,
                maxd,
                (ge2 / float(wall)) if wall else 0.0,
                (ge1 / float(wall)) if wall else 0.0,
                UNKNOWN,
            )
        )
    # inter-graph CPU gaps
    gaps = []
    for a, b in zip(order, order[1:]):
        gaps.append((a, b, walls[b][0] - walls[a][1]))
    fixed = []
    for line in lines[1:]:
        parts = line.split("\t")
        gi = int(parts[0])
        gap = next((g for a, _b, g in gaps if a == gi), None)
        parts[-1] = str(gap) if gap is not None else UNKNOWN
        fixed.append("\t".join(parts))
    body = [lines[0]] + fixed

    all_iv = [(k["start"], k["end"]) for k in kernels]
    first = min(s for s, _e in all_iv)
    last = max(e for _s, e in all_iv)
    maxd, ge2, ge1 = concurrency_profile(all_iv)
    summary = [
        "",
        "WHOLE RUN",
        "first_kernel_start_ns\t%d" % first,
        "last_kernel_end_ns\t%d" % last,
        "kernel_span_ns\t%d" % (last - first),
        "gpu_busy_ns_union\t%d" % ge1,
        "gpu_busy_fraction_of_kernel_span\t%.6f" % (ge1 / float(last - first)),
        "gpu_two_or_more_ns\t%d" % ge2,
        "gpu_two_or_more_fraction_of_kernel_span\t%.6f" % (ge2 / float(last - first)),
        "max_concurrent_kernels_whole_run\t%d" % maxd,
        "summed_kernel_duration_ns\t%d" % sum(e - s for s, e in all_iv),
    ]
    with open(out, "w") as fh:
        fh.write("\n".join(body + summary) + "\n")
    return "\n".join(body + summary)


# ------------------------------------------------------------------------ main


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sqlite", required=True)
    ap.add_argument("--proc-raw", required=True)
    ap.add_argument("--out-dir", required=True)
    ap.add_argument("--ncu-csv", default=None)
    ap.add_argument("--derived-out", required=True)
    args = ap.parse_args()

    os.makedirs(args.out_dir, exist_ok=True)
    con = sqlite3.connect(args.sqlite)
    cur = con.cursor()

    corr_to_graph, launch_rows = graph_launch_order(cur)
    print("cuGraphLaunch count: %d" % len(launch_rows))

    ncu_launch_rows, ncu_by_kernel = [], {}
    if args.ncu_csv and os.path.exists(args.ncu_csv):
        records, _hdr = read_ncu_csv(args.ncu_csv)
        ncu_launch_rows, ncu_by_kernel = ncu_rows(records)
        print("ncu profiled launches: %d" % len(ncu_launch_rows))

    kt = os.path.join(args.out_dir, "kernel-timeline.tsv")
    kernels = write_kernel_timeline(cur, kt, corr_to_graph)
    print("kernel-timeline.tsv rows: %d" % len(kernels))

    tt = os.path.join(args.out_dir, "transfer-timeline.tsv")
    transfers = write_transfer_timeline(cur, tt, corr_to_graph)
    print("transfer-timeline.tsv rows: %d" % len(transfers))

    at = os.path.join(args.out_dir, "cpu-api-timeline.tsv")
    n_api = write_cpu_api_timeline(cur, at)
    print("cpu-api-timeline.tsv rows: %d" % n_api)

    samples = parse_proc_raw(args.proc_raw)
    cp = os.path.join(args.out_dir, "cpu-process.tsv")
    n_proc = write_cpu_process(samples, cp)
    print("cpu-process.tsv rows: %d" % n_proc)

    kr = os.path.join(args.out_dir, "kernel-resources.tsv")
    n_res = write_kernel_resources(kernels, kr, ncu_by_kernel)
    print("kernel-resources.tsv rows: %d" % n_res)

    ss = os.path.join(args.out_dir, "scheduler-states.tsv")
    classes = sorted({k["name"] for k in kernels})
    n_sched = write_scheduler_states(ncu_launch_rows, ss, classes)
    print("scheduler-states.tsv rows: %d" % n_sched)

    print()
    print(derived_report(kernels, transfers, args.derived_out))
    con.close()


if __name__ == "__main__":
    sys.exit(main())

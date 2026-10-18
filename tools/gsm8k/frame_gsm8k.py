"""Frame GSM8K train rows as HLSN1 sections for the listener (the exterior bridge from the pinned
train.jsonl and the train-only partition to the driver's framed files). test.jsonl is never read.

Writes three files to OUT_DIR:
- learn.hlsn: the partition's train rows in index order, question as the one octet passage and the
  complete solution (annotations and the final '#### N' line) as the target.
- development_release.hlsn: the development rows with an EMPTY target, so the driver can only
  release on them (question-only); their answers never enter this file.
- development_read.hlsn: the development rows with their solutions as targets, for the
  teacher-forced code-length read (--read). Never pass it in the same run as a development release.

usage: python3 -I frame_gsm8k.py TRAIN_JSONL PARTITION_JSON OUT_DIR
"""
import json
import struct
import sys


def frame(sections):
    out = bytearray(b"HLSN1\n")
    for question, target in sections:
        out += struct.pack(">I", 1)
        out += bytes([0]) + struct.pack(">I", len(question)) + question
        out += struct.pack(">I", len(target)) + target
    return bytes(out)


def main():
    train_path, partition_path, out_dir = sys.argv[1:4]
    rows = []
    with open(train_path, "rb") as handle:
        for line in handle:
            if line.strip():
                row = json.loads(line)
                rows.append((row["question"].encode("utf-8"), row["answer"].encode("utf-8")))
    partition = json.load(open(partition_path))
    learn = [rows[i] for i in partition["train_indices"]]
    dev = [rows[i] for i in partition["dev_indices"]]
    nul = sum(q.count(0) + a.count(0) for q, a in rows)
    cells = lambda q, a: 2 * (len(q) + 1) + 2 * (len(a) + 1)
    longest = max(cells(q, a) for q, a in learn + dev)
    longest_solution = max(len(a) for q, a in learn)
    total = sum(cells(q, a) for q, a in learn)
    targets = sum(2 * (len(a) + 1) for q, a in learn)
    open(f"{out_dir}/learn.hlsn", "wb").write(frame(learn))
    open(f"{out_dir}/development_release.hlsn", "wb").write(frame([(q, b"") for q, a in dev]))
    open(f"{out_dir}/development_read.hlsn", "wb").write(frame(dev))
    print(
        f"rows={len(rows)} learn={len(learn)} development={len(dev)} nul_octets={nul} "
        f"longest_section_cells={longest} longest_learning_solution_octets={longest_solution} "
        f"learning_pass_cells={total} learning_target_cells={targets}"
    )
    first = learn[0]
    print(f"learn[0] question_octets={len(first[0])} solution_octets={len(first[1])}")
    print(f"development[0] question_octets={len(dev[0][0])}")


main()

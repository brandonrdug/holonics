"""Render the GSM8K training partition as the design thread's corpus: the train_indices of the
partition written by tools/gsm8k/partition.py, in index order, each problem as question, newline,
answer, blank line (3,528,168 bytes for all 6,726 problems; 519,633 for the first 1,000). Also
writes the cell offsets (four cells a byte) after 100, 1,000, 2,000, ..., 6,000 and all problems.

usage: python3 -I render_partition.py TRAIN_JSONL PARTITION_JSON OUT_TEXT OUT_MARKS
"""
import json
import sys

train, partition, out_text, out_marks = sys.argv[1:5]
rows = [json.loads(x) for x in open(train, 'rb').read().splitlines() if x.strip()]
indices = json.load(open(partition))['train_indices']
want = {100, 1000, 2000, 3000, 4000, 5000, 6000, len(indices)}
out, marks = bytearray(), []
for k, i in enumerate(indices, 1):
    out += (rows[i]['question'] + '\n' + rows[i]['answer'] + '\n\n').encode()
    if k in want:
        marks.append(4 * len(out))
open(out_text, 'wb').write(out)
open(out_marks, 'w').write(','.join(map(str, marks)) + '\n')
print(len(out), marks)

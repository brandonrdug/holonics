# usage: python3 -I recite.py TRAIN_TEXT SAMPLE_BIN
# Prints the longest runs of the sample that occur verbatim in the training text, greedily
# left to right: each printed run is the longest copied run starting at or after the last one's end.
import sys

train = open(sys.argv[1], 'rb').read()
sample = open(sys.argv[2], 'rb').read()

def longest_from(i):
    lo, hi = 0, len(sample) - i
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if sample[i:i + mid] in train:
            lo = mid
        else:
            hi = mid - 1
    return lo

runs = []
i = 0
while i < len(sample):
    n = longest_from(i)
    runs.append((n, i))
    i += max(n, 1)
runs.sort(reverse=True)
covered = sum(n for n, _ in runs if n >= 24)
print(f"RECITE bytes={len(sample)} longest={runs[0][0]} bytes_in_runs_of_24_or_more={covered}")
for n, i in runs[:5]:
    print(f"RECITE_RUN length={n} at={i} text={sample[i:i + n].decode('utf-8', 'replace')!r}")

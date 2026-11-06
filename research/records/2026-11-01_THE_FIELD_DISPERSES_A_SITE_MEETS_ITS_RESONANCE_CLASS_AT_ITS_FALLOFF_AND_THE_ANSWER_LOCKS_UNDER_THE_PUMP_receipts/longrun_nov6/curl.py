#!/usr/bin/env python3
"""The curl on two-place squares by band of distance (the unified-theory reading of November 6, 18:28): CURL.tsv's lambda_i,
lambda_j (log2 odds ratios through each place's faces, on 2^-20 bits). Per band: squares, the mean and spread of
lambda = (lambda_i + lambda_j) / 2, the spread of the curl lambda_i - lambda_j, their ratio, and the mean |curl|, in bits.
Usage: curl.py CURL_DIR. A reading only."""
import csv, statistics, sys
B = 1 << 20
NAMES = ["1", "2-3", "4-7", "8-15", "16+"]
rows = list(csv.DictReader(open(f"{sys.argv[1]}/CURL.tsv"), delimiter="\t"))
print("band\tsquares\tlambda_mean\tlambda_sd\tcurl_sd\tcurl/lambda\tmean_abs_curl\tcorr")
for b, name in enumerate(NAMES):
    r = [(int(x["lambda_i"]) / B, int(x["lambda_j"]) / B) for x in rows if int(x["band"]) == b]
    if len(r) < 3:
        continue
    lam = [(i + j) / 2 for i, j in r]
    curl = [i - j for i, j in r]
    li, lj = [i for i, _ in r], [j for _, j in r]
    corr = statistics.correlation(li, lj) if statistics.pstdev(li) and statistics.pstdev(lj) else float("nan")
    ls, cs = statistics.pstdev(lam), statistics.pstdev(curl)
    print(f"{name}\t{len(r)}\t{statistics.mean(lam):+.3f}\t{ls:.3f}\t{cs:.3f}\t{cs / ls if ls else float('nan'):.2f}\t{statistics.mean(abs(c) for c in curl):.3f}\t{corr:+.2f}")

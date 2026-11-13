"""P55 part B, B3 to B5 (a ruler on read-cavity's codes): by slice, c0 and cK in nats, their ratio and rank agreement, the share of c0 over the cut's
bar; the restarting cut at 5.545 nats on c0 along each stretch (epochs, one-place epochs, the spread of an epoch's news, the screen ratio at the
openings); the sites kept under a start seven places later and, on the code slice, under each line's leading spaces doubled, beside a carry on the
running sum and packets of the cut's mean epoch. Numbers only. Argument: the read's OUT directory (cavity.tsv)."""
import math
import sys
from collections import defaultdict

BAR = 5.545
NATS = math.log(2) / (1 << 20)
SHIFT, PAST = 7, 32
P_rows = defaultdict(lambda: defaultdict(dict))  # slice -> stretch -> t -> (c0, cK)
C_rows = defaultdict(dict)  # stretch -> t_copy -> (c0, source)
for line in open(f"{sys.argv[1]}/cavity.tsv"):
    f = line.rstrip("\n").split("\t")
    if f[0] == "P":
        P_rows[f[1]][int(f[2])][int(f[3])] = (int(f[5]) * NATS, int(f[6]) * NATS)
    elif f[0] == "C":
        C_rows[int(f[2])][int(f[3])] = (int(f[5]) * NATS, int(f[7]))


def ranks(xs):
    order = sorted(range(len(xs)), key=lambda i: xs[i])
    r = [0.0] * len(xs)
    i = 0
    while i < len(order):
        j = i
        while j + 1 < len(order) and xs[order[j + 1]] == xs[order[i]]:
            j += 1
        for k in range(i, j + 1):
            r[order[k]] = (i + j) / 2
        i = j + 1
    return r


def spearman(a, b):
    ra, rb = ranks(a), ranks(b)
    ma, mb = sum(ra) / len(ra), sum(rb) / len(rb)
    cov = sum((x - ma) * (y - mb) for x, y in zip(ra, rb))
    va, vb = sum((x - ma) ** 2 for x in ra), sum((y - mb) ** 2 for y in rb)
    return cov / math.sqrt(va * vb) if va > 0 and vb > 0 else float("nan")


def cut(codes, start=0):
    """The restarting cut from place `start`: the openings' places."""
    opens, a = [], None
    for t in range(start, len(codes)):
        c = codes[t]
        if a is None:
            opens.append(t)
            a = c
        elif a + c > BAR:
            opens.append(t)
            a = c
        else:
            a += c
    return opens


def carry(codes, start=0):
    opens, run, last = [], 0.0, None
    for t in range(start, len(codes)):
        run += codes[t]
        step = math.floor(run / BAR)
        if last is None or step != last:
            opens.append(t)
            last = step
    return opens


def packets(n, size, start=0):
    return [t for t in range(start, n) if (t - start) % size == 0]


def epochs(opens, n):
    """Whole epochs (an opening to the next) and the last, cut by the stretch's end."""
    whole = [(opens[i], opens[i + 1]) for i in range(len(opens) - 1)]
    return whole, (opens[-1], n) if opens else None


print("# P55 part B: a held place's news at its cavity opening, by slice (nats a place; the cut's bar 5.545 nats).")
pooled = defaultdict(list)
pooled_epochs = []
mean_epoch_of = {}
for name, stretches in P_rows.items():
    c0 = [v[0] for s in stretches.values() for v in (s[t] for t in sorted(s))]
    ck = [v[1] for s in stretches.values() for v in (s[t] for t in sorted(s))]
    pooled["c0"] += c0
    pooled["ck"] += ck
    rho = spearman(c0, ck)
    m0, mk = sum(c0) / len(c0), sum(ck) / len(ck)
    over = sum(1 for x in c0 if x > BAR) / len(c0)
    print(f"B3 slice={name} places={len(c0)} stretches={len(stretches)} mean_c0={m0:.3f} mean_cK={mk:.3f} c0_over_cK={m0 / mk:.3f} spearman={rho:.3f} share_c0_over_bar={over:.4f}")
    lengths, ones, news, screen_open, screen_rest = [], 0, [], [], []
    for s in stretches.values():
        codes = [s[t][0] for t in sorted(s)]
        opens = cut(codes)
        whole, _ = epochs(opens, len(codes))
        for a, b in whole:
            lengths.append(b - a)
            ones += (b - a) == 1
            news.append(sum(codes[a:b]))
        os_ = set(opens)
        screen_open += [codes[t] for t in os_]
        screen_rest += [codes[t] for t in range(len(codes)) if t not in os_]
    me = sum(lengths) / max(len(lengths), 1)
    mean_epoch_of[name] = me
    pooled_epochs += lengths
    mn = sum(news) / max(len(news), 1)
    sd = math.sqrt(sum((x - mn) ** 2 for x in news) / max(len(news), 1))
    so, sr = sum(screen_open) / max(len(screen_open), 1), sum(screen_rest) / max(len(screen_rest), 1)
    print(f"B4 slice={name} whole_epochs={len(lengths)} mean_epoch_places={me:.3f} one_place_share={ones / max(len(lengths), 1):.3f} news_spread={sd / mn if mn else float('nan'):.3f} opening_code_over_rest={so / sr if sr else float('nan'):.3f}")
    # B5 (i): a start seven places later, against the carry and packets.
    size = max(1, round(me))
    for law, f in (("cut", lambda c, st: cut(c, st)), ("carry", lambda c, st: carry(c, st)), ("packets", lambda c, st: packets(len(c), size, st))):
        kept = total = 0
        for s in stretches.values():
            codes = [s[t][0] for t in sorted(s)]
            a = set(t for t in f(codes, 0) if t > PAST)
            b = set(f(codes, SHIFT))
            total += len(a)
            kept += len(a & b)
        print(f"B5i slice={name} law={law} openings_past_32={total} kept_under_start_7_later={kept / max(total, 1):.4f}" + (f" packet_size={size}" if law == "packets" else ""))
m0, mk = sum(pooled["c0"]) / len(pooled["c0"]), sum(pooled["ck"]) / len(pooled["ck"])
print(f"B3 slice=pooled places={len(pooled['c0'])} mean_c0={m0:.3f} mean_cK={mk:.3f} c0_over_cK={m0 / mk:.3f} spearman={spearman(pooled['c0'], pooled['ck']):.3f}")
print(f"B4 slice=pooled whole_epochs={len(pooled_epochs)} mean_epoch_places={sum(pooled_epochs) / len(pooled_epochs):.3f} one_place_share={sum(1 for x in pooled_epochs if x == 1) / len(pooled_epochs):.3f}")
# B5 (ii): the code slice's copies with each line's leading spaces doubled.
if "code" in P_rows and C_rows:
    size = max(1, round(mean_epoch_of["code"]))
    for law in ("cut", "carry", "packets"):
        kept = total = 0
        for k, s in P_rows["code"].items():
            codes = [s[t][0] for t in sorted(s)]
            copy = C_rows.get(k, {})
            ccodes = [copy[t][0] for t in sorted(copy)]
            source = [copy[t][1] for t in sorted(copy)]
            fits = set(source)
            if law == "cut":
                a, b = cut(codes), set(cut(ccodes))
            elif law == "carry":
                a, b = carry(codes), set(carry(ccodes))
            else:
                a, b = packets(len(codes), size), set(packets(len(ccodes), size))
            opened_sources = set(source[t] for t in b)
            for t in a:
                if t in fits:
                    total += 1
                    kept += t in opened_sources
        print(f"B5ii slice=code law={law} openings_that_fit={total} kept_under_doubled_leading_spaces={kept / max(total, 1):.4f}" + (f" packet_size={size}" if law == "packets" else ""))

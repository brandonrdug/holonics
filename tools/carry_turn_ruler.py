#!/usr/bin/env -S python3 -I
"""A ruler: whether a carry circle's turn follows the site's symbol (the lead, November 18; the record of the two streams §17).

A carry circle carries `Q_t = κ_t b_t + γ_t Q_(t−1)` along a strand. Where the gate's turn `arg γ_t` is a stride of the site's own
symbol, the carried product holds the places before it in their order (`navigator.content-stride-moment`: a moment whose advance is
each letter's own stride holds products of every order of the written letters). Where the turn stands the same at every site, the
advance is fixed and a linear reading of the circle holds a sum of one-place terms and no conjunction. `athena host
complete-language read-strand-states` writes each known site's gate on every circle at every tick; this reads, for each tick over
the circles, with a site's weight its gate's modulus:

- `one_turn`: `|Σ_t γ_t| / Σ_t |γ_t|`, the resultant of the turn over all sites. One where the turn is the same at every site.
- `by_symbol`: `Σ_c |Σ_(t in c) γ_t| / Σ_t |γ_t|`, the same resultant taken within each symbol and summed. One where the turn is a
  function of the site's symbol alone.
- `by_pair`: the same within each pair of the site's symbol and the symbol before it.
- `symbols_share`: `(by_symbol − one_turn) / (1 − one_turn)`, how much of what the turn varies by is the site's symbol.
- `stride_spread`: the circular standard deviation, in thousandths of a turn, of the symbols' mean turns (each symbol by its count).
- `modulus`: the mean `|γ|` (a reach of `1 / (1 − |γ|)` places).

Given per tick as the mean over circles, with the least and the greatest circle. The same statistics are printed for two planted
gates on the same sites, in the same run: `planted_fixed` (one turn at every site) and `planted_stride` (a drawn turn a symbol), so a
reading that finds no stride is held to an instrument that finds a planted one. Outside the machine; shares only.

Usage: carry_turn_ruler.py DUMP"""
import sys
import numpy as np

def stats(gamma, classes, pairs):
    """`gamma` complex `[places][circles]`. Returns each statistic by circle."""
    weight = np.abs(gamma).sum(axis=0)
    one = np.abs(gamma.sum(axis=0)) / weight
    def within(keys):
        order = np.argsort(keys, kind="stable")
        k = keys[order]
        starts = np.flatnonzero(np.r_[True, k[1:] != k[:-1]])
        sums = np.add.reduceat(gamma[order], starts, axis=0)
        return sums, np.diff(np.r_[starts, len(k)])
    sym, counts = within(classes)
    by_symbol = np.abs(sym).sum(axis=0) / weight
    pair, _ = within(pairs)
    by_pair = np.abs(pair).sum(axis=0) / weight
    unit = sym / np.maximum(np.abs(sym), 1e-30)
    r = np.abs((unit * counts[:, None]).sum(axis=0)) / counts.sum()
    spread = np.sqrt(-2.0 * np.log(np.maximum(r, 1e-12))) / (2 * np.pi) * 1000.0
    share = (by_symbol - one) / np.maximum(1.0 - one, 1e-12)
    modulus = np.abs(gamma).mean(axis=0)
    return {"one_turn": one, "by_symbol": by_symbol, "by_pair": by_pair, "symbols_share": share, "stride_spread": spread, "modulus": modulus}

def line(name, s):
    return name + ": " + " | ".join(f"{k} {v.mean():.3f} ({v.min():.3f} to {v.max():.3f})" for k, v in s.items())

def main():
    d = sys.argv[1]
    dims = dict(l.split("\t") for l in open(d + "/dims.tsv").read().split("\n") if l)
    ticks, circles = int(dims["ticks"]), int(dims["circles"])
    rows, places, classes = [], [], []
    for l in open(d + "/rows.tsv"):
        f = l.rstrip("\n").split("\t")
        rows.append(int(f[0])); places.append(int(f[2])); classes.append(int(f[3]))
    rows, places, classes = np.array(rows), np.array(places), np.array(classes)
    n = len(rows)
    before = np.where(places > 0, np.r_[0, classes[:-1]], -1)
    pairs = classes * 1024 + (before + 1)
    keep = places > 0                      # a passage's first site has no place before it
    print(f"CARRY_TURN places={int(keep.sum())} passages={len(set(rows.tolist()))} circles={circles} ticks={ticks} symbols={len(set(classes[keep].tolist()))}")
    rng = np.random.default_rng(20261118)
    drawn = np.exp(2j * np.pi * rng.random((classes.max() + 1, circles)))
    fixed = np.exp(2j * np.pi * rng.random(circles))
    for tick in range(ticks):
        g = np.fromfile(f"{d}/gates_{tick}.i64", dtype="<i8").reshape(n, 2 * circles).astype(np.float64) / float(1 << 30)
        gamma = (g[:, :circles] + 1j * g[:, circles:])[keep]
        print(line(f"CARRY_TURN tick={tick + 1}", stats(gamma, classes[keep], pairs[keep])), flush=True)
        if tick == 0:
            mod = np.abs(gamma)
            print(line("CARRY_TURN planted_fixed", stats(mod * fixed[None, :], classes[keep], pairs[keep])), flush=True)
            print(line("CARRY_TURN planted_stride", stats(mod * drawn[classes[keep]], classes[keep], pairs[keep])), flush=True)

if __name__ == "__main__":
    main()

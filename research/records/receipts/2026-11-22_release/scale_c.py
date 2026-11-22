"""A ruler's arithmetic on receipts already committed: tools/state_travel.py scale lines (TRAVEL_SCALE ...), read as the c of
length.py. For a block of root mean square rms (form_rms over 2^grain: 2^-16 for the letters' rows and the biases, 2^-24 for the
rest), lengthening eps a lap (eps_ppk, parts a thousand), rate r and n sections a lap: c = 2 eps rms^2 2^(2r) / n, 1 where every
step of a part read as a ratio lengthens it and nothing else does. sd is the c of one standard deviation of a cosine drawn among
the block's entries, (travel/form)/sqrt(entries). travel is the block's travel a lap in its own unit, and free the same over a
free walk's lap, 2^(-r) sqrt(n). Outside the machine. Usage: scale_c.py FILE RATE SECTIONS"""
import sys, re, math
path, rate, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
G16 = ('enc', 'before', 'after')
for line in open(path):
    if not line.startswith('TRAVEL_SCALE'): continue
    f = dict(p.split('=', 1) for p in line.split()[1:] if '=' in p)
    if 'form_rms' not in f: continue
    grain = 16 if f['block'] in G16 or f['block'].endswith('_bias') else 24
    rms = float(f['form_rms']) / 2 ** grain
    k = 2 * rms * rms * 2.0 ** (2 * rate) / n / 1000
    c = float(f['eps_ppk']) * k
    sd = 1000 * float(f['travel_rms']) / float(f['form_rms']) / math.sqrt(int(f['entries'])) * k
    travel = float(f['travel_rms']) / 2 ** grain
    print(f"C lap={f['lap']} lane={f['lane']} {f['block']:17s} {f['contacts']:3s} {f['role']:6s} n={int(f['entries']):5d} rms={rms:7.4f} "
          f"travel={travel:.5f} free={travel / (2.0 ** -rate * math.sqrt(n)):5.3f} turn={100 * travel / rms:5.2f}% rho={float(f['rho']):+.3f} "
          f"eps_ppk={float(f['eps_ppk']):+8.3f} c={c:+7.2f} sd={sd:5.2f}")

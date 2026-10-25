# The held-out text's code by medium: each AT line (cell, class, next class, code on 2^-20 of a bit)
# is counted under the medium of the byte it predicts (dev.roles: one role a byte, 0 prose, 1 lean,
# 2 rust, 3 arithmetic). Usage: DEV_BY_MEDIUM.py ROLES READ...
import sys
roles = open(sys.argv[1], 'rb').read()
names = ['prose', 'lean', 'rust', 'arithmetic']
for path in sys.argv[2:]:
    bits, cells = [0] * 4, [0] * 4
    for line in open(path):
        if line.startswith('AT '):
            _, t, _, _, code = line.split()
            m = roles[int(t) + 1]
            bits[m] += int(code); cells[m] += 1
    whole = sum(bits) / 2**20 / sum(cells)
    print(path, ' '.join(f'{names[m]}={bits[m] / 2**20 / cells[m]:.3f}' for m in range(4)), f'whole={whole:.3f}')

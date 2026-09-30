"""Parse the bank_causes dumps (exact rationals) into numpy (exterior probe)."""
from fractions import Fraction
import numpy as np


def rat(s):
    return float(Fraction(s))


def parse_read(path):
    lines = open(path).read().split('\n')
    i = 0
    out = {'requests': [], 'exact': []}
    assert lines[0].startswith('E ')
    rows, cols = map(int, lines[0].split()[1:])
    out['E_real_exact'] = [[Fraction(x) for x in lines[1 + r].split()] for r in range(rows)]
    out['E_real'] = np.array([[float(x) for x in row] for row in out['E_real_exact']])
    i = 1 + rows
    out['nu'] = {}
    cur = None
    while i < len(lines):
        ln = lines[i]
        if ln.startswith('nu '):
            _, n, v = ln.split()
            out['nu'][int(n)] = Fraction(v)
        elif ln.startswith('request '):
            head, rest = ln.split(' [', 1)
            req, tgt = rest.split('] [')
            cur = {
                'request': [int(x) for x in req.split(',')],
                'target': [int(x) for x in tgt.rstrip(']').split(',')],
                'images': {},
            }
            out['requests'].append(cur)
        elif ln.startswith('base '):
            cur['base'] = np.array([rat(x) for x in ln.split()[1:]])
        elif ln.startswith('image '):
            parts = ln.split()
            cur['images'][(int(parts[1]), int(parts[2]))] = np.array([rat(x) for x in parts[3:]])
        elif ln.startswith('exact '):
            left, storage = ln.split(' | ')[:-1], ln.split(' | ')[-1]
            head = ln.split(' | ')[0].split()
            label, cls = head[1], int(head[2])
            members = [(Fraction(head[3]), Fraction(head[4]))]
            for seg in ln.split(' | ')[1:-1]:
                a, b = seg.split()
                members.append((Fraction(a), Fraction(b)))
            out['exact'].append({'label': label, 'class': cls, 'members': members,
                                 'storage': np.array([rat(x) for x in storage.split()])})
        i += 1
    return out


def to_complex(real_vec):
    return real_vec[0::2] + 1j * real_vec[1::2]


def turn(storage_real):
    z = to_complex(storage_real)
    d = len(z)
    return np.array([z[d - 1 - t] for t in range(d)])


def parse_learn(path):
    lines = open(path).read().split('\n')
    Es = []
    train = []
    i = 0
    while i < len(lines):
        ln = lines[i]
        if ln.startswith('E '):
            rows, cols = map(int, ln.split()[1:])
            exact = [[Fraction(x) for x in lines[i + 1 + r].split()] for r in range(rows)]
            real = np.array([[float(x) for x in row] for row in exact])
            Es.append((real[0::2] + 1j * real[1::2], exact))
            i += 1 + rows
            continue
        if ln.startswith('train '):
            rest = ln[len('train ['):]
            req, tgt = rest.split('] [')
            train.append(([int(x) for x in req.split(',')], [int(x) for x in tgt.rstrip(']').split(',')]))
        i += 1
    return Es, train

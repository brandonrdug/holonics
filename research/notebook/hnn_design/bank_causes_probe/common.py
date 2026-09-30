import os
import sys
import time
import resource
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from model import *

DIR = os.environ.get('BANK_CAUSES_DIR', os.path.dirname(os.path.abspath(__file__)))
P = 5 / 8


def peak_bytes():
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024


def decisions(pairs, mode, rng=None):
    """The station decisions of a set of pairs: (request, placed dict, station, target).
    mode 'open': nothing locked (generation's first refinement, every station);
    'causal': stations < j placed at their truth;
    'partition': a drawn partition (each station locked with probability 1/2), the unlocked compared."""
    out = []
    for req, tgt in pairs:
        if mode == 'open':
            for j in range(M_ST):
                out.append((req, {}, j, tgt[j]))
        elif mode == 'causal':
            for j in range(M_ST):
                out.append((req, {i: tgt[i] for i in range(j)}, j, tgt[j]))
        elif mode == 'first2':
            for j in range(2):
                out.append((req, {}, j, tgt[j]))
        elif mode == 'partition':
            locked = rng.integers(0, 2, M_ST).astype(bool)
            if locked.all():
                locked[rng.integers(0, M_ST)] = False
            placed = {i: tgt[i] for i in range(M_ST) if locked[i]}
            for j in range(M_ST):
                if not locked[j]:
                    out.append((req, placed, j, tgt[j]))
    return out


def counts_of(decs):
    """C (B*5, D, X) for every candidate of every decision, and targets."""
    Cs = np.concatenate([candidates_counts(req, placed, j) for req, placed, j, _ in decs])
    targets = np.array([t for *_, t in decs])
    return Cs, targets


def read(Cs, E, p=P, grad=False, want_face=False):
    z = to_turn(storage_nodes(Cs, E))
    a, G, members, cert = joint_growth(z, p, want_grad=grad)
    out = {'a': a.reshape(-1, CLASSES), 'members': members.reshape(-1, CLASSES, 4),
           'cert': cert.reshape(-1, CLASSES)}
    if grad:
        # per-candidate E-gradient: G_node = reversed turn gradient
        G_node = G[:, ::-1]
        FC = np.fft.fft(Cs, axis=1)
        FG = np.fft.fft(G_node, axis=1)
        GE = np.fft.ifft(np.conj(FC) * FG[:, :, None], axis=1)   # (B, D, X)
        out['GE'] = GE.reshape(-1, CLASSES, D, CLASSES)
    if want_face:
        A, GA = face(z, p, want_grad=grad)
        out['A'] = A.reshape(-1, CLASSES)
        if grad:
            G_node = GA[:, ::-1]
            FC = np.fft.fft(Cs, axis=1)
            FG = np.fft.fft(G_node, axis=1)
            out['GA'] = np.fft.ifft(np.conj(FC) * FG[:, :, None], axis=1).reshape(-1, CLASSES, D, CLASSES)
    return out


def inner(G, dE):
    """Re sum conj(G) dE over the last two axes."""
    return (np.conj(G) * dE).real.sum(axis=(-2, -1))


def dy(x, grain=16):
    """A dyadic reading at grain 2^-g: floor(x*2^g)/2^g with its cell, for reporting."""
    from fractions import Fraction
    import math
    if not np.isfinite(x):
        return 'inf'
    n = math.floor(x * (1 << grain))
    return str(Fraction(n, 1 << grain)) + '+[0,2^-%d)' % grain


def log2cell(x):
    import math
    if x <= 0:
        return 'nonpositive'
    k = math.floor(math.log2(x))
    return '[2^%d, 2^%d)' % (k, k + 1)

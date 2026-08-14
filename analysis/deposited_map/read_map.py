"""The deposited map, read by Ratio and Winding.

Record:
  research/records/2026-08-13_THE_DEPOSITED_MAP_IS_READ_BY_RATIO_AND_WINDING_THE_ARCHETYPE_IS_A_FINITE_TYPE_WITH_INFINITE_MODULI.md
Roadmap:
  blueprint/THE_ROADMAP.md, "THE DEPOSITED MAP".

EXTERIOR INSTRUMENT. This is not part of the body. It reads foreign material (a pretrained
weight file) and returns receiver faces of it. The mouth is exact -- bf16 is exactly a dyadic
rational -- and the spectral arithmetic below is declared floating-point apparatus, never a
carrier. Nothing here is imported by any crate under soma/ or crates/.

THE MODEL IS NEVER RUN. Every quantity is per-head or per-matrix, streamed by mmap, peak
residency one circuit. That is the requirement that makes the method transfer to a model this
hardware cannot load.

THE READING LAW (horizon law): across a frame boundary only a Ratio (dimensionless invariant)
or an integer Winding (a count) survives. Magnitudes do not. RMSNorm is that horizon in this
architecture. Admitted here: projectivised spectra, principal angles, sym/antisym ratios,
integer winding counts, rank. Refused: norms, condition numbers, raw eigenvalue magnitudes,
cosine similarity.
"""
import json
import mmap
import struct

import numpy as np

MODEL = "/home/b/models/gemma-4-E4B-it/model.safetensors"
CONFIG = "/home/b/models/gemma-4-E4B-it/config.json"
TOKENIZER = "/home/b/models/gemma-4-E4B-it/tokenizer.json"


class Map:
    """Streaming reader over the deposited map. Never loads the whole file."""

    def __init__(self, path=MODEL):
        self.f = open(path, "rb")
        n = struct.unpack("<Q", self.f.read(8))[0]
        self.header = json.loads(self.f.read(n))
        self.header.pop("__metadata__", None)
        self.base = 8 + n
        self.mm = mmap.mmap(self.f.fileno(), 0, access=mmap.ACCESS_READ)
        self.cfg = json.load(open(CONFIG))
        self.text = self.cfg["text_config"]

    def take(self, name):
        """One tensor as f32. bf16 -> f32 is a bit-shift widening: exact, not a conversion."""
        e = self.header[name]
        a, b = e["data_offsets"]
        assert e["dtype"] == "BF16", e["dtype"]
        w = np.frombuffer(self.mm[self.base + a : self.base + b], dtype="<u2")
        return (w.astype("<u4") << 16).view("<f4").reshape(e["shape"])

    def rows(self, name, ids):
        """Selected rows of a big matrix, without materialising the matrix."""
        e = self.header[name]
        a, _ = e["data_offsets"]
        V, D = e["shape"]
        out = np.empty((len(ids), D), dtype=np.float32)
        for i, t in enumerate(ids):
            off = self.base + a + t * D * 2
            w = np.frombuffer(self.mm[off : off + D * 2], dtype="<u2")
            out[i] = (w.astype("<u4") << 16).view("<f4")
        return out

    def layer_species(self):
        return self.text["layer_types"]

    # --- the two composed circuits, per head -------------------------------
    def ov(self, layer, head):
        """W_OV = W_O W_V restricted to one head: an endomorphism of the bus.

        Its spectrum is invariant under ANY conjugation, hence under the residual gauge.
        """
        v = self.take(f"model.language_model.layers.{layer}.self_attn.v_proj.weight")
        o = self.take(f"model.language_model.layers.{layer}.self_attn.o_proj.weight")
        d = self.text["global_head_dim"] if self.layer_species()[layer] == "full_attention" else self.text["head_dim"]
        nq = self.text["num_attention_heads"]
        nkv = self.text["num_key_value_heads"]
        g = head // (nq // nkv)  # GQA: this head's KV group
        Wv = v[g * d : (g + 1) * d, :]  # [d, bus]
        Wo = o[:, head * d : (head + 1) * d]  # [bus, d]
        return Wo, Wv  # composed lazily; W_OV = Wo @ Wv

    def qk(self, layer, head):
        """W_QK = W_Q^T W_K: a bilinear form on the bus, returned in factored form."""
        q = self.take(f"model.language_model.layers.{layer}.self_attn.q_proj.weight")
        k = self.take(f"model.language_model.layers.{layer}.self_attn.k_proj.weight")
        d = self.text["global_head_dim"] if self.layer_species()[layer] == "full_attention" else self.text["head_dim"]
        nq = self.text["num_attention_heads"]
        nkv = self.text["num_key_value_heads"]
        g = head // (nq // nkv)
        return q[head * d : (head + 1) * d, :], k[g * d : (g + 1) * d, :]


# --- admitted observables --------------------------------------------------
# Every function here returns a Ratio or a Winding. None returns a magnitude.


def projectivised_spectrum(evals, keep=None):
    """Eigenvalues divided by the largest modulus: a Ratio. Overall scale is a Rank and is
    discarded at the horizon, so it must not appear in the return."""
    m = np.abs(evals)
    top = m.max()
    if top == 0:
        return np.zeros_like(evals)
    z = evals / top
    order = np.argsort(-np.abs(z))
    z = z[order]
    return z if keep is None else z[:keep]


def winding_census(evals, tol=1e-9):
    """The Winding face: how many conjugate pairs, and their turns.

    A real eigenvalue carries no turn. A conjugate pair carries a turn +-theta. This is the
    'name the windings, do not count the signs' obligation (CLAUDE.md 2b).
    """
    im = np.abs(evals.imag)
    scale = max(np.abs(evals).max(), 1e-30)
    pairs = evals[(im > tol * scale) & (evals.imag > 0)]
    turns = np.angle(pairs)
    neg_real = int(np.sum((im <= tol * scale) & (evals.real < 0)))
    pos_real = int(np.sum((im <= tol * scale) & (evals.real > 0)))
    return {
        "conjugate_pairs": int(pairs.size),
        "real_positive": pos_real,
        "real_negative": neg_real,  # each is a half turn, pi
        "turns": np.sort(turns),
    }


def sym_antisym_ratio(M):
    """||antisym|| / ||sym|| of a bilinear form: a Ratio (both parts share the frame, so the
    quotient is dimensionless and survives the horizon). O-type vs Sp-type character."""
    S = 0.5 * (M + M.T)
    A = 0.5 * (M - M.T)
    ns, na = np.linalg.norm(S), np.linalg.norm(A)
    return float(na / ns) if ns > 0 else float("inf")


def principal_angles(A, B, k=None):
    """Principal angles between the column spaces of A and B: Ratios (pure angles)."""
    Qa, _ = np.linalg.qr(A)
    Qb, _ = np.linalg.qr(B)
    s = np.linalg.svd(Qa.T @ Qb, compute_uv=False)
    s = np.clip(s, -1.0, 1.0)
    a = np.arccos(s)
    return a if k is None else a[:k]


def participation_ratio(s):
    """(sum s^2)^2 / sum s^4 -- a dimensionless effective-rank Ratio, scale-free by
    construction. Not a norm: multiplying s by any constant leaves it unchanged."""
    s2 = s.astype(np.float64) ** 2
    return float(s2.sum() ** 2 / (s2**2).sum())


def probe_ids(names):
    t = json.load(open(TOKENIZER))
    v = t["model"]["vocab"]
    out, missing = {}, []
    for n in names:
        if n in v:
            out[n] = v[n]
        else:
            missing.append(n)
    return out, missing

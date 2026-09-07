#include <metal_stdlib>
using namespace metal;

// Exact Apple realization of the local phase relation.  `W` is a signed 128-bit
// carrier represented by four little-endian u32 limbs.  The public wire remains
// signed i64; values which cannot be returned to that wire refuse the operation.
constant uint REFUSED_CARRIER = 1u;
constant uint REFUSED_MALFORMED = 2u;
constant uint REFUSED_INVERTED = 4u;
constant uint REFUSED_UPSTREAM = 8u;
constant uint REFUSED_BOUND = 16u;
constant uint SLOT_WORDS = 16u, SLOT_REFUSED = 0u, SLOT_REACH = 1u, SLOT_WRITTEN = 2u;
constant uint SLOT_INVERTED = 3u, SLOT_OCTAVE = 4u, SLOT_BOUND = 5u, SLOT_WIDTH = 6u;
constant uint SLOT_WIDTH_SUM = 12u, SLOT_NONZERO_WIDTHS = 14u, SLOT_UPSTREAM_FLAGS = 8u,
              SLOT_UPSTREAM_FIRST = 9u, SLOT_UPSTREAM_COUNT = 10u, SLOT_LINEAGE = 11u;

struct U {
  uint x[4];
};
struct W {
  U m;
  bool neg;
};

inline U uzero() {
  U a;
  a.x[0] = a.x[1] = a.x[2] = a.x[3] = 0;
  return a;
}
inline U uone() {
  U a = uzero();
  a.x[0] = 1;
  return a;
}
inline bool uzero_p(U a) { return !(a.x[0] | a.x[1] | a.x[2] | a.x[3]); }
inline bool ueq(U a, U b) {
  return a.x[0] == b.x[0] && a.x[1] == b.x[1] && a.x[2] == b.x[2] && a.x[3] == b.x[3];
}
inline bool ult(U a, U b) {
  for (int i = 3; i >= 0; --i) {
    if (a.x[i] != b.x[i])
      return a.x[i] < b.x[i];
  }
  return false;
}
inline U uadd(U a, U b, thread bool &ov) {
  U c;
  ulong carry = 0;
  for (uint i = 0; i < 4; ++i) {
    ulong z = (ulong)a.x[i] + b.x[i] + carry;
    c.x[i] = (uint)z;
    carry = z >> 32;
  }
  ov = carry != 0;
  return c;
}
inline U usub(U a, U b, thread bool &ov) {
  U c;
  ulong borrow = 0;
  for (uint i = 0; i < 4; ++i) {
    ulong ai = a.x[i], bi = (ulong)b.x[i] + borrow;
    c.x[i] = (uint)(ai - bi);
    borrow = ai < bi;
  }
  ov = borrow != 0;
  return c;
}
inline U ushl1(U a, thread bool &ov) {
  U c;
  uint carry = 0;
  for (uint i = 0; i < 4; ++i) {
    ulong z = ((ulong)a.x[i] << 1) | carry;
    c.x[i] = (uint)z;
    carry = (uint)(z >> 32);
  }
  ov = carry != 0;
  return c;
}
inline U ushr1(U a) {
  U c;
  uint carry = 0;
  for (int i = 3; i >= 0; --i) {
    c.x[i] = (a.x[i] >> 1) | (carry << 31);
    carry = a.x[i] & 1;
  }
  return c;
}
inline U umag(long v) {
  ulong q = v < 0 ? (ulong)0 - (ulong)v : (ulong)v;
  U a = uzero();
  a.x[0] = (uint)q;
  a.x[1] = (uint)(q >> 32);
  return a;
}
inline W wzero() {
  W a;
  a.m = uzero();
  a.neg = false;
  return a;
}
inline W wof(U m, bool neg, device uint *slot) {
  W a;
  a.m = m;
  a.neg = neg && !uzero_p(m);
  if ((m.x[3] & 0x80000000u)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER, memory_order_relaxed);
    return wzero();
  }
  return a;
}
inline W wi64(long v) {
  W a;
  a.m = umag(v);
  a.neg = v < 0 && !uzero_p(a.m);
  return a;
}
inline bool wzero_p(W a) { return uzero_p(a.m); }
inline bool wneg_p(W a) { return a.neg && !wzero_p(a); }
inline W wneg(W a) {
  if (!wzero_p(a))
    a.neg = !a.neg;
  return a;
}
inline W wadd(W a, W b, device uint *slot) {
  if (a.neg == b.neg) {
    bool ov;
    U m = uadd(a.m, b.m, ov);
    if (ov) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER, memory_order_relaxed);
      return wzero();
    }
    return wof(m, a.neg, slot);
  }
  bool ov;
  if (ult(a.m, b.m))
    return wof(usub(b.m, a.m, ov), b.neg, slot);
  return wof(usub(a.m, b.m, ov), a.neg, slot);
}
inline W wsub(W a, W b, device uint *slot) { return wadd(a, wneg(b), slot); }
inline uint ubit(U a, uint n) { return (a.x[n >> 5] >> (n & 31)) & 1u; }
inline U uset(U a, uint n) {
  a.x[n >> 5] |= 1u << (n & 31);
  return a;
}
inline U umul(U a, U b, thread bool &ov) {
  // Exact one-limb product: (2^32-1)^2 fits in ulong. This is a carrier
  // specialization, not a different field law or a truncated product.
  if (!(a.x[1] | a.x[2] | a.x[3] | b.x[1] | b.x[2] | b.x[3])) {
    ulong product = (ulong)a.x[0] * (ulong)b.x[0];
    U r = uzero();
    r.x[0] = (uint)product;
    r.x[1] = (uint)(product >> 32);
    ov = false;
    return r;
  }
  uint p[8] = {0, 0, 0, 0, 0, 0, 0, 0};
  for (uint i = 0; i < 4; ++i) {
    ulong carry = 0;
    for (uint j = 0; j < 4; ++j) {
      // (2^32-1)^2 + (2^32-1) + (2^32-1) = 2^64-1: no intermediate wraps.
      ulong z = (ulong)a.x[i] * (ulong)b.x[j] + (ulong)p[i + j] + carry;
      p[i + j] = (uint)z;
      carry = z >> 32;
    }
    for (uint k = i + 4; carry != 0 && k < 8; ++k) {
      ulong z = (ulong)p[k] + carry;
      p[k] = (uint)z;
      carry = z >> 32;
    }
  }
  ov = (p[4] | p[5] | p[6] | p[7]) != 0;
  U r = uzero();
  r.x[0] = p[0]; r.x[1] = p[1]; r.x[2] = p[2]; r.x[3] = p[3];
  return r;
}
inline W wmul(W a, W b, device uint *slot) {
  if (wzero_p(a) || wzero_p(b))
    return wzero();
  bool ov;
  U m = umul(a.m, b.m, ov);
  if (ov) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER, memory_order_relaxed);
    return wzero();
  }
  return wof(m, a.neg != b.neg, slot);
}
inline U udiv(U n, U d, thread U &rem) {
  // Callers have already established d != 0. Avoid emulated wider division
  // when both complete magnitudes inhabit the native uint chart.
  if (!(n.x[1] | n.x[2] | n.x[3] | d.x[1] | d.x[2] | d.x[3])) {
    U q = uzero();
    q.x[0] = n.x[0] / d.x[0];
    rem = uzero();
    rem.x[0] = n.x[0] % d.x[0];
    return q;
  }
  if (n.x[2] == 0 && n.x[3] == 0 && d.x[2] == 0 && d.x[3] == 0) {
    ulong nn = (ulong)n.x[0] | ((ulong)n.x[1] << 32);
    ulong dd = (ulong)d.x[0] | ((ulong)d.x[1] << 32);
    ulong qq = nn / dd;
    ulong rr = nn % dd;
    U q = uzero();
    q.x[0] = (uint)qq; q.x[1] = (uint)(qq >> 32);
    rem = uzero();
    rem.x[0] = (uint)rr; rem.x[1] = (uint)(rr >> 32);
    return q;
  }
  U q = uzero();
  rem = uzero();
  for (int i = 127; i >= 0; --i) {
    bool ov;
    rem = ushl1(rem, ov);
    if (ubit(n, (uint)i))
      rem = uset(rem, 0);
    if (!ult(rem, d)) {
      rem = usub(rem, d, ov);
      q = uset(q, (uint)i);
    }
  }
  return q;
}
inline W wdiv(W n, W d, device uint *slot) {
  if (wzero_p(d)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return wzero();
  }
  U r;
  U q = udiv(n.m, d.m, r);
  return wof(q, n.neg != d.neg, slot);
}
inline W wgcd(W a, W b, device uint *slot) {
  a.neg = false;
  b.neg = false;
  while (!wzero_p(b)) {
    U r;
    udiv(a.m, b.m, r);
    a.m = b.m;
    b.m = r;
  }
  return a;
}
inline W wnorm(thread W *row, uint width, thread W *den, device uint *slot) {
  W d = den ? (!wzero_p(*den) ? *den : wzero()) : wzero();
  for (uint j = 0; j < width && !ueq(d.m, uone()); ++j)
    d = wgcd(d, row[j], slot);
  if (wzero_p(d) || ueq(d.m, uone()))
    return d;
  for (uint j = 0; j < width; ++j)
    row[j] = wdiv(row[j], d, slot);
  if (den)
    *den = wdiv(*den, d, slot);
  return d;
}
inline W wnorm(threadgroup W *row, uint width, threadgroup W *den, device uint *slot) {
  W d = den ? (!wzero_p(*den) ? *den : wzero()) : wzero();
  for (uint j = 0; j < width && !ueq(d.m, uone()); ++j)
    d = wgcd(d, row[j], slot);
  if (wzero_p(d) || ueq(d.m, uone()))
    return d;
  for (uint j = 0; j < width; ++j)
    row[j] = wdiv(row[j], d, slot);
  if (den)
    *den = wdiv(*den, d, slot);
  return d;
}
inline W wnorm(threadgroup W *row, uint width, thread W *den, device uint *slot) {
  W d = den ? (!wzero_p(*den) ? *den : wzero()) : wzero();
  for (uint j = 0; j < width && !ueq(d.m, uone()); ++j) d = wgcd(d, row[j], slot);
  if (wzero_p(d) || ueq(d.m, uone())) return d;
  for (uint j = 0; j < width; ++j) row[j] = wdiv(row[j], d, slot);
  if (den) *den = wdiv(*den, d, slot);
  return d;
}
inline long toword(W a, device uint *slot) {
  if (a.m.x[2] || a.m.x[3] || (a.m.x[1] == 0x80000000u && a.m.x[0] != 0) ||
      (a.m.x[1] == 0x80000000u && !a.neg) || (a.m.x[1] > 0x80000000u)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER, memory_order_relaxed);
    return 0;
  }
  ulong q = (ulong)a.m.x[0] | ((ulong)a.m.x[1] << 32);
  // Unsigned subtraction preserves the admitted i64 minimum without signed overflow.
  return as_type<long>(a.neg ? (ulong)0 - q : q);
}
inline W fromword(long v) { return wi64(v); }
inline W fibre_entry(device const long *basis, uint width, uint row, uint col,
                     threadgroup const W *staged, long pivot) {
  return (long)row == pivot ? staged[col] : fromword(basis[(ulong)row * width + col]);
}
inline void fibre_query(device const long *basis, uint source_width, uint width,
                        threadgroup W *query, threadgroup W *den, threadgroup const W *staged,
                        long staged_pivot, thread uint *disp, thread uint *rank,
                        device uint *slot) {
  uint vertical = 0;
  *rank = 0;
  for (uint p = 0; p < width; ++p) {
    W pivot = fibre_entry(basis, width, p, p, staged, staged_pivot);
    if (wneg_p(pivot)) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
      return;
    }
    if (!wzero_p(pivot)) {
      ++*rank;
      if (p >= source_width)
        ++vertical;
    }
    if (p >= source_width || wzero_p(pivot) || wzero_p(query[p]))
      continue;
    W coefficient = query[p];
    for (uint j = 0; j < width; ++j)
      query[j] = wsub(
          wmul(pivot, query[j], slot),
          wmul(coefficient, fibre_entry(basis, width, p, j, staged, staged_pivot), slot), slot);
    *den = wmul(*den, pivot, slot);
    if (*slot)
      return;
    wnorm(query, width, den, slot);
    if (*slot)
      return;
  }
  *disp = vertical ? 2u : 0u;
  for (uint j = 0; j < source_width; ++j)
    if (!wzero_p(query[j]))
      *disp = 1u;
}
inline void fibre_query(device const long *basis, uint source_width, uint width,
                        threadgroup W *query, thread W *den, threadgroup const W *staged,
                        long staged_pivot, thread uint *disp, thread uint *rank,
                        device uint *slot) {
  uint vertical = 0; *rank = 0;
  for (uint p = 0; p < width; ++p) {
    W pivot = fibre_entry(basis, width, p, p, staged, staged_pivot);
    if (wneg_p(pivot)) { atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed); return; }
    if (!wzero_p(pivot)) { ++*rank; if (p >= source_width) ++vertical; }
    if (p >= source_width || wzero_p(pivot) || wzero_p(query[p])) continue;
    W coefficient = query[p];
    for (uint j = 0; j < width; ++j)
      query[j] = wsub(wmul(pivot, query[j], slot), wmul(coefficient, fibre_entry(basis,width,p,j,staged,staged_pivot),slot),slot);
    *den = wmul(*den, pivot, slot); if (*slot) return;
    wnorm(query, width, den, slot); if (*slot) return;
  }
  *disp = vertical ? 2u : 0u; for (uint j=0;j<source_width;++j) if(!wzero_p(query[j])) *disp=1u;
}
inline long fibre_stage(device const long *basis, uint width, thread W *formed, device uint *slot) {
  long inserted = -1;
  for (uint p = 0; p < width; ++p) {
    if (wzero_p(formed[p]))
      continue;
    long pivot = basis[(ulong)p * width + p];
    if (!pivot) {
      inserted = (long)p;
      break;
    }
    W pv = fromword(pivot), co = formed[p];
    for (uint j = 0; j < width; ++j)
      formed[j] = wsub(wmul(pv, formed[j], slot),
                       wmul(co, fromword(basis[(ulong)p * width + j]), slot), slot);
    if (*slot)
      return -1;
    wnorm(formed, width, (thread W *)nullptr, slot);
    if (*slot)
      return -1;
  }
  if (inserted >= 0) {
    wnorm(formed, width, (thread W *)nullptr, slot);
    if (*slot)
      return -1;
    if (wneg_p(formed[inserted]))
      for (uint j = 0; j < width; ++j)
        formed[j] = wneg(formed[j]);
  }
  return inserted;
}
inline long fibre_stage(device const long *basis, uint width, threadgroup W *formed,
                        device uint *slot) {
  long inserted = -1;
  for (uint p = 0; p < width; ++p) {
    if (wzero_p(formed[p]))
      continue;
    long pivot = basis[(ulong)p * width + p];
    if (!pivot) {
      inserted = (long)p;
      break;
    }
    W pv = fromword(pivot), co = formed[p];
    for (uint j = 0; j < width; ++j)
      formed[j] = wsub(wmul(pv, formed[j], slot),
                       wmul(co, fromword(basis[(ulong)p * width + j]), slot), slot);
    if (*slot)
      return -1;
    wnorm(formed, width, (threadgroup W *)nullptr, slot);
    if (*slot)
      return -1;
  }
  if (inserted >= 0) {
    wnorm(formed, width, (threadgroup W *)nullptr, slot);
    if (*slot)
      return -1;
    if (wneg_p(formed[inserted]))
      for (uint j = 0; j < width; ++j)
        formed[j] = wneg(formed[j]);
  }
  return inserted;
}
inline W flcm(W a, W b, device uint *slot) {
  if (wneg_p(a) || wneg_p(b) || wzero_p(a) || wzero_p(b)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return wi64(1);
  }
  W g = wgcd(a, b, slot);
  return wmul(wdiv(a, g, slot), b, slot);
}
inline void phaseprod(W ar, W ai, W ad, W br, W bi, W bd, thread W *o, device uint *slot) {
  if (wneg_p(ad) || wzero_p(ad) || wneg_p(bd) || wzero_p(bd)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  o[0] = wsub(wmul(ar, br, slot), wmul(ai, bi, slot), slot);
  o[1] = wadd(wmul(ai, br, slot), wmul(ar, bi, slot), slot);
  o[2] = wmul(ad, bd, slot);
  wnorm(o, 2, &o[2], slot);
}
inline void phaseprod(W ar, W ai, W ad, W br, W bi, W bd, threadgroup W *o, device uint *slot) {
  if (wneg_p(ad) || wzero_p(ad) || wneg_p(bd) || wzero_p(bd)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  o[0] = wsub(wmul(ar, br, slot), wmul(ai, bi, slot), slot);
  o[1] = wadd(wmul(ai, br, slot), wmul(ar, bi, slot), slot);
  o[2] = wmul(ad, bd, slot);
  wnorm(o, 2, &o[2], slot);
}
inline bool upstream(device const uint *census, device const uint *lineage, uint count,
                     device uint *slot) {
  uint f = 0, first = 0, n = 0;
  for (uint i = 0; i < count; ++i) {
    uint p = lineage[i], pf = census[(ulong)p * SLOT_WORDS + SLOT_REFUSED];
    if (pf) {
      f |= pf;
      if (!first || p < first - 1)
        first = p + 1;
      ++n;
    }
  }
  if (count) {
    slot[SLOT_LINEAGE] = count;
    slot[SLOT_UPSTREAM_FLAGS] = f;
    slot[SLOT_UPSTREAM_FIRST] = first;
    slot[SLOT_UPSTREAM_COUNT] = n;
  }
  if (f) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_UPSTREAM, memory_order_relaxed);
    return true;
  }
  return false;
}
inline uint octword(long v) {
  U m = umag(v);
  for (int i = 3; i >= 0; --i)
    if (m.x[i]) {
      uint x = m.x[i], n = 0;
      while (x) {
        x >>= 1;
        ++n;
      }
      return (uint)i * 32 + n;
    }
  return 0;
}
inline void census_serial_impl(device const long *lo, device const long *hi, uint count,
                               uint admitted, device uint *slot, uint3 tid) {
  if (tid.x || tid.y || tid.z)
    return;
  if (*slot != 0u) {
    if (count > 0)
      slot[SLOT_WRITTEN] = 1u;
    return;
  }
  uint oct = 0, inv = 0, bnd = 0;
  ulong maxw = 0, sum = 0, nz = 0;
  for (uint i = 0; i < count; ++i) {
    long a = lo[i], b = hi[i];
    uint oa = octword(a), ob = octword(b);
    if (oa > oct)
      oct = oa;
    if (ob > oct)
      oct = ob;
    if (b >= a) {
      ulong wa = (ulong)a, wb = (ulong)b, w = wb - wa;
      if (w > maxw)
        maxw = w;
      sum += w;
      if (w)
        ++nz;
    } else
      inv = 1;
    if (oct > admitted || oa > admitted || ob > admitted)
      bnd = 1;
  }
  if (oct)
    atomic_fetch_max_explicit((device atomic_uint *)(slot + SLOT_OCTAVE), oct,
                              memory_order_relaxed);
  device ulong *u = (device ulong *)slot;
  if (maxw > u[3])
    u[3] = maxw;
  if (sum)
    u[6] += sum;
  if (nz)
    atomic_fetch_add_explicit((device atomic_uint *)(slot + SLOT_NONZERO_WIDTHS), (uint)nz,
                              memory_order_relaxed);
  if (inv) {
    atomic_fetch_or_explicit((device atomic_uint *)(slot + SLOT_INVERTED), 1u,
                             memory_order_relaxed);
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_INVERTED, memory_order_relaxed);
  }
  if (bnd) {
    atomic_fetch_or_explicit((device atomic_uint *)(slot + SLOT_BOUND), 1u, memory_order_relaxed);
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_BOUND, memory_order_relaxed);
  }
  if (count > 0)
    slot[SLOT_WRITTEN] = 1u;
}

// Standalone arithmetic witness used by the Apple apparatus harness. It is excluded from
// production libraries; the experiment compiles this source with HOLONICS_ARITHMETIC_PROBE.
#ifdef HOLONICS_ARITHMETIC_PROBE
kernel void native_phase_arithmetic_probe(device const long *a [[buffer(0)]],
                                          device const long *b [[buffer(1)]],
                                          device long *out [[buffer(2)]],
                                          device uint *refused [[buffer(3)]],
                                          uint3 tid [[thread_position_in_grid]]) {
  if (tid.x || tid.y || tid.z)
    return;
  W x = fromword(a[0]), y = fromword(b[0]);
  out[0] = toword(wadd(x, y, refused), refused);
  out[1] = toword(wmul(fromword(a[1]), fromword(b[1]), refused), refused);
  out[2] = toword(wgcd(fromword(a[2]), fromword(b[2]), refused), refused);
  out[3] = toword(wdiv(fromword(a[3]), fromword(b[3]), refused), refused);
  out[4] = toword(wneg(fromword(a[4])), refused);
}

kernel void native_phase_wide_probe(device const uint *a [[buffer(0)]],
                                    device const uint *b [[buffer(1)]],
                                    device uint *out [[buffer(2)]],
                                    device uint *refused [[buffer(3)]],
                                    uint3 tid [[thread_position_in_grid]]) {
  if (tid.x || tid.y || tid.z)
    return;
  U ua, ub;
  for (uint i = 0; i < 4; ++i) {
    ua.x[i] = a[i];
    ub.x[i] = b[i];
  }
  W x = wof(ua, false, refused), y = wof(ub, false, refused);
  W p = wmul(x, y, refused), g = wgcd(x, y, refused), q = wdiv(x, y, refused);
  for (uint i = 0; i < 4; ++i) {
    out[i] = p.m.x[i];
    out[4 + i] = g.m.x[i];
    out[8 + i] = q.m.x[i];
  }
}
#endif

// Complete multi-port field recurrence.  The field uses four source coordinates per node
// (outgoing and held complex branches) followed by the two-coordinate target face.  All
// intermediates remain W until the checked exterior conversion at the commit boundary.
kernel void section_constitutive_field(
    device const long *seed [[buffer(0)]], device long *memory_lo [[buffer(1)]],
    device long *memory_hi [[buffer(2)]], device long *basis_lo [[buffer(3)]],
    device long *basis_hi [[buffer(4)]], device const long *incoming [[buffer(5)]],
    device const long *origin [[buffer(6)]], device const long *current_frame [[buffer(7)]],
    device const long *origin_frame [[buffer(8)]], constant uint &nodes [[buffer(9)]],
    constant uint &linked [[buffer(10)]], device long *output_lo [[buffer(11)]],
    device long *output_hi [[buffer(12)]], device uint *slot [[buffer(13)]],
    device const uint *census [[buffer(14)]], device const uint *lineage [[buffer(15)]],
    constant uint &lineage_count [[buffer(16)]], threadgroup W *scratch [[threadgroup(0)]],
    uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  if (!nodes || linked > 1 || nodes > 0xffffffffu / 6u) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  uint sw = 4u * nodes, width = 6u * nodes;
  if (width < sw || !current_frame || (linked && (!origin || !origin_frame))) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  for (uint n = 0; n < nodes; ++n) {
    device const long *f = current_frame + 3u * n;
    W lhs = wadd(wmul(fromword(f[0]), fromword(f[0]), slot),
                 wmul(fromword(f[1]), fromword(f[1]), slot), slot);
    W rhs = wmul(fromword(f[2]), fromword(f[2]), slot);
    if (f[2] <= 0 || *slot || !ueq(lhs.m, rhs.m)) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
      return;
    }
    if (linked) {
      device const long *b = origin_frame + 3u * n;
      W bl = wadd(wmul(fromword(b[0]), fromword(b[0]), slot),
                  wmul(fromword(b[1]), fromword(b[1]), slot), slot),
        br = wmul(fromword(b[2]), fromword(b[2]), slot);
      if (b[2] <= 0 || *slot || !ueq(bl.m, br.m)) {
        atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                                 memory_order_relaxed);
        return;
      }
    }
  }
  threadgroup W *cur = scratch, *prior = cur + width, *formed = prior + width;
  threadgroup W *out = formed + width, *held = out + 3u * nodes;
  for (uint j = 0; j < width; ++j) {
    cur[j] = prior[j] = formed[j] = wzero();
  }
  W incoming_den = wi64(1);
  for (uint n = 0; n < nodes; ++n) {
    device const long *law = seed + 5u * n, *mem = memory_lo + 3u * n, *arr = incoming + 3u * n;
    if (law[0] <= 0 || law[1] <= 0 || law[4] <= 0 || mem[2] <= 0 || arr[2] <= 0) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
      return;
    }
    W unit = wadd(wmul(fromword(law[2]), fromword(law[2]), slot),
                  wmul(fromword(law[3]), fromword(law[3]), slot), slot);
    if (*slot || !ueq(unit.m, wmul(fromword(law[4]), fromword(law[4]), slot).m)) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
      return;
    }
    if (linked)
      incoming_den = flcm(incoming_den, fromword(arr[2]), slot);
    W ir = wsub(wmul(fromword(law[2]), fromword(arr[0]), slot),
                wmul(fromword(law[3]), fromword(arr[1]), slot), slot);
    W ii = wadd(wmul(fromword(law[3]), fromword(arr[0]), slot),
                wmul(fromword(law[2]), fromword(arr[1]), slot), slot);
    W id = wmul(fromword(law[4]), fromword(arr[2]), slot);
    W inc[3] = {ir, ii, id};
    wnorm(inc, 2, &inc[2], slot);
    W common = flcm(inc[2], fromword(mem[2]), slot),
      adm = wadd(fromword(law[0]), fromword(law[1]), slot), den = wmul(common, adm, slot);
    for (uint c = 0; c < 2; ++c) {
      W entering = wmul(inc[c], wdiv(common, inc[2], slot), slot),
        retained = wmul(fromword(mem[c]), wdiv(common, fromword(mem[2]), slot), slot);
      W vel = wmul(wi64(2),
                   wadd(wmul(fromword(law[0]), entering, slot),
                        wmul(fromword(law[1]), retained, slot), slot),
                   slot);
      out[3 * n + c] = wsub(vel, wmul(adm, entering, slot), slot);
      held[3 * n + c] = wsub(vel, wmul(adm, retained, slot), slot);
    }
    out[3 * n + 2] = held[3 * n + 2] = den;
    wnorm(out + 3 * n, 2, out + 3 * n + 2, slot);
    wnorm(held + 3 * n, 2, held + 3 * n + 2, slot);
    if (*slot)
      return;
  }
  W source_den = wi64(1);
  for (uint n = 0; n < nodes; ++n) {
    source_den = flcm(source_den, out[3 * n + 2], slot);
    source_den = flcm(source_den, held[3 * n + 2], slot);
  }
  for (uint n = 0; n < nodes; ++n)
    for (uint c = 0; c < 2; ++c) {
      cur[4 * n + c] = wmul(out[3 * n + c], wdiv(source_den, out[3 * n + 2], slot), slot);
      cur[4 * n + 2 + c] = wmul(held[3 * n + c], wdiv(source_den, held[3 * n + 2], slot), slot);
    }
  wnorm(cur, sw, &source_den, slot);
  if (*slot)
    return;
  for (uint j = 0; j < sw; ++j)
    output_lo[j] = output_hi[j] = toword(cur[j], slot);
  output_lo[sw] = output_hi[sw] = toword(source_den, slot);
  if (*slot)
    return;
  for (uint n = 0; n < nodes; ++n) {
    out[3 * n] = cur[4 * n + 2];
    out[3 * n + 1] = cur[4 * n + 3];
    out[3 * n + 2] = source_den;
    wnorm(out + 3 * n, 2, out + 3 * n + 2, slot);
  }
  if (*slot)
    return;
  W prior_den = wi64(1);
  uint prior_status = 3, prior_rank = 0, cur_status = 0, succ_rank = 0;
  long ins = -1;
  if (linked) {
    W od = fromword(origin[sw]);
    if (wzero_p(od) || wneg_p(od)) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
      return;
    }
    for (uint n = 0; n < nodes; ++n) {
      W cross[3];
      device const long *now = current_frame + 3 * n;
      device const long *before = origin_frame + 3 * n;
      phaseprod(fromword(now[0]), fromword(now[1]), fromword(now[2]), fromword(before[0]),
                wneg(fromword(before[1])), fromword(before[2]), cross, slot);
      phaseprod(cross[0], cross[1], cross[2], fromword(origin[4 * n]), fromword(origin[4 * n + 1]),
                od, held + 3 * n, slot);
      prior_den = flcm(prior_den, held[3 * n + 2], slot);
      phaseprod(cross[0], cross[1], cross[2], fromword(origin[4 * n + 2]),
                fromword(origin[4 * n + 3]), od, held + 3 * n, slot);
      prior_den = flcm(prior_den, held[3 * n + 2], slot);
    }
    W paired = flcm(prior_den, incoming_den, slot);
    for (uint n = 0; n < nodes; ++n) {
      W cross[3];
      device const long *now = current_frame + 3 * n;
      device const long *before = origin_frame + 3 * n;
      phaseprod(fromword(now[0]), fromword(now[1]), fromword(now[2]), fromword(before[0]),
                wneg(fromword(before[1])), fromword(before[2]), cross, slot);
      for (uint branch = 0; branch < 2; ++branch) {
        phaseprod(cross[0], cross[1], cross[2], fromword(origin[4 * n + 2 * branch]),
                  fromword(origin[4 * n + 2 * branch + 1]), od, held + 3 * n, slot);
        for (uint c = 0; c < 2; ++c) {
          prior[4 * n + 2 * branch + c] =
              wmul(held[3 * n + c], wdiv(prior_den, held[3 * n + 2], slot), slot);
          formed[4 * n + 2 * branch + c] =
              wmul(held[3 * n + c], wdiv(paired, held[3 * n + 2], slot), slot);
        }
      }
      for (uint c = 0; c < 2; ++c)
        formed[sw + 2 * n + c] = wmul(fromword(incoming[3 * n + c]),
                                      wdiv(paired, fromword(incoming[3 * n + 2]), slot), slot);
    }
    fibre_query(basis_lo, sw, width, prior, &prior_den, (threadgroup const W *)nullptr, -1,
                &prior_status, &prior_rank, slot);
    wnorm(formed, width, (threadgroup W *)nullptr, slot);
    ins = fibre_stage(basis_lo, width, formed, slot);
    if (*slot)
      return;
  }
  W cd = source_den;
  fibre_query(basis_lo, sw, width, cur, &cd, formed, ins, &cur_status, &succ_rank, slot);
  if (*slot)
    return;
  for (uint j = 0; j < width; ++j) {
    if (j >= sw) {
      cur[j] = wneg(cur[j]);
      prior[j] = wneg(prior[j]);
    }
    toword(cur[j], slot);
    toword(prior[j], slot);
    if (ins >= 0)
      toword(formed[j], slot);
  }
  toword(cd, slot);
  toword(prior_den, slot);
  for (uint j = 0; j < 3 * nodes; ++j)
    toword(out[j], slot);
  if (*slot)
    return;
  uint ca = sw + 1, pa = ca + width + 4;
  for (uint j = 0; j < width; ++j) {
    output_lo[ca + j] = output_hi[ca + j] = toword(cur[j], slot);
    output_lo[pa + j] = output_hi[pa + j] = toword(prior[j], slot);
  }
  output_lo[ca + width] = output_hi[ca + width] = toword(cd, slot);
  output_lo[ca + width + 1] = output_hi[ca + width + 1] = cur_status;
  output_lo[ca + width + 2] = output_hi[ca + width + 2] = ins;
  output_lo[ca + width + 3] = output_hi[ca + width + 3] = succ_rank;
  output_lo[pa + width] = output_hi[pa + width] = toword(prior_den, slot);
  output_lo[pa + width + 1] = output_hi[pa + width + 1] = prior_status;
  output_lo[pa + width + 2] = output_hi[pa + width + 2] = -1;
  output_lo[pa + width + 3] = output_hi[pa + width + 3] = prior_rank;
  if (ins >= 0)
    for (uint j = 0; j < width; ++j) {
      ulong at = (ulong)ins * width + j;
      basis_lo[at] = basis_hi[at] = toword(formed[j], slot);
    }
  for (uint j = 0; j < 3 * nodes; ++j) {
    memory_lo[j] = memory_hi[j] = toword(out[j], slot);
  }
}

kernel void section_constitutive_field_rechart(
    device const long *seed [[buffer(0)]], device const long *memory [[buffer(1)]],
    device const long *root_frame [[buffer(2)]], device const long *basis [[buffer(3)]],
    device const long *change [[buffer(4)]], constant uint &nodes [[buffer(5)]],
    device long *seed_lo [[buffer(6)]], device long *seed_hi [[buffer(7)]],
    device long *memory_lo [[buffer(8)]], device long *memory_hi [[buffer(9)]],
    device long *frame_lo [[buffer(10)]], device long *frame_hi [[buffer(11)]],
    device long *basis_lo [[buffer(12)]], device long *basis_hi [[buffer(13)]],
    device long *report_lo [[buffer(14)]], device long *report_hi [[buffer(15)]],
    device uint *slot [[buffer(16)]], device const uint *census [[buffer(17)]],
    device const uint *lineage [[buffer(18)]], constant uint &lineage_count [[buffer(19)]],
    threadgroup W *row [[threadgroup(0)]], uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  if (!nodes || nodes > 0xffffffffu / 6u) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  uint sw = 4 * nodes, width = 6 * nodes;
  W common = wi64(1);
  for (uint n = 0; n < nodes; ++n) {
    device const long *g = change + 6 * n;
    device const long *law = seed + 5 * n;
    device const long *mem = memory + 3 * n;
    device const long *rf = root_frame + 3 * n;
    W u = wadd(wmul(fromword(g[0]), fromword(g[0]), slot),
               wmul(fromword(g[1]), fromword(g[1]), slot), slot);
    W d = wmul(fromword(g[2]), fromword(g[2]), slot);
    W ou = wadd(wmul(fromword(rf[0]), fromword(rf[0]), slot),
                wmul(fromword(rf[1]), fromword(rf[1]), slot), slot);
    W od = wmul(fromword(rf[2]), fromword(rf[2]), slot);
    if (g[2] <= 0 || rf[2] <= 0 || law[0] <= 0 || law[1] <= 0 || law[4] <= 0 || mem[2] <= 0 ||
        *slot || !ueq(u.m, d.m) || !ueq(ou.m, od.m)) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
      return;
    }
    common = flcm(common, fromword(g[2]), slot);
    W t[3], h[3], f[3], i[3];
    phaseprod(fromword(g[0]), fromword(g[1]), fromword(g[2]), fromword(law[2]), fromword(law[3]),
              fromword(law[4]), t, slot);
    phaseprod(fromword(g[0]), fromword(g[1]), fromword(g[2]), fromword(mem[0]), fromword(mem[1]),
              fromword(mem[2]), h, slot);
    phaseprod(fromword(g[0]), fromword(g[1]), fromword(g[2]), fromword(rf[0]), fromword(rf[1]),
              fromword(rf[2]), f, slot);
    phaseprod(fromword(g[0]), fromword(g[1]), fromword(g[2]), fromword(g[3]), fromword(g[4]),
              fromword(g[5]), i, slot);
    seed_lo[5 * n] = seed_hi[5 * n] = law[0];
    seed_lo[5 * n + 1] = seed_hi[5 * n + 1] = law[1];
    for (uint j = 0; j < 3; ++j) {
      seed_lo[5 * n + 2 + j] = seed_hi[5 * n + 2 + j] = toword(t[j], slot);
      memory_lo[3 * n + j] = memory_hi[3 * n + j] = toword(h[j], slot);
      frame_lo[3 * n + j] = frame_hi[3 * n + j] = toword(f[j], slot);
      report_lo[9 * n + j] = report_hi[9 * n + j] = toword(t[j], slot);
      report_lo[9 * n + 3 + j] = report_hi[9 * n + 3 + j] = toword(i[j], slot);
      report_lo[9 * n + 6 + j] = report_hi[9 * n + 6 + j] = toword(f[j], slot);
    }
  }
  if (*slot)
    return;
  for (ulong j = 0; j < (ulong)width * width; ++j)
    basis_lo[j] = basis_hi[j] = 0;
  for (uint p = 0; p < width; ++p) {
    if (!basis[(ulong)p * width + p])
      continue;
    for (uint n = 0; n < nodes; ++n) {
      device const long *g = change + 6 * n;
      row[4 * n] = wmul(
          wsub(wmul(fromword(g[0]), fromword(basis[(ulong)p * width + 4 * n]), slot),
               wmul(fromword(g[1]), fromword(basis[(ulong)p * width + 4 * n + 1]), slot), slot),
          wdiv(common, fromword(g[2]), slot), slot);
      row[4 * n + 1] = wmul(
          wadd(wmul(fromword(g[1]), fromword(basis[(ulong)p * width + 4 * n]), slot),
               wmul(fromword(g[0]), fromword(basis[(ulong)p * width + 4 * n + 1]), slot), slot),
          wdiv(common, fromword(g[2]), slot), slot);
      row[4 * n + 2] = wmul(
          wsub(wmul(fromword(g[0]), fromword(basis[(ulong)p * width + 4 * n + 2]), slot),
               wmul(fromword(g[1]), fromword(basis[(ulong)p * width + 4 * n + 3]), slot), slot),
          wdiv(common, fromword(g[2]), slot), slot);
      row[4 * n + 3] = wmul(
          wadd(wmul(fromword(g[1]), fromword(basis[(ulong)p * width + 4 * n + 2]), slot),
               wmul(fromword(g[0]), fromword(basis[(ulong)p * width + 4 * n + 3]), slot), slot),
          wdiv(common, fromword(g[2]), slot), slot);
    }
    for (uint j = sw; j < width; ++j)
      row[j] = wmul(fromword(basis[(ulong)p * width + j]), common, slot);
    wnorm(row, width, (threadgroup W *)nullptr, slot);
    long ins = fibre_stage(basis_lo, width, row, slot);
    if (ins >= 0)
      for (uint j = 0; j < width; ++j)
        basis_lo[(ulong)ins * width + j] = basis_hi[(ulong)ins * width + j] = toword(row[j], slot);
    if (*slot)
      return;
  }
}

kernel void section_constitutive_fibre(
    device long *basis_lo [[buffer(0)]], device long *basis_hi [[buffer(1)]],
    device const long *input_lo [[buffer(2)]], device const long *input_hi [[buffer(3)]],
    constant uint &source_width [[buffer(4)]], constant uint &target_width [[buffer(5)]],
    constant uint &paired [[buffer(6)]], device long *output_lo [[buffer(7)]],
    device long *output_hi [[buffer(8)]], device uint *slot [[buffer(9)]],
    device const uint *census [[buffer(10)]], device const uint *lineage [[buffer(11)]],
    constant uint &lineage_count [[buffer(12)]], threadgroup W *scratch [[threadgroup(0)]],
    uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  uint width = source_width + target_width;
  if (!source_width || !target_width || width < source_width || paired > 1) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  threadgroup W *q = scratch;
  threadgroup W *f = q + width;
  for (uint j = 0; j < width; ++j) {
    if (input_lo[j] != input_hi[j]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
      return;
    }
    q[j] = j < source_width ? fromword(input_lo[j]) : wzero();
    f[j] = fromword(input_lo[j]);
  }
  threadgroup W *denp = scratch + 2 * width;
  *denp = wi64(1);
  uint disp = 0, rank = 0;
  fibre_query(basis_lo, source_width, width, q, denp, nullptr, -1, &disp, &rank, slot);
  if (*slot)
    return;
  long ins = paired ? fibre_stage(basis_lo, width, f, slot) : -1;
  if (*slot)
    return;
  for (uint j = 0; j < width; ++j) {
    if (j >= source_width)
      q[j] = wneg(q[j]);
    toword(q[j], slot);
    if (ins >= 0)
      toword(f[j], slot);
  }
  toword(*denp, slot);
  if (*slot)
    return;
  for (uint j = 0; j < width; ++j)
    output_lo[j] = output_hi[j] = toword(q[j], slot);
  output_lo[width] = output_hi[width] = toword(*denp, slot);
  output_lo[width + 1] = output_hi[width + 1] = disp;
  output_lo[width + 2] = output_hi[width + 2] = ins;
  output_lo[width + 3] = output_hi[width + 3] = rank + (ins >= 0 ? 1 : 0);
  if (ins >= 0)
    for (uint j = 0; j < width; ++j) {
      ulong at = (ulong)ins * width + j;
      basis_lo[at] = basis_hi[at] = toword(f[j], slot);
    }
}

kernel void
section_carry(device const long *in_lo [[buffer(0)]], device const long *in_hi [[buffer(1)]],
              constant uint &count [[buffer(2)]], device long *out_lo [[buffer(3)]],
              device long *out_hi [[buffer(4)]], device uint *refused [[buffer(5)]],
              device const uint *census [[buffer(6)]], device const uint *lineage [[buffer(7)]],
              constant uint &lineage_count [[buffer(8)]], uint3 tid [[thread_position_in_grid]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, refused))
    return;
  for (uint i = 0; i < count; ++i) {
    out_lo[i] = in_lo[i];
    out_hi[i] = in_hi[i];
  }
}

kernel void section_census(device const long *lo [[buffer(0)]], device const long *hi [[buffer(1)]],
                           constant uint &count [[buffer(2)]],
                           constant uint &admitted [[buffer(3)]], device uint *slot [[buffer(4)]],
                           uint3 tid [[thread_position_in_threadgroup]]) {
  census_serial_impl(lo, hi, count, admitted, slot, tid);
}
kernel void section_census_serial_control(device const long *lo [[buffer(0)]],
                                          device const long *hi [[buffer(1)]],
                                          constant uint &count [[buffer(2)]],
                                          constant uint &admitted [[buffer(3)]],
                                          device uint *slot [[buffer(4)]],
                                          uint3 tid [[thread_position_in_threadgroup]]) {
  census_serial_impl(lo, hi, count, admitted, slot, tid);
}

kernel void section_constitutive_rechart(
    device const long *seed [[buffer(0)]], device const long *memory [[buffer(1)]],
    device const long *root_frame [[buffer(2)]], device const long *basis [[buffer(3)]],
    device const long *change [[buffer(4)]], constant uint &nodes [[buffer(5)]],
    device long *seed_lo [[buffer(6)]], device long *seed_hi [[buffer(7)]],
    device long *memory_lo [[buffer(8)]], device long *memory_hi [[buffer(9)]],
    device long *frame_lo [[buffer(10)]], device long *frame_hi [[buffer(11)]],
    device long *basis_lo [[buffer(12)]], device long *basis_hi [[buffer(13)]],
    device long *report_lo [[buffer(14)]], device long *report_hi [[buffer(15)]],
    device uint *slot [[buffer(16)]], device const uint *census [[buffer(17)]],
    device const uint *lineage [[buffer(18)]], constant uint &lineage_count [[buffer(19)]],
    threadgroup W *scratch [[threadgroup(0)]], uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  uint sw = 2 * nodes, width = sw + 2;
  W common = wi64(1);
  for (uint n = 0; n < nodes; ++n) {
    device const long *g = change + 6 * n;
    W unit = wadd(wmul(fromword(g[0]), fromword(g[0]), slot),
                  wmul(fromword(g[1]), fromword(g[1]), slot), slot);
    if (g[2] <= 0 || !ueq(wmul(fromword(g[2]), fromword(g[2]), slot).m, unit.m))
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    if (*slot)
      return;
    common = flcm(common, fromword(g[2]), slot);
    W t[3], h[3], r[3], i[3];
    device const long *law = seed + 5 * n, *held = memory + 3 * n, *rf = root_frame + 3 * n;
    phaseprod(fromword(g[0]), fromword(g[1]), fromword(g[2]), fromword(law[2]), fromword(law[3]),
              fromword(law[4]), t, slot);
    phaseprod(fromword(g[0]), fromword(g[1]), fromword(g[2]), fromword(held[0]), fromword(held[1]),
              fromword(held[2]), h, slot);
    phaseprod(fromword(g[0]), fromword(g[1]), fromword(g[2]), fromword(rf[0]), fromword(rf[1]),
              fromword(rf[2]), r, slot);
    phaseprod(fromword(g[0]), fromword(g[1]), fromword(g[2]), fromword(g[3]), fromword(g[4]),
              fromword(g[5]), i, slot);
    if (*slot)
      return;
    seed_lo[5 * n] = seed_hi[5 * n] = law[0];
    seed_lo[5 * n + 1] = seed_hi[5 * n + 1] = law[1];
    for (uint j = 0; j < 3; ++j) {
      seed_lo[5 * n + 2 + j] = seed_hi[5 * n + 2 + j] = toword(t[j], slot);
      memory_lo[3 * n + j] = memory_hi[3 * n + j] = toword(h[j], slot);
      frame_lo[3 * n + j] = frame_hi[3 * n + j] = toword(r[j], slot);
      report_lo[9 * n + j] = report_hi[9 * n + j] = toword(t[j], slot);
      report_lo[9 * n + 3 + j] = report_hi[9 * n + 3 + j] = toword(i[j], slot);
      report_lo[9 * n + 6 + j] = report_hi[9 * n + 6 + j] = toword(r[j], slot);
    }
  }
  if (*slot)
    return;
  for (ulong j = 0; j < (ulong)width * width; ++j)
    basis_lo[j] = basis_hi[j] = 0;
  for (uint p = 0; p < width; ++p) {
    if (!basis[(ulong)p * width + p])
      continue;
    for (uint n = 0; n < nodes; ++n) {
      device const long *g = change + 6 * n;
      W x = fromword(basis[(ulong)p * width + 2 * n]),
        y = fromword(basis[(ulong)p * width + 2 * n + 1]);
      W a = wsub(wmul(fromword(g[0]), x, slot), wmul(fromword(g[1]), y, slot), slot);
      W b = wadd(wmul(fromword(g[1]), x, slot), wmul(fromword(g[0]), y, slot), slot);
      scratch[2 * n] = wmul(a, wdiv(common, fromword(g[2]), slot), slot);
      scratch[2 * n + 1] = wmul(b, wdiv(common, fromword(g[2]), slot), slot);
    }
    for (uint j = sw; j < width; ++j)
      scratch[j] = wmul(fromword(basis[(ulong)p * width + j]), common, slot);
    if (*slot)
      return;
    wnorm(scratch, width, (threadgroup W *)nullptr, slot);
    long ins = fibre_stage(basis_lo, width, scratch, slot);
    if (*slot)
      return;
    if (ins >= 0)
      for (uint j = 0; j < width; ++j) {
        ulong at = (ulong)ins * width + j;
        basis_lo[at] = basis_hi[at] = toword(scratch[j], slot);
      }
  }
}

kernel void section_constitutive_circulation(
    device const long *seed [[buffer(0)]], device long *memory_lo [[buffer(1)]],
    device long *memory_hi [[buffer(2)]], device long *basis_lo [[buffer(3)]],
    device long *basis_hi [[buffer(4)]], device const long *incoming [[buffer(5)]],
    device const long *origin [[buffer(6)]], device const long *current_frame [[buffer(7)]],
    device const long *origin_frame [[buffer(8)]], constant uint &nodes [[buffer(9)]],
    constant uint &linked [[buffer(10)]], device long *output_lo [[buffer(11)]],
    device long *output_hi [[buffer(12)]], device uint *slot [[buffer(13)]],
    device const uint *census [[buffer(14)]], device const uint *lineage [[buffer(15)]],
    constant uint &lineage_count [[buffer(16)]], threadgroup W *scratch [[threadgroup(0)]],
    uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  uint sw = 2 * nodes, width = sw + 2;
  if (!nodes || width < sw || incoming[2] <= 0 || linked > 1) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  threadgroup W *cur = scratch, *prior = cur + width, *formed = prior + width,
                *depart = formed + width, *succ = depart + 3 * nodes;
  threadgroup W *sden = succ + 3 * nodes, *pden = sden + 1, *cden = sden + 2;
  *pden = wi64(1);
  *cden = wi64(1);
  for (uint j = 0; j < width; ++j) {
    cur[j] = prior[j] = formed[j] = wzero();
  }
  for (uint n = 0; n < nodes; ++n) {
    device const long *law = seed + 5 * n;
    device const long *held = memory_lo + 3 * n;
    if (law[0] <= 0 || law[1] <= 0 || law[4] <= 0 || held[2] <= 0) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
      return;
    }
    W ir = wsub(wmul(fromword(law[2]), fromword(incoming[0]), slot),
                wmul(fromword(law[3]), fromword(incoming[1]), slot), slot),
      ii = wadd(wmul(fromword(law[3]), fromword(incoming[0]), slot),
                wmul(fromword(law[2]), fromword(incoming[1]), slot), slot),
      id = wmul(fromword(law[4]), fromword(incoming[2]), slot);
    W inc[3] = {ir, ii, id};
    wnorm(inc, 2, &inc[2], slot);
    W common = flcm(inc[2], fromword(held[2]), slot),
      adm = wadd(fromword(law[0]), fromword(law[1]), slot), den = wmul(common, adm, slot);
    for (uint c = 0; c < 2; ++c) {
      W entering = wmul(inc[c], wdiv(common, inc[2], slot), slot),
        retained = wmul(fromword(held[c]), wdiv(common, fromword(held[2]), slot), slot);
      W vel = wmul(wi64(2),
                   wadd(wmul(fromword(law[0]), entering, slot),
                        wmul(fromword(law[1]), retained, slot), slot),
                   slot);
      depart[3 * n + c] = wsub(vel, wmul(adm, entering, slot), slot);
      succ[3 * n + c] = wsub(vel, wmul(adm, retained, slot), slot);
    }
    depart[3 * n + 2] = succ[3 * n + 2] = den;
    wnorm(depart + 3 * n, 2, depart + 3 * n + 2, slot);
    wnorm(succ + 3 * n, 2, succ + 3 * n + 2, slot);
    if (*slot)
      return;
  }
  *sden = wi64(1);
  for (uint n = 0; n < nodes; ++n)
    *sden = flcm(*sden, depart[3 * n + 2], slot);
  for (uint n = 0; n < nodes; ++n)
    for (uint c = 0; c < 2; ++c)
      cur[2 * n + c] = wmul(depart[3 * n + c], wdiv(*sden, depart[3 * n + 2], slot), slot);
  wnorm(cur, sw, sden, slot);
  if (*slot)
    return;
  for (uint j = 0; j < sw; ++j)
    output_lo[j] = output_hi[j] = toword(cur[j], slot);
  output_lo[sw] = output_hi[sw] = toword(*sden, slot);
  if (*slot)
    return;
  *pden = wi64(1);
  uint prior_status = 3, prior_rank = 0, current_status = 0, successor_rank = 0;
  long ins = -1;
  if (linked) {
    if (origin[sw] <= 0) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
      return;
    }
    for (uint n = 0; n < nodes; ++n) {
      W cross[3],
          now[3] = {fromword(current_frame[3 * n]), fromword(current_frame[3 * n + 1]),
                    fromword(current_frame[3 * n + 2])},
          before[3] = {fromword(origin_frame[3 * n]), fromword(origin_frame[3 * n + 1]),
                       fromword(origin_frame[3 * n + 2])};
      phaseprod(now[0], now[1], now[2], before[0], wneg(before[1]), before[2], cross, slot);
      phaseprod(cross[0], cross[1], cross[2], fromword(origin[2 * n]), fromword(origin[2 * n + 1]),
                fromword(origin[sw]), depart + 3 * n, slot);
      *pden = flcm(*pden, depart[3 * n + 2], slot);
    }
    W paired_den = flcm(*pden, fromword(incoming[2]), slot);
    for (uint n = 0; n < nodes; ++n)
      for (uint c = 0; c < 2; ++c) {
        prior[2 * n + c] = wmul(depart[3 * n + c], wdiv(*pden, depart[3 * n + 2], slot), slot);
        formed[2 * n + c] =
            wmul(depart[3 * n + c], wdiv(paired_den, depart[3 * n + 2], slot), slot);
      }
    formed[sw] = wmul(fromword(incoming[0]), wdiv(paired_den, fromword(incoming[2]), slot), slot);
    formed[sw + 1] =
        wmul(fromword(incoming[1]), wdiv(paired_den, fromword(incoming[2]), slot), slot);
    fibre_query(basis_lo, sw, width, prior, pden, nullptr, -1, &prior_status, &prior_rank, slot);
    wnorm(formed, width, (threadgroup W *)nullptr, slot);
    ins = fibre_stage(basis_lo, width, formed, slot);
    if (*slot)
      return;
  }
  *cden = *sden;
  fibre_query(basis_lo, sw, width, cur, cden, formed, ins, &current_status, &successor_rank, slot);
  if (*slot)
    return;
  for (uint j = 0; j < width; ++j) {
    if (j >= sw) {
      cur[j] = wneg(cur[j]);
      prior[j] = wneg(prior[j]);
    }
    toword(cur[j], slot);
    toword(prior[j], slot);
    if (ins >= 0)
      toword(formed[j], slot);
  }
  toword(*cden, slot);
  toword(*pden, slot);
  for (uint j = 0; j < 3 * nodes; ++j)
    toword(succ[j], slot);
  if (*slot)
    return;
  uint ca = sw + 1, pa = ca + width + 4;
  for (uint j = 0; j < width; ++j) {
    output_lo[ca + j] = output_hi[ca + j] = toword(cur[j], slot);
    output_lo[pa + j] = output_hi[pa + j] = toword(prior[j], slot);
  }
  output_lo[ca + width] = output_hi[ca + width] = toword(*cden, slot);
  output_lo[ca + width + 1] = output_hi[ca + width + 1] = current_status;
  output_lo[ca + width + 2] = output_hi[ca + width + 2] = ins;
  output_lo[ca + width + 3] = output_hi[ca + width + 3] = successor_rank;
  output_lo[pa + width] = output_hi[pa + width] = toword(*pden, slot);
  output_lo[pa + width + 1] = output_hi[pa + width + 1] = prior_status;
  output_lo[pa + width + 2] = output_hi[pa + width + 2] = -1;
  output_lo[pa + width + 3] = output_hi[pa + width + 3] = prior_rank;
  if (ins >= 0)
    for (uint j = 0; j < width; ++j) {
      ulong at = (ulong)ins * width + j;
      basis_lo[at] = basis_hi[at] = toword(formed[j], slot);
    }
  for (uint j = 0; j < 3 * nodes; ++j)
    memory_lo[j] = memory_hi[j] = toword(succ[j], slot);
}

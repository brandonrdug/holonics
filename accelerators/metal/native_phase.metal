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

// Stage one condition-family row and publish it only after every reduced carrier
// has returned to the i64 wire. The high face mirrors the low face for this point
// chart; a refusal leaves the derived graph unpublished.
inline void condition_stage_row(device long *lo, device long *hi, uint width,
                                 threadgroup W *row, device uint *slot) {
  long inserted = fibre_stage(lo, width, row, slot);
  for (uint j = 0; j < width; ++j)
    toword(row[j], slot);
  if (*slot)
    return;
  if (inserted >= 0)
    for (uint j = 0; j < width; ++j) {
      ulong at = (ulong)inserted * width + j;
      long value = toword(row[j], slot);
      lo[at] = hi[at] = value;
    }
}

inline void condition_store_report(device const long *basis, uint source_width, uint width,
                                    threadgroup W *query, thread W den, uint status, uint rank,
                                    device long *lo, device long *hi, device uint *slot) {
  for (uint j = 0; j < width; ++j)
    toword(query[j], slot);
  toword(den, slot);
  if (*slot)
    return;
  for (uint j = 0; j < width; ++j)
    lo[j] = hi[j] = toword(query[j], slot);
  lo[width] = hi[width] = toword(den, slot);
  lo[width + 1] = hi[width + 1] = (long)status;
  lo[width + 2] = hi[width + 2] = -1;
  lo[width + 3] = hi[width + 3] = (long)rank;
  uint target_width = width - source_width;
  for (uint p = 0; p < target_width; ++p)
    for (uint j = 0; j < target_width; ++j) {
      ulong at = (ulong)(source_width + p) * width + source_width + j;
      long value = basis[(ulong)(source_width + p) * width + source_width + p] != 0
          ? basis[at] : 0;
      ulong out_at = (ulong)width + 4ul + (ulong)p * target_width + j;
      lo[out_at] = hi[out_at] = value;
    }
}

inline void condition_empty_report(device long *lo, device long *hi, uint source_width,
                                   uint target_width) {
  uint width = source_width + target_width;
  ulong count = (ulong)width + 4ul + (ulong)target_width * target_width;
  for (ulong i = 0; i < count; ++i)
    lo[i] = hi[i] = 0;
  lo[width] = hi[width] = 1;
  lo[width + 1] = hi[width + 1] = 1;
  lo[width + 2] = hi[width + 2] = -1;
}

inline void condition_project(device const long *joint, uint source_width, uint joint_target,
                               uint start, uint target_width, device long *basis_lo,
                               device long *basis_hi, device long *lo, device long *hi,
                               threadgroup W *row, device uint *slot) {
  uint joint_width = source_width + joint_target;
  uint width = source_width + target_width;
  for (ulong i = 0; i < (ulong)target_width * target_width; ++i)
    basis_lo[i] = basis_hi[i] = 0;
  for (uint p = 0; p < joint_target; ++p) {
    ulong base = (ulong)joint_width + 4ul + (ulong)p * joint_target + start;
    for (uint j = 0; j < target_width; ++j)
      row[j] = fromword(joint[base + j]);
    condition_stage_row(basis_lo, basis_hi, target_width, row, slot);
    if (*slot)
      return;
  }
  uint rank = 0;
  for (uint p = 0; p < target_width; ++p)
    if (basis_lo[(ulong)p * target_width + p] != 0)
      ++rank;
  for (uint j = 0; j < source_width; ++j)
    lo[j] = hi[j] = joint[j];
  for (uint j = 0; j < target_width; ++j)
    lo[source_width + j] = hi[source_width + j] = joint[source_width + start + j];
  lo[width] = hi[width] = joint[joint_width];
  lo[width + 1] = hi[width + 1] = joint[joint_width + 1] == 1 ? 1 : (rank ? 2 : 0);
  lo[width + 2] = hi[width + 2] = -1;
  lo[width + 3] = hi[width + 3] = rank;
  for (ulong i = 0; i < (ulong)target_width * target_width; ++i)
    lo[width + 4ul + i] = hi[width + 4ul + i] = basis_lo[i];
}

inline bool condition_nonzero(threadgroup W *value, uint count) {
  for (uint j = 0; j < count; ++j)
    if (!wzero_p(value[j]))
      return true;
  return false;
}

inline void condition_coverage_write(uint kind, long generator, threadgroup W *witness,
                                     thread W witness_denominator, uint condition_width,
                                     threadgroup W *residual, thread W residual_denominator,
                                     uint residual_width, uint output_width, device long *lo,
                                     device long *hi, device uint *slot) {
  wnorm(witness, condition_width, &witness_denominator, slot);
  wnorm(residual, residual_width, &residual_denominator, slot);
  for (uint j = 0; j < condition_width; ++j)
    toword(witness[j], slot);
  for (uint j = 0; j < residual_width; ++j)
    toword(residual[j], slot);
  toword(witness_denominator, slot);
  toword(residual_denominator, slot);
  if (*slot)
    return;
  lo[0] = hi[0] = kind;
  lo[1] = hi[1] = generator;
  lo[2] = hi[2] = toword(witness_denominator, slot);
  for (uint j = 0; j < condition_width; ++j)
    lo[3u + j] = hi[3u + j] = toword(witness[j], slot);
  lo[3u + condition_width] = hi[3u + condition_width] = toword(residual_denominator, slot);
  for (uint j = 0; j < output_width; ++j)
    lo[4u + condition_width + j] = hi[4u + condition_width + j]
        = j < residual_width ? toword(residual[j], slot) : 0;
}
inline W flcm(W a, W b, device uint *slot);
inline bool upstream(device const uint *census, device const uint *lineage, uint count,
                     device uint *slot);
inline W fibre_current_denominator(device const long *lo, device const long *hi,
                                   uint denominator_at, uint disposition_at,
                                   device uint *slot);

// Found the five rows: predecessor, successor, incoming normal, returned normal,
// and oriented difference. Initially both currents agree and all differences vanish.
kernel void section_constitutive_condition_current_found(
    device const long *lo [[buffer(0)]], device const long *hi [[buffer(1)]],
    constant uint &at [[buffer(2)]], constant uint &denominator_at [[buffer(3)]],
    constant uint &status_at [[buffer(4)]], constant uint &condition_width [[buffer(5)]],
    device long *out [[buffer(6)]], device long *out_hi [[buffer(7)]],
    device uint *slot [[buffer(8)]], device const uint *census [[buffer(9)]],
    device const uint *lineage [[buffer(10)]], constant uint &lineage_count [[buffer(11)]],
    uint3 tid [[thread_position_in_grid]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  uint c = condition_width;
  if (!c) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  W den = fibre_current_denominator(lo, hi, denominator_at, status_at, slot);
  for (uint j = 0; j < c; ++j)
    if (lo[at + j] != hi[at + j])
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
  toword(den, slot);
  if (*slot)
    return;
  for (uint j = 0; j < 5u * c; ++j)
    out[j] = out_hi[j] = j < 2u * c ? lo[at + (j % c)] : 0;
  out[5u * c] = out_hi[5u * c] = toword(den, slot);
  out[5u * c + 1u] = out_hi[5u * c + 1u] = 0;
}

// Unit-admittance contact with an affine condition family F=a+V in the realified
// phase chart. The Gram graph computes the exact projection onto V; the successor
// preserves the prior tangent current and exchanges the normal current at both ports.
kernel void section_constitutive_condition_contact(
    device const long *lo [[buffer(0)]], device const long *hi [[buffer(1)]],
    constant uint &at [[buffer(2)]], constant uint &denominator_at [[buffer(3)]],
    constant uint &status_at [[buffer(4)]], device const long *pf [[buffer(5)]],
    device const long *pf_hi [[buffer(6)]], constant uint &condition_source_width [[buffer(7)]],
    constant uint &condition_width [[buffer(8)]], device long *graph_lo [[buffer(9)]],
    device long *graph_hi [[buffer(10)]], device long *out [[buffer(11)]],
    device long *out_hi [[buffer(12)]], device uint *slot [[buffer(13)]],
    device const uint *census [[buffer(14)]], device const uint *lineage [[buffer(15)]],
    constant uint &lineage_count [[buffer(16)]], threadgroup W *scratch [[threadgroup(0)]],
    uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  uint ps = condition_source_width;
  uint c = condition_width;
  if (!c || ps > 0xfffffffbU - c || c > 0x7fffffffu) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  uint pk = ps + c;
  uint k = 2u * c;
  ulong count = (ulong)pk + 4ul + (ulong)c * c;
  if (count > 0xfffffffbUL) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  for (ulong j = 0; j < count; ++j)
    if (pf[j] != pf_hi[j])
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
  if (pf[pk] <= 0 || pf[pk + 1u] < 0 || pf[pk + 1u] > 2) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
  }
  W held_den = fibre_current_denominator(lo, hi, denominator_at, status_at, slot);
  for (uint j = 0; j < c; ++j)
    if (lo[at + j] != hi[at + j])
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
  if (*slot)
    return;

  threadgroup W *row = scratch;
  threadgroup W *query = row + k;
  threadgroup W *values = query + k;
  for (uint j = 0; j < 5u * c; ++j)
    values[j] = j < 2u * c ? fromword(lo[at + (j % c)]) : wzero();
  W den = held_den;
  // An empty compatible family preserves the actual current and reports the
  // family obstruction; no fabricated point is selected.
  if (pf[pk + 1u] != 1) {
    for (ulong j = 0; j < (ulong)k * k; ++j)
      graph_lo[j] = graph_hi[j] = 0;
    for (uint i = 0; i < c; ++i) {
      for (uint j = 0; j < c; ++j) {
        row[j] = wzero();
        for (uint n = 0; n < c; ++n)
          row[j] = wadd(row[j],
                        wmul(fromword(pf[pk + 4u + (ulong)j * c + n]),
                             fromword(pf[pk + 4u + (ulong)i * c + n]), slot), slot);
        row[c + j] = fromword(pf[pk + 4u + (ulong)i * c + j]);
      }
      if (*slot)
        return;
      condition_stage_row(graph_lo, graph_hi, k, row, slot);
      if (*slot)
        return;
    }
    W projection_den[2];
    for (uint which = 0; which < 2; ++which) {
      bool condition_input = which != 0;
      device const long *input = condition_input ? pf + ps : lo + at;
      W projection = condition_input ? fromword(pf[pk]) : held_den;
      for (uint j = 0; j < k; ++j)
        query[j] = wzero();
      for (uint j = 0; j < c; ++j)
        for (uint n = 0; n < c; ++n)
          query[j] = wadd(query[j],
                          wmul(fromword(pf[pk + 4u + (ulong)j * c + n]),
                               fromword(input[n]), slot), slot);
      if (*slot)
        return;
      uint disposition = 0, rank = 0;
      fibre_query(graph_lo, c, k, query, &projection,
                  (threadgroup const W *)nullptr, -1, &disposition, &rank, slot);
      if (*slot)
        return;
      if (disposition != 0) {
        atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                                 memory_order_relaxed);
        return;
      }
      for (uint j = 0; j < c; ++j)
        values[(which + 1u) * c + j] = wneg(query[c + j]);
      projection_den[which] = projection;
    }
    den = flcm(held_den, fromword(pf[pk]), slot);
    den = flcm(den, projection_den[0], slot);
    den = flcm(den, projection_den[1], slot);
    if (*slot)
      return;
    for (uint j = 0; j < c; ++j) {
      W h = wmul(fromword(lo[at + j]), wdiv(den, held_den, slot), slot);
      W ph = wmul(values[c + j], wdiv(den, projection_den[0], slot), slot);
      W pa = wmul(values[2u * c + j], wdiv(den, projection_den[1], slot), slot);
      W incoming = wsub(wmul(fromword(pf[ps + j]), wdiv(den, fromword(pf[pk]), slot), slot), pa, slot);
      W returned = wsub(h, ph, slot);
      values[j] = h;
      values[c + j] = wadd(ph, incoming, slot);
      values[2u * c + j] = incoming;
      values[3u * c + j] = returned;
      values[4u * c + j] = wsub(incoming, returned, slot);
    }
  }
  wnorm(values, 5u * c, &den, slot);
  for (uint j = 0; j < 5u * c; ++j)
    toword(values[j], slot);
  toword(den, slot);
  if (*slot)
    return;
  for (uint j = 0; j < 5u * c; ++j)
    out[j] = out_hi[j] = toword(values[j], slot);
  out[5u * c] = out_hi[5u * c] = toword(den, slot);
  out[5u * c + 1u] = out_hi[5u * c + 1u] = pf[pk + 1u] == 1 ? 1 : 0;
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
inline void field_constitutive_prepare(
    device const long *seed, device const long *memory_lo, device const long *basis_lo,
    device const long *incoming, device const long *origin, device const long *current_frame,
    device const long *origin_frame, uint nodes, uint linked,
    device long *output_lo, device long *output_hi, device uint *slot,
    device const uint *census, device const uint *lineage, uint lineage_count,
    threadgroup W *scratch) {
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

// A point-current aperture may consume only a complete rational current.  A
// disposition marks a non-singleton fibre and is therefore accepted only when
// it is the zero codeword; an absent denominator is the unit denominator.
inline W fibre_current_denominator(device const long *lo, device const long *hi,
                                   uint denominator_at, uint disposition_at,
                                   device uint *slot) {
  if (disposition_at != 0xffffffffu
      && (lo[disposition_at] != hi[disposition_at] || lo[disposition_at] != 0)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return wi64(1);
  }
  if (denominator_at == 0xffffffffu)
    return wi64(1);
  if (lo[denominator_at] != hi[denominator_at] || lo[denominator_at] <= 0) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return wi64(1);
  }
  return fromword(lo[denominator_at]);
}

// Causal convolution of two resident complex polynomial currents. The two
// raw extents are the active coefficient populations; coordinates after them
// must be structural zero and cannot conceal an unadmitted current.
kernel void section_phase_convolution(
    device const long *source_lo [[buffer(0)]], device const long *source_hi [[buffer(1)]],
    constant uint &source_at [[buffer(2)]], constant uint &source_denominator_at [[buffer(3)]],
    constant uint &source_disposition_at [[buffer(4)]],
    device const long *response_lo [[buffer(5)]], device const long *response_hi [[buffer(6)]],
    constant uint &response_at [[buffer(7)]], constant uint &response_denominator_at [[buffer(8)]],
    constant uint &response_disposition_at [[buffer(9)]],
    constant uint &source_complex_coordinates [[buffer(10)]],
    constant uint &response_complex_coordinates [[buffer(11)]],
    constant uint &source_raw_extent [[buffer(12)]], constant uint &response_raw_extent [[buffer(13)]],
    device long *output_lo [[buffer(14)]], device long *output_hi [[buffer(15)]],
    device uint *slot [[buffer(16)]], device const uint *census [[buffer(17)]],
    device const uint *lineage [[buffer(18)]], constant uint &lineage_count [[buffer(19)]],
    threadgroup W *scratch [[threadgroup(0)]], uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  ulong source_complex = (ulong)source_complex_coordinates;
  ulong response_complex = (ulong)response_complex_coordinates;
  ulong source_raw = (ulong)source_raw_extent;
  ulong response_raw = (ulong)response_raw_extent;
  if (!source_complex || !response_complex || !source_raw || !response_raw
      || source_raw > source_complex || response_raw > response_complex
      || source_complex > 0x7ffffffful || response_complex > 0x7ffffffful) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  ulong output_extent64 = source_raw + response_raw - 1ul;
  if (output_extent64 > 0x7ffffffful
      || output_extent64 > (0xfffffffful - 1ul) / 2ul) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  uint source_complex_count = (uint)source_complex;
  uint response_complex_count = (uint)response_complex;
  uint source_raw_count = (uint)source_raw;
  uint response_raw_count = (uint)response_raw;
  uint output_extent = (uint)output_extent64;
  uint output_width = 2u * output_extent + 1u;

  W source_den = fibre_current_denominator(source_lo, source_hi,
                                           source_denominator_at,
                                           source_disposition_at, slot);
  W response_den = fibre_current_denominator(response_lo, response_hi,
                                             response_denominator_at,
                                             response_disposition_at, slot);
  if (*slot)
    return;
  for (uint coordinate = 0; coordinate < source_complex_count; ++coordinate) {
    uint at = source_at + 2u * coordinate;
    if (source_lo[at] != source_hi[at] || source_lo[at + 1u] != source_hi[at + 1u]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
    if (coordinate >= source_raw_count
        && (source_lo[at] != 0 || source_lo[at + 1u] != 0)) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  }
  for (uint coordinate = 0; coordinate < response_complex_count; ++coordinate) {
    uint at = response_at + 2u * coordinate;
    if (response_lo[at] != response_hi[at] || response_lo[at + 1u] != response_hi[at + 1u]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
    if (coordinate >= response_raw_count
        && (response_lo[at] != 0 || response_lo[at + 1u] != 0)) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  }
  W common = wmul(source_den, response_den, slot);
  if (*slot)
    return;
  for (uint target = 0; target < output_extent; ++target) {
    W real = wzero(), imaginary = wzero();
    uint source_first = target >= response_raw_count
        ? target - response_raw_count + 1u
        : 0u;
    uint source_last = min(target, source_raw_count - 1u);
    for (uint source = source_first; source <= source_last; ++source) {
      uint response = target - source;
      W product[3];
      phaseprod(fromword(source_lo[source_at + 2u * source]),
                fromword(source_lo[source_at + 2u * source + 1u]), source_den,
                fromword(response_lo[response_at + 2u * response]),
                fromword(response_lo[response_at + 2u * response + 1u]), response_den,
                product, slot);
      if (*slot)
        return;
      W factor = wdiv(common, product[2], slot);
      real = wadd(real, wmul(product[0], factor, slot), slot);
      imaginary = wadd(imaginary, wmul(product[1], factor, slot), slot);
      if (*slot)
        return;
    }
    scratch[2u * target] = real;
    scratch[2u * target + 1u] = imaginary;
  }
  wnorm(scratch, output_width - 1u, &common, slot);
  if (*slot)
    return;
  for (uint j = 0; j < output_width - 1u; ++j)
    toword(scratch[j], slot);
  toword(common, slot);
  if (*slot)
    return;
  for (uint j = 0; j < output_width - 1u; ++j)
    output_lo[j] = output_hi[j] = toword(scratch[j], slot);
  output_lo[output_width - 1u] = output_hi[output_width - 1u] = toword(common, slot);
}

// Fixed-source condition preimage.  The graph and right-hand side are derived
// evidence owned by this operation; the learned relation basis is read-only.
// A refusal may leave partial derived evidence, but it never publishes a row
// into the original basis.
kernel void section_constitutive_condition_preimage(
    device const long *basis [[buffer(0)]], device const long *source_lo [[buffer(1)]],
    device const long *source_hi [[buffer(2)]], constant uint &source_at [[buffer(3)]],
    constant uint &source_denominator_at [[buffer(4)]], constant uint &source_disposition_at [[buffer(5)]],
    device const long *observed_lo [[buffer(6)]], device const long *observed_hi [[buffer(7)]],
    constant uint &observed_at [[buffer(8)]], constant uint &observed_denominator_at [[buffer(9)]],
    constant uint &observed_disposition_at [[buffer(10)]], constant uint &source_complex [[buffer(11)]],
    constant uint &condition_complex [[buffer(12)]], constant uint &target_width [[buffer(13)]],
    device long *graph_lo [[buffer(14)]], device long *graph_hi [[buffer(15)]],
    device long *rhs_lo [[buffer(16)]], device long *rhs_hi [[buffer(17)]],
    device long *output_lo [[buffer(18)]], device long *output_hi [[buffer(19)]],
    device uint *slot [[buffer(20)]], device const uint *census [[buffer(21)]],
    device const uint *lineage [[buffer(22)]], constant uint &lineage_count [[buffer(23)]],
    threadgroup W *scratch [[threadgroup(0)]], uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;

  ulong sc = (ulong)source_complex, cc = (ulong)condition_complex;
  ulong source_inner = sc + cc;
  ulong mixed = sc * cc;
  if (!source_complex || !condition_complex || !target_width || (target_width & 1u)
      || mixed > 0x7fffffffffffffffUL
      || source_inner > 0x7fffffffffffffffUL - mixed) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  source_inner += mixed;
  ulong source_width64 = 2ul * source_inner;
  if (source_width64 > 0xffffffffffffffffUL - target_width) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  ulong residual_width64 = source_width64 + target_width;
  ulong conditions64 = 2ul * cc;
  if (residual_width64 > 0xffffffffffffffffUL - conditions64) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  ulong width64 = residual_width64 + conditions64;
  if (width64 > 0xfffffffbUL) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  uint source_width = (uint)source_width64;
  uint residual_width = (uint)residual_width64;
  uint conditions = (uint)conditions64;
  uint width = (uint)width64;

  W source_den = fibre_current_denominator(source_lo, source_hi,
                                           source_denominator_at,
                                           source_disposition_at, slot);
  W observed_den = fibre_current_denominator(observed_lo, observed_hi,
                                             observed_denominator_at,
                                             observed_disposition_at, slot);
  if (*slot)
    return;
  for (uint j = 0; j < 2u * source_complex; ++j)
    if (source_lo[source_at + j] != source_hi[source_at + j]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  for (uint j = 0; j < target_width; ++j)
    if (observed_lo[observed_at + j] != observed_hi[observed_at + j]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }

  threadgroup W *residual = scratch;
  threadgroup W *formed = residual + residual_width;
  threadgroup W *query = formed + width;
  // The derived graph starts empty and is separate from the learned relation.
  for (ulong j = 0; j < (ulong)width * width; ++j)
    graph_lo[j] = graph_hi[j] = 0;
  uint ignored_status = 0, ignored_rank = 0;
  for (uint coordinate = 0; coordinate < conditions; ++coordinate) {
    for (uint j = 0; j < residual_width; ++j)
      residual[j] = wzero();
    residual[2u * source_complex + coordinate] = source_den;
    uint condition = coordinate / 2u;
    uint mixed_at = 2u * (source_complex + condition_complex)
                    + 2u * condition * source_complex;
    for (uint s = 0; s < source_complex; ++s) {
      W real = fromword(source_lo[source_at + 2u * s]);
      W imaginary = fromword(source_lo[source_at + 2u * s + 1u]);
      if (coordinate & 1u) {
        residual[mixed_at + 2u * s] = wneg(imaginary);
        residual[mixed_at + 2u * s + 1u] = real;
      } else {
        residual[mixed_at + 2u * s] = real;
        residual[mixed_at + 2u * s + 1u] = imaginary;
      }
    }
    W denominator = source_den;
    fibre_query(basis, residual_width, residual_width, residual, &denominator,
                (threadgroup const W *)nullptr, -1, &ignored_status, &ignored_rank, slot);
    if (*slot)
      return;
    for (uint j = 0; j < width; ++j) {
      formed[j] = wzero();
      if (j < residual_width)
        formed[j] = residual[j];
      else if (j - residual_width == coordinate)
        formed[j] = denominator;
    }
    long inserted = fibre_stage(graph_lo, width, formed, slot);
    // Validate the entire staged row before adding it to the derived graph.
    for (uint j = 0; j < width; ++j)
      toword(formed[j], slot);
    if (*slot)
      return;
    if (inserted >= 0)
      for (uint j = 0; j < width; ++j) {
        ulong at = (ulong)inserted * width + j;
        graph_lo[at] = graph_hi[at] = toword(formed[j], slot);
      }
    if (*slot)
      return;
  }

  // The affine constant uses the actual observed receiver and its own
  // denominator; source and observation are never replaced by a guessed
  // condition point.
  W denominator = flcm(source_den, observed_den, slot);
  for (uint j = 0; j < residual_width; ++j) {
    residual[j] = wzero();
    if (j < 2u * source_complex)
      residual[j] = wmul(fromword(source_lo[source_at + j]),
                         wdiv(denominator, source_den, slot), slot);
    else if (j >= source_width)
      residual[j] = wmul(fromword(observed_lo[observed_at + j - source_width]),
                         wdiv(denominator, observed_den, slot), slot);
  }
  if (*slot)
    return;
  fibre_query(basis, residual_width, residual_width, residual, &denominator,
              (threadgroup const W *)nullptr, -1, &ignored_status, &ignored_rank, slot);
  if (*slot)
    return;
  for (uint j = 0; j < residual_width; ++j)
    query[j] = wneg(residual[j]);
  for (uint j = 0; j < residual_width; ++j)
    toword(query[j], slot);
  toword(denominator, slot);
  if (*slot)
    return;
  for (uint j = 0; j < residual_width; ++j)
    rhs_lo[j] = rhs_hi[j] = toword(query[j], slot);
  rhs_lo[residual_width] = rhs_hi[residual_width] = toword(denominator, slot);
  if (*slot)
    return;
  for (uint j = residual_width; j < width; ++j)
    query[j] = wzero();
  uint disposition = 0, rank = 0;
  fibre_query(graph_lo, residual_width, width, query, &denominator,
              (threadgroup const W *)nullptr, -1, &disposition, &rank, slot);
  if (*slot)
    return;
  for (uint j = residual_width; j < width; ++j)
    query[j] = wneg(query[j]);
  for (uint j = 0; j < width; ++j)
    toword(query[j], slot);
  toword(denominator, slot);
  if (*slot)
    return;
  for (uint j = 0; j < width; ++j)
    output_lo[j] = output_hi[j] = toword(query[j], slot);
  output_lo[width] = output_hi[width] = toword(denominator, slot);
  output_lo[width + 1] = output_hi[width + 1] = (long)disposition;
  output_lo[width + 2] = output_hi[width + 2] = -1;
  output_lo[width + 3] = output_hi[width + 3] = (long)rank;
  for (uint p = 0; p < conditions; ++p) {
    bool occupied = graph_lo[(ulong)(residual_width + p) * width + residual_width + p] != 0;
    for (uint j = 0; j < conditions; ++j) {
      ulong at = (ulong)width + 4ul + (ulong)p * conditions + j;
      long value = occupied
          ? graph_lo[(ulong)(residual_width + p) * width + residual_width + j]
          : 0;
      output_lo[at] = output_hi[at] = value;
    }
  }
}

// Joint affine image and condition-domain coverage. The scalar metadata is packed
// because the CUDA ABI has 34 direct arguments while Metal exposes 31 buffer slots.
// The packing contains only launch metadata; all numerical carriers remain resident.
kernel void section_constitutive_condition_image(
    device const long *basis [[buffer(0)]], device const long *source_lo [[buffer(1)]],
    device const long *source_hi [[buffer(2)]], device const long *condition_lo [[buffer(3)]],
    device const long *condition_hi [[buffer(4)]], device long *graph_lo [[buffer(5)]],
    device long *graph_hi [[buffer(6)]], device long *rhs_lo [[buffer(7)]],
    device long *rhs_hi [[buffer(8)]], device long *joint_lo [[buffer(9)]],
    device long *joint_hi [[buffer(10)]], device long *domain_basis_lo [[buffer(11)]],
    device long *domain_basis_hi [[buffer(12)]], device long *output_basis_lo [[buffer(13)]],
    device long *output_basis_hi [[buffer(14)]], device long *domain_lo [[buffer(15)]],
    device long *domain_hi [[buffer(16)]], device long *output_lo [[buffer(17)]],
    device long *output_hi [[buffer(18)]], device long *coverage_lo [[buffer(19)]],
    device long *coverage_hi [[buffer(20)]], device long *safe_lo [[buffer(21)]],
    device long *safe_hi [[buffer(22)]], device uint *slot [[buffer(23)]],
    device const uint *census [[buffer(24)]], device const uint *lineage [[buffer(25)]],
    constant uint *shape [[buffer(26)]], threadgroup W *scratch [[threadgroup(0)]],
    uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, shape[7], slot))
    return;

  uint source_at = shape[0], source_denominator_at = shape[1], source_disposition_at = shape[2];
  uint ps = shape[3], ns = shape[4], nc = shape[5], y = shape[6];
  ulong mixed = (ulong)ns * nc;
  ulong source_linear = (ulong)ns + nc;
  if (!ns || !nc || !y || (y & 1u) || !ps
      || mixed > 0x7fffffffffffffffUL
      || source_linear > 0x7fffffffffffffffUL - mixed) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  ulong source_inner = source_linear + mixed;
  if (source_inner > 0x7fffffffffffffffUL / 2ul) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  ulong sw64 = 2ul * source_inner;
  ulong w64 = sw64 + y;
  ulong c64 = 2ul * nc;
  ulong joint_target64 = c64 + y;
  ulong k64 = w64 + joint_target64;
  if (w64 < sw64 || k64 < w64 || ps > w64 || sw64 > 0xfffffffbUL || w64 > 0xfffffffbUL || k64 > 0xfffffffbUL
      || c64 > 0xfffffffbUL || joint_target64 > 0xfffffffbUL) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  uint sw = (uint)sw64, width = (uint)w64, condition_width = (uint)c64;
  uint joint_target = (uint)joint_target64, width_with_joint = (uint)k64;
  uint pk = ps + condition_width;
  ulong condition_words = (ulong)pk + 4ul + (ulong)condition_width * condition_width;
  if (condition_words > 0xfffffffbUL) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  for (ulong i = 0; i < condition_words; ++i)
    if (condition_lo[i] != condition_hi[i]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  long condition_den_word = condition_lo[pk];
  long condition_status = condition_lo[pk + 1u];
  if (condition_den_word <= 0 || condition_status < 0 || condition_status > 2) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  W source_den = fibre_current_denominator(source_lo, source_hi,
                                           source_denominator_at,
                                           source_disposition_at, slot);
  W condition_den = fromword(condition_den_word);
  if (*slot)
    return;
  for (uint i = 0; i < 2u * ns; ++i)
    if (source_lo[source_at + i] != source_hi[source_at + i]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }

  threadgroup W *residual = scratch;
  threadgroup W *row = residual + width;
  threadgroup W *query = row + width_with_joint;
  for (ulong i = 0; i < (ulong)width_with_joint * width_with_joint; ++i)
    graph_lo[i] = graph_hi[i] = 0;
  for (uint i = 0; i <= width; ++i)
    rhs_lo[i] = rhs_hi[i] = 0;
  rhs_lo[width] = rhs_hi[width] = 1;
  condition_empty_report(joint_lo, joint_hi, width, joint_target);
  condition_empty_report(domain_lo, domain_hi, width, condition_width);
  condition_empty_report(output_lo, output_hi, width, y);
  for (uint i = 0; i < 4u + condition_width + width; ++i)
    coverage_lo[i] = coverage_hi[i] = 0;
  coverage_lo[1] = coverage_hi[1] = -1;
  coverage_lo[2] = coverage_hi[2] = 1;
  coverage_lo[3u + condition_width] = coverage_hi[3u + condition_width] = 1;
  for (uint i = 0; i < y + 2u; ++i)
    safe_lo[i] = safe_hi[i] = 0;
  safe_lo[y] = safe_hi[y] = 1;
  safe_lo[y + 1u] = safe_hi[y + 1u] = 1;
  if (condition_status == 1) {
    coverage_lo[0] = coverage_hi[0] = 3;
    for (uint i = 0; i < ps; ++i)
      joint_lo[i] = joint_hi[i] = domain_lo[i] = domain_hi[i]
          = output_lo[i] = output_hi[i] = rhs_lo[i] = rhs_hi[i] = condition_lo[i];
    rhs_lo[width] = rhs_hi[width] = condition_den_word;
    joint_lo[width_with_joint] = joint_hi[width_with_joint]
        = domain_lo[width + condition_width] = domain_hi[width + condition_width]
        = output_lo[width + y] = output_hi[width + y] = condition_den_word;
    return;
  }

  uint ignored = 0, rank = 0;
  for (uint column = 0; column < joint_target; ++column) {
    for (uint i = 0; i < width; ++i)
      residual[i] = wzero();
    W denominator = wi64(1);
    if (column < condition_width) {
      ulong vbase = (ulong)pk + 4ul + (ulong)column * condition_width;
      denominator = source_den;
      for (uint i = 0; i < condition_width; ++i)
        residual[2u * ns + i] = wmul(fromword(condition_lo[vbase + i]), source_den, slot);
      for (uint a = 0; a < nc; ++a)
        for (uint b = 0; b < ns; ++b) {
          W product[3];
          phaseprod(fromword(source_lo[source_at + 2u * b]),
                    fromword(source_lo[source_at + 2u * b + 1u]), wi64(1),
                    fromword(condition_lo[vbase + 2u * a]),
                    fromword(condition_lo[vbase + 2u * a + 1u]), wi64(1), product, slot);
          uint at = 2u * ns + condition_width + 2u * (a * ns + b);
          residual[at] = product[0];
          residual[at + 1u] = product[1];
        }
    } else {
      residual[sw + column - condition_width] = wi64(1);
    }
    if (*slot)
      return;
    fibre_query(basis, width, width, residual, &denominator,
                (threadgroup const W *)nullptr, -1, &ignored, &rank, slot);
    if (*slot)
      return;
    for (uint i = 0; i < width_with_joint; ++i)
      row[i] = i < width ? residual[i] : wzero();
    if (column < condition_width) {
      ulong vbase = (ulong)pk + 4ul + (ulong)column * condition_width;
      for (uint i = 0; i < condition_width; ++i)
        row[width + i] = wmul(fromword(condition_lo[vbase + i]), denominator, slot);
    } else {
      row[width + condition_width + column - condition_width] = denominator;
    }
    if (*slot)
      return;
    condition_stage_row(graph_lo, graph_hi, width_with_joint, row, slot);
    if (*slot)
      return;
  }

  W denominator = wmul(source_den, condition_den, slot);
  for (uint i = 0; i < width; ++i)
    residual[i] = wzero();
  for (uint i = 0; i < 2u * ns; ++i)
    residual[i] = wmul(fromword(source_lo[source_at + i]), condition_den, slot);
  for (uint i = 0; i < condition_width; ++i)
    residual[2u * ns + i] = wmul(fromword(condition_lo[ps + i]), source_den, slot);
  for (uint a = 0; a < nc; ++a)
    for (uint b = 0; b < ns; ++b) {
      W product[3];
      phaseprod(fromword(source_lo[source_at + 2u * b]),
                fromword(source_lo[source_at + 2u * b + 1u]), wi64(1),
                fromword(condition_lo[ps + 2u * a]),
                fromword(condition_lo[ps + 2u * a + 1u]), wi64(1), product, slot);
      uint at = 2u * ns + condition_width + 2u * (a * ns + b);
      residual[at] = product[0];
      residual[at + 1u] = product[1];
    }
  if (*slot)
    return;
  fibre_query(basis, width, width, residual, &denominator,
              (threadgroup const W *)nullptr, -1, &ignored, &rank, slot);
  if (*slot)
    return;
  for (uint i = 0; i < width_with_joint; ++i)
    query[i] = i < width ? wneg(residual[i]) : wzero();
  for (uint i = 0; i < width; ++i)
    toword(query[i], slot);
  toword(denominator, slot);
  if (*slot)
    return;
  for (uint i = 0; i < width; ++i)
    rhs_lo[i] = rhs_hi[i] = toword(query[i], slot);
  rhs_lo[width] = rhs_hi[width] = toword(denominator, slot);
  if (*slot)
    return;
  uint status = 0;
  fibre_query(graph_lo, width, width_with_joint, query, &denominator,
              (threadgroup const W *)nullptr, -1, &status, &rank, slot);
  if (*slot)
    return;
  for (uint i = width; i < width_with_joint; ++i)
    query[i] = wneg(query[i]);
  if (status != 1) {
    W common = flcm(denominator, condition_den, slot);
    for (uint i = 0; i < width_with_joint; ++i)
      query[i] = wmul(query[i], wdiv(common, denominator, slot), slot);
    for (uint i = 0; i < condition_width; ++i)
      query[width + i] = wadd(query[width + i],
                              wmul(fromword(condition_lo[ps + i]),
                                   wdiv(common, condition_den, slot), slot), slot);
    denominator = common;
    wnorm(query, width_with_joint, &denominator, slot);
  }
  if (*slot)
    return;
  condition_store_report(graph_lo, width, width_with_joint, query, denominator,
                         status, rank, joint_lo, joint_hi, slot);
  if (*slot)
    return;
  condition_project(joint_lo, width, joint_target, 0, condition_width,
                    domain_basis_lo, domain_basis_hi, domain_lo, domain_hi, row, slot);
  condition_project(joint_lo, width, joint_target, condition_width, y,
                    output_basis_lo, output_basis_hi, output_lo, output_hi, row, slot);
  if (*slot)
    return;
  if (status == 1) {
    for (uint i = 0; i < condition_width; ++i)
      row[i] = fromword(condition_lo[ps + i]);
    for (uint i = 0; i < width; ++i)
      query[i] = fromword(joint_lo[i]);
    condition_coverage_write(2, -1, row, condition_den, condition_width, query,
                              fromword(joint_lo[width_with_joint]), width, width,
                              coverage_lo, coverage_hi, slot);
    return;
  }
  W domain_den = fromword(domain_lo[width + condition_width]);
  W residual_den = flcm(condition_den, domain_den, slot);
  for (uint i = 0; i < condition_width; ++i)
    query[i] = wsub(wmul(fromword(condition_lo[ps + i]),
                         wdiv(residual_den, condition_den, slot), slot),
                    wmul(fromword(domain_lo[width + i]),
                         wdiv(residual_den, domain_den, slot), slot), slot);
  if (*slot)
    return;
  fibre_query(domain_basis_lo, condition_width, condition_width, query, &residual_den,
              (threadgroup const W *)nullptr, -1, &ignored, &rank, slot);
  if (*slot)
    return;
  long failed = -1;
  bool partial = condition_nonzero(query, condition_width);
  if (!partial)
    for (uint p = 0; p < condition_width; ++p) {
      for (uint i = 0; i < condition_width; ++i)
        query[i] = fromword(condition_lo[pk + 4u + (ulong)p * condition_width + i]);
      residual_den = wi64(1);
      fibre_query(domain_basis_lo, condition_width, condition_width, query, &residual_den,
                  (threadgroup const W *)nullptr, -1, &ignored, &rank, slot);
      if (*slot)
        return;
      if (condition_nonzero(query, condition_width)) {
        partial = true;
        failed = (long)p;
        break;
      }
    }
  if (partial) {
    for (uint i = 0; i < condition_width; ++i) {
      W value = fromword(condition_lo[ps + i]);
      if (failed >= 0)
        value = wadd(value, wmul(condition_den,
                                 fromword(condition_lo[pk + 4u
                                                       + (ulong)failed * condition_width + i]),
                                 slot), slot);
      row[i] = value;
    }
    if (*slot)
      return;
    condition_coverage_write(1, failed, row, condition_den, condition_width, query,
                              residual_den, condition_width, width, coverage_lo, coverage_hi, slot);
  }
  if (*slot)
    return;
  for (uint i = 0; i < y; ++i)
    safe_lo[i] = safe_hi[i] = output_lo[width + i];
  safe_lo[y] = safe_hi[y] = output_lo[width + y];
  safe_lo[y + 1u] = safe_hi[y + 1u]
      = partial ? 1 : output_lo[width + y + 1u];
}

// Restrict a complete-domain joint affine family by an actual later output.
// Homogenization pins the base-point coefficient to one, retaining absolute
// condition coordinates and the complete vertical fibre.
kernel void section_constitutive_condition_receive(
    device const long *joint [[buffer(0)]], device const long *joint_hi [[buffer(1)]],
    constant uint &joint_source_width [[buffer(2)]], constant uint &condition_width [[buffer(3)]],
    constant uint &output_width [[buffer(4)]], device const long *coverage [[buffer(5)]],
    device const long *coverage_hi [[buffer(6)]], device const long *observed_lo [[buffer(7)]],
    device const long *observed_hi [[buffer(8)]], constant uint &observed_at [[buffer(9)]],
    constant uint &observed_denominator_at [[buffer(10)]],
    constant uint &observed_disposition_at [[buffer(11)]],
    device long *graph_lo [[buffer(12)]], device long *graph_hi [[buffer(13)]],
    device long *rhs_lo [[buffer(14)]], device long *rhs_hi [[buffer(15)]],
    device long *output_lo [[buffer(16)]], device long *output_hi [[buffer(17)]],
    device uint *slot [[buffer(18)]], device const uint *census [[buffer(19)]],
    device const uint *lineage [[buffer(20)]], constant uint &lineage_count [[buffer(21)]],
    threadgroup W *scratch [[threadgroup(0)]], uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;

  ulong c = (ulong)condition_width;
  ulong y = (ulong)output_width;
  ulong j64 = c + y;
  ulong k64 = j64 + 1ul;
  ulong joint_width64 = (ulong)joint_source_width + j64;
  if (!condition_width || !output_width || (condition_width & 1u) || (output_width & 1u)
      || k64 > 0xfffffffbUL || joint_width64 > 0xfffffffbUL
      || !coverage || !coverage_hi || coverage[0] != coverage_hi[0] || coverage[0] != 0u) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  uint condition_count = (uint)c;
  uint response_count = (uint)y;
  uint joint_target = (uint)j64;
  uint width = (uint)k64;
  uint joint_width = (uint)joint_width64;
  ulong report_words = (ulong)joint_width + 4ul + (ulong)joint_target * joint_target;
  for (ulong i = 0; i < report_words; ++i)
    if (joint[i] != joint_hi[i]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  ulong output_words = (ulong)condition_count * condition_count + (ulong)width + 4ul;
  if (joint[joint_source_width + joint_target] <= 0
      || (joint[joint_source_width + joint_target + 1u] != 0
          && joint[joint_source_width + joint_target + 1u] != 2)
      || output_words > 0xfffffffbUL) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  W den = fibre_current_denominator(observed_lo, observed_hi,
                                    observed_denominator_at,
                                    observed_disposition_at, slot);
  if (*slot)
    return;
  for (uint i = 0; i < response_count; ++i)
    if (observed_lo[observed_at + i] != observed_hi[observed_at + i]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }

  threadgroup W *row = scratch;
  threadgroup W *query = row + width;
  for (ulong i = 0; i < (ulong)width * width; ++i)
    graph_lo[i] = graph_hi[i] = 0;
  uint source_for_query = 1u + response_count;
  for (uint p = 0; p <= joint_target; ++p) {
    row[0] = p == 0 ? fromword(joint[joint_source_width + joint_target]) : wzero();
    for (uint i = 0; i < response_count; ++i) {
      row[1u + i] = p == 0
          ? fromword(joint[joint_source_width + condition_count + i])
          : fromword(joint[(ulong)joint_source_width + joint_target + 4ul
                           + (ulong)(p - 1u) * joint_target + condition_count + i]);
    }
    for (uint i = 0; i < condition_count; ++i) {
      row[source_for_query + i] = p == 0 ? fromword(joint[joint_source_width + i])
                                         : fromword(joint[(ulong)joint_source_width + joint_target
                                                          + 4ul + (ulong)(p - 1u) * joint_target + i]);
    }
    long inserted = fibre_stage(graph_lo, width, row, slot);
    for (uint i = 0; i < width; ++i)
      toword(row[i], slot);
    if (*slot)
      return;
    if (inserted >= 0)
      for (uint i = 0; i < width; ++i) {
        ulong at = (ulong)inserted * width + i;
        long value = toword(row[i], slot);
        graph_lo[at] = graph_hi[at] = value;
      }
    if (*slot)
      return;
  }

  query[0] = den;
  for (uint i = 0; i < response_count; ++i)
    query[1u + i] = fromword(observed_lo[observed_at + i]);
  for (uint i = source_for_query; i < width; ++i)
    query[i] = wzero();
  for (uint i = 0; i < source_for_query; ++i)
    rhs_lo[i] = rhs_hi[i] = toword(query[i], slot);
  rhs_lo[source_for_query] = rhs_hi[source_for_query] = toword(den, slot);
  if (*slot)
    return;

  uint status = 0, rank = 0;
  fibre_query(graph_lo, source_for_query, width, query, &den,
              (threadgroup const W *)nullptr, -1, &status, &rank, slot);
  if (*slot)
    return;
  for (uint i = source_for_query; i < width; ++i)
    query[i] = wneg(query[i]);
  condition_store_report(graph_lo, source_for_query, width, query, den, status, rank,
                         output_lo, output_hi, slot);
}

// The current relation consumes a source point and, when paired, a receiving
// point. The returned section retains the original complete vertical fibre
// before the staged row joins the continuing relation.
kernel void section_constitutive_current(
    device long *basis_lo [[buffer(0)]], device long *basis_hi [[buffer(1)]],
    device const long *source_lo [[buffer(2)]], device const long *source_hi [[buffer(3)]],
    constant uint &source_at [[buffer(4)]], constant uint &source_denominator_at [[buffer(5)]],
    constant uint &source_disposition_at [[buffer(6)]],
    device const long *receiving_lo [[buffer(7)]], device const long *receiving_hi [[buffer(8)]],
    constant uint &receiving_at [[buffer(9)]], constant uint &receiving_denominator_at [[buffer(10)]],
    constant uint &receiving_disposition_at [[buffer(11)]], constant uint &source_width [[buffer(12)]],
    constant uint &target_width [[buffer(13)]], constant uint &paired [[buffer(14)]],
    device long *output_lo [[buffer(15)]], device long *output_hi [[buffer(16)]],
    device uint *slot [[buffer(17)]], device const uint *census [[buffer(18)]],
    device const uint *lineage [[buffer(19)]], constant uint &lineage_count [[buffer(20)]],
    threadgroup W *scratch [[threadgroup(0)]], uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  uint width = source_width + target_width;
  if (!source_width || !target_width || width < source_width || paired > 1) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  W source_den = fibre_current_denominator(source_lo, source_hi,
                                           source_denominator_at,
                                           source_disposition_at, slot);
  W receiving_den = paired
      ? fibre_current_denominator(receiving_lo, receiving_hi,
                                  receiving_denominator_at,
                                  receiving_disposition_at, slot)
      : wi64(1);
  if (*slot)
    return;
  W common = paired ? flcm(source_den, receiving_den, slot) : source_den;
  if (*slot)
    return;

  threadgroup W *query = scratch;
  threadgroup W *formed = query + width;
  for (uint j = 0; j < width; ++j) {
    W value = wzero();
    if (j < source_width) {
      if (source_lo[source_at + j] != source_hi[source_at + j]) {
        atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                                 memory_order_relaxed);
        return;
      }
      value = fromword(source_lo[source_at + j]);
      query[j] = value;
      formed[j] = wmul(value, wdiv(common, source_den, slot), slot);
    } else {
      query[j] = wzero();
      if (paired) {
        uint at = receiving_at + j - source_width;
        if (receiving_lo[at] != receiving_hi[at]) {
          atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                                   memory_order_relaxed);
          return;
        }
        value = fromword(receiving_lo[at]);
      }
      formed[j] = wmul(value, wdiv(common, receiving_den, slot), slot);
    }
  }
  if (*slot)
    return;
  W denominator = source_den;
  uint disposition = 0, rank = 0;
  fibre_query(basis_lo, source_width, width, query, &denominator,
              (threadgroup const W *)nullptr, -1, &disposition, &rank, slot);
  if (*slot)
    return;
  long inserted = paired ? fibre_stage(basis_lo, width, formed, slot) : -1;
  if (*slot)
    return;
  for (uint j = 0; j < width; ++j)
    if (j >= source_width)
      query[j] = wneg(query[j]);

  // Validate every exterior conversion before publishing either the returned
  // section or the staged row into the continuing relation.
  for (uint j = 0; j < width; ++j) {
    toword(query[j], slot);
    if (inserted >= 0)
      toword(formed[j], slot);
  }
  toword(denominator, slot);
  if (*slot)
    return;
  for (uint p = 0; p < target_width; ++p) {
    bool occupied = basis_lo[(ulong)(source_width + p) * width + source_width + p] != 0;
    for (uint j = 0; j < target_width; ++j) {
      ulong at = (ulong)width + 4ul + (ulong)p * target_width + j;
      long value = occupied
          ? basis_lo[(ulong)(source_width + p) * width + source_width + j]
          : 0;
      output_lo[at] = output_hi[at] = value;
    }
  }
  for (uint j = 0; j < width; ++j)
    output_lo[j] = output_hi[j] = toword(query[j], slot);
  output_lo[width] = output_hi[width] = toword(denominator, slot);
  output_lo[width + 1] = output_hi[width + 1] = (long)disposition;
  output_lo[width + 2] = output_hi[width + 2] = inserted;
  output_lo[width + 3] = output_hi[width + 3] = (long)rank + (inserted >= 0 ? 1 : 0);
  if (*slot)
    return;
  if (inserted >= 0)
    for (uint j = 0; j < width; ++j) {
      ulong at = (ulong)inserted * width + j;
      basis_lo[at] = basis_hi[at] = toword(formed[j], slot);
    }
}

// Construct s ⊕ c ⊕ (c ⊗ s) from two complete complex rational currents.
// The mixed products retain every source/condition pair in declaration order.
kernel void section_constitutive_bilinear_source(
    device const long *source_lo [[buffer(0)]], device const long *source_hi [[buffer(1)]],
    constant uint &source_at [[buffer(2)]], constant uint &source_denominator_at [[buffer(3)]],
    constant uint &source_disposition_at [[buffer(4)]],
    device const long *condition_lo [[buffer(5)]], device const long *condition_hi [[buffer(6)]],
    constant uint &condition_at [[buffer(7)]], constant uint &condition_denominator_at [[buffer(8)]],
    constant uint &condition_disposition_at [[buffer(9)]], constant uint &source_complex [[buffer(10)]],
    constant uint &condition_complex [[buffer(11)]], device long *output_lo [[buffer(12)]],
    device long *output_hi [[buffer(13)]], device uint *slot [[buffer(14)]],
    device const uint *census [[buffer(15)]], device const uint *lineage [[buffer(16)]],
    constant uint &lineage_count [[buffer(17)]], threadgroup W *scratch [[threadgroup(0)]],
    uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  ulong width64 = 2ul * ((ulong)source_complex + condition_complex
                         + (ulong)source_complex * condition_complex);
  if (!source_complex || !condition_complex || width64 >= 0xfffffffful) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  uint width = (uint)width64;
  W source_den = fibre_current_denominator(source_lo, source_hi,
                                           source_denominator_at,
                                           source_disposition_at, slot);
  W condition_den = fibre_current_denominator(condition_lo, condition_hi,
                                              condition_denominator_at,
                                              condition_disposition_at, slot);
  if (*slot)
    return;
  W common = wmul(source_den, condition_den, slot);
  for (uint j = 0; j < 2u * source_complex; ++j) {
    if (source_lo[source_at + j] != source_hi[source_at + j])
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
    scratch[j] = wmul(fromword(source_lo[source_at + j]), condition_den, slot);
  }
  for (uint j = 0; j < 2u * condition_complex; ++j) {
    if (condition_lo[condition_at + j] != condition_hi[condition_at + j])
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
    scratch[2u * source_complex + j] =
        wmul(fromword(condition_lo[condition_at + j]), source_den, slot);
  }
  if (*slot)
    return;
  uint mixed_at = 2u * (source_complex + condition_complex);
  W one = wi64(1);
  for (uint c = 0; c < condition_complex; ++c)
    for (uint s = 0; s < source_complex; ++s) {
      W product[3];
      phaseprod(fromword(source_lo[source_at + 2u * s]),
                fromword(source_lo[source_at + 2u * s + 1u]), one,
                fromword(condition_lo[condition_at + 2u * c]),
                fromword(condition_lo[condition_at + 2u * c + 1u]), one,
                product, slot);
      uint at = mixed_at + 2u * (c * source_complex + s);
      scratch[at] = product[0];
      scratch[at + 1u] = product[1];
    }
  if (*slot)
    return;
  wnorm(scratch, width, &common, slot);
  for (uint j = 0; j < width; ++j)
    toword(scratch[j], slot);
  toword(common, slot);
  if (*slot)
    return;
  for (uint j = 0; j < width; ++j)
    output_lo[j] = output_hi[j] = toword(scratch[j], slot);
  output_lo[width] = output_hi[width] = toword(common, slot);
}

// Push both actual source branches through their producing-to-current
// unit-phase frame.  The source section remains a complete two-branch carrier;
// this transport does not read a paired-junction enclosure or choose a centre.
kernel void section_field_source_frame(
    device const long *source_lo [[buffer(0)]], device const long *source_hi [[buffer(1)]],
    device const long *before_lo [[buffer(2)]], device const long *before_hi [[buffer(3)]],
    device const long *current_lo [[buffer(4)]], device const long *current_hi [[buffer(5)]],
    constant uint &nodes [[buffer(6)]], device long *output_lo [[buffer(7)]],
    device long *output_hi [[buffer(8)]], device uint *slot [[buffer(9)]],
    device const uint *census [[buffer(10)]], device const uint *lineage [[buffer(11)]],
    constant uint &lineage_count [[buffer(12)]], threadgroup W *scratch [[threadgroup(0)]],
    uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  if (!nodes || nodes > 0xffffffffu / 4u || source_lo[4u * nodes] <= 0) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  for (uint j = 0; j <= 4u * nodes; ++j)
    if (source_lo[j] != source_hi[j]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  for (uint node = 0; node < nodes; ++node) {
    for (uint j = 0; j < 3; ++j)
      if (before_lo[3u * node + j] != before_hi[3u * node + j]
          || current_lo[3u * node + j] != current_hi[3u * node + j]) {
        atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                                 memory_order_relaxed);
        return;
      }
    for (uint frame = 0; frame < 2; ++frame) {
      device const long *g = frame ? current_lo + 3u * node : before_lo + 3u * node;
      W norm = wadd(wmul(fromword(g[0]), fromword(g[0]), slot),
                    wmul(fromword(g[1]), fromword(g[1]), slot), slot);
      W denom = wmul(fromword(g[2]), fromword(g[2]), slot);
      if (g[2] <= 0 || *slot || !ueq(norm.m, denom.m)) {
        atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                                 memory_order_relaxed);
        return;
      }
    }
  }
  if (*slot)
    return;
  W common = wi64(1);
  for (uint pass = 0; pass < 2; ++pass)
    for (uint node = 0; node < nodes; ++node) {
      device const long *a = before_lo + 3u * node;
      device const long *b = current_lo + 3u * node;
      W crossing[3];
      phaseprod(fromword(b[0]), fromword(b[1]), fromword(b[2]), fromword(a[0]),
                wneg(fromword(a[1])), fromword(a[2]), crossing, slot);
      for (uint branch = 0; branch < 2; ++branch) {
        uint at = 4u * node + 2u * branch;
        W value[3];
        phaseprod(crossing[0], crossing[1], crossing[2],
                  fromword(source_lo[at]), fromword(source_lo[at + 1u]),
                  fromword(source_lo[4u * nodes]), value, slot);
        if (*slot)
          return;
        if (pass == 0)
          common = flcm(common, value[2], slot);
        else {
          scratch[at] = wmul(value[0], wdiv(common, value[2], slot), slot);
          scratch[at + 1u] = wmul(value[1], wdiv(common, value[2], slot), slot);
        }
        if (*slot)
          return;
      }
    }
  wnorm(scratch, 4u * nodes, &common, slot);
  for (uint j = 0; j < 4u * nodes; ++j)
    toword(scratch[j], slot);
  toword(common, slot);
  if (*slot)
    return;
  for (uint j = 0; j < 4u * nodes; ++j)
    output_lo[j] = output_hi[j] = toword(scratch[j], slot);
  output_lo[4u * nodes] = output_hi[4u * nodes] = toword(common, slot);
}

// Differential receiver of a complete affine current fibre.  Any nonzero
// image of a vertical direction remains unresolved; no particular fibre point
// is selected to manufacture a differential value.
kernel void section_constitutive_differential(
    device const long *lo [[buffer(0)]], device const long *hi [[buffer(1)]],
    constant uint &source_width [[buffer(2)]], constant uint &target_width [[buffer(3)]],
    constant uint &first_complex [[buffer(4)]], constant uint &pairs [[buffer(5)]],
    device const long *coverage_lo [[buffer(6)]], device const long *coverage_hi [[buffer(7)]],
    device long *output_lo [[buffer(8)]], device long *output_hi [[buffer(9)]],
    device uint *slot [[buffer(10)]], device const uint *census [[buffer(11)]],
    device const uint *lineage [[buffer(12)]], constant uint &lineage_count [[buffer(13)]],
    uint3 tid [[thread_position_in_grid]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  ulong width64 = (ulong)source_width + target_width;
  if (!source_width || !target_width || width64 >= 0xfffffffful || !pairs || pairs > 63
      || (target_width & 1u)
      || (ulong)first_complex + 2ul * pairs > (ulong)(target_width / 2u)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  uint width = (uint)width64;
  if (coverage_lo) {
    if (!coverage_hi || coverage_lo[0] != coverage_hi[0] || coverage_lo[0] < 0
        || coverage_lo[0] > 3) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
    if (coverage_lo[0] != 0) {
      output_lo[0] = output_hi[0] = 0;
      output_lo[1] = output_hi[1] = 0;
      output_lo[2] = output_hi[2] = as_type<long>((1ul << pairs) - 1ul);
      output_lo[3] = output_hi[3] = 0;
      output_lo[4] = output_hi[4] = 1;
      return;
    }
  }
  ulong words = width64 + 4ul + (ulong)target_width * target_width;
  for (ulong j = 0; j < words; ++j)
    if (lo[j] != hi[j]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  if (lo[width] <= 0 || lo[width + 1] < 0 || lo[width + 1] > 2) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  ulong positive = 0, negative = 0, unresolved = 0, zero = 0;
  for (uint bit = 0; bit < pairs; ++bit) {
    uint left = 2u * (first_complex + 2u * bit), right = left + 2u;
    ulong mask = 1ul << bit;
    bool variable = lo[width + 1] == 1;
    for (uint row = 0; row < target_width && !variable; ++row) {
      ulong at = width64 + 4ul + (ulong)row * target_width;
      variable = lo[at + left] != lo[at + right];
    }
    if (variable) {
      unresolved |= mask;
      continue;
    }
    W gap = wsub(fromword(lo[source_width + right]),
                 fromword(lo[source_width + left]), slot);
    if (*slot)
      return;
    if (!wzero_p(gap) && !wneg_p(gap))
      positive |= mask;
    else if (wneg_p(gap))
      negative |= mask;
    else {
      unresolved |= mask;
      zero |= mask;
    }
  }
  output_lo[0] = output_hi[0] = as_type<long>(positive);
  output_lo[1] = output_hi[1] = as_type<long>(negative);
  output_lo[2] = output_hi[2] = as_type<long>(unresolved);
  output_lo[3] = output_hi[3] = as_type<long>(zero);
  output_lo[4] = output_hi[4] = lo[width + 1];
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

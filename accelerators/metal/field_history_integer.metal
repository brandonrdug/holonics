// Signed-magnitude 256-bit history arithmetic for the complete-current material path.
//
// This file is concatenated after the resident W/enclosed helpers.  HistoryInteger is a
// separate exact carrier: W remains the signed-128 resident wire and every narrowing or
// malformed condition refuses through the shared slot.  No host numeric readback or
// floating representation participates in these helpers.

struct HistoryInteger {
  uint limb[8];
  bool negative;
  bool overflow;
};

inline HistoryInteger history_zero() {
  HistoryInteger value;
  for (uint i = 0; i < 8u; ++i)
    value.limb[i] = 0u;
  value.negative = false;
  value.overflow = false;
  return value;
}

inline bool history_zero_p(HistoryInteger value) {
  uint any = 0u;
  for (uint i = 0; i < 8u; ++i)
    any |= value.limb[i];
  return any == 0u;
}

inline HistoryInteger history_i64(long input) {
  HistoryInteger value = history_zero();
  ulong magnitude = input < 0 ? (ulong)0 - (ulong)input : (ulong)input;
  value.limb[0] = (uint)magnitude;
  value.limb[1] = (uint)(magnitude >> 32);
  value.negative = input < 0 && !history_zero_p(value);
  return value;
}

inline int history_compare_magnitude(HistoryInteger left, HistoryInteger right) {
  for (int i = 7; i >= 0; --i) {
    if (left.limb[i] != right.limb[i])
      return left.limb[i] < right.limb[i] ? -1 : 1;
  }
  return 0;
}

inline int history_compare(HistoryInteger left, HistoryInteger right) {
  if (left.negative != right.negative)
    return left.negative ? -1 : 1;
  int magnitude = history_compare_magnitude(left, right);
  return left.negative ? -magnitude : magnitude;
}

inline HistoryInteger history_add_magnitude(HistoryInteger left, HistoryInteger right) {
  HistoryInteger result = history_zero();
  ulong carry = 0ul;
  for (uint i = 0; i < 8u; ++i) {
    ulong sum = (ulong)left.limb[i] + (ulong)right.limb[i] + carry;
    result.limb[i] = (uint)sum;
    carry = sum >> 32;
  }
  result.overflow = left.overflow || right.overflow || carry != 0ul;
  return result;
}

inline HistoryInteger history_subtract_magnitude(HistoryInteger larger, HistoryInteger smaller) {
  HistoryInteger result = history_zero();
  ulong borrow = 0ul;
  for (uint i = 0; i < 8u; ++i) {
    ulong left = (ulong)larger.limb[i];
    ulong right = (ulong)smaller.limb[i] + borrow;
    result.limb[i] = (uint)(left - right);
    borrow = left < right ? 1ul : 0ul;
  }
  result.overflow = larger.overflow || smaller.overflow || borrow != 0ul;
  return result;
}

inline HistoryInteger history_negate(HistoryInteger value) {
  if (!history_zero_p(value))
    value.negative = !value.negative;
  return value;
}

inline HistoryInteger history_add(HistoryInteger left, HistoryInteger right) {
  if (left.negative == right.negative) {
    HistoryInteger result = history_add_magnitude(left, right);
    result.negative = left.negative && !history_zero_p(result);
    return result;
  }
  int ordering = history_compare_magnitude(left, right);
  if (ordering == 0) {
    HistoryInteger result = history_zero();
    result.overflow = left.overflow || right.overflow;
    return result;
  }
  if (ordering > 0) {
    HistoryInteger result = history_subtract_magnitude(left, right);
    result.negative = left.negative;
    return result;
  }
  HistoryInteger result = history_subtract_magnitude(right, left);
  result.negative = right.negative;
  return result;
}

inline HistoryInteger history_subtract(HistoryInteger left, HistoryInteger right) {
  return history_add(left, history_negate(right));
}

inline HistoryInteger history_multiply(HistoryInteger left, HistoryInteger right) {
  HistoryInteger result = history_zero();
  for (uint left_index = 0; left_index < 8u; ++left_index) {
    ulong carry = 0ul;
    for (uint right_index = 0; right_index + left_index < 8u; ++right_index) {
      uint output = left_index + right_index;
      ulong product = (ulong)left.limb[left_index] * (ulong)right.limb[right_index]
                    + (ulong)result.limb[output] + carry;
      result.limb[output] = (uint)product;
      carry = product >> 32;
    }
    if (carry != 0ul)
      result.overflow = true;
    for (uint right_index = 8u - left_index; right_index < 8u; ++right_index) {
      if (left.limb[left_index] != 0u && right.limb[right_index] != 0u)
        result.overflow = true;
    }
  }
  result.negative = left.negative != right.negative && !history_zero_p(result);
  result.overflow = result.overflow || left.overflow || right.overflow;
  return result;
}

inline HistoryInteger operator+(HistoryInteger left, HistoryInteger right) {
  return history_add(left, right);
}
inline HistoryInteger operator-(HistoryInteger left, HistoryInteger right) {
  return history_subtract(left, right);
}
inline HistoryInteger operator-(HistoryInteger value) {
  return history_negate(value);
}
inline HistoryInteger operator*(HistoryInteger left, HistoryInteger right) {
  return history_multiply(left, right);
}
inline bool operator<(HistoryInteger left, HistoryInteger right) {
  return history_compare(left, right) < 0;
}
inline bool operator<=(HistoryInteger left, HistoryInteger right) {
  return history_compare(left, right) <= 0;
}
inline bool operator==(HistoryInteger left, HistoryInteger right) {
  return history_compare(left, right) == 0;
}
inline bool operator!=(HistoryInteger left, HistoryInteger right) {
  return history_compare(left, right) != 0;
}

inline HistoryInteger history_integer(W value) {
  HistoryInteger result = history_zero();
  for (uint i = 0; i < 4u; ++i)
    result.limb[i] = value.m.x[i];
  result.negative = value.neg && !history_zero_p(result);
  return result;
}

inline HistoryInteger history_read_integer(device const long *words, device uint *slot) {
  HistoryInteger value = history_zero();
  for (uint i = 0; i < 4u; ++i) {
    ulong word = (ulong)words[i];
    value.limb[2u * i] = (uint)word;
    value.limb[2u * i + 1u] = (uint)(word >> 32);
  }
  if (words[4] < 0 || words[4] > 1 || (words[4] != 0 && history_zero_p(value)))
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
  value.negative = words[4] != 0;
  return value;
}

inline void history_write_integer(HistoryInteger value, device long *lo, device long *hi,
                                  device uint *slot) {
  if (value.overflow) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER,
                             memory_order_relaxed);
    return;
  }
  for (uint i = 0; i < 4u; ++i) {
    ulong word = (ulong)value.limb[2u * i] | ((ulong)value.limb[2u * i + 1u] << 32);
    lo[i] = hi[i] = as_type<long>(word);
  }
  lo[4] = hi[4] = value.negative ? 1l : 0l;
}

inline W history_narrow(HistoryInteger value, device uint *slot) {
  if (value.overflow || value.limb[4] || value.limb[5] || value.limb[6] || value.limb[7]) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER,
                             memory_order_relaxed);
    return wzero();
  }
  U magnitude = uzero();
  magnitude.x[0] = value.limb[0];
  magnitude.x[1] = value.limb[1];
  magnitude.x[2] = value.limb[2];
  magnitude.x[3] = value.limb[3];
  return wof(magnitude, value.negative, slot);
}

inline W history_norm_ceiling(HistoryInteger value, device uint *slot) {
  if (value.negative || value.overflow) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER,
                             memory_order_relaxed);
    return wzero();
  }
  HistoryInteger root = history_zero();
  for (int bit = 127; bit >= 0; --bit) {
    HistoryInteger candidate = root;
    candidate.limb[(uint)bit / 32u] |= 1u << ((uint)bit % 32u);
    HistoryInteger square = candidate * candidate;
    if (!square.overflow && square <= value)
      root = candidate;
  }
  if (!(root * root == value))
    root = root + history_i64(1l);
  return history_narrow(root, slot);
}

inline void history_complex_add_product(thread HistoryInteger &real,
                                        thread HistoryInteger &imaginary,
                                        W ar, W ai, W br, W bi,
                                        bool conjugate_left = false) {
  HistoryInteger a = history_integer(ar), b = history_integer(ai);
  HistoryInteger c = history_integer(br), d = history_integer(bi);
  if (conjugate_left)
    b = -b;
  real = real + a * c - b * d;
  imaginary = imaginary + a * d + b * c;
}

// The complete material path keeps its coefficient and rounding grids in this same exact
// 256-bit carrier. `rounds` is a W counter because the caller's final error certificate is
// required to return through the resident signed-128 chart.
inline HistoryInteger complete_power(uint bit, device uint *slot) {
  HistoryInteger result = history_zero();
  if (bit >= 256u) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER,
                             memory_order_relaxed);
    return result;
  }
  result.limb[bit / 32u] = 1u << (bit % 32u);
  return result;
}

inline W complete_to_grid(HistoryInteger value, uint shift, thread W *rounds,
                          device uint *slot) {
  HistoryInteger result = history_zero();
  if (value.overflow || shift >= 256u) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER,
                             memory_order_relaxed);
    return wzero();
  }
  bool discarded = false;
  for (uint bit = 0; bit < 256u; ++bit) {
    if (!((value.limb[bit / 32u] >> (bit % 32u)) & 1u))
      continue;
    if (bit < shift)
      discarded = true;
    else
      result.limb[(bit - shift) / 32u] |= 1u << ((bit - shift) % 32u);
  }
  result.negative = value.negative && !history_zero_p(result);
  if (discarded)
    *rounds = field_add_checked(*rounds, wi64(1l), slot);
  return history_narrow(result, slot);
}

struct HistoryRemainder {
  uint limb[9];
};

inline HistoryRemainder history_remainder_zero() {
  HistoryRemainder value;
  for (uint i = 0; i < 9u; ++i)
    value.limb[i] = 0u;
  return value;
}

inline void history_remainder_shift_bit(thread HistoryRemainder &value, uint bit) {
  uint carry = bit;
  for (uint i = 0; i < 9u; ++i) {
    ulong shifted = ((ulong)value.limb[i] << 1) | (ulong)carry;
    value.limb[i] = (uint)shifted;
    carry = (uint)(shifted >> 32);
  }
}

inline int history_remainder_compare(HistoryRemainder left, HistoryRemainder right) {
  for (int i = 8; i >= 0; --i) {
    if (left.limb[i] != right.limb[i])
      return left.limb[i] < right.limb[i] ? -1 : 1;
  }
  return 0;
}

inline void history_remainder_subtract(thread HistoryRemainder &left,
                                       HistoryRemainder right) {
  ulong borrow = 0ul;
  for (uint i = 0; i < 9u; ++i) {
    ulong a = (ulong)left.limb[i];
    ulong b = (ulong)right.limb[i] + borrow;
    left.limb[i] = (uint)(a - b);
    borrow = a < b ? 1ul : 0ul;
  }
}

inline bool history_remainder_zero_p(HistoryRemainder value) {
  uint any = 0u;
  for (uint i = 0; i < 9u; ++i)
    any |= value.limb[i];
  return any == 0u;
}

inline HistoryInteger complete_divide(HistoryInteger numerator, HistoryInteger denominator,
                                     thread W *rounds, device uint *slot) {
  HistoryInteger result = history_zero();
  if (numerator.overflow || denominator.overflow || denominator.negative
      || history_zero_p(denominator)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_CARRIER,
                             memory_order_relaxed);
    return result;
  }
  HistoryRemainder remainder = history_remainder_zero();
  HistoryRemainder divisor = history_remainder_zero();
  for (uint i = 0; i < 8u; ++i)
    divisor.limb[i] = denominator.limb[i];
  for (int bit = 255; bit >= 0; --bit) {
    history_remainder_shift_bit(remainder,
        (numerator.limb[(uint)bit / 32u] >> ((uint)bit % 32u)) & 1u);
    if (history_remainder_compare(remainder, divisor) >= 0) {
      history_remainder_subtract(remainder, divisor);
      result.limb[(uint)bit / 32u] |= 1u << ((uint)bit % 32u);
    }
  }
  if (!history_remainder_zero_p(remainder))
    *rounds = field_add_checked(*rounds, wi64(1l), slot);
  result.negative = numerator.negative && !history_zero_p(result);
  return result;
}

inline void complete_complex_product(HistoryInteger ar, HistoryInteger ai,
                                     HistoryInteger br, HistoryInteger bi,
                                     thread HistoryInteger &real,
                                     thread HistoryInteger &imaginary) {
  real = ar * br - ai * bi;
  imaginary = ar * bi + ai * br;
}

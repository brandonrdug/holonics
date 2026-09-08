// Complete-current material transport. This file is concatenated after the resident W,
// junction, current-history-source and HistoryInteger helpers. All section buffers retain
// the Rust resident wire ABI: one packed W occupies two adjacent long words; history integers
// and metadata remain scalar long words. No Metal W pointer is formed from a wire buffer.

inline ulong complete_ball_words(uint n) { return 12ul * (2ul * (ulong)n + 1ul); }
inline ulong complete_forward_at(uint n) { return complete_ball_words(n) + 4ul * (ulong)n; }
inline ulong complete_source_at(uint n) { return complete_forward_at(n) + 10ul * (ulong)n; }
inline ulong complete_extra_at(uint n) { return complete_source_at(n) + 36ul * (ulong)n + 22ul; }
inline ulong complete_state_words(uint n) {
  return 60ul * (ulong)n * (ulong)n + 22ul * (ulong)n + 12ul;
}

inline W complete_wire_read(device const long *values, ulong raw_at) {
  return field_wire_read(values + raw_at, 0);
}
inline void complete_wire_write(device long *lo, device long *hi, ulong raw_at, W value,
                                device uint *slot) {
  if (raw_at & 1ul) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  field_wire_write(lo, hi, raw_at / 2ul, value, slot);
}

inline W ft_ceil_product(W left, W right, uint grain, device uint *slot) {
  if (wneg_p(left) || wneg_p(right)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return wzero();
  }
  return field_product_shift(left, right, grain, true, slot);
}

inline W complete_norm(thread const W *values, uint count, device uint *slot) {
  HistoryInteger sum = history_zero();
  for (uint i = 0; i < count; ++i) {
    HistoryInteger value = history_integer(values[i]);
    sum = sum + value * value;
  }
  return history_norm_ceiling(sum, slot);
}

inline W complete_norm(device const long *values, ulong raw_at, uint count,
                       device uint *slot) {
  HistoryInteger sum = history_zero();
  for (uint i = 0; i < count; ++i) {
    HistoryInteger value = history_integer(complete_wire_read(values, raw_at + 2ul * (ulong)i));
    sum = sum + value * value;
  }
  return history_norm_ceiling(sum, slot);
}

inline W complete_forward_error(W et, W nt, device const long *source, uint dimension,
                                uint grain, W rounding, device uint *slot) {
  W source_error = complete_wire_read(source, 6ul * (ulong)dimension + 16ul);
  W source_norm = complete_wire_read(source, 6ul * (ulong)dimension + 20ul);
  if (wneg_p(et) || wneg_p(nt) || wneg_p(source_error) || wneg_p(source_norm)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return wzero();
  }
  return field_add_checked(
      rounding,
      field_add_checked(ft_ceil_product(et, field_add_checked(source_norm, source_error, slot),
                                         grain, slot),
                        ft_ceil_product(nt, source_error, grain, slot), slot),
      slot);
}

// Metal's indirect-table runtime retains and declares the two GPU buffers in each row.
struct CompleteMaterialFactor {
  device const long *increment;
  device const long *origin;
};

kernel void section_complete_material_source_current(
    device const long *source_report [[buffer(0)]], device const CompleteMaterialFactor *tail [[buffer(1)]],
    constant uint &tail_count [[buffer(2)]], constant uint &nodes [[buffer(3)]],
    device long *out_lo [[buffer(4)]], device long *out_hi [[buffer(5)]],
    device uint *slot [[buffer(6)]], device const uint *census [[buffer(7)]],
    device const uint *lineage [[buffer(8)]], constant uint &lineage_count [[buffer(9)]],
    uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z || upstream(census, lineage, lineage_count, slot))
    return;
  uint dimension = 6u * nodes;
  ulong forward = complete_forward_at(nodes);
  ulong feature = complete_source_at(nodes);
  ulong beta = complete_ball_words(nodes);
  for (uint row = 0; row < nodes; ++row) {
  HistoryInteger real = history_read_integer(source_report + forward + 10ul * (ulong)row, slot);
  HistoryInteger imaginary = history_read_integer(
      source_report + forward + 10ul * (ulong)row + 5ul, slot);
  for (uint i = 0; i < tail_count; ++i) {
    device const long *increment = tail[i].increment;
    device const long *origin = tail[i].origin;
    if (!increment || !origin) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
    HistoryInteger kr = history_zero(), ki = history_zero();
    HistoryInteger dr = history_zero(), di = history_zero();
    history_pairing_value(origin + feature, source_report + feature, dimension, kr, ki, slot);
    W beta_real = complete_wire_read(increment, beta + 4ul * (ulong)row);
    W beta_imaginary = complete_wire_read(increment, beta + 4ul * (ulong)row + 2ul);
    complete_complex_product(history_integer(beta_real), history_integer(beta_imaginary), kr, ki,
                             dr, di);
    real = real + dr;
    imaginary = imaginary + di;
  }
  history_write_integer(real, out_lo + 10ul * (ulong)row,
                        out_hi + 10ul * (ulong)row, slot);
  history_write_integer(imaginary, out_lo + 10ul * (ulong)row + 5ul,
                        out_hi + 10ul * (ulong)row + 5ul, slot);
  }
}

kernel void section_complete_material_source_reading(
    device const long *state [[buffer(0)]], device const long *source_report [[buffer(1)]],
    device const long *refreshed [[buffer(2)]], constant uint &nodes [[buffer(3)]],
    constant uint &grain [[buffer(4)]], device long *out_lo [[buffer(5)]],
    device long *out_hi [[buffer(6)]], device uint *slot [[buffer(7)]],
    device const uint *census [[buffer(8)]], device const uint *lineage [[buffer(9)]],
    constant uint &lineage_count [[buffer(10)]], uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  ulong extra = complete_state_words(nodes) - 4ul;
  device const long *bounds = state + extra;
  device const long *exact = refreshed ? refreshed : source_report + complete_forward_at(nodes);
  W rounds = wzero();
  uint count = 2u * nodes;
  for (uint i = 0; i < count; ++i) {
    W value = complete_to_grid(history_read_integer(exact + 5ul * (ulong)i, slot),
                               2u * grain, &rounds, slot);
    complete_wire_write(out_lo, out_hi, 2ul * (ulong)i, value, slot);
  }
  W error = complete_forward_error(complete_wire_read(bounds, 0ul),
                                   complete_wire_read(bounds, 2ul),
                                   source_report + complete_source_at(nodes),
                                   6u * nodes, grain, rounds, slot);
  complete_wire_write(out_lo, out_hi, 2ul * (ulong)count, error, slot);
}

inline void complete_material_transport_prepare(
    device const long *state, device const long *origin_report, device const long *refreshed,
    device const long *query, device const long *origin, device const long *incoming,
    device const long *frame, device const long *origin_frame, device const long *covariance,
    device const long *before, device const long *current, uint nodes, uint linked, uint grain,
    ulong occurrence, device long *proposal_lo, device long *proposal_hi,
    device long *report_lo, device long *report_hi, threadgroup W *scratch, device uint *slot) {
  uint dimension = 6u * nodes;
  uint real_count = 2u * nodes;
  ulong ga = 2ul * (ulong)dimension + 8ul;
  ulong coefficients = (ulong)real_count * ((ulong)dimension / 2ul);
  ulong matrix_words = 5ul * coefficients;
  ulong m_at = ga;
  ulong a_at = ga + matrix_words;
  ulong offset_at = a_at + matrix_words;
  ulong state_extra = offset_at + 5ul * (ulong)real_count;
  ulong stride = (ulong)real_count + 1ul;
  ulong beta_at = complete_ball_words(nodes);
  ulong forward_at = complete_forward_at(nodes);
  ulong feature_at = complete_source_at(nodes);
  ulong extra_at = complete_extra_at(nodes);
  ulong state_words = complete_state_words(nodes);

  for (ulong i = 0; i < extra_at + 10ul; ++i)
    report_lo[i] = report_hi[i] = 0l;
  field_current_history_source_prepare(
      query, origin, incoming, frame, origin_frame, covariance, before, current, state,
      nodes, linked, grain, occurrence, proposal_lo, proposal_hi,
      report_lo + feature_at, report_hi + feature_at, scratch, slot);
  if (*slot)
    return;
  for (ulong i = ga; i < state_words; ++i)
    proposal_lo[i] = proposal_hi[i] = state[i];

  W old_et = complete_wire_read(state, state_extra);
  W old_nt = complete_wire_read(state, state_extra + 2ul);
  if (wneg_p(old_et) || wneg_p(old_nt) || (linked && !origin_report)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  W target_error = wzero();
  for (uint i = 0; i < real_count; ++i) {
    device const long *input = incoming + 3u * (i / 2u);
    if (input[2] <= 0) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
    W numerator = wi64(input[i % 2u]);
    W denominator = wi64(input[2]);
    W floor_value = field_signed_product_divide_2(numerator,
        wof(field_pow2(grain - 1u), false, slot), denominator, false, slot);
    W ceil_value = field_signed_product_divide_2(numerator,
        wof(field_pow2(grain - 1u), false, slot), denominator, true, slot);
    W observed = numerator.neg ? ceil_value : floor_value;
    complete_wire_write(report_lo, report_hi, 4ul * stride + 2ul * (ulong)i,
                        observed, slot);
    if (!ueq(floor_value.m, ceil_value.m) || floor_value.neg != ceil_value.neg)
      target_error = field_add_checked(target_error, wi64(1l), slot);
  }
  complete_wire_write(report_lo, report_hi, 4ul * stride + 2ul * (ulong)real_count,
                      target_error, slot);
  W target_norm = complete_norm(report_lo, 4ul * stride, real_count, slot);
  W old_rounds = wzero(), beta_rounds = wzero(), new_rounds = wzero();
  W next_et = old_et, next_nt = old_nt, numeric_error = wzero();

  if (linked) {
    device const long *source = origin_report + feature_at;
    device const long *exact = refreshed ? refreshed : origin_report + forward_at;
    for (uint i = 0; i < real_count; ++i) {
      W present = complete_to_grid(history_read_integer(exact + 5ul * (ulong)i, slot),
                                   2u * grain, &old_rounds, slot);
      complete_wire_write(report_lo, report_hi, 2ul * stride + 2ul * (ulong)i, present, slot);
    }
    W present_error = complete_forward_error(old_et, old_nt, source, dimension, grain,
                                             old_rounds, slot);
    complete_wire_write(report_lo, report_hi, 2ul * stride + 2ul * (ulong)real_count,
                        present_error, slot);

    for (uint i = 0; i < real_count; ++i) {
      W observed = complete_wire_read(report_lo, 4ul * stride + 2ul * (ulong)i);
      W old_forward = complete_wire_read(origin_report, 2ul * (ulong)i);
      W present = complete_wire_read(report_lo, 2ul * stride + 2ul * (ulong)i);
      complete_wire_write(report_lo, report_hi, 6ul * stride + 2ul * (ulong)i,
                          field_sub_checked(observed, old_forward, slot), slot);
      complete_wire_write(report_lo, report_hi, 8ul * stride + 2ul * (ulong)i,
                          field_sub_checked(present, old_forward, slot), slot);
      W difference = field_sub_checked(observed, present, slot);
      complete_wire_write(report_lo, report_hi, 10ul * stride + 2ul * (ulong)i,
                          difference, slot);
    }
    complete_wire_write(report_lo, report_hi, 6ul * stride + 2ul * (ulong)real_count,
                        field_add_checked(target_error,
                          complete_wire_read(origin_report, 2ul * (ulong)real_count), slot), slot);
    complete_wire_write(report_lo, report_hi, 8ul * stride + 2ul * (ulong)real_count,
                        field_add_checked(present_error,
                          complete_wire_read(origin_report, 2ul * (ulong)real_count), slot), slot);
    complete_wire_write(report_lo, report_hi, 10ul * stride + 2ul * (ulong)real_count,
                        field_add_checked(target_error, present_error, slot), slot);

    HistoryInteger denominator_integer = history_read_integer(source + 6ul * dimension + 10ul, slot)
                                       + complete_power(2u * grain, slot);
    for (uint i = 0; i < real_count; ++i) {
      W difference = complete_wire_read(report_lo, 10ul * stride + 2ul * (ulong)i);
      HistoryInteger numerator = history_integer(difference) * complete_power(2u * grain, slot);
      HistoryInteger quotient = complete_divide(numerator, denominator_integer, &beta_rounds, slot);
      complete_wire_write(report_lo, report_hi, beta_at + 2ul * (ulong)i,
                          history_narrow(quotient, slot), slot);
    }
    W source_error = complete_wire_read(source, 6ul * (ulong)dimension + 16ul);
    W source_norm = complete_wire_read(source, 6ul * (ulong)dimension + 20ul);
    if (wneg_p(source_error) || wneg_p(source_norm)) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
    numeric_error = field_add_checked(
        field_div_ceil(old_rounds, wi64(2l), slot),
        ft_ceil_product(beta_rounds, source_norm, grain, slot), slot);
    next_et = field_add_checked(old_et,
        field_add_checked(numeric_error,
          field_add_checked(field_div_ceil(target_error, wi64(2l), slot),
            ft_ceil_product(field_add_checked(old_nt, target_norm, slot), source_error,
                            grain, slot), slot), slot), slot);
    next_nt = field_add_checked(old_nt,
        ft_ceil_product(complete_norm(report_lo, beta_at, real_count, slot), source_norm,
                        grain, slot), slot);

    bool phase = (((ulong)source[6ul * dimension + 19ul]) & 1ul) != 0ul;
    for (uint row = 0; row < nodes; ++row) {
      HistoryInteger br = history_integer(complete_wire_read(report_lo, beta_at + 4ul * row));
      HistoryInteger bi = history_integer(complete_wire_read(report_lo, beta_at + 4ul * row + 2ul));
      for (uint column = 0; column < dimension / 2u; ++column) {
        ulong cell = 2ul * ((ulong)row * ((ulong)dimension / 2ul) + column);
        HistoryInteger dr = history_zero(), di = history_zero();
        complete_complex_product(br, bi,
            history_integer(complete_wire_read(source, 4ul * (ulong)column)),
            -history_integer(complete_wire_read(source, 4ul * (ulong)column + 2ul)), dr, di);
        history_write_integer(history_read_integer(state + m_at + 5ul * cell, slot) + dr,
                              proposal_lo + m_at + 5ul * cell,
                              proposal_hi + m_at + 5ul * cell, slot);
        history_write_integer(history_read_integer(state + m_at + 5ul * (cell + 1ul), slot) + di,
                              proposal_lo + m_at + 5ul * (cell + 1ul),
                              proposal_hi + m_at + 5ul * (cell + 1ul), slot);
        complete_complex_product(br, bi,
            history_integer(complete_wire_read(source, 4ul * (ulong)dimension + 4ul * column)),
            -history_integer(complete_wire_read(source, 4ul * (ulong)dimension + 4ul * column + 2ul)),
            dr, di);
        if (phase) { dr = -dr; di = -di; }
        history_write_integer(history_read_integer(state + a_at + 5ul * cell, slot) + dr,
                              proposal_lo + a_at + 5ul * cell,
                              proposal_hi + a_at + 5ul * cell, slot);
        history_write_integer(history_read_integer(state + a_at + 5ul * (cell + 1ul), slot) + di,
                              proposal_lo + a_at + 5ul * (cell + 1ul),
                              proposal_hi + a_at + 5ul * (cell + 1ul), slot);
      }
      HistoryInteger dr = history_zero(), di = history_zero();
      complete_complex_product(br, bi,
          history_read_integer(source + 6ul * dimension, slot),
          -history_read_integer(source + 6ul * dimension + 5ul, slot), dr, di);
      if (phase) { dr = -dr; di = -di; }
      history_write_integer(history_read_integer(state + offset_at + 10ul * row, slot) + dr,
                            proposal_lo + offset_at + 10ul * row,
                            proposal_hi + offset_at + 10ul * row, slot);
      history_write_integer(history_read_integer(state + offset_at + 10ul * row + 5ul, slot) + di,
                            proposal_lo + offset_at + 10ul * row + 5ul,
                            proposal_hi + offset_at + 10ul * row + 5ul, slot);
    }
  }

  complete_wire_write(proposal_lo, proposal_hi, state_extra, next_et, slot);
  complete_wire_write(proposal_lo, proposal_hi, state_extra + 2ul, next_nt, slot);
  if (*slot)
    return;

  for (uint row = 0; row < nodes; ++row) {
    HistoryInteger real = history_zero(), imaginary = history_zero();
    HistoryInteger internal_real = -history_read_integer(proposal_lo + offset_at + 10ul * row, slot);
    HistoryInteger internal_imaginary = -history_read_integer(
        proposal_lo + offset_at + 10ul * row + 5ul, slot);
    for (uint column = 0; column < dimension / 2u; ++column) {
      ulong cell = 2ul * ((ulong)row * ((ulong)dimension / 2ul) + column);
      HistoryInteger dr = history_zero(), di = history_zero();
      complete_complex_product(
          history_read_integer(proposal_lo + m_at + 5ul * cell, slot),
          history_read_integer(proposal_lo + m_at + 5ul * (cell + 1ul), slot),
          history_integer(complete_wire_read(report_lo + feature_at, 4ul * column)),
          history_integer(complete_wire_read(report_lo + feature_at, 4ul * column + 2ul)),
          dr, di);
      real = real + dr;
      imaginary = imaginary + di;
      complete_complex_product(
          history_read_integer(proposal_lo + a_at + 5ul * cell, slot),
          history_read_integer(proposal_lo + a_at + 5ul * (cell + 1ul), slot),
          history_integer(complete_wire_read(report_lo + feature_at,
                                             2ul * (ulong)dimension + 4ul * column)),
          history_integer(complete_wire_read(report_lo + feature_at,
                                             2ul * (ulong)dimension + 4ul * column + 2ul)),
          dr, di);
      internal_real = internal_real + dr;
      internal_imaginary = internal_imaginary + di;
    }
    if (occurrence & 1ul) {
      internal_real = -internal_real;
      internal_imaginary = -internal_imaginary;
    }
    real = real + internal_real;
    imaginary = imaginary + internal_imaginary;
    history_write_integer(real, report_lo + forward_at + 10ul * row,
                          report_hi + forward_at + 10ul * row, slot);
    history_write_integer(imaginary, report_lo + forward_at + 10ul * row + 5ul,
                          report_hi + forward_at + 10ul * row + 5ul, slot);
    complete_wire_write(report_lo, report_hi, 4ul * row,
                        complete_to_grid(real, 2u * grain, &new_rounds, slot), slot);
    complete_wire_write(report_lo, report_hi, 4ul * row + 2ul,
                        complete_to_grid(imaginary, 2u * grain, &new_rounds, slot), slot);
  }
  complete_wire_write(report_lo, report_hi, 2ul * (ulong)real_count,
                      complete_forward_error(next_et, next_nt,
                                             report_lo + feature_at, dimension, grain,
                                             new_rounds, slot), slot);
  complete_wire_write(report_lo, report_hi, extra_at,
                      next_et, slot);
  complete_wire_write(report_lo, report_hi, extra_at + 2ul,
                      next_nt, slot);
  complete_wire_write(report_lo, report_hi, extra_at + 4ul,
                      numeric_error, slot);
  complete_wire_write(report_lo, report_hi, extra_at + 6ul,
                      old_rounds, slot);
  complete_wire_write(report_lo, report_hi, extra_at + 8ul,
                      new_rounds, slot);
  if (*slot)
    return;
  for (ulong i = 0; i < beta_at + 4ul * (ulong)nodes; ++i)
    report_hi[i] = report_lo[i];
  for (ulong i = extra_at; i < extra_at + 10ul; ++i)
    report_hi[i] = report_lo[i];
}

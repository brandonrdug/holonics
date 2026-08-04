#pragma once

#include <holonics/organ/conditioning_schema.hpp>

namespace holonics::organ {

enum class conditioning_obstruction : std::uint8_t {
  none,
  invalid_morphology,
  arithmetic_refused,
  stale_return,
  continuation_refused,
  rest_refused
};

struct navigation_consequence final {
  exact::word response{};
  exact::word incidence{};
  exact::word transport{};
  exact::word codec{};
  exact::word obstruction{};
};

struct mounting_receipt final {
  exact::word organ{};
  exact::word provenance{};
  navigation_morphology before{};
  navigation_morphology after{};
  bool inherited{};
  bool conduct_changed{};
};

struct exposure_receipt final {
  exposure_occurrence occurrence{};
  navigation_consequence received{};
  navigation_morphology before{};
  navigation_morphology after{};
  bool crossing_material{};
  bool morphology_changed{};
  bool source_retained{};
};

struct reference_receipt final {
  reference_occurrence occurrence{};
  navigation_consequence consulted{};
  bool separately_retained_testimony{};
  bool applied_to_morphology{};
};

struct morphology_delta final {
  exact::word response_weight{};
  exact::word transport_weight{};
  exact::word incidence_gate{};
  exact::word codec_bias{};
  exact::word obstruction_threshold{};
};

struct training_receipt final {
  conditioning_obstruction obstruction{conditioning_obstruction::none};
  training_return returned{};
  exact::word predecessor{};
  exact::word successor{};
  exact::word continuation{};
  navigation_morphology before{};
  navigation_morphology after{};
  morphology_delta delta{};
  bool founded_by_return{};
  bool count_threshold_used{};
  bool committed{};
};

struct source_access_audit final {
  exact::word retained_source_bytes{};
  exact::word lookup_entries{};
  exact::word source_accesses_after_training{};
  bool lossless_corpus_encoding{};
  bool reusable_native_morphology{};
  bool source_detached{};
};

}  // namespace holonics::organ

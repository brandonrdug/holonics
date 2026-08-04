#pragma once

#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::organ {

enum class conditioning_option : std::uint8_t {
  response_spectrum,
  incidence,
  transport,
  codec,
  obstruction
};

struct navigation_morphology final {
  exact::word identity{};
  exact::word provenance{};
  exact::word response_weight{};
  exact::word transport_weight{};
  exact::word incidence_gate{};
  exact::word codec_bias{};
  exact::word obstruction_threshold{};
};

struct exposure_occurrence final {
  exact::word occurrence{};
  exact::word port{};
  exact::word lineage{};
  exact::word source_identity{};
  exact::word support{};
  exact::word path_length{};
  exact::word unknown_count{};
};

struct training_return final {
  exact::word occurrence{};
  exact::word return_port{};
  exact::word lineage{};
  exact::word response_weight{};
  exact::word transport_weight{};
  exact::word incidence_gate{};
  exact::word codec_bias{};
  exact::word obstruction_threshold{};
};

struct reference_occurrence final {
  exact::word occurrence{};
  exact::word lineage{};
  exact::word testimony{};
};

}  // namespace holonics::organ

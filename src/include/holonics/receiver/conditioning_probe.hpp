#pragma once

#include <holonics/exact/word.hpp>

namespace holonics::receiver {

struct conditioning_question final {
  exact::word identity{};
  exact::word receiver{};
  exact::word support{};
  exact::word path_length{};
  exact::word unknown_count{};
};

struct conditioning_consequence final {
  exact::word response{};
  exact::word incidence{};
  exact::word transport{};
  exact::word codec{};
  exact::word obstruction{};
};

struct conditioning_probe_receipt final {
  conditioning_question question{};
  exact::word body_head{};
  exact::word organ{};
  exact::word morphology_response_weight{};
  conditioning_consequence consequence{};
  bool live_body_consumed{};
  bool live_body_cloned{};
};

}  // namespace holonics::receiver

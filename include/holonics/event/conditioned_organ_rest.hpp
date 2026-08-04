#pragma once

#include <holonics/body/rest_record.hpp>
#include <holonics/organ/conditioning_receipt.hpp>

namespace holonics::event {

struct conditioned_organ_rest_record final {
  body::rest_record body{};
  organ::navigation_morphology morphology{};
};

struct conditioned_organ_rest_receipt final {
  organ::conditioning_obstruction obstruction{organ::conditioning_obstruction::none};
  body::rest_receipt body{};
  exact::word organ{};
  exact::word response_weight{};
  bool source_detached{};
};

struct conditioned_organ_remount_receipt final {
  organ::conditioning_obstruction obstruction{organ::conditioning_obstruction::none};
  body::rest_receipt body{};
  exact::word organ{};
  exact::word response_weight{};
  bool same_body{};
  bool source_replayed{};
};

}  // namespace holonics::event

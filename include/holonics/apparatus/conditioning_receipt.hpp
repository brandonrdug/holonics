#pragma once

#include <cstdint>

#include <holonics/event/conditioned_organ_rest.hpp>
#include <holonics/receiver/conditioning_probe.hpp>

namespace holonics::apparatus {

struct conditioning_foundation final {
  organ::navigation_morphology morphology{};
  body::rest_region regions[body::live_region_capacity]{};
  std::uint64_t production_seed{};
  std::uint64_t ablation_seed{};
};

struct conditioning_passage final {
  organ::exposure_occurrence exposure{};
  organ::training_return training{};
  organ::reference_occurrence reference{};
};

struct conditioning_mount final {
  conditioning_foundation foundation{};
  conditioning_passage passage{};
  receiver::conditioning_question held_out{};
};

struct excluding_fiber_receipt final {
  exact::word production_body{};
  exact::word ablation_body{};
  organ::morphology_delta excluded{};
  receiver::conditioning_probe_receipt production{};
  receiver::conditioning_probe_receipt ablated{};
  bool separately_founded{};
  bool owner_cloned{};
  bool consequence_lost{};
};

struct conditioning_observation final {
  organ::conditioning_obstruction obstruction{organ::conditioning_obstruction::none};
  organ::mounting_receipt mounting{};
  receiver::conditioning_probe_receipt before{};
  organ::exposure_receipt exposure{};
  organ::reference_receipt reference{};
  organ::training_receipt training{};
  organ::source_access_audit source_access{};
  event::conditioned_organ_rest_receipt rest{};
  event::conditioned_organ_remount_receipt remount{};
  receiver::conditioning_probe_receipt after{};
  excluding_fiber_receipt ablation{};
  exact::word final_head{};
  body::rest_region final_region{};
  bool behavior_changed{};
  bool final_continuation_valid{};
};

}  // namespace holonics::apparatus

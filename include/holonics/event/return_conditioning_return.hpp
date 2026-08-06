#pragma once

#include <holonics/event/dependent_theorem_setup.hpp>
#include <holonics/event/theorem_production_rest.hpp>
#include <holonics/event/resident_theorem_production.hpp>

namespace holonics::event {

struct return_conditioning_observation final {
  theorem_production_remount_receipt production_remount{};
  theorem_production_remount_receipt ablation_remount{};
  organ::theorem_probe_receipt production{};
  organ::theorem_probe_receipt ablated{};
  dependent_theorem_setup setup{};
  theorem_production_rest_receipt handoff{};
  exact::word production_head{};
  exact::word ablation_head{};
  bool behavior_changed{};
  bool source_detached{};
  bool dependency_exact{};
  bool handoff_continuation_valid{};
};

}  // namespace holonics::event

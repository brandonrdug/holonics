#pragma once

#include <holonics/organ/intrinsic_composition_receipt.hpp>
#include <holonics/organ/intrinsic_phase_receipt.hpp>

namespace holonics::organ {

struct intrinsic_hypergeometry_receipt final {
  intrinsic_hypergeometry_card mounted{};
  intrinsic_hypergeometry_question question{};
  intrinsic_phase_case_receipt cases[intrinsic_case_capacity]{};
  intrinsic_series_receipt series{};
  intrinsic_local_system_receipt local_system{};
  intrinsic_supported_cycle_receipt supported{};
  intrinsic_control_receipt controls{};
  intrinsic_hypergeometry_plan theory{};
  intrinsic_hypergeometry_obstruction obstruction{
      intrinsic_hypergeometry_obstruction::invalid_foundation};
  std::uint16_t source_mask{};
  bool source_currents_independent{};
  bool no_expected_invariants{};
  bool alternatives_retained{};
  bool all_exact{};
  bool theory_formed{};
};

}  // namespace holonics::organ

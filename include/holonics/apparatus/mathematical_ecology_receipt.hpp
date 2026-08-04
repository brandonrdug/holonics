#pragma once

#include <cstdint>

#include <holonics/body/continuing_body.hpp>
#include <holonics/organ/mathematical_receipt.hpp>
#include <holonics/receiver/mathematical_question.hpp>

namespace holonics::apparatus {

struct mathematical_ecology_mount final {
  organ::mathematical_foundation canonical{};
  organ::mathematical_foundation reordered{};
  body::rest_region regions[body::live_region_capacity]{};
  receiver::mathematical_question held_out{};
  receiver::mathematical_question mismatch{};
  receiver::mathematical_question unsolved{};
  std::uint64_t canonical_body_seed{};
  std::uint64_t reordered_body_seed{};
};

struct mathematical_ecology_observation final {
  organ::mathematical_neighborhood_receipt canonical{};
  organ::mathematical_neighborhood_receipt reordered{};
  organ::mathematical_neighborhood_receipt mismatch{};
  organ::mathematical_neighborhood_receipt unsolved{};
  organ::mathematical_obstruction canonical_mount{organ::mathematical_obstruction::invalid_foundation};
  organ::mathematical_obstruction reordered_mount{organ::mathematical_obstruction::invalid_foundation};
  bool storage_order_invariant{};
  bool source_detached{};
  bool exact_material_comparison{};
  bool local_incidence_only{};
  bool final_continuations_valid{};
};

}  // namespace holonics::apparatus

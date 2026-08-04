#pragma once

#include <cstdint>

#include <holonics/current/weave_receipt.hpp>

namespace holonics::apparatus {

struct realization_variant_receipt final {
  std::uint16_t partition_count{};
  std::uint16_t completion_order{};
  current::weave_snapshot successor{};
  bool non_resumable{};
};

struct weave_case_observation final {
  current::weave_semantic_observation semantic{};
  realization_variant_receipt variants[current::weave_variant_capacity]{};
  bool partition_successors_equal{};
  bool completion_successors_equal{};
};

struct weave_batch_observation final {
  std::uint16_t count{};
  weave_case_observation cases[current::weave_case_capacity]{};
};

}  // namespace holonics::apparatus

#pragma once

#include <cuda_runtime_api.h>

#include <holonics/organ/cultivated_organ_schema.hpp>

namespace holonics::apparatus {

struct cultivated_current_set final {
  cudaStream_t currents[organ::cultivation_family_count]{};
};
[[nodiscard]] bool open_cultivated_currents(cultivated_current_set &) noexcept;
[[nodiscard]] bool join_cultivated_currents(const cultivated_current_set &) noexcept;
void close_cultivated_currents(cultivated_current_set &) noexcept;

}  // namespace holonics::apparatus

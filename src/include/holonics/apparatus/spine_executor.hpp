#pragma once

#include <cstddef>

#include <holonics/apparatus/exact_executor.hpp>
#include <holonics/body/spine_execute.hpp>

namespace holonics::apparatus {

struct spine_deed_batch final {
  const exact::spine_deed_input* inputs{};
  exact::spine_deed_output* outputs{};
  std::size_t count{};
};

/// Execute the minimum-carrier spine deed family on the resident card.
[[nodiscard]] exact_executor_receipt execute_spine_deeds(spine_deed_batch batch) noexcept;

}  // namespace holonics::apparatus

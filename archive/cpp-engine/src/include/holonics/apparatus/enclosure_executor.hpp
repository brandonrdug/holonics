#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/apparatus/exact_executor.hpp>
#include <holonics/exact/enclosure_deed.hpp>

namespace holonics::apparatus {

struct enclosure_deed_batch final {
  const exact::enclosure_deed_input* inputs{};
  exact::enclosure_deed_output* outputs{};
  std::size_t count{};
};

/// Execute the certified-enclosure deed family on the resident card. The
/// returned receipt carries the deterministic crossing sizes separately from the
/// physical residency interval; neither substitutes for the returned artifacts.
[[nodiscard]] exact_executor_receipt execute_enclosure_deeds(
    enclosure_deed_batch batch) noexcept;

}  // namespace holonics::apparatus

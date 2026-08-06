#pragma once

#include <array>
#include <cstddef>
#include <string_view>

#include <holonics/body/spine_execute.hpp>

namespace holonics::tests {

inline constexpr std::size_t spine_case_count = 8;

[[nodiscard]] std::array<holonics::exact::spine_deed_input, spine_case_count> spine_cases();
[[nodiscard]] std::array<std::string_view, spine_case_count> spine_case_names();

/// The named laws this spine owes. Each predicate is one clause's falsifier.
[[nodiscard]] bool swing_laws_hold(
    const std::array<holonics::exact::spine_deed_output, spine_case_count>& out);
[[nodiscard]] bool standing_shares_rather_than_copies(
    const std::array<holonics::exact::spine_deed_output, spine_case_count>& out);
[[nodiscard]] bool open_never_concludes(
    const std::array<holonics::exact::spine_deed_output, spine_case_count>& out);
/// Phase 1, 2 and 5 laws that need no device crossing.
[[nodiscard]] bool carrier_laws_hold();
[[nodiscard]] bool substrate_laws_hold();
[[nodiscard]] bool information_laws_hold();

}  // namespace holonics::tests

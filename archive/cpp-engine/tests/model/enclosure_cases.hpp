#pragma once

#include <array>
#include <cstddef>
#include <string_view>

#include <holonics/exact/enclosure_deed.hpp>

namespace holonics::tests {

inline constexpr std::size_t enclosure_case_count = 10;

/// The declared occurrence family for the certified-enclosure organ. Every case
/// names the question it settles; none is a nearby fixture standing in for the
/// deed.
[[nodiscard]] std::array<holonics::exact::enclosure_deed_input, enclosure_case_count>
enclosure_cases();

[[nodiscard]] std::array<std::string_view, enclosure_case_count> enclosure_case_names();

/// The named returns this organ owes. Each predicate is the falsifier of one
/// clause of the Movement A contract.
[[nodiscard]] bool certified_enclosure_returns(
    const std::array<holonics::exact::enclosure_deed_output, enclosure_case_count>& outputs);

[[nodiscard]] bool certificate_ablation_holds(
    const std::array<holonics::exact::enclosure_deed_output, enclosure_case_count>& outputs);

[[nodiscard]] bool aperture_refusal_holds(
    const std::array<holonics::exact::enclosure_deed_output, enclosure_case_count>& outputs);

/// Independent host oracle: recomputes the enclosure endpoints by direct
/// interval halving over rationals held as separate integer pairs, without using
/// the dyadic carrier under test.
[[nodiscard]] bool independent_enclosure_agrees(
    const holonics::exact::enclosure_deed_input& input,
    const holonics::exact::enclosure_deed_output& output);

}  // namespace holonics::tests

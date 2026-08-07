#pragma once

#include <holonics/apparatus/blind_reconstruction_executor.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::blind_reconstruction_mount r21_case(
    const event::regular_singular_rest_record& inherited,
    const organ::binary_code_problem_card& code,
    const organ::moment_problem_card& moments) noexcept;
[[nodiscard]] organ::binary_code_problem_card r21_host_code_card() noexcept;
[[nodiscard]] organ::moment_problem_card r21_host_moment_card() noexcept;
[[nodiscard]] event::regular_singular_rest_record r21_host_regular_singular_rest() noexcept;

}  // namespace holonics::tests

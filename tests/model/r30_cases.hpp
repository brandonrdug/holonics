#pragma once

#include <holonics/apparatus/rederivation_executor.hpp>

namespace holonics::tests {
[[nodiscard]] apparatus::rederivation_mount
r30_case(const event::arithmetic_spectral_rest_record &,
         const organ::matching_problem_card &,
         const organ::lattice_problem_card &,
         const organ::cover_problem_card &) noexcept;
[[nodiscard]] organ::rederivation_foundation r30_host_foundation() noexcept;
} // namespace holonics::tests

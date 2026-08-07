#pragma once

#include <cstdint>

#include <holonics/apparatus/arithmetic_spectral_store_adapter.hpp>
#include <holonics/event/rederivation_rest.hpp>

namespace holonics::apparatus {

using rederivation_store_status = arithmetic_store_status;
using rederivation_store_receipt = arithmetic_store_receipt;

[[nodiscard]] rederivation_store_receipt
read_matching_problem_card(const char *path,
                           organ::matching_problem_card &card) noexcept;
[[nodiscard]] rederivation_store_receipt
read_lattice_problem_card(const char *path,
                          organ::lattice_problem_card &card) noexcept;
[[nodiscard]] rederivation_store_receipt
read_cover_problem_card(const char *path,
                        organ::cover_problem_card &card) noexcept;
[[nodiscard]] rederivation_store_receipt read_arithmetic_rederivation_handoff(
    const char *path, event::arithmetic_spectral_rest_record &record) noexcept;
[[nodiscard]] rederivation_store_receipt write_rederivation_handoff(
    const char *path, const event::rederivation_rest_record &record) noexcept;
[[nodiscard]] rederivation_store_receipt
read_rederivation_handoff(const char *path,
                          event::rederivation_rest_record &record) noexcept;

} // namespace holonics::apparatus

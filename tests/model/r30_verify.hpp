#pragma once
#include <cstddef>
#include <holonics/apparatus/rederivation_executor.hpp>
#include <holonics/apparatus/rederivation_store_adapter.hpp>
namespace holonics::tests {
[[nodiscard]] std::size_t
r30_verification_failures(bool, const apparatus::rederivation_store_receipt &,
                          const apparatus::rederivation_executor_receipt &,
                          const event::rederivation_observation &,
                          const organ::rederivation_workspace &,
                          const event::rederivation_rest_record &) noexcept;
}

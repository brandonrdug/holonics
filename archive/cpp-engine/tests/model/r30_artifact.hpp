#pragma once
#include <holonics/apparatus/rederivation_executor.hpp>
#include <holonics/apparatus/rederivation_store_adapter.hpp>
#include <iosfwd>
namespace holonics::tests {
void write_r30_artifact(std::ostream &, bool,
                        const apparatus::rederivation_store_receipt (&)[3],
                        const apparatus::rederivation_store_receipt &,
                        const apparatus::rederivation_store_receipt &,
                        const apparatus::rederivation_executor_receipt &,
                        const event::rederivation_observation &,
                        const event::rederivation_rest_record &, std::size_t);
}

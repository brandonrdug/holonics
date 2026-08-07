#pragma once

#include <iosfwd>

#include <holonics/event/hodge_realization_return.hpp>

namespace holonics::tests {

void write_r28_atlas(std::ostream& out,
    const event::hodge_realization_observation& observation);

}  // namespace holonics::tests

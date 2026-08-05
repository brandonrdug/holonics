#pragma once

#include <iosfwd>

#include <holonics/event/expression_geometry_return.hpp>

namespace holonics::tests {
void write_r27_atlas(std::ostream& out,
    const event::expression_geometry_observation& observation);
}  // namespace holonics::tests

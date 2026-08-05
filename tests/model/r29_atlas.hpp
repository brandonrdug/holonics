#pragma once

#include <iosfwd>

#include <holonics/event/arithmetic_spectral_return.hpp>

namespace holonics::tests {

void write_r29_atlas(std::ostream& output,
    const event::arithmetic_spectral_observation& observation,
    const organ::arithmetic_spectral_workspace& workspace);

}  // namespace holonics::tests

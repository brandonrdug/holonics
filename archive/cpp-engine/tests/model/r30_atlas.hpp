#pragma once
#include <holonics/event/rederivation_return.hpp>
#include <iosfwd>
namespace holonics::tests {
void write_r30_atlas(std::ostream &, const event::rederivation_observation &,
                     const organ::rederivation_workspace &);
}

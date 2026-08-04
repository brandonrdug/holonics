#pragma once

#include <holonics/apparatus/lean_checker_executor.hpp>

namespace holonics::tests {

[[nodiscard]] apparatus::lean_checker_mount r13_case(const char* generated_source) noexcept;

}  // namespace holonics::tests

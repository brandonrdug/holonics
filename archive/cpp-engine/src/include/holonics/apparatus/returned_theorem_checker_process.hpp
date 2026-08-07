#pragma once

#include <holonics/apparatus/lean_checker_process.hpp>

namespace holonics::apparatus {

[[nodiscard]] lean_process_receipt run_returned_theorem_checker_process(
    const codec::formal_checker_face& face,
    const event::checker_outbound_occurrence& outbound,
    const lean_process_configuration& configuration,
    event::checker_raw_return& returned) noexcept;

[[nodiscard]] lean_process_receipt run_returned_theorem_checker_source(
    const lean_source_view& source,
    const event::checker_outbound_occurrence& outbound,
    const lean_process_configuration& configuration,
    event::checker_raw_return& returned) noexcept;

}  // namespace holonics::apparatus

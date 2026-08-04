#pragma once

#include <holonics/exact/word.hpp>

namespace holonics::event {

struct serial_gluing_receipt final {
  exact::word common_predecessor{};
  exact::word first_event{};
  exact::word second_event{};
  exact::word first_output_port{};
  exact::word second_input_port{};
  exact::word intermediate_occurrence{};
  exact::word intermediate_lineage{};
  exact::word retained_boundary{};
  bool port_typed{};
  bool lineage_retained{};
  bool chronology_retained{};
};

}  // namespace holonics::event

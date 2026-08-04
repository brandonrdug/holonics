#pragma once

#include <cstdint>

#include <holonics/current/weave_schema.hpp>

namespace holonics::current {

struct restaging_receipt final {
  exact::word common_predecessor{};
  exact::word first_event{};
  exact::word second_event{};
  exact::word second_staged_predecessor{};
  exact::word read_support{};
  exact::word change_support{};
  exact::word lineage_order{};
};

struct combined_weave_delta final {
  exact::word common_predecessor{};
  exact::word event_support{};
  exact::word read_support{};
  exact::word change_support{};
  exact::word value_deltas[weave_cell_capacity]{};
  exact::word morphology_deltas[weave_cell_capacity]{};
  exact::word successor_currents[weave_cell_capacity]{};
  exact::word consequences[weave_event_capacity]{};
  exact::word stress{};
  exact::word logical_resource{};
  exact::word lineage_order{};
};

struct interchange_certificate final {
  exact::word common_predecessor{};
  exact::word left_event{};
  exact::word right_event{};
  restaging_receipt left_then_right[2]{};
  restaging_receipt right_then_left[2]{};
  combined_weave_delta canonical_delta{};
  weave_snapshot left_right{};
  weave_snapshot right_left{};
  weave_snapshot canonical{};
  bool identity_equal{};
  bool causal_order_equal{};
  bool incidence_equal{};
  bool morphology_equal{};
  bool current_equal{};
  bool consequence_equal{};
  bool obstruction_equal{};
  bool logical_resource_equal{};
  bool complete_successor_equal{};
};

struct higher_coherence_receipt final {
  exact::word common_predecessor{};
  exact::word events[3]{};
  std::uint16_t orders[coherence_permutation_capacity][3]{};
  weave_snapshot successors[coherence_permutation_capacity]{};
  bool adjacent_interchanges{};
  bool braid_equal{};
  bool complete_successors_equal{};
};

struct interaction_equalizer_receipt final {
  exact::word common_predecessor{};
  exact::word left_event{};
  exact::word right_event{};
  exact::word overlap_support{};
  exact::word interaction{};
  exact::word combined_value_delta{};
  exact::word combined_morphology_delta{};
  exact::word combined_current{};
  exact::word combined_consequence{};
  exact::word lineage{};
  weave_snapshot successor{};
  bool compatible{};
  bool equalized{};
};

}  // namespace holonics::current

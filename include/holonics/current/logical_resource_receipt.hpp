#pragma once

#include <holonics/exact/word.hpp>
#include <holonics/structure/receipt.hpp>

namespace holonics::current {

struct logical_resource_receipt final {
  using holonics_receipt = structure::receipt_marker;

  exact::word read_support;
  exact::word change_support;
  exact::word alternatives_retained;
  exact::word obstructions_retained;
  exact::word reservations_consumed;
};

static_assert(structure::receipt<logical_resource_receipt>);

}  // namespace holonics::current

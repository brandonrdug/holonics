#pragma once

#include <concepts>

namespace holonics::structure {

struct receipt_marker final {};

template<class Receipt>
concept receipt = requires {
  typename Receipt::holonics_receipt;
} && std::same_as<typename Receipt::holonics_receipt, receipt_marker>;

}  // namespace holonics::structure

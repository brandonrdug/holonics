#pragma once

#include <cstdint>

#include <holonics/exact/word.hpp>
#include <holonics/structure/receipt.hpp>

namespace holonics::apparatus {

enum class telemetry_status : std::uint8_t { unknown, calibrated_interval };

struct calibrated_integer_interval final {
  telemetry_status status;
  exact::word lower;
  exact::word upper;
  exact::word aperture;
};

struct physical_telemetry_receipt final {
  using holonics_receipt = structure::receipt_marker;

  calibrated_integer_interval elapsed_nanoseconds;
  calibrated_integer_interval resident_bytes;
  calibrated_integer_interval temperature_millikelvin;
  calibrated_integer_interval power_microwatts;
  calibrated_integer_interval energy_microjoules;
};

static_assert(structure::receipt<physical_telemetry_receipt>);

}  // namespace holonics::apparatus

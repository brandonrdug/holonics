#pragma once

#include <holonics/organ/rederivation_receipt.hpp>

namespace holonics::organ::rederivation_matching_injection_detail {

[[nodiscard]] HOLONICS_CALLABLE inline std::int64_t
power(std::int64_t base, std::uint8_t exponent) noexcept {
  std::int64_t out = 1;
  while (exponent-- != 0)
    out *= base;
  return out;
}

HOLONICS_CALLABLE inline std::uint16_t
retain(std::uint8_t side, const matching_problem_card &card,
       injection_receipt *output) noexcept {
  const auto &values = side == 0 ? card.p : card.q;
  std::uint16_t used = 0;
  for (std::uint8_t subset = 0; subset < 7; ++subset) {
    std::uint8_t indices[3]{}, count = 0;
    for (std::uint8_t bit = 0; bit < 3; ++bit)
      if ((subset & (1U << bit)) != 0)
        indices[count++] = bit;
    for (std::uint8_t forbidden = 0; forbidden < 7; ++forbidden) {
      if (count == 0) {
        output[used] = {side,
                        subset,
                        forbidden,
                        {0, 0, 0},
                        0,
                        1,
                        exact::word{card.metadata.lineage.value() + 20'000U +
                                    side * 1'000U + used}};
        ++used;
        continue;
      }
      for (std::uint8_t a = 0; a < 7; ++a) {
        if (a == forbidden)
          continue;
        if (count == 1) {
          output[used] = {
              side,
              subset,
              forbidden,
              {a, 0, 0},
              1,
              power(values[a], static_cast<std::uint8_t>(1U << indices[0])),
              exact::word{card.metadata.lineage.value() + 20'000U +
                          side * 1'000U + used}};
          ++used;
          continue;
        }
        for (std::uint8_t b = 0; b < 7; ++b) {
          if (b == forbidden || b == a)
            continue;
          if (count == 2) {
            output[used] = {
                side,
                subset,
                forbidden,
                {a, b, 0},
                2,
                power(values[a], static_cast<std::uint8_t>(1U << indices[0])) *
                    power(values[b],
                          static_cast<std::uint8_t>(1U << indices[1])),
                exact::word{card.metadata.lineage.value() + 20'000U +
                            side * 1'000U + used}};
            ++used;
            continue;
          }
          for (std::uint8_t c = 0; c < 7; ++c) {
            if (c == forbidden || c == a || c == b)
              continue;
            output[used] = {
                side,
                subset,
                forbidden,
                {a, b, c},
                3,
                power(values[a], static_cast<std::uint8_t>(1U << indices[0])) *
                    power(values[b],
                          static_cast<std::uint8_t>(1U << indices[1])) *
                    power(values[c],
                          static_cast<std::uint8_t>(1U << indices[2])),
                exact::word{card.metadata.lineage.value() + 20'000U +
                            side * 1'000U + used}};
            ++used;
          }
        }
      }
    }
  }
  return used;
}

} // namespace holonics::organ::rederivation_matching_injection_detail

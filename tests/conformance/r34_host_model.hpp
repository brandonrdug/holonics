#pragma once

#include <array>
#include <cstdint>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>

namespace r34_host {
using Matrix = std::array<std::int64_t, 4>;
struct Word {
  Matrix matrix{};
  std::vector<std::uint8_t> letters{};
  std::uint16_t ordinal{};
  std::uint64_t lineage{};
};
struct Card {
  std::uint64_t lineage{};
  std::uint8_t admitted{};
  std::uint8_t alphabet{};
  std::uint8_t length{};
  bool recharted{};
  Matrix rechart{};
  std::array<Matrix, 4> generators{};
  std::array<std::uint8_t, 4> inverse{};
};
struct Triple {
  std::array<Matrix, 8> matrices{};
  std::array<std::int64_t, 6> lower{};
  std::array<std::int64_t, 2> ordered{};
  std::array<std::int64_t, 2> symmetric{};
  std::array<std::uint16_t, 3> words{};
  std::int64_t discriminant{};
  std::int64_t gap{};
  std::uint8_t source{};
  bool branch{};
};
struct Group {
  std::array<std::int64_t, 6> lower{};
  std::array<std::int64_t, 2> roots{};
  std::uint16_t population{};
  bool branch{};
};
inline std::vector<std::int64_t> numbers(const char *path) {
  std::ifstream in{path};
  std::vector<std::int64_t> out{};
  std::int64_t value = 0;
  while (in >> value)
    out.push_back(value);
  return out;
}
inline std::string bytes(const char *path) {
  std::ifstream in{path, std::ios::binary};
  std::ostringstream out;
  out << in.rdbuf();
  return out.str();
}
inline Matrix matrix(const std::vector<std::int64_t> &v, std::size_t &at) {
  Matrix out{};
  for (auto &x : out)
    x = v.at(at++);
  return out;
}
inline Matrix multiply(const Matrix &a, const Matrix &b) {
  return {a[0] * b[0] + a[1] * b[2], a[0] * b[1] + a[1] * b[3],
          a[2] * b[0] + a[3] * b[2], a[2] * b[1] + a[3] * b[3]};
}
inline Matrix inverse(const Matrix &a) { return {a[3], -a[1], -a[2], a[0]}; }
inline std::int64_t trace(const Matrix &a) { return a[0] + a[3]; }
inline std::int64_t determinant(const Matrix &a) {
  return a[0] * a[3] - a[1] * a[2];
}
inline Card card(const char *path) {
  const auto v = numbers(path);
  std::size_t at = 4;
  Card out{};
  out.lineage = static_cast<std::uint64_t>(v.at(at++));
  out.admitted = static_cast<std::uint8_t>(v.at(at++));
  out.alphabet = static_cast<std::uint8_t>(v.at(at++));
  out.length = static_cast<std::uint8_t>(v.at(at++));
  out.recharted = v.at(at++) != 0;
  out.rechart = matrix(v, at);
  for (auto &g : out.generators)
    g = matrix(v, at);
  for (auto &i : out.inverse)
    i = static_cast<std::uint8_t>(v.at(at++));
  return out;
}
inline std::vector<Word> words(const Card &c) {
  std::array<Matrix, 4> generators = c.generators;
  if (c.recharted) {
    const auto p = inverse(c.rechart);
    for (std::uint8_t i = 0; i < c.alphabet; ++i)
      generators[i] = multiply(multiply(c.rechart, generators[i]), p);
  }
  std::vector<Word> out{};
  const auto visit = [&](auto &&self, std::vector<std::uint8_t> letters,
                         Matrix formed, std::uint8_t last) -> void {
    if (!letters.empty())
      out.push_back({formed, letters, static_cast<std::uint16_t>(out.size()),
                     c.lineage + out.size() + 1U});
    if (letters.size() >= c.length || out.size() >= c.admitted)
      return;
    for (std::uint8_t i = 0; i < c.alphabet && out.size() < c.admitted; ++i) {
      if (!letters.empty() && c.inverse[last] == i)
        continue;
      auto next = letters;
      next.push_back(i);
      self(self, next, multiply(formed, generators[i]), i);
    }
  };
  visit(visit, {}, Matrix{1, 0, 0, 1}, 0);
  return out;
}
inline Triple triple(const Word &a, const Word &b, const Word &c,
                     std::uint8_t source) {
  Triple out{};
  out.matrices[0] = a.matrix;
  out.matrices[1] = b.matrix;
  out.matrices[2] = c.matrix;
  out.matrices[3] = multiply(a.matrix, b.matrix);
  out.matrices[4] = multiply(a.matrix, c.matrix);
  out.matrices[5] = multiply(b.matrix, c.matrix);
  out.matrices[6] = multiply(out.matrices[3], c.matrix);
  out.matrices[7] = multiply(out.matrices[4], b.matrix);
  for (std::size_t i = 0; i < out.lower.size(); ++i)
    out.lower[i] = trace(out.matrices[i]);
  out.ordered = {trace(out.matrices[6]), trace(out.matrices[7])};
  out.symmetric = {out.ordered[0] + out.ordered[1],
                   out.ordered[0] * out.ordered[1]};
  out.discriminant = out.symmetric[0] * out.symmetric[0] - 4 * out.symmetric[1];
  const auto difference = out.ordered[0] - out.ordered[1];
  out.gap = difference < 0 ? -difference : difference;
  out.words = {a.ordinal, b.ordinal, c.ordinal};
  out.source = source;
  out.branch = out.ordered[0] == out.ordered[1];
  return out;
}
inline std::vector<Triple>
triples(const std::array<std::vector<Word>, 3> &populations) {
  std::vector<Triple> out{};
  for (std::uint8_t source = 0; source < 3; ++source)
    for (const auto &a : populations[source])
      for (const auto &b : populations[source])
        for (const auto &c : populations[source])
          out.push_back(triple(a, b, c, source));
  return out;
}
inline std::array<std::int64_t, 2> roots(const Triple &t) {
  return t.ordered[0] < t.ordered[1]
             ? std::array<std::int64_t, 2>{t.ordered[0], t.ordered[1]}
             : std::array<std::int64_t, 2>{t.ordered[1], t.ordered[0]};
}
inline std::vector<Group> groups(const std::vector<Triple> &triples) {
  std::vector<Group> out{};
  for (const auto &t : triples) {
    const auto r = roots(t);
    auto at = out.begin();
    while (at != out.end() && !(at->lower == t.lower && at->roots == r))
      ++at;
    if (at != out.end()) {
      ++at->population;
      continue;
    }
    out.push_back({t.lower, r, 1, t.branch});
  }
  return out;
}
inline void matrix_out(std::ostream &out, const Matrix &m) {
  for (const auto value : m)
    out << '\t' << value;
}
} // namespace r34_host

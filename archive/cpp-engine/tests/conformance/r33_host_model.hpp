#pragma once

#include <array>
#include <cstdint>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>

namespace r33_host {
using Matrix = std::array<std::int64_t, 4>;
struct Word {
  Matrix matrix{};
  std::vector<std::uint8_t> letters{};
  std::uint16_t ordinal{};
  std::uint64_t lineage{};
};
struct Card {
  std::uint64_t lineage{};
  std::uint8_t alphabet{};
  std::uint8_t length{};
  bool recharted{};
  Matrix rechart{};
  std::array<Matrix, 4> generators{};
  std::array<std::uint8_t, 4> inverse{};
};
struct Pair {
  Matrix a{}, b{}, ab{}, closed{};
  std::int64_t traces[4]{};
  std::int64_t discriminants[4]{};
  std::int8_t strata[4]{};
  std::uint8_t ranks[4]{};
  std::uint16_t left{}, right{};
  std::uint8_t source{};
};
struct Group {
  std::int64_t coordinates[4]{};
  std::int8_t strata[4]{};
  std::uint16_t population{};
  std::uint8_t rank{};
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
inline std::int8_t stratum(std::int64_t d) {
  return d < 0 ? -1 : (d == 0 ? 0 : 1);
}
inline std::uint8_t rank(const Matrix &a) {
  const Matrix n{a[0] - 1, a[1], a[2], a[3] - 1};
  if (n == Matrix{0, 0, 0, 0})
    return 2;
  return determinant(n) == 0 ? 1 : 0;
}
inline Card card(const char *path) {
  const auto v = numbers(path);
  std::size_t at = 0;
  at += 4;
  Card out{};
  out.lineage = static_cast<std::uint64_t>(v.at(at++));
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
  std::array<Matrix, 4> g = c.generators;
  if (c.recharted) {
    const auto p = inverse(c.rechart);
    for (std::uint8_t i = 0; i < c.alphabet; ++i)
      g[i] = multiply(multiply(c.rechart, g[i]), p);
  }
  std::vector<Word> out{};
  const auto visit = [&](auto &&self, std::vector<std::uint8_t> letters,
                         Matrix formed, std::uint8_t last) -> void {
    if (!letters.empty())
      out.push_back({formed, letters, static_cast<std::uint16_t>(out.size()),
                     c.lineage + out.size() + 1U});
    if (letters.size() >= c.length)
      return;
    for (std::uint8_t i = 0; i < c.alphabet; ++i) {
      if (!letters.empty() && c.inverse[last] == i)
        continue;
      auto next = letters;
      next.push_back(i);
      self(self, next, multiply(formed, g[i]), i);
    }
  };
  visit(visit, {}, Matrix{1, 0, 0, 1}, 0);
  return out;
}
inline Pair pair(const Word &a, const Word &b, std::uint8_t source) {
  Pair p{};
  p.a = a.matrix;
  p.b = b.matrix;
  p.ab = multiply(p.a, p.b);
  p.closed = multiply(multiply(multiply(p.a, p.b), inverse(p.a)), inverse(p.b));
  const Matrix m[4]{p.a, p.b, p.ab, p.closed};
  for (std::uint8_t i = 0; i < 4; ++i) {
    p.traces[i] = trace(m[i]);
    p.discriminants[i] = p.traces[i] * p.traces[i] - 4;
    p.strata[i] = stratum(p.discriminants[i]);
    p.ranks[i] = rank(m[i]);
  }
  p.left = a.ordinal;
  p.right = b.ordinal;
  p.source = source;
  return p;
}
inline std::vector<Pair> pairs(const std::array<std::vector<Word>, 3> &w) {
  std::vector<Pair> out{};
  for (std::uint8_t s = 0; s < 3; ++s)
    for (const auto &a : w[s])
      for (const auto &b : w[s])
        out.push_back(pair(a, b, s));
  return out;
}
inline bool same(const Group &g, const Pair &p) {
  for (std::uint8_t i = 0; i < 4; ++i)
    if (g.coordinates[i] != p.traces[i] || g.strata[i] != p.strata[i])
      return false;
  return g.rank == p.ranks[3];
}
inline std::vector<Group> groups(const std::vector<Pair> &pairs) {
  std::vector<Group> out{};
  for (const auto &p : pairs) {
    auto at = out.begin();
    while (at != out.end() && !same(*at, p))
      ++at;
    if (at != out.end()) {
      ++at->population;
      continue;
    }
    Group g{};
    for (std::uint8_t i = 0; i < 4; ++i) {
      g.coordinates[i] = p.traces[i];
      g.strata[i] = p.strata[i];
    }
    g.population = 1;
    g.rank = p.ranks[3];
    out.push_back(g);
  }
  return out;
}
inline void matrix_out(std::ostream &out, const Matrix &m) {
  for (const auto v : m)
    out << '\t' << v;
}
} // namespace r33_host

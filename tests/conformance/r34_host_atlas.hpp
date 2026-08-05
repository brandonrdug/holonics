#pragma once

#include "r34_host_law.hpp"

namespace r34_host {
inline std::string word_atlas(const std::array<std::vector<Word>, 3> &w) {
  std::ostringstream out;
  out << "source\tordinal\tlength\tletters\ta\tb\tc\td\tlineage\n";
  for (std::uint8_t s = 0; s < 3; ++s)
    for (const auto &x : w[s]) {
      out << static_cast<unsigned>(s) << '\t' << x.ordinal << '\t'
          << x.letters.size() << '\t';
      for (const auto letter : x.letters)
        out << static_cast<unsigned>(letter);
      matrix_out(out, x.matrix);
      out << '\t' << x.lineage << '\n';
    }
  return out.str();
}
inline std::string triple_atlas(const std::vector<Triple> &triples) {
  std::ostringstream out;
  out << "source\ta_word\tb_word\tc_word\tA\tB\tC\tAB\tAC\tBC\tABC\tACB"
         "\ta\tb\tc\td\te\tf\tp\tq\ts\tr\tdiscriminant\tgap\tbranch\n";
  for (const auto &t : triples) {
    out << static_cast<unsigned>(t.source) << '\t' << t.words[0] << '\t'
        << t.words[1] << '\t' << t.words[2];
    for (const auto &m : t.matrices)
      matrix_out(out, m);
    for (const auto value : t.lower)
      out << '\t' << value;
    out << '\t' << t.ordered[0] << '\t' << t.ordered[1] << '\t'
        << t.symmetric[0] << '\t' << t.symmetric[1] << '\t'
        << t.discriminant << '\t' << t.gap << '\t' << t.branch << '\n';
  }
  return out.str();
}
inline std::string group_atlas(const std::vector<Group> &groups) {
  std::ostringstream out;
  out << "a\tb\tc\td\te\tf\troot0\troot1\tbranch\tpopulation\n";
  for (const auto &g : groups) {
    for (const auto value : g.lower)
      out << value << '\t';
    out << g.roots[0] << '\t' << g.roots[1] << '\t' << g.branch << '\t'
        << g.population << '\n';
  }
  return out.str();
}
inline bool same_lower(const Triple &a, const Triple &b) {
  return a.lower == b.lower;
}
inline bool same_fiber(const Triple &a, const Triple &b) {
  return a.lower == b.lower && roots(a) == roots(b);
}
inline std::array<std::array<std::uint16_t, 2>, 5>
witnesses(const std::vector<Triple> &t) {
  std::array<std::array<std::uint16_t, 2>, 5> out{};
  bool found[5]{};
  for (std::uint8_t source = 0; source < 3 && !found[0]; ++source)
    for (std::uint8_t a = 0; a < 12 && !found[0]; ++a)
      for (std::uint8_t b = 0; b < 12; ++b)
        for (std::uint8_t c = static_cast<std::uint8_t>(b + 1U); c < 12; ++c) {
          const auto first = static_cast<std::uint16_t>(source * 1'728U +
                                                        a * 144U + b * 12U + c);
          const auto second = static_cast<std::uint16_t>(source * 1'728U +
                                                         a * 144U + c * 12U + b);
          if (same_lower(t[first], t[second]) && !t[first].branch &&
              t[first].ordered[0] == t[second].ordered[1] &&
              t[first].ordered[1] == t[second].ordered[0]) {
            out[0] = {first, second};
            found[0] = true;
            break;
          }
        }
  for (std::uint16_t i = 0; i < 1'728 && !found[1]; ++i)
    for (std::uint16_t j = 0; j < 1'728; ++j)
      if (same_fiber(t[i], t[1'728U + j]) &&
          (t[i].matrices[0] != t[1'728U + j].matrices[0] ||
           t[i].matrices[1] != t[1'728U + j].matrices[1] ||
           t[i].matrices[2] != t[1'728U + j].matrices[2])) {
        out[1] = {i, static_cast<std::uint16_t>(1'728U + j)};
        found[1] = true;
        break;
      }
  for (std::uint16_t i = 0; i < 1'728 && !found[2]; ++i)
    if (same_fiber(t[1'728U + i], t[3'456U + i]) &&
        (t[1'728U + i].matrices[0] != t[3'456U + i].matrices[0] ||
         t[1'728U + i].matrices[1] != t[3'456U + i].matrices[1] ||
         t[1'728U + i].matrices[2] != t[3'456U + i].matrices[2])) {
      out[2] = {static_cast<std::uint16_t>(1'728U + i),
                static_cast<std::uint16_t>(3'456U + i)};
      found[2] = true;
    }
  for (std::uint16_t i = 0; i < 5'184; ++i) {
    if (!found[3] && t[i].branch) {
      out[3] = {i, i};
      found[3] = true;
    }
    if (!found[4] && !t[i].branch) {
      out[4] = {i, i};
      found[4] = true;
    }
  }
  return out;
}
inline std::vector<Candidate> candidates(const std::vector<Triple> &t) {
  std::vector<Candidate> out{};
  for (std::size_t source = 0; source < 3; ++source)
    out.push_back(candidate(t, source * 1'728U, 1'728, 0, Mode::complete));
  out.push_back(out[0]);
  out[3].rows = 5'184;
  out[3].selected = true;
  for (std::size_t source = 0; source < 3; ++source)
    out.push_back(candidate(t, source * 1'728U, 1'728, 1, Mode::complete));
  out.push_back(out[4]);
  out[7].rows = 5'184;
  out[7].selected = true;
  out.push_back(candidate(t, 0, 1'728, 0, Mode::degree_two));
  out.push_back(candidate(t, 0, 1'728, 1, Mode::degree_two));
  out.push_back(candidate(t, 0, 1'728, 0, Mode::delete_sixth));
  out.push_back(candidate(t, 0, 1'728, 1, Mode::delete_sixth));
  out.push_back(candidate(t, 0, 16, 0, Mode::complete));
  out.push_back(candidate(t, 0, 1'728, 0, Mode::delete_target));
  return out;
}
inline std::string law_atlas(const std::vector<Triple> &t) {
  std::ostringstream out;
  out << "kind\tindex\ttarget\tmode\trows\tfeatures\trank\tnullity\tobstruction"
         "\tselected\tvalue\n";
  const auto all = candidates(t);
  for (std::size_t i = 0; i < all.size(); ++i) {
    const auto &c = all[i];
    out << "candidate\t" << i << '\t' << static_cast<unsigned>(c.target) << '\t'
        << static_cast<unsigned>(c.mode) << '\t' << c.rows << '\t'
        << static_cast<unsigned>(c.features) << '\t' << static_cast<unsigned>(c.rank)
        << '\t' << static_cast<unsigned>(c.nullity) << '\t'
        << static_cast<unsigned>(c.obstruction) << '\t' << c.selected << '\t';
    for (const auto value : c.coefficients)
      out << value << ',';
    out << '\n';
  }
  const auto w = witnesses(t);
  for (std::size_t i = 0; i < w.size(); ++i)
    out << "witness\t" << i << "\t-\t-\t-\t-\t-\t-\t0\t1\t" << w[i][0]
        << ',' << w[i][1] << '\n';
  const auto branch = static_cast<std::uint16_t>(
      std::count_if(t.begin(), t.end(), [](const Triple &x) { return x.branch; }));
  out << "strata\t0\t-\t-\t5184\t-\t-\t-\t0\t1\t" << branch << ','
      << static_cast<std::uint16_t>(5'184U - branch) << '\n';
  return out.str();
}
inline std::string heldout_atlas(const char *path) {
  const auto v = numbers(path);
  std::size_t at = 5;
  const auto changed_matrix = static_cast<std::size_t>(v.at(at++));
  const auto changed_slot = static_cast<std::size_t>(v.at(at++));
  const auto changed_value = v.at(at++);
  std::array<Matrix, 6> edges{};
  for (auto &edge : edges)
    edge = matrix(v, at);
  std::array<Matrix, 8> m{};
  m[0] = multiply(edges[0], edges[1]);
  m[1] = multiply(edges[2], edges[3]);
  m[2] = multiply(edges[4], edges[5]);
  m[3] = multiply(m[0], m[1]);
  m[4] = multiply(m[0], m[2]);
  m[5] = multiply(m[1], m[2]);
  m[6] = multiply(m[3], m[2]);
  m[7] = multiply(m[4], m[1]);
  std::array<std::int64_t, 6> lower{};
  for (std::size_t i = 0; i < 6; ++i)
    lower[i] = trace(m[i]);
  const auto anchor = trace(m[6]), companion = trace(m[7]);
  const auto sum = anchor + companion, product = anchor * companion;
  auto changed = m[changed_matrix];
  changed[changed_slot] = changed_value;
  std::ostringstream out;
  out << "kind\tvalue\nvisible\t";
  for (const auto value : lower)
    out << value << ',';
  out << "\nquadratic\t1," << -sum << ',' << product << "\nroots\t"
      << (anchor < companion ? anchor : companion) << ','
      << (anchor < companion ? companion : anchor) << "\norientation\t" << anchor
      << ',' << companion << "\nsource_companion\t" << companion
      << "\ndiscriminant\t" << sum * sum - 4 * product
      << "\norgan_exclusion\t7\norientation_exclusion\t8\ndeterminant_foil\t"
      << (determinant(changed) == 1 ? 12 : 9)
      << "\ncomparison\t1\nmatrices";
  for (const auto &value : m)
    matrix_out(out, value);
  out << '\n';
  return out.str();
}
} // namespace r34_host

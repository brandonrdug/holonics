#pragma once

#include "r33_host_model.hpp"

namespace r33_host {
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
inline std::string pair_atlas(const std::vector<Pair> &pairs) {
  std::ostringstream out;
  out << "source\tleft\tright\tA\tB\tAB\tC\tx\ty\tz\tk\tdx\tdy\tdz\tdk\tsx\tsy"
         "\tsz\tsk\trA\trB\trAB\trC\n";
  for (const auto &p : pairs) {
    out << static_cast<unsigned>(p.source) << '\t' << p.left << '\t' << p.right;
    matrix_out(out, p.a);
    matrix_out(out, p.b);
    matrix_out(out, p.ab);
    matrix_out(out, p.closed);
    for (const auto v : p.traces)
      out << '\t' << v;
    for (const auto v : p.discriminants)
      out << '\t' << v;
    for (const auto v : p.strata)
      out << '\t' << static_cast<int>(v);
    for (const auto v : p.ranks)
      out << '\t' << static_cast<unsigned>(v);
    out << '\n';
  }
  return out.str();
}
inline std::string group_atlas(const std::vector<Group> &groups) {
  std::ostringstream out;
  out << "x\ty\tz\tk\tsx\tsy\tsz\tsk\tfixed\tpopulation\n";
  for (const auto &g : groups) {
    for (const auto v : g.coordinates)
      out << v << '\t';
    for (const auto v : g.strata)
      out << static_cast<int>(v) << '\t';
    out << static_cast<unsigned>(g.rank) << '\t' << g.population << '\n';
  }
  return out.str();
}
inline std::string law_atlas() {
  return "kind\tindex\trows\tfeatures\trank\tnullity\tobstruction\tselected\tva"
         "lue\n"
         "candidate\t0\t900\t21\t20\t1\t0\t0\t2,0,0,0,-1,0,0,-1,0,-1,0,0,0,0,1,"
         "0,0,0,0,0,1,\n"
         "candidate\t1\t2704\t21\t20\t1\t0\t0\t2,0,0,0,-1,0,0,-1,0,-1,0,0,0,0,"
         "1,0,0,0,0,0,1,\n"
         "candidate\t2\t2704\t21\t20\t1\t0\t0\t2,0,0,0,-1,0,0,-1,0,-1,0,0,0,0,"
         "1,0,0,0,0,0,1,\n"
         "candidate\t3\t6308\t21\t20\t1\t0\t1\t2,0,0,0,-1,0,0,-1,0,-1,0,0,0,0,"
         "1,0,0,0,0,0,1,\n"
         "candidate\t4\t6308\t11\t11\t0\t2\t0\t0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,"
         "0,0,0,0,0,\n"
         "candidate\t5\t6308\t20\t20\t0\t2\t0\t0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,"
         "0,0,0,0,0,\n"
         "candidate\t6\t8\t21\t4\t17\t1\t0\t0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,"
         "0,0,0,0,\n"
         "witness\t0\t-\t-\t-\t-\t0\t1\t0,15\n"
         "witness\t1\t-\t-\t-\t-\t0\t1\t4096,8192\n"
         "witness\t2\t-\t-\t-\t-\t0\t1\t4,120\n"
         "witness\t3\t-\t-\t-\t-\t0\t1\t4096,8192\n"
         "witness\t4\t-\t-\t-\t-\t0\t1\t15,15\n"
         "strata\tclosed\t-\t-\t-\t-\t0\t1\t0,440,5868\n";
}
inline std::string heldout_atlas(const char *path) {
  const auto v = numbers(path);
  std::size_t at = 5;
  const auto count = v.at(at++), split = v.at(at++), slot = v.at(at++),
             changed = v.at(at++);
  static_cast<void>(slot);
  static_cast<void>(changed);
  std::vector<Matrix> edges{};
  for (std::int64_t i = 0; i < count; ++i)
    edges.push_back(matrix(v, at));
  Matrix a{1, 0, 0, 1}, b{1, 0, 0, 1};
  for (std::int64_t i = 0; i < split; ++i)
    a = multiply(a, edges[static_cast<std::size_t>(i)]);
  for (std::int64_t i = split; i < count; ++i)
    b = multiply(b, edges[static_cast<std::size_t>(i)]);
  const auto p = multiply(a, b);
  const auto c = multiply(multiply(multiply(a, b), inverse(a)), inverse(b));
  const auto x = trace(a), y = trace(b), z = trace(p), k = trace(c);
  std::ostringstream out;
  out << "face\ta\tb\tc\td\tvalue\nA";
  matrix_out(out, a);
  out << "\t-\nB";
  matrix_out(out, b);
  out << "\t-\nAB";
  matrix_out(out, p);
  out << "\t-\nC";
  matrix_out(out, c);
  out << '\t' << k << "\nvisible\t0\t0\t0\t0\t" << x << ',' << y << ',' << z
      << "\npredicted\t0\t0\t0\t0\t" << k << "\ndiscriminant\t0\t0\t0\t0\t"
      << k * k - 4 << "\ncharacteristic\t0\t0\t0\t0\t1," << -k
      << ",1\ncontrol_exclusion\t0\t0\t0\t0\t6\ncontrol_"
         "determinant\t0\t0\t0\t0\t7\n";
  return out.str();
}
} // namespace r33_host

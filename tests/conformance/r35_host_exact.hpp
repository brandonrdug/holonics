#pragma once

#include <algorithm>
#include <numeric>

#include "r35_host_model.hpp"

namespace r35_host {
inline constexpr std::int64_t prime=1'000'003;
inline std::int64_t residue(std::int64_t value) {
  value%=prime; return value<0?value+prime:value;
}
inline std::int64_t product(std::int64_t a,std::int64_t b) { return (a*b)%prime; }
inline std::int64_t field_inverse(std::int64_t value) {
  std::int64_t out=1; std::uint64_t exponent=prime-2;
  while(exponent!=0) { if((exponent&1U)!=0) out=product(out,value);
    value=product(value,value); exponent>>=1U; } return out;
}
struct Basis { std::vector<std::vector<std::int64_t>> rows{}; std::vector<std::size_t> pivots{}; };
inline void insert(Basis &basis,std::vector<std::int64_t> values,std::size_t pivot_columns) {
  for(std::size_t row=0;row<basis.rows.size();++row) { const auto factor=values[basis.pivots[row]];
    for(std::size_t column=basis.pivots[row];column<values.size();++column)
      values[column]=residue(values[column]-product(factor,basis.rows[row][column])); }
  std::size_t pivot=0; while(pivot<pivot_columns&&values[pivot]==0) ++pivot;
  if(pivot==pivot_columns)
    return;
  const auto scale=field_inverse(values[pivot]);
  for(std::size_t column=pivot;column<values.size();++column)
    values[column]=product(values[column],scale);
  basis.pivots.push_back(pivot); basis.rows.push_back(std::move(values));
}
inline std::uint8_t monomial_count(std::uint8_t degree) {
  return static_cast<std::uint8_t>(exponents(degree).size());
}
inline std::uint8_t feature_rank(const std::vector<State> &states,
                                 std::uint8_t degree,int excluded=-1) {
  Basis basis{}; const auto columns=monomial_count(degree);
  for(const auto &state:states) if(state.source!=excluded&&basis.rows.size()<columns) {
    const auto all=monomials(state.chart); std::vector<std::int64_t> row(columns);
    for(std::size_t i=0;i<columns;++i) row[i]=residue(all[i]);
    insert(basis,std::move(row),columns);
  } return static_cast<std::uint8_t>(basis.rows.size());
}
inline std::uint8_t controlled_rank(const std::vector<State> &states,
    const std::vector<Edge> &edges,int deleted,bool target_present,
    std::size_t limit=1272) {
  const auto powers=exponents(); Basis basis{}; std::size_t columns=0;
  for(std::size_t state=0;state<std::min(limit,states.size());++state) {
    const auto all=monomials(states[state].chart); std::vector<std::int64_t> row{};
    for(std::size_t i=0;i<120;++i) if(deleted<0||powers[i][static_cast<std::size_t>(deleted)]==0)
      row.push_back(residue(all[i]));
    if(target_present) row.push_back(residue(edges[state*5].target[6]));
    columns=row.size(); insert(basis,std::move(row),columns);
  } return static_cast<std::uint8_t>(basis.rows.size());
}
inline Fiber discover_fiber(const std::vector<State> &states) {
  const auto powers=exponents(4); const auto columns=powers.size(); Basis basis{};
  for(const auto &state:states) {
    const auto values=monomial_values(state.chart,4); std::vector<std::int64_t> row(columns);
    for(std::size_t i=0;i<columns;++i) row[i]=residue(values[i]);
    insert(basis,std::move(row),columns);
    if(basis.rows.size()+1U==columns) break;
  }
  Fiber out{}; out.coefficients.resize(columns);
  if(basis.rows.size()+1U!=columns) return out;
  std::vector<bool> pivoted(columns,false); for(const auto pivot:basis.pivots) pivoted[pivot]=true;
  std::size_t free=0; while(free<columns&&pivoted[free]) ++free;
  if(free==columns) return out;
  std::vector<std::int64_t> modular(columns); modular[free]=1;
  for(std::size_t at=basis.rows.size();at--!=0;) {
    const auto pivot=basis.pivots[at]; std::int64_t sum=0;
    for(std::size_t column=pivot+1U;column<columns;++column)
      sum=residue(sum+product(basis.rows[at][column],modular[column]));
    modular[pivot]=residue(-sum);
  }
  for(std::size_t i=0;i<columns;++i)
    out.coefficients[i]=modular[i]>prime/2?modular[i]-prime:modular[i];
  std::int64_t divisor=0; for(const auto value:out.coefficients) divisor=std::gcd(divisor,value);
  if(divisor==0) return out;
  for(auto &value:out.coefficients) value/=divisor;
  std::int64_t quadratic=0;
  for(std::size_t term=0;term<powers.size();++term) if(powers[term][6]==2) {
    bool receiver_constant=true;
    for(std::uint8_t coordinate=0;coordinate<6;++coordinate)
      receiver_constant=receiver_constant&&powers[term][coordinate]==0;
    if(receiver_constant) quadratic=out.coefficients[term];
  }
  if(quadratic<0)
    for(auto &value:out.coefficients) value=-value;
  out.valid=true;
  for(const auto &state:states) {
    const auto values=monomial_values(state.chart,4); std::int64_t total=0;
    for(std::size_t i=0;i<columns;++i) total+=out.coefficients[i]*values[i];
    out.valid=out.valid&&total==0;
  }
  return out;
}
inline Vector gradient(const Fiber &fiber,const Chart &x) {
  Vector out{}; const auto powers=exponents(4);
  if(!fiber.valid||fiber.coefficients.size()!=powers.size()) return out;
  for(std::size_t term=0;term<powers.size();++term)
    for(std::uint8_t variable=0;variable<7;++variable) if(powers[term][variable]!=0) {
      std::int64_t value=fiber.coefficients[term]*powers[term][variable];
      for(std::uint8_t i=0;i<7;++i)
        value*=power(x[i],static_cast<std::uint8_t>(powers[term][i]-(i==variable)));
      out[variable]+=value;
    }
  return out;
}
inline Jacobian jacobian(const Map &map,const Chart &x) {
  Jacobian out{}; const auto powers=exponents();
  for(std::uint8_t target=0;target<7;++target) for(std::uint8_t variable=0;variable<7;++variable) {
    std::int64_t sum=0;
    for(std::uint8_t term=0;term<120;++term) if(powers[term][variable]!=0) {
      std::int64_t value=powers[term][variable];
      for(std::uint8_t i=0;i<7;++i) value*=power(x[i],static_cast<std::uint8_t>(powers[term][i]-(i==variable)));
      sum+=map.coefficients[target][term]*value;
    } out[target][variable]=-sum/map.coefficients[target][120];
  } return out;
}
using Tangent=std::array<Vector,6>;
inline std::pair<Tangent,std::uint8_t> tangent(const Vector &gradient) {
  Tangent out{}; std::uint8_t pivot=0; while(pivot<7&&gradient[pivot]==0) ++pivot;
  if(pivot==7)
    return {out,0};
  std::uint8_t row=0;
  for(std::uint8_t free=0;free<7;++free) if(free!=pivot) {
    out[row][free]=gradient[pivot]; out[row][pivot]=-gradient[free]; ++row; }
  return {out,row};
}
inline Tangent transport(const Jacobian &j,const Tangent &source) {
  Tangent out{};
  for(std::uint8_t vector=0;vector<6;++vector)
    for(std::uint8_t row=0;row<7;++row)
      for(std::uint8_t column=0;column<7;++column)
        out[vector][row]+=j[row][column]*source[vector][column];
  return out;
}
inline std::uint8_t row_rank(const Tangent &rows) {
  Basis basis{};
  for(const auto &source:rows) {
    std::vector<std::int64_t> row(7);
    for(std::uint8_t i=0;i<7;++i)
      row[i]=residue(source[i]);
    insert(basis,std::move(row),7);
  }
  return static_cast<std::uint8_t>(basis.rows.size());
}
inline bool chain(const Vector &gradient,const Tangent &vectors) {
  for(const auto &v:vectors) {
    std::int64_t sum=0;
    for(std::uint8_t i=0;i<7;++i)
      sum+=gradient[i]*v[i];
    if(sum!=0)
      return false;
  }
  return true;
}
inline std::vector<std::string> fields(const std::string &line,char delimiter='\t') {
  std::vector<std::string> out{}; std::stringstream in(line); std::string value;
  while(std::getline(in,value,delimiter))
    out.push_back(value);
  if(!line.empty()&&line.back()==delimiter)
    out.emplace_back();
  return out;
}
inline std::vector<std::int64_t> list(const std::string &source) {
  std::vector<std::int64_t> out{};
  for(const auto &value:fields(source,','))
    if(!value.empty())
      out.push_back(std::stoll(value));
  return out;
}
template<std::size_t N> inline bool same(const std::array<std::int64_t,N> &expected,
                                         const std::vector<std::int64_t> &actual) {
  return actual.size()==N&&std::equal(expected.begin(),expected.end(),actual.begin());
}
} // namespace r35_host

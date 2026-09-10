"""Exterior integer oracle for the production exact-division header; no model operation.

Usage: python verify_division.py NEW_RECEIPT.json
Compiles the shared header with only its device annotations/intrinsic adapted for the CPU.
"""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
SOURCE = r'''
#include <cstdint>
#include <iostream>
#include <iomanip>
#include <string>
#define __device__
inline int __clz(uint32_t value) { return __builtin_clz(value); }
#include "crates/holonic-engine/kernels/exact_integer.cuh"
template<int N> ExactInteger<N> read(std::string value, bool negative, bool overflow) {
    ExactInteger<N> result; result.negative=negative; result.overflow=overflow;
    for(int i=0;!value.empty() && i<N;++i) {
        auto count=value.size()<8?value.size():8;
        result.limb[i]=std::stoul(value.substr(value.size()-count),nullptr,16);
        value.resize(value.size()-count);
    }
    return result;
}
template<int N> void run(std::string a,std::string b,bool an,bool bn,bool ao,bool bo) {
    bool remainder=false;
    auto q=exact_divide_positive(read<N>(a,an,ao),read<N>(b,bn,bo),&remainder);
    std::cout<<q.negative<<' '<<remainder<<' '<<q.overflow<<' ';
    for(int i=N-1;i>=0;--i)std::cout<<std::hex<<std::setw(8)<<std::setfill('0')<<q.limb[i];
    std::cout<<std::dec<<'\n';
}
int main(){int n;bool an,bn,ao,bo;std::string a,b;
    while(std::cin>>n>>an>>bn>>ao>>bo>>a>>b){
        if(n==8)run<8>(a,b,an,bn,ao,bo);
        else if(n==21)run<21>(a,b,an,bn,ao,bo);else return 1;
    }
}
'''


def cases(limbs):
    bits = limbs * 32  # The production header's uint32_t limbs.
    maximum = (1 << bits) - 1
    values = {0, 1, 2, maximum}
    boundaries = {1, bits - 1, bits // 2}
    for bit in range(32, bits, 32):
        boundaries.update((bit - 1, bit, bit + 1))
    for bit in boundaries:
        values.update((1 << bit) + offset for offset in (-1, 0, 1)
                      if 0 <= (1 << bit) + offset <= maximum)
    for numerator in sorted(values):
        for denominator in sorted(values - {0}):
            for negative in (False, True):
                yield limbs, negative, False, False, False, numerator, denominator
    for bit in range(bits):
        yield limbs, bool(bit % 2), False, False, False, maximum ^ (1 << bit), (1 << bit) | 1
    for negative_den, overflow_num, overflow_den, denominator in (
        (False, False, False, 0), (True, False, False, 1),
        (False, True, False, 1), (False, False, True, 1),
    ):
        yield limbs, False, negative_den, overflow_num, overflow_den, maximum, denominator


def main():
    destination = Path(sys.argv[1])
    population = [item for limbs in (8, 21) for item in cases(limbs)]
    wire = "".join(f"{n} {int(an)} {int(bn)} {int(ao)} {int(bo)} {a:x} {b:x}\n"
                   for n, an, bn, ao, bo, a, b in population)
    with tempfile.TemporaryDirectory(prefix="holonics-division-") as directory:
        path = Path(directory)
        (path / "check.cpp").write_text(SOURCE)
        subprocess.run(["c++", "-std=c++20", "-O2", "-I", str(ROOT), str(path / "check.cpp"),
                        "-o", str(path / "check")], check=True)
        result = subprocess.run([str(path / "check")], input=wire, text=True, capture_output=True, check=True)
    lines = result.stdout.splitlines()
    assert len(lines) == len(population)
    refused = 0
    for entry, line in zip(population, lines):
        n, an, bn, ao, bo, a, b = entry
        negative, remainder, overflow, magnitude = line.split()
        if bn or ao or bo or b == 0:
            assert overflow == "1", (entry, line)
            refused += 1
            continue
        quotient, expected_remainder = divmod(a, b)
        assert (int(magnitude, 16), bool(int(negative)), bool(int(remainder)), overflow) == (
            quotient, an and quotient != 0, expected_remainder != 0, "0"), (entry, line)
    receipt = {
        "grade": "established-bounded", "evidence": ["implemented-exact", "computational-witness"],
        "scope": "Production shared header compiled on CPU; signed quotient and remainder compared "
                 "with Python integers at limb boundaries and complete carrier widths. Native model regressions remain separate.",
        "carrier_bits": [8 * 32, 21 * 32], "cases": len(population), "refusals": refused,
        "all_comparisons_passed": True,
    }
    with destination.open("x") as out:
        json.dump(receipt, out, indent=2)
        out.write("\n")
    print(json.dumps(receipt))


if __name__ == "__main__":
    main()

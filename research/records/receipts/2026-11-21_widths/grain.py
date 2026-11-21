"""Numbers the record quotes, from the laws it names (integers and one logarithm; a ruler's arithmetic).

1. The grain a reading count confirms (atlas receiver.grain-lemma): the least L with 2 L^2 >= N ln 2.
2. The reading count at which a grain of 2^-16 is the coarsest right one: N = 2 * 2^32 / ln 2.
3. The deposit's walk (crates/engine/src/deposit.rs, deposit_over): an entry's step is (m/root) 2^-rate, and a covector that is
   noise moves an entry as a walk of 2^-rate a section, so over T sections it stands 2^-rate sqrt(T) from where it began.
4. The skin's horizon (crates/engine/src/navigator.rs, skin_of): e^(-2 pi d/n) released to 2^-30 is zero past d/n = 31 ln 2 / 2 pi.
5. The register file (the record of November 20, section 4): resident threads a multiprocessor at r registers a thread.
"""
import math

print('1. the grain a reading count confirms')
for n in (6148, 43470, 10**7, 10**9, 10**10):
    L = math.isqrt(int(n * math.log(2) / 2))
    while 2 * L * L < n * math.log(2):
        L += 1
    print(f'   N = {n:>11}: L = {L:>6}, {math.log2(L):.2f} places')
print(f'2. a grain of 2^-16 is the coarsest its readings confirm at N = {2 * 2**32 / math.log(2):.4g} readings')
print('3. the walk of an entry at rate 2^-12, in places above the grain 2^-24')
for t in (1, 8, 100, 1000, 3000):
    print(f'   after {t:>4} sections: 2^{-12 + 0.5 * math.log2(t):.2f}, place {24 - 12 + 0.5 * math.log2(t):.1f}')
print(f'4. the skin is zero past {31 * math.log(2) / (2 * math.pi):.3f} periods at a grain of 2^-30; '
      f'under one face grain (2^-16) past {16 * math.log(2) / (2 * math.pi):.3f} periods')
print('5. resident threads a multiprocessor: ' + ', '.join(f'{r} registers {min(1536, 32 * (65536 // (32 * r)))}' for r in (32, 42, 64, 96, 128)))

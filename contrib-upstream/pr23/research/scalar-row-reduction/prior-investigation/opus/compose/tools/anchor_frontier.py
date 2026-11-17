"""Minimal admissible anchor exponent E (multiple of 6) per high detector order k.

Exact integer versions of the package's sufficient margins
(arithmetic_round8.tex; higher-detector-precision/PROOF.md at bc51100;
scalar-chain-reduction/PROOF.md):
  scalar (order s=31, target h(beta)<c/sdiv):  c*^(32s-P) > (sdiv*H)^(32s)
  Lucas (order k, |F|<5B^4, transfer 7H):      b*^(16k-4P/... ) see below
with alpha=P/32 (P=577 baseline), c*=2*3^(E/2-1), b*=c*/2 (bc51100 convention).
Lucas: B^(2-4alpha/k) < 7H*5^(alpha/k)+6 < 24H, contradiction iff
  b*^(2k*32-4P) > (24H)^(32k)   (reduces to b*^(16k-577)>(24H)^(8k) at P=577).
Digits model: max coefficient 28902*3^(2E/3) (fits both measured points).
"""
import json, math, sys
sys.set_int_max_str_digits(0)
from fractions import Fraction


def H_of(eps_den=192, Kfrac=None):
    # baseline: eps=1/192 -> H = 3*2^106*C^6*BS^18 + 128
    C = 2**32 * 3**9
    BS = 46410
    return 3 * 2**106 * C**6 * BS**18 + 128


H0 = H_of()


def scalar_ok(E, H, P=577, s=31, sdiv=4):
    cstar = 2 * 3**(E // 2 - 1)
    return cstar**(32 * s - P) > (sdiv * H)**(32 * s)


def lucas_ok(E, k, H, P=577, mult=24, bstar_mode='half'):
    cstar = 2 * 3**(E // 2 - 1)
    bstar = cstar // 2 if bstar_mode == 'half' else cstar - 1
    ex = 64 * k - 4 * P
    if ex <= 0:
        return False
    return bstar**ex > (mult * H)**(32 * k)


def min_E(pred, start=6, step=6, limit=200000):
    # predicates are monotone in E; binary search over multiples of 6
    lo, hi = start, start
    while not pred(hi):
        lo, hi = hi, hi * 2
        if hi > limit:
            return None
    # smallest multiple of 6 in (lo, hi] satisfying pred
    a, b = lo // 6, hi // 6
    while a + 1 < b:
        m = (a + b) // 2
        if pred(6 * m):
            b = m
        else:
            a = m
    if pred(6 * a):
        return 6 * a
    return 6 * b


def digits(E):
    v = 28902 * 3**(2 * E // 3)
    return len(str(v)), v.bit_length()


def frontier(H=H0, P=577, sdiv=4, mult=24, bstar_mode='half', ks=range(37, 52)):
    Es = min_E(lambda E: scalar_ok(E, H, P, 31, sdiv))
    rows = []
    for k in ks:
        El = min_E(lambda E: lucas_ok(E, k, H, P, mult, bstar_mode))
        E = max(Es, El) if El else None
        d = digits(E) if E else (None, None)
        rows.append(dict(k=k, E_scalar=Es, E_lucas=El, E=E, digits=d[0], bits=d[1],
                         binding='lucas' if El and El > Es else 'scalar'))
    return rows


if __name__ == '__main__':
    out = {}
    # sanity: measured calibrations
    assert digits(2130) == (682, 2266), digits(2130)
    assert digits(2016) == (646, 2146), digits(2016)
    for sd in (4, 5, 10):
        out[f'baseline_sdiv{sd}'] = frontier(sdiv=sd)
    for r in out['baseline_sdiv4']:
        print(r)
    print('scalar-only E for sdiv 5,10:', out['baseline_sdiv5'][0]['E_scalar'], out['baseline_sdiv10'][0]['E_scalar'])
    json.dump(out, open(sys.argv[1] if len(sys.argv) > 1 else 'anchor_frontier.json', 'w'), indent=1)

# hx-used: is R = -theta4(0; q^(1/4)) / (2 theta2(0)) a formal product identity?  u = q^(1/8).
# Each factor (1 - eps u^k), eps = +-1; (1 + u^k) = (1 - u^(2k)) / (1 - u^k).  Track exponents e_k of (1 - u^k), k <= K.
from collections import defaultdict
K = 400
def addfac(E, eps, k, mult):
    # (1 - eps u^k)^mult
    if k <= 0: raise ValueError(k)
    if eps == 1:
        E[k] += mult
    else:
        E[2*k] += mult; E[k] -= mult
def theta1(E, a, b, mult):
    # theta1 at z with x = e^{2 pi i z} = eps * u^(8a)... we pass x = s * u^m (s = +-1, m integer, in u units)
    s, m = a, b
    for n in range(1, K):
        if 16*n > K + 64: break
        addfac(E, 1, 16*n, mult)                 # (1 - q^{2n}),  q = u^8
        if 16*n + m > 0: addfac(E, s, 16*n + m, mult)       # (1 - q^{2n} x)
        if 16*n - 16 - m > 0: addfac(E, s, 16*n - 16 - m, mult)  # (1 - q^{2n-2}/x)
        # factors with nonpositive exponent are monomial-type; report them
def theta2(E, s, m, mult):
    theta1(E, -s, m, mult)
def main():
    num = defaultdict(int); den = defaultdict(int)
    # R numerator: theta1(-tau/8) theta1(1 + tau/8) theta1(3 tau/8)^2 ; denominator: theta1(1/2)^2 theta1(tau/4 - 1/2) theta1(1/2 + tau/2)
    # x values: -tau/8 -> u^-2 ; 1 + tau/8 -> u^2 ; 3tau/8 -> u^6 ; 1/2 -> -1 ; tau/4 - 1/2 -> -u^4 ; 1/2 + tau/2 -> -u^8
    for (s, m, mult) in [(1, -2, 1), (1, 2, 1), (1, 6, 2)]:
        theta1(num, s, m, mult)
    for (s, m, mult) in [(-1, 0, 2), (-1, 4, 1), (-1, 8, 1)]:
        theta1(den, s, m, mult)
    # target: theta4(0; q^{1/4}) / theta2(0; q):  theta4(nome u^2) = prod (1 - u^{4n})(1 - u^{4n-2})^2 ; theta2(0) = 2 q^{1/4} prod (1-q^{2n})(1+q^{2n})^2
    tn = defaultdict(int); td = defaultdict(int)
    for n in range(1, K):
        if 4*n <= K: addfac(tn, 1, 4*n, 1)
        if 4*n - 2 <= K: addfac(tn, 1, 4*n - 2, 2)
        if 16*n <= K: addfac(td, 1, 16*n, 1); addfac(td, -1, 16*n, 2)
    lhs = {k: num[k] - den[k] for k in range(1, K//2)}
    rhs = {k: tn[k] - td[k] for k in range(1, K//2)}
    diff = {k: lhs[k] - rhs[k] for k in lhs if lhs[k] != rhs[k]}
    print('first mismatches (k: lhs-rhs):', list(diff.items())[:20])
main()

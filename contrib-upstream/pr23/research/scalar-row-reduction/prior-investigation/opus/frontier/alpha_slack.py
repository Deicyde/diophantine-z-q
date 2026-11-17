"""ESTIMATE: effect of changing the Euler-product cutoff exponent eps (alpha = 18 + 6 eps).

arithmetic_round8.tex: prod_{p|N}(1+1/p) <= rad(N)^eps * prod_{p: a_p>1} a_p,
a_p=(1+1/p)p^(-eps); with eps=1/192 the constant is bounded by 32/9.
Then d_H < T = 4608*K*C*R^(3+eps), h(z) < 2^23*(4608 K C)^6 R^(18+6eps) + 128,
and R = B_S*M, so H_eps = 2^23 (4608 K)^6 C^6 B_S^(18+6eps) + 128.
(Baseline uses K=32/9 and B_S^(1/32)<3/2 -> H=3*2^106*C^6*B_S^18+128.)
Float logs only: this is an estimate of the minimal anchor, not a certificate.
"""
import math
from sympy import primerange

C = 2**32 * 3**9
BS = 46410
lnH0 = math.log(3 * 2**106 * C**6 * BS**18 + 128)


def K_of(eps):
    lk = 0.0
    for p in primerange(2, 10**7):
        a = math.log(1 + 1 / p) - eps * math.log(p)
        if a > 0:
            lk += a
        elif p > 100 and (1 + 1 / p) ** (1 / eps) < p:
            # a_p<=1 for all larger p once (1+1/x)^(1/eps)/x decreasing and <1
            break
    return lk


def lnH(eps, exact_baseline=False):
    if exact_baseline:
        return lnH0
    lk = K_of(eps)
    return 23 * math.log(2) + 6 * (math.log(4608) + lk + math.log(C)) + (18 + 6 * eps) * math.log(BS)


def minE(alpha, lh, k, s=31, sdiv=4):
    ln3 = math.log(3)
    # scalar: c*^((s-alpha)/s) > sdiv*H, c*=2*3^(E/2-1)
    lc = (math.log(sdiv) + lh) * s / (s - alpha)
    Es = 2 * ((lc - math.log(2)) / ln3 + 1)
    # Lucas: b*^(2-4alpha/k) > 24H, b*=3^(E/2-1)
    if 2 - 4 * alpha / k <= 0:
        return None
    lb = (math.log(24) + lh) / (2 - 4 * alpha / k)
    El = 2 * (lb / ln3 + 1)
    E = max(Es, El)
    return 6 * math.ceil(E / 6 - 1e-12), Es, El


if __name__ == '__main__':
    print('baseline eps=1/192 exact-H:', [(k, minE(577 / 32, lnH0, k)[0]) for k in (40, 44, 45, 46, 47)])
    print('baseline eps=1/192 recomputed K:', round(lnH(1 / 192), 2), 'vs exact lnH0', round(lnH0, 2))
    for den in (96, 192, 384, 768, 1536, 3072):
        eps = 1 / den
        lh = lnH(eps)
        alpha = 18 + 6 * eps
        row = [(k, minE(alpha, lh, k)[0]) for k in (37, 40, 44, 45, 46, 47)]
        print(f'eps=1/{den} alpha={alpha:.5f} lnH={lh:.1f} lnK={K_of(eps):.2f}', row)

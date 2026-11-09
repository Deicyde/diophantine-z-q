"""Markdown table: Elkies' rational CM points of X*(6) in the manuscript coordinate j = 16(t-1)/27."""
import ast, re
from fractions import Fraction as Fr
import sympy as sp
src = open('scratch/h-cm/cm_table.py').read()
T = ast.literal_eval(re.search(r"^T = (\[.*?\])\n", src, re.S | re.M).group(1))
def sqf(q):
    n = q.numerator*q.denominator; r = 1
    for p, e in sp.factorint(abs(n)).items():
        if e % 2: r *= p
    return r if n > 0 else -r
print("| -Δ | t = A/B (Elkies) | j = 16(t-1)/27 | 0<t<1 | t mod squares | t-1 mod squares |")
print("|---|---|---|---|---|---|")
for d, A, B in T:
    t = Fr(A, B); j = Fr(16, 27)*(t - 1)
    print(f"| {d} | {t} | {j} | {'yes' if 0 < t < 1 else 'no'} | {sqf(t)} | {sqf(t-1)} |")

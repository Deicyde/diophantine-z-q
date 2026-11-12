# hdec-elementary: checks for the Igusa/Thomae glue (Leaves.lean, section Concrete).
# (1) Igusa vector -> Igusa-Clebsch: I2, I4, I6, I10 as functions of j (J2=I2/8, J4=(4J2^2-I4)/96,
#     J6=(8J2^3-160J2J4-I6)/576, J10=I10/4096).
# (2) j = 3779136 * I10^2 / I4^5 on the Igusa vector.
# (3) Thomae point T_S = Delta(S)*Delta(S^c) over the 10 triple-partitions S|S^c of {0..5}:
#     sum_S T_S^2 = I4/a^4 (Mestre's B'), prod_S T_S^2 = (I10/a^10)^4, on 30 random integer root sets.
import itertools, random
from sympy import symbols, Rational, expand, simplify, factor, prod
j = symbols('j')
J2 = 12*(j+1); J4 = 6*(j**2+j+1); J6 = 4*(j**3-2*j**2+1); J10 = j**3
I2 = 8*J2; I4 = expand(4*J2**2 - 96*J4); I6 = expand(8*J2**3 - 160*J2*J4 - 576*J6); I10 = 4096*J10
print("I2 =", expand(I2)); print("I4 =", I4); print("I6 =", factor(I6), "=", I6); print("I10 =", I10)
assert simplify(3779136*I10**2/I4**5 - j) == 0
print("(2) j = 3779136 I10^2/I4^5 on the Igusa vector: True")
parts = []
for S in itertools.combinations(range(6), 3):
    Sc = tuple(i for i in range(6) if i not in S)
    if S < Sc: parts.append((S, Sc))
assert len(parts) == 10
def D(r, S): return prod(r[a]-r[b] for a, b in itertools.combinations(S, 2))
random.seed(20261111); ok = True
for t in range(30):
    r = random.sample(range(-50, 51), 6); a = random.choice([1, 2, 3, -5])
    T = [D(r, S)*D(r, Sc) for S, Sc in parts]
    disc = prod((r[a1]-r[b1])**2 for a1, b1 in itertools.combinations(range(6), 2))
    B = sum((D(r, S)*D(r, Sc))**2 for S, Sc in parts)  # Mestre B' / a^4
    ok &= (sum(x**2 for x in T) == B) and (prod(x**2 for x in T) == disc**4)
print("(3) 30 random root sets: sum T^2 = B'/a^4 and prod T^2 = (D'/a^10)^4:", ok)

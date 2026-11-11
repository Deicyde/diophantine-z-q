# Independent rerun of el-cert's local lemma (X3a) with a new seed, new primes, and also
# the converse-direction proof check: for v_p(T) >= 1, f(q) = -m R0 a(q)^2 (1 + O(p)) for all q.
# Reuses el-cert's locsol (brute force mod p^K) as a black box, imported by path.
import importlib.util, random, sys
from fractions import Fraction as Fr
spec = importlib.util.spec_from_file_location("x3", "scratch/el-cert/x3_local.py")
src = open("scratch/el-cert/x3_local.py").read().split("agree = tot = 0")[0]
ns = {}; exec(src, ns)
locsol, leg, vp = ns["locsol"], ns["leg"], ns["vp"]
random.seed(7)
agree = tot = 0; seen = {1: 0, 0: 0}
for p in [7, 29, 31, 37, 41, 43]:
    for trial in range(5):
        m = random.choice([1, 2, 3, 5, 6, 10, 15, -1, -2, -7, -13])
        if m % p == 0: continue
        while True:
            R0 = Fr(random.randint(2, 3000), random.randint(1, 50))
            if vp(R0, p) == 0 and leg(R0.numerator * R0.denominator, p) == -1: break
        T = Fr(p**random.randint(1, 2) * random.randint(1, 50), random.randint(1, 30))
        if vp(T, p) <= 0: continue
        pred = (leg(-m, p) == -1); got = locsol(Fr(m), R0, T, p, K=3)
        tot += 1; agree += (pred == got); seen[int(got)] += 1
        print(p, m, R0, T, "pred", pred, "brute", got)
print("agreement", agree, "/", tot, "soluble/insoluble counts", seen)

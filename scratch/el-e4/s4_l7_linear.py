# Step 4: L7 multiplier group G = <-1, primes <= 324> (rank 68). For each proxy instance (s3_out.json),
# is the affine F2-system  (-m0/p) = -1 for all obstruction primes p (p not | m0)  solvable with m0 in G
# using only generators not in Obs (so p does not divide m0)?  Also: random model of the cofactor --
# how many obstruction primes r make the system unsolvable (random Legendre characters).
import json, random
import cypari2; pari = cypari2.Pari()
recs = json.load(open("scratch/el-e4/s3_out.json"))
P = [int(p) for p in pari.primes(70) if int(p) <= 324]
def solvable(obs):
    gens = [-1] + [p for p in P if p not in obs]
    rows = []
    for p in obs:   # want chi_p(-1)*chi_p(m0) = -1  ->  sum over gens e_g * [chi_p(g) = -1] = [chi_p(-1) = 1]
        bits = [1 if pari.kronecker(g, p) == -1 else 0 for g in gens]
        rhs = 1 if pari.kronecker(-1, p) == 1 else 0
        rows.append(bits + [rhs])
    # gaussian elimination over F2
    rows = [int("".join(map(str, r)), 2) for r in rows]; n = len(gens)
    basis = []
    for r in rows:
        for b in basis: r = min(r, r ^ b)
        if r == 1: return False      # 0 = 1
        if r: basis.append(r)
    return True
print("proxy instances, L7 system solvable:", sum(solvable(r["obs"]) for r in recs), "/", len(recs))
random.seed(1)
big = [int(p) for p in pari.primes(20000) if int(p) > 400]
for r in (10, 30, 50, 60, 65, 68, 70, 80):
    ok = sum(solvable(random.sample(big, r)) for _ in range(30))
    print(f"r = {r} random obstruction primes > 400: solvable {ok}/30")

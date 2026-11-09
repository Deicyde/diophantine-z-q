"""Test the theta-transfer lemma symbolically on actual small primes:
hub h (=1 mod 8, partner of an aux z), partners r_l (l in T): [r_l/l]=1, [r_l/h]=1, other symbols 0;
all other aux have trivial symbols at T.  Claim: dim Sel(C_{d1}) = dim Sel(C_{d1*theta})."""
import sys, random, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "descent-alt"))
from symsel import legbit, config_of, selmer_dim, has_first
def primerange(a, b):
    s = bytearray([1]) * b; s[0] = s[1] = 0
    for i in range(2, int(b ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(a, b) if s[i]]
PR = list(primerange(3, 3000000))
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)

def find_prime(cond, used):
    i0 = random.randrange(len(PR))
    for k in range(len(PR)):
        q = PR[(i0 + k) % len(PR)]
        if q not in used and cond(q):
            return q
    raise RuntimeError

def trial():
    used = set()
    P = random.sample(PR[:300], random.randint(1, 3)); used |= set(P)
    beta = 1
    for p in P: beta *= p
    # theta: primes l with (beta/l)=1, product theta = 1 mod 8, (theta/p)=1 for p in P
    for _ in range(1000):
        T = []
        for _ in range(random.randint(1, 3)):
            T.append(find_prime(lambda l: legbit(beta, l) == 0, used | set(T)))
        th = 1
        for l in T: th *= l
        if th % 8 == 1 and all(legbit(th, p) == 0 for p in P) and len(set(T)) == len(T):
            break
    else:
        return None
    used |= set(T)
    # aux Q': random primes, trivial symbols at T  ([q/l]=0 for all l)
    Q = []
    for _ in range(random.randint(1, 3)):
        Q.append(find_prime(lambda q: all(legbit(q, l) == 0 for l in T), used | set(Q)))
    used |= set(Q)
    z = Q[0]
    S1 = P + Q
    h = find_prime(lambda q: q % 8 == 1 and legbit(q, z) == 1 and all(legbit(q, s) == 0 for s in S1 if s != z)
                   and all(legbit(q, l) == 0 for l in T), used)
    used.add(h)
    R = []
    for l in T:
        r = find_prime(lambda q: q % 8 == 1 and legbit(q, l) == 1 and legbit(q, h) == 1
                       and all(legbit(q, s) == 0 for s in S1 + R + [x for x in T if x != l]), used)
        R.append(r); used.add(r)
    c1 = config_of(S1 + [h] + R)
    c2 = config_of(S1 + [h] + R + T)
    c0 = config_of(S1)
    um = (1 << len(P)) - 1
    return (selmer_dim(c0), selmer_dim(c1), selmer_dim(c2), has_first(c0, um), has_first(c1, um), has_first(c2, um))

bad = 0; n = 0
for i in range(200):
    try:
        r = trial()
    except RuntimeError:
        continue
    if r is None: continue
    n += 1
    if not (r[0] == r[1] == r[2]) :
        bad += 1; print("dim mismatch", r)
print("trials", n, "dim mismatches", bad)
# second pass: first-coordinate agreement
random.seed(99); stats = {}
for i in range(200):
    try:
        r = trial()
    except RuntimeError:
        continue
    if r is None: continue
    key = (r[3], r[4], r[5]); stats[key] = stats.get(key, 0) + 1
print("(beta in pi1 for c0, c1, c2):", stats)

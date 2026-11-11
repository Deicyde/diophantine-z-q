"""wk-cr3: on minimal-Selmer curves C_d (d = 5 mod 8 squarefree, #Sel2 = 8), compare the class
mod 4 of the non-torsion first Kummer coordinates with TYZ's sums T5a, T5b (g from PARI class
groups).  Question: can row 5a (|a| = 1 mod 4) replace row 5b (|a| = 3 mod 4) in a slot design?
Usage: python -I row5a_check.py COUNT SEED"""
import random
import sys

here = __file__.rsplit("/", 1)[0]
sys.path.insert(0, here + "/../rv-cr5b-sec3")
sys.path.insert(0, here + "/../nt-tyz")
from mirror import sel2, pari  # noqa: E402
from literal_reading import sums  # noqa: E402


def main():
    count, seed = int(sys.argv[1]), int(sys.argv[2])
    rnd = random.Random(seed)
    primes = [int(p) for p in pari.primes(30)[1:]]
    gcache, stats, seen, tried = {}, {}, 0, set()
    while seen < count:
        k = rnd.randint(3, 5)
        ps = sorted(rnd.sample(primes, k))
        d = 1
        for p in ps:
            d *= p
        if d % 8 != 5 or d in tried or d > 400000:
            continue
        tried.add(d)
        S = sel2(d)
        if len(S) != 8:
            continue
        seen += 1
        tors = {1, -1, d, -d}
        nt = sorted({abs(a) % 4 for a, b in S if a not in tors})
        T5a, T5b, _, _ = sums(d, ps, gcache)
        key = (tuple(nt), T5a, T5b)
        stats[key] = stats.get(key, 0) + 1
        print(f"d={d} primes={ps} nontorsion|a|mod4={nt} T5a={T5a} T5b={T5b}", flush=True)
    print("(|a| mod 4 of non-torsion classes, T5a, T5b) -> count:", dict(sorted(stats.items())))


if __name__ == "__main__":
    main()

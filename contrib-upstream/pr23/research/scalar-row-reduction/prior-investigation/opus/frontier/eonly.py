"""e-exponent projection of the weight-circuit problem (necessary condition).
Base e-exponents {0,1,2,3,4}; gate new=x+y-z; targets 2j-1,4j-2,2k-1,4k-2,6k-3.
Finds all minimal chains of length <= L (as sets of new e-values)."""
import sys, itertools
def search(j, k, L):
    targets = {2*j-1, 4*j-2, 2*k-1, 4*k-2, 6*k-3}
    base = (0, 1, 2, 3, 4)
    maxT = max(targets)
    sols = []
    def rec(s, new, depth):
        miss = targets - s
        if not miss:
            sols.append(tuple(new)); return
        rem = L - depth
        if len(miss) > rem: return
        cm = max(s); g = 0
        while cm < max(miss): cm *= 2; g += 1
        if g > rem: return
        cands = set()
        sl = sorted(s)
        for a in sl:
            for b in sl:
                if b < a: continue
                for z in sl:
                    v = a + b - z
                    if 0 < v <= maxT and v not in s: cands.add(v)
        for v in sorted(cands):
            if new and v < new[-1] and (v in prevc(s, new)): continue
            rec(s | {v}, new + [v], depth + 1)
    cache = {}
    def prevc(s, new):
        key = frozenset(s - {new[-1]})
        if key not in cache:
            c = set(); sl = sorted(key)
            for a in sl:
                for b in sl:
                    for z in sl:
                        c.add(a + b - z)
            cache[key] = c
        return cache[key]
    rec(set(base), [], 0)
    return sols
L = int(sys.argv[1])
for j in (10, 11, 12):
    for k in range(37, 52):
        s = search(j, k, L)
        print(j, k, L, len(s), s[:3], flush=True)

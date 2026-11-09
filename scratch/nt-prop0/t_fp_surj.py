# For odd primes p and units d mod p: the Kummer map delta: E(F_p) -> (F_p*/F_p*^2)^2 of
# y^2 = x(x-d)(x+d) is onto (4 classes). Also: every F_p-class is hit by a point with y != 0
# unless it is a torsion class (used for Hensel lifting along y).
def chi(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p-1)//2, p) == 1 else -1
def primes(n):
    s = [True]*(n+1); s[0]=s[1]=False
    for i in range(2, int(n**.5)+1):
        if s[i]: s[i*i::i] = [False]*len(s[i*i::i])
    return [i for i in range(3, n+1) if s[i]]
if __name__ == "__main__":
    bad = 0; nonsmooth_needed = 0; tested = 0
    for p in primes(400):
        for d in range(1, p):
            img = {(1, 1)}
            img |= {(chi(-1,p), chi(-d,p)), (chi(d,p), chi(2,p)), (chi(-d,p), chi(-2*d,p))}
            gen = set()
            for x in range(p):
                if x in (0, d % p, (-d) % p): continue
                f = x*(x-d)*(x+d) % p
                if chi(f, p) == 1:
                    gen.add((chi(x,p), chi(x-d,p)))
            img |= gen
            tested += 1
            if len(img) != 4: bad += 1; print("not onto", p, d, img)
            # classes not reached by a point with y != 0 (would need the torsion lift)
            if len(gen | {(1,1)}) != 4: nonsmooth_needed += 1
    print("pairs (p,d) tested", tested, "not onto:", bad, "need torsion/O:", nonsmooth_needed)

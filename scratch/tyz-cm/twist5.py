exec(open('twist3.py').read().split("for n in [5,13")[0])
from math import isqrt
def solve(n):
    r = run(n); X, XN = r[1], r[2]
    u = [x for x in X if x[1]==0][0][0]; v = [x for x in X if x[1]!=0][0]
    vN = [x for x in XN if x[1]!=0][0]
    assert v[1] == vN[1] and ((v[0]-vN[0])/(u/32)).denominator == 1
    # tau_X = v/u = (v0 + v1 w)/u ; as form: tau=(-B+8w)/(2A): 2A = 8u/v1
    A = 4*u/v[1]; Bx = -8*v[0]/v[1]
    assert A.denominator == 1
    A = int(A); A0 = 16*(n+1)
    sols = []
    for d in range(-200,201):
        rem = A - 16*n*d*d
        if rem < 0: continue
        s = isqrt(rem)
        if s*s != rem: continue
        for t in (s,-s):
            c = t - 4*d
            if c % 32 == 0 and gcd(c,d)==1: sols.append((c,d))
    out = []
    for (c,d) in sols:
        # c_K = u/(c tau + d), tau = (1+w)/(4(n+1)) -> c tau + d = (c + 4(n+1)d + c w)/(4(n+1))
        m = 4*(n+1)
        z = (Fr(c + m*d, m), Fr(c, m))
        N = z[0]**2 + n*z[1]**2
        cK = (u*z[0]/N, -u*z[1]/N)
        out.append(((c,d), cK))
    return u, out
for n in [5,13,21,29,37,45,53,61]:
    u, out = solve(n)
    print(n, u, out[:4])

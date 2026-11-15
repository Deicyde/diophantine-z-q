# O/3O for O = Z<1, i, (1+j)/2, (i+k)/2> in B = (2,-3); multiplication via mulCoord (ZInQKernel/HDecomp/QM/Structures.lean)
import itertools
def mul(n, m):
    return ((m[0]*n[0] + 2*m[1]*n[1] + 2*m[1]*n[3] - m[2]*n[2] + 2*m[3]*n[3]) % 3,
            (m[0]*n[1] + m[1]*n[0] + m[1]*n[2] - m[2]*n[3] + m[3]*n[2]) % 3,
            (m[0]*n[2] - 2*m[1]*n[3] + m[2]*n[0] + m[2]*n[2] + 2*m[3]*n[1]) % 3,
            (m[0]*n[3] - m[1]*n[2] + m[2]*n[1] + m[2]*n[3] + m[3]*n[0]) % 3)
# NB: ofInt n * ofInt m = ofInt (mulCoord n m)
R = list(itertools.product(range(3), repeat=4))
one = (1,0,0,0); zero=(0,0,0,0); neg1=(2,0,0,0)
units = [x for x in R if any(mul(x,y)==one and mul(y,x)==one for y in R)]
inv = {x: next(y for y in R if mul(x,y)==one) for x in units}
print("units", len(units))
def add(a,b): return tuple((x+y)%3 for x,y in zip(a,b))
# type 4: u^2 = -1 ; type 3 (action w with w^2 - w + 1 = 0; T uses u = w^-1, so u^2 - u + 1 = 0 as well? check)
t4 = [u for u in units if mul(u,u)==neg1]
t3 = [u for u in units if add(add(mul(u,u), tuple((-c)%3 for c in u)), one)==zero]
t3inv = [inv[w] for w in t3]
print("t4", len(t4), "t3", len(t3), "t3inv", len(t3inv), set(t3inv)==set(t3))
def bad(u):
    # does there exist v1, v2 units with conj(v1,u^-1), conj(v2,u^-1) not commuting
    ui = inv[u]
    cs = [mul(mul(inv[v], ui), v) for v in units]
    for a in cs:
        for b in cs:
            if mul(a,b) != mul(b,a):
                return (a,b)
    return None
print("t4 all good:", all(bad(u) for u in t4))
print("t3 all good:", all(bad(u) for u in t3))
for u in t4[:2]: print(u, bad(u))
def comm(a,b): return mul(a,b)==mul(b,a)
ok4 = all(any(not comm(mul(mul(inv[v],inv[u]),v), inv[u]) for v in units) for u in t4)
print("CM4 single v (commute with own action u^-1):", ok4)
ok3 = all(all(any(not comm(mul(mul(inv[v],inv[u]),v), w4) for v in units) for w4 in t4) for u in t3)
print("CM3 via P4 witness:", ok3)
ok3own = [u for u in t3 if any(not comm(mul(mul(inv[v],inv[u]),v), inv[u]) for v in units)]
print("CM3 own works for", len(ok3own), "of", len(t3))

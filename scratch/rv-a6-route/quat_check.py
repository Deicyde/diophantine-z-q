# Checks for the Raynaud route of A6 (rv-a6-route). Lambda = Z<i,j>, i^2=2, j^2=-3, ij=-ji.
import itertools, cypari2
pari = cypari2.Pari()
print("hilbert(2,-3,p) for p=2,3,oo:", pari('hilbert(2,-3,2)'), pari('hilbert(2,-3,3)'), pari('hilbert(2,-3,0)'))
# multiplication of a+bi+cj+dk (k=ij): i^2=2, j^2=-3, k^2=-ij ji... k^2 = ijij = -i i j j = -2*-3 = 6
A,B = 2,-3
def mul(x,y,m):
    a1,b1,c1,d1 = x; a2,b2,c2,d2 = y
    a = a1*a2 + A*b1*b2 + B*c1*c2 - A*B*d1*d2
    b = a1*b2 + b1*a2 - B*c1*d2 + B*d1*c2
    c = a1*c2 + c1*a2 + A*b1*d2 - A*d1*b2
    d = a1*d2 + d1*a2 + b1*c2 - c1*b2
    return (a%m,b%m,c%m,d%m)
# sanity: associativity on a random sample, relations
import random
for _ in range(30):
    x,y,z=[tuple(random.randrange(81) for _ in range(4)) for _ in range(3)]
    assert mul(mul(x,y,81),z,81)==mul(x,mul(y,z,81),81)
i=(0,1,0,0); j=(0,0,1,0)
assert mul(i,i,81)==(2,0,0,0) and mul(j,j,81)==(78,0,0,0) and mul(i,j,81)==tuple((-t)%81 for t in mul(j,i,81))
# reduced trace form discriminant of basis 1,i,j,ij
basis=[(1,0,0,0),i,j,(0,0,0,1)]
tr=lambda x: 2*x[0]
M=pari.matrix(4,4,[tr(mul(u,v,10**9)) if True else 0 for u in basis for v in basis])
print("det trace form (= (4ab)^2 up to sign; reduced disc 24):", pari.matdet(M))
# k=1: all c in Lambda/9 with c^2 = 0 lie in 3 Lambda
bad=[c for c in itertools.product(range(9),repeat=4) if mul(c,c,9)==(0,0,0,0) and any(t%3 for t in c)]
print("k=1: c^2=0 mod 9 but c not in 3Lambda:", len(bad))
# k=2 sample of 30 elements of 9*Lambda/81 + random: check c^2=0 mod 81 => c in 9 Lambda on all c in 3Lambda/81 (3^12 elems)
cnt=0; bad2=0
for c0 in itertools.product(range(27),repeat=4):
    c=tuple(3*t for t in c0)
    if mul(c,c,81)==(0,0,0,0):
        cnt+=1
        if any(t%9 for t in c): bad2+=1
print("k=2 (c in 3Lambda, mod 81): #c^2=0:", cnt, " not in 9Lambda:", bad2)
# Split contrast: in M2(Z/9), nilpotent not in 3*M2
print("split contrast: [[0,1],[0,0]]^2=0 and not divisible by 3 (division algebra needed)")
# exact trace-form determinant
def mulZ(x,y):
    a1,b1,c1,d1 = x; a2,b2,c2,d2 = y
    return (a1*a2 + A*b1*b2 + B*c1*c2 - A*B*d1*d2, a1*b2 + b1*a2 - B*c1*d2 + B*d1*c2,
            a1*c2 + c1*a2 + A*b1*d2 - A*d1*b2, a1*d2 + d1*a2 + b1*c2 - c1*b2)
M=pari.matrix(4,4,[2*mulZ(u,v)[0] for u in basis for v in basis])
print("det trace form exact:", pari.matdet(M), "= 24^2 *", pari.matdet(M)/576)
# group structure of Lambda/Pi^a, Pi=j (j^2=-3): SNF of lattice j^a*Lambda (left ideal)
def jpow(a):
    x=(1,0,0,0)
    for _ in range(a): x=mulZ(j,x)
    return x
for a in range(1,6):
    gens=[mulZ(jpow(a),u) for u in basis]
    G=pari.matrix(4,4,[g[r] for r in range(4) for g in gens])
    print("Lambda/Pi^%d as group: elementary divisors"%a, pari.matsnf(G))
print("=> Lambda/Pi^(2n-1) + Lambda/Pi has order 3^(4n) and exponent 3^n but is not (Z/3^n)^4;"
      " for n=1 it is (Z/3)^4 = A[3] group-theoretically but killed by Pi (not free).")

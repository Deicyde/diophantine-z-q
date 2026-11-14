import itertools
def mul(n,m):
    return (m[0]*n[0] + 2*m[1]*n[1] + 2*m[1]*n[3] - m[2]*n[2] + 2*m[3]*n[3],
    m[0]*n[1] + m[1]*n[0] + m[1]*n[2] - m[2]*n[3] + m[3]*n[2],
    m[0]*n[2] - 2*m[1]*n[3] + m[2]*n[0] + m[2]*n[2] + 2*m[3]*n[1],
    m[0]*n[3] - m[1]*n[2] + m[2]*n[1] + m[2]*n[3] + m[3]*n[0])
# mulCoord n m = coords of ofInt n * ofInt m
e=(1,0,0,0)
R=range(-6,7)
units={}
vecs=list(itertools.product(R,repeat=4))
# find inverse by search: norm via quaternion
from fractions import Fraction as F
def quat(n):
    return (n[0]+F(n[2],2), n[1]+F(n[3],2), F(n[2],2), F(n[3],2))
def nrd(n):
    a,b,c,d=quat(n); return a*a-2*b*b+3*c*c-6*d*d
def conjc(n):
    a,b,c,d=quat(n); # conj = a - bi - cj - dk ; convert back: n2=2*(-c), n3=2*(-d), n0=a-n2/2, n1=b' - n3/2
    n2=-2*c; n3=-2*d; n0=a-F(n2,2); n1=-b-F(n3,2)
    return tuple(int(x) for x in (n0,n1,n2,n3))
found={}
for n in vecs:
    N=nrd(n)
    if N in (1,-1):
        cl=tuple(x%3 for x in n)
        if cl not in found or sum(abs(x) for x in n)<sum(abs(x) for x in found[cl]):
            c=conjc(n); m=tuple(N*x for x in c)
            assert mul(n,m)==e and mul(m,n)==e, (n,m)
            found[cl]=n
# unit classes mod 3
def mulmod(d,c): return tuple(x%3 for x in mul(d,c))
allc=list(itertools.product(range(3),repeat=4))
unitcl=[c for c in allc if any(mulmod(d,c)==e for d in allc)]
print(len(unitcl), len(found), set(unitcl)<=set(found), set(found)<=set(unitcl))
missing=[c for c in unitcl if c not in found]; print("missing",missing)
import json
out={str(c):(found[c], tuple(int(nrd(found[c]))*x for x in conjc(found[c]))) for c in unitcl}
json.dump(out,open('/tmp/units.json','w'))
print(max(max(abs(x) for x in found[c]) for c in unitcl))

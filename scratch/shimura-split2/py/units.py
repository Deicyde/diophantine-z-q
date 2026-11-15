# units of O = Z<1, i, (1+j)/2, (i+k)/2> in B = (2,-3|Q) covering (O/3O)^x
from fractions import Fraction as Fr
import itertools
def coords(n):
    n0,n1,n2,n3=n
    return (n0+Fr(n2,2), n1+Fr(n3,2), Fr(n2,2), Fr(n3,2))
def nrd(n):
    x0,x1,x2,x3=coords(n)
    return x0*x0-2*x1*x1+3*x2*x2-6*x3*x3
def mulCoord(n,m):
    return (m[0]*n[0]+2*m[1]*n[1]+2*m[1]*n[3]-m[2]*n[2]+2*m[3]*n[3],
            m[0]*n[1]+m[1]*n[0]+m[1]*n[2]-m[2]*n[3]+m[3]*n[2],
            m[0]*n[2]-2*m[1]*n[3]+m[2]*n[0]+m[2]*n[2]+2*m[3]*n[1],
            m[0]*n[3]-m[1]*n[2]+m[2]*n[1]+m[2]*n[3]+m[3]*n[0])
def star(n):
    n0,n1,n2,n3=n
    return (n0+n2,-n1,-n2,-n3)
# integer nrd formula in n-coords
def nrdZ(n):
    v=nrd(n); assert v.denominator==1; return int(v)
res={}
R=range(-6,7)
for n in itertools.product(R,repeat=4):
    v=nrdZ(n)
    if v in (1,-1):
        r=tuple(x%3 for x in n)
        if r not in res or sum(map(abs,n))<sum(map(abs,res[r])):
            res[r]=n
good=[r for r in itertools.product(range(3),repeat=4) if nrdZ(r)%3!=0]
print(len(good), len(res), all(r in res for r in good))
# polynomial for nrd in n coords
import sympy
a,b,c,d=sympy.symbols('a b c d')
x0=a+c/sympy.Integer(2); x1=b+d/sympy.Integer(2); x2=c/sympy.Integer(2); x3=d/sympy.Integer(2)
print(sympy.expand(x0**2-2*x1**2+3*x2**2-6*x3**2))
tab=[res[r] for r in good]
inv=[]
for n in tab:
    s=nrdZ(n); st=star(n); iv=tuple(s*x for x in st)
    assert mulCoord(n,iv)==(1,0,0,0) and mulCoord(iv,n)==(1,0,0,0), (n,iv,mulCoord(n,iv))
    inv.append(iv)
def lean(v): return "!["+", ".join(str(x) for x in v)+"]"
print("TAB", "![" + ", ".join(lean(n) for n in tab) + "]")
print("INV", "![" + ", ".join(lean(n) for n in inv) + "]")
# nested tables indexed by residues (a,b,c,d) in {0,1,2}^4; non-units get the zero vector
def nested(f):
    out=[]
    for a in range(3):
        A=[]
        for b in range(3):
            Bl=[]
            for c in range(3):
                C=[]
                for d in range(3):
                    r=(a,b,c,d)
                    C.append(lean(f(r)) if r in res and nrdZ(r)%3!=0 else lean((0,0,0,0)))
                Bl.append("!["+", ".join(C)+"]")
            A.append("!["+", ".join(Bl)+"]")
        out.append("!["+",\n    ".join(A)+"]")
    return "![" + ",\n  ".join(out) + "]"
invd={r:tuple(nrdZ(res[r])*x for x in star(res[r])) for r in res}
open("/home/jackmccarthy/dzq-wt/shimura-split2/scratch/shimura-split2/py/tabU.lean","w").write(nested(lambda r: res[r]))
open("/home/jackmccarthy/dzq-wt/shimura-split2/scratch/shimura-split2/py/tabV.lean","w").write(nested(lambda r: invd[r]))

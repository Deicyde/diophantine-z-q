# rv-qm-polar: exact checks on B=(2,-3), O = Z<1, i, (1+j)/2, (i+k)/2>, mu = 2j+k.
from fractions import Fraction as F
import itertools
def mul(x,y):
    a0,a1,a2,a3=x; b0,b1,b2,b3=y   # i^2=2, j^2=-3, k=ij, k^2=6, ij=-ji
    return (a0*b0+2*a1*b1-3*a2*b2+6*a3*b3,
            a0*b1+a1*b0+3*a2*b3-3*a3*b2,
            a0*b2+a2*b0+2*a1*b3-2*a3*b1,
            a0*b3+a3*b0+a1*b2-a2*b1)
def conj(x): return (x[0],-x[1],-x[2],-x[3])
def nrd(x): return x[0]**2-2*x[1]**2+3*x[2]**2-6*x[3]**2
def trd(x): return 2*x[0]
def sc(r,x): return tuple(r*t for t in x)
def inv(x): n=F(nrd(x)); return tuple(F(t)/n for t in conj(x))
def add(x,y): return tuple(a+b for a,b in zip(x,y))
basis=[(1,0,0,0),(0,1,0,0),(F(1,2),0,F(1,2),0),(0,F(1,2),0,F(1,2))]
def ofInt(n): return tuple(sum(n[r]*basis[r][c] for r in range(4)) for c in range(4))
def coords(x):  # inverse of ofInt
    n2=2*x[2]; n3=2*x[3]; n0=x[0]-F(n2,2); n1=x[1]-F(n3,2); return (n0,n1,n2,n3)
def inO(x): return all(F(c).denominator==1 for c in coords(x))
mu=(0,0,2,1); i=(0,1,0,0); j=(0,0,1,0); k=(0,0,0,1)
print("mu^2", mul(mu,mu))
chi2=i; chi3=add(j,k)
for name,c in [("i",chi2),("j+k",chi3)]:
    print(name, "sq", mul(c,c), "inO", inO(c), "anticommutes with mu", add(mul(c,mu),mul(mu,c))==(0,0,0,0))
print("i(j+k) =", mul(chi2,chi3), "= mu")
def dag(m,x): return mul(mul(inv(m),conj(x)),m)
def E(m,x,y): return trd(mul(mul(inv(m),x),conj(y)))
# twisting preserves the Rosati type
for c in [chi2,chi3,mu]:
    ok=all(dag(mu,mul(mul(c,b),inv(c)))==mul(mul(c,dag(mu,b)),inv(c)) for b in basis)
    print("Ad",c,"commutes with dag_mu on O:",ok)
# all pure mu' in O with mu'^2=-6 and small coords
sols=[]
R=range(-6,7)
for n in itertools.product(R,repeat=4):
    x=ofInt(n)
    if x[0]==0 and nrd(x)==6: sols.append(x)
print("pure mu' in O, mu'^2=-6, coords in [-6,6]:", len(sols))
import sympy
def gram(m): return sympy.Matrix(4,4,lambda r,s: E(m,basis[r],basis[s]))
for x in sols[:6]:
    G=gram(x); print(" mu'=",x,"det",G.det(),"integral",all(sympy.Rational(t).q==1 for t in G))
mup=(0,0,2,-1)
print("mu'=2j-k: sq",mul(mup,mup),"inO",inO(mup),"det gram",gram(mup).det())
print(" dag_mu(i)",dag(mu,i)," dag_mu'(i)",dag(mup,i))
# a unit u with u mu u^-1 = mu' ?
found=None
for n in itertools.product(range(-3,4),repeat=4):
    u=ofInt(n)
    if abs(nrd(u))==1 and mul(mul(u,mu),inv(u))==mup: found=(n,u,nrd(u)); break
print("unit u with u mu u^-1 = 2j-k:",found)
# norms of elements anticommuting with mu: span{i, j+k}: nrd(a i + b(j+k)) = -2a^2-3b^2 <0
print("nrd(a i + b(j+k)) = -2a^2 - 3b^2 (check a=1,b=1):", nrd(add(i,chi3)))
# mu^{-1} alpha(mu) in O^1 for inner alpha = Ad u, u unit: check sample
cnt=0
for n in itertools.product(range(-2,3),repeat=4):
    u=ofInt(n)
    if abs(nrd(u))==1:
        v=mul(inv(mu),mul(mul(u,mu),inv(u)))
        assert inO(v) and nrd(v)==1, (n,v)
        cnt+=1
print("mu^-1 (u mu u^-1) in O, nrd 1, for",cnt,"units u with coords in [-2,2]")
print("--- part 2")
for b in basis+[j,k]:
    print(" b",b,"dag_mu",dag(mu,b),"dag_mu'",dag(mup,b))
vp=add((-1,0,0,0),i)
print("v'=-1+i: nrd",nrd(vp),"inO",inO(vp),"; -v' mu v'^-1 == 2j-k:", sc(-1,mul(mul(vp,mu),inv(vp)))==mup)
# E_mu' is not a multiple of E_mu: compare Gram matrices
print("Gram mu ", gram(mu).tolist()); print("Gram mu'", gram(mup).tolist())
# each small mu' : find unit u with u mu u^-1 = +-mu'
units=[ofInt(n) for n in itertools.product(range(-4,5),repeat=4) if abs(nrd(ofInt(n)))==1]
print("units with coords in [-4,4]:",len(units))
for x in sols:
    w=next((u for u in units if mul(mul(u,mu),inv(u)) in (x,sc(-1,x))),None)
    print(" mu'",tuple(str(t) for t in x),"conj to +-mu by unit:",w is not None)

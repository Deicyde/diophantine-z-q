"""igusa-generic: verify (exact, pure python) on the normal form f = x^5 + p x^3 + q x^2 + r x + s
(a = [s, r, q, p, 0, 1, 0]) the 16 identities M3 (pair(y_i,y_j) = gramJ, p6(f, y_i y_j y_k) = cubJ),
and in general (7 variables) the translation identities D(y_n0) = y_n1, D(y_n1) = 2 y_n2, D(y_n2) = 0,
D = sum (i+1) a_{i+1} d/da_i.  Run from the repo root: python3 -I scratch/igusa-generic/nf_check.py"""
import sys, re, itertools
sys.path.insert(0,'scratch/igusa-generic')
from poly import *
GEN='ZInQKernel/HDecomp/Textbook/Igusa/Generic.lean'
FWD='ZInQKernel/HDecomp/Textbook/Igusa/Forward.lean'
Y=parse_defs(GEN)
fwd=open(FWD).read()
def parseJ(name):
    body=re.search(r"def %s \(a : Fin 7 → K\) : K :=\n(.*?)\n\n"%name, fwd, re.S).group(1)
    r={}
    for t in body.split(" +\n"):
        t=t.strip(); m=re.match(r"\((-?\d+) : K\)",t); c=Fr(int(m.group(1))); e=[0]*7
        for v in re.finditer(r"a (\d)(?: \^ (\d+))?", t[m.end():]): e[int(v.group(1))]+=int(v.group(2) or 1)
        r=add(r,{tuple(e):c})
    return r
J={'J2':parseJ('J2'),'J4':parseJ('J4'),'J6':parseJ('J6')}
j10=re.search(r"def j10Data : List \(ℤ × List ℕ\) :=\n(.*?)\]\n\n", fwd, re.S).group(1)
r={}
for m in re.finditer(r"\((-?\d+), \[([\d, ]+)\]\)", j10):
    r=add(r,{tuple(int(u) for u in m.group(2).split(", ")):Fr(int(m.group(1)))})
J['J10']=r
print("J sizes", {k:len(v) for k,v in J.items()})
gen=open(GEN).read()
def parseM3(name):
    body=re.search(r"def m3%s \{K : Type\*\} \[Field K\] \(j2 j4 j6 j10 : K\) : K :=\n(.*?)\n\n"%name, gen, re.S).group(1)
    body=" ".join(body.split())
    # terms: ((c : K) / d) * monomial  separated by ' + '
    r={}
    for m in re.finditer(r"\(\((-?\d+) :\s*K\) /\s*(\d+)\)((?:\s*\*\s*j\d+(?:\s*\^\s*\d+)?)*)", body):
        c=Fr(int(m.group(1)),int(m.group(2))); e=[0]*4
        for v in re.finditer(r"j(\d+)(?:\s*\^\s*(\d+))?", m.group(3)):
            e[[2,4,6,10].index(int(v.group(1)))]+=int(v.group(2) or 1)
        r=add(r,{tuple(e):c})
    return r
names=['G11','G12','G13','G22','G23','G33']+['a'+''.join(str(u+1) for u in t) for t in itertools.combinations_with_replacement(range(3),3)]
M3={n:parseM3(n) for n in names}
print("m3 sizes", {k:len(v) for k,v in M3.items()})
# check weighted homogeneity of the m3 polys
deg=[3,5,7]
for n,pp in M3.items():
    ds={2*e[0]+4*e[1]+6*e[2]+10*e[3] for e in pp}
    assert len(ds)==1, n
# (1) D-identities in 7 variables
def D(p):
    r={}
    for k,v in p.items():
        for i in range(6):
            if k[i]:
                e=list(k); e[i]-=1; e[i+1]+=1
                r=add(r,{tuple(e):v*k[i]*(i+1)})
    return r
for n in range(1,4):
    assert D(Y[(n,0)])==Y[(n,1)], n
    assert D(Y[(n,1)])==scal(Fr(2),Y[(n,2)]), n
    assert D(Y[(n,2)])=={}, n
print("D-identities OK")
for k in J: assert D(J[k])=={}, k
print("J translation-invariant OK")
# (2) normal form
def v4(i): e=[0]*4; e[i]=1; return {tuple(e):Fr(1)}
one={(0,0,0,0):Fr(1)}
A=[v4(3),v4(2),v4(1),v4(0),{},one,{}]
y=[[subst(Y[(n,k)],A) for k in range(3)] for n in range(1,4)]
Jn=[subst(J[k],A) for k in ('J2','J4','J6','J10')]
print("J on nf sizes",[len(t) for t in Jn])
w6=[60,-10,4,-3,4,-10,60]
def cub(u,v,t):
    out=[]
    for m in range(7):
        acc={}
        for i in range(3):
            for j in range(3):
                k=m-i-j
                if 0<=k<=2: acc=add(acc,mul(mul(u[i],v[j]),t[k]))
        out.append(acc)
    return out
def p6(u,v):
    r={}
    for i in range(7): r=add(r, scal(Fr(w6[i]),mul(u[i],v[6-i])))
    return r
def pair(u,v): return sub(add(scal(Fr(2),mul(u[0],v[2])),scal(Fr(2),mul(u[2],v[0]))),mul(u[1],v[1]))
for n in names:
    rhs=subst(M3[n],Jn)
    idx=[int(c)-1 for c in n[1:]]
    lhs=pair(y[idx[0]],y[idx[1]]) if n[0]=='G' else p6(A,cub(y[idx[0]],y[idx[1]],y[idx[2]]))
    assert lhs==rhs, n
print("M3 on normal form: all 16 OK")
# integer scalings: LCD of the coefficients of y_n (common to its 3 coefficients)
from math import lcm
for n in range(1,4):
    L=1
    for k in range(3):
        for v in Y[(n,k)].values(): L=lcm(L,v.denominator)
    print("N%d ="%n, L)

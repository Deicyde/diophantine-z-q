"""Generate Lean text: integer-coefficient versions z{n}c{k} = N_n * y{n}c{k} over any CommRing.
Run from the repo root: python3 -I scratch/igusa-generic/gen_cov.py > scratch/igusa-generic/gen_z.lean"""
import sys
sys.path.insert(0,'scratch/igusa-generic')
from poly import *
Y=parse_defs('ZInQKernel/HDecomp/Textbook/Igusa/Generic.lean')
N={1:2250,2:168750,3:12656250}
def mono(e):
    return " * ".join(f"a {i}"+(f" ^ {x}" if x>1 else "") for i,x in enumerate(e) if x)
def body(terms):
    out=[]
    for e,c in terms:
        assert c.denominator==1
        out.append(f"({c.numerator} : R) * {mono(e)}")
    return " +\n    ".join(out)
for n in range(1,4):
    for k in range(3):
        p={e:c*N[n] for e,c in Y[(n,k)].items()}
        terms=sorted(p.items(),reverse=True)
        if len(terms)<=30:
            print(f"def z{n}c{k} {{R : Type*}} [CommRing R] (a : Fin 7 → R) : R :=\n    {body(terms)}\n")
        else:
            ch=[terms[i:i+22] for i in range(0,len(terms),22)]
            for m,c in enumerate(ch):
                print(f"def z{n}c{k}_{m} {{R : Type*}} [CommRing R] (a : Fin 7 → R) : R :=\n    {body(c)}\n")
            print(f"def z{n}c{k} {{R : Type*}} [CommRing R] (a : Fin 7 → R) : R :=\n  "+" + ".join(f"z{n}c{k}_{m} a" for m in range(len(ch)))+"\n")

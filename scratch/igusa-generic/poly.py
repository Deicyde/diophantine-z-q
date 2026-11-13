"""Minimal exact sparse polynomial arithmetic (pure python3, no sympy) + parser for the Lean
definitions y1c0..y3c2_4 of ZInQKernel/HDecomp/Textbook/Igusa/Generic.lean."""
from fractions import Fraction as Fr
import re
NV = 7
def P(d=None): return dict(d or {})
def const(c, nv=NV): return {(0,)*nv: Fr(c)} if c else {}
def var(i, nv=NV):
    e=[0]*nv; e[i]=1; return {tuple(e): Fr(1)}
def add(p, q):
    r=dict(p)
    for k,v in q.items():
        s=r.get(k,0)+v
        if s: r[k]=s
        else: r.pop(k,None)
    return r
def scal(c, p): return {k: c*v for k,v in p.items()} if c else {}
def sub(p,q): return add(p, scal(Fr(-1),q))
def mul(p, q):
    r={}
    for k1,v1 in p.items():
        for k2,v2 in q.items():
            k=tuple(a+b for a,b in zip(k1,k2)); s=r.get(k,0)+v1*v2
            if s: r[k]=s
            else: r.pop(k,None)
    return r
def pw(p,n):
    r=const(1, len(next(iter(p))) if p else NV)
    for _ in range(n): r=mul(r,p)
    return r
def ev(p, vals):
    s=Fr(0)
    for k,v in p.items():
        t=v
        for x,e in zip(vals,k):
            if e: t*=Fr(x)**e
        s+=t
    return s
def subst(p, polys):
    """substitute variable i -> polys[i] (polys over a common ring)"""
    nv=len(next(iter(polys[0]))) if polys[0] else None
    r={}
    cache={}
    for k,v in p.items():
        t=None
        for i,e in enumerate(k):
            if e:
                key=(i,e)
                if key not in cache: cache[key]=pw(polys[i],e)
                t=cache[key] if t is None else mul(t,cache[key])
        if t is None: t={tuple([0]*len(next(iter(polys[0])))): Fr(1)}
        r=add(r, scal(v,t))
    return r

TERM=re.compile(r"\(\((-?\d+) : K\) / (\d+)\)|\((-?\d+) : K\)")
def parse_defs(path):
    src=open(path).read()
    defs={}
    for m in re.finditer(r"def (y\dc\d(?:_\d)?) \{K : Type\*\} \[Field K\] \(a : Fin 7 → K\) : K :=\n(.*?)\n\n", src, re.S):
        name, body = m.group(1), m.group(2)
        defs[name]=body
    polys={}
    def getp(name):
        if name in polys: return polys[name]
        body=defs[name].strip()
        if re.fullmatch(r"(y\dc\d_\d a)( \+ y\dc\d_\d a)*", body):
            r={}
            for sub_ in body.split(" + "): r=add(r, getp(sub_.split()[0]))
            polys[name]=r; return r
        r={}
        for t in body.split(" +\n"):
            t=t.strip()
            mm=TERM.match(t)
            if mm.group(1): c=Fr(int(mm.group(1)),int(mm.group(2)))
            else: c=Fr(int(mm.group(3)))
            e=[0]*7
            for v in re.finditer(r"a (\d)(?: \^ (\d+))?", t[mm.end():]):
                e[int(v.group(1))]+=int(v.group(2) or 1)
            r=add(r,{tuple(e):c})
        polys[name]=r; return r
    out={}
    for n in range(1,4):
        for k in range(3):
            out[(n,k)]=getp(f"y{n}c{k}")
    return out

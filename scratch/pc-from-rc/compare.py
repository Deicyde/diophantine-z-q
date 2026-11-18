# Compare brute-force local solubility (selmer.selmer) with the local-image formulas used in the
# dimension-three count: a>0 (real); a,b odd, b = 1 mod 4 (2-adic); 3 does not divide b, b = 1 mod 3
# (3-adic); at q | l, (a,b) in the span of the torsion classes (l,1), (3,-l) mod Q_q^*2.
import sys
sys.path.insert(0,'scratch/pc-from-rc')
from selmer import factor, leg, selmer, sqfree_divs
def cls_q(x,q):  # class of nonzero integer x in Q_q^*/Q_q^*2 as (v mod 2, leg(unit))
    v=0
    while x%q==0: x//=q; v+=1
    return (v%2, leg(x,q))
def add(c,d): return ((c[0]+d[0])%2,(c[1]+d[1])%2)
def formula(l):
    fs=factor(l); out=[]
    for a in sqfree_divs([2,3]+fs):
        for b in sqfree_divs([2,3]+fs):
            if a<0 or a%2==0 or b%2==0 or (b%4)!=1: continue
            if b%3==0 or b%3!=1: continue
            ok=True
            for q in fs:
                ca,cb=cls_q(a,q),cls_q(b,q)
                span=set()
                for e1 in (0,1):
                    for e2 in (0,1):
                        A=(0,0);B=(0,0)
                        if e1: A=add(A,cls_q(l,q))
                        if e2: A=add(A,cls_q(3,q)); B=add(B,cls_q(-l,q))
                        span.add((A,B))
                if (ca,cb) not in span: ok=False;break
            if ok: out.append((a,b))
    return sorted(out)
if __name__=='__main__':
  bad=0;cnt=0
  for l in range(11,int(sys.argv[1])):
      if l%12!=11: continue
      fs=factor(l)
      if len(set(fs))!=len(fs): continue
      S=sorted(selmer(l)); Fm=formula(l); cnt+=1
      if S!=Fm: bad+=1; print("MISMATCH",l,S,Fm)
  print("checked",cnt,"mismatches",bad)

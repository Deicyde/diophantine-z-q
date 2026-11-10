# Independent check of Prop 1.6: literal point counts vs c_p description, p < 30000.
import sys
from math import gcd
def primes(n):
    s=bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2,int(n**.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]
NMAX=int(sys.argv[1]) if len(sys.argv)>1 else 30000
fails=[]; nclass=0; npairs=0; ngood_lit=0; ngood_pred=0; mism=[]; badl=set()
for p in primes(NMAX):
    if p==2: continue
    # number of square roots of each residue
    nsq=[0]*p
    for y in range(p): nsq[y*y%p]+=1
    def pc(a):  # literal pointCount
        return sum(nsq[(x*x*x+a*x)%p] for x in range(p))+1
    roots=[r for r in range(p) if r*r%p==2]
    lit=False
    for r in roots:
        d=(75-53*r)%p; db=(75+53*r)%p
        if d==0 or db==0: continue
        n1=pc((-d*d)%p); n2=pc((-db*db)%p)
        if gcd(n1,n2)==4: lit=True
        if p%8==1 and p%7 in (3,5,6):
            npairs+=1
            phi1=pc(1)-p-1
            c=phi1//2
            # nonresidue
            r0=next(t for t in range(2,p) if pow(t,(p-1)//2,p)==p-1)
            e=(pc(r0)-p-1)//2
            ok = phi1%2==0 and c%2==1 and c*c+e*e==p and sorted([n1,n2])==sorted([p+1-2*c,p+1+2*c]) \
                 and gcd(n1,n2)==4*gcd(c,p+1)
            if not ok: fails.append((p,r))
            g=gcd(c,p+1)
            for l in primes(abs(g)+1) if g>1 else []:
                if g%l==0: badl.add(l%4)
    pred = p%8==1 and p%7 in (3,5,6)
    if pred:
        nclass+=1
        phi1=pc(1)-p-1; pred = gcd(phi1//2,p+1)==1
    if lit: ngood_lit+=1
    if pred: ngood_pred+=1
    if lit!=pred: mism.append(p)
print("class primes",nclass,"pairs",npairs,"fails",fails[:10])
print("GoodSlopePrime literal",ngood_lit,"predicted",ngood_pred,"mismatches",mism[:20])
print("residues mod 4 of bad l:",badl)

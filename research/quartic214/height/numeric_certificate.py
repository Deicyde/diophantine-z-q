#!/usr/bin/env python3
"""Portable exact numeric/contact certificate. Does not certify arithmetic premises."""
from fractions import Fraction as Q
from math import prod,gcd
from pathlib import Path
import argparse,copy,json
HERE=Path(__file__).resolve().parent
DEFAULT={'S':[2,3,5,7,11,13,17,37,41,2399], 'alpha':'2103/1024', 'C2Bits':'7557/32', 'kUpper':'9339/1000'}

def log_interval(x,n=40):
    """Positive rational log; scale to[1,2), then atanh and geometric tail."""
    x=Q(x); assert x>=1
    k=0
    while x>=2:x/=2;k+=1
    def red(y):
        z=(y-1)/(y+1)
        low=2*sum((z**(2*j+1)/Q(2*j+1) for j in range(n)),Q(0))
        return low,low+2*z**(2*n+1)/(Q(2*n+1)*(1-z*z))
    a,b=red(x);c,d=red(Q(2));return a+k*c,b+k*d
def lo(x):return log_interval(x)[0]
def hi(x):return log_interval(x)[1]
def vp(n,p):
    r=0
    while n%p==0:r+=1;n//=p
    return r
def support(n):
    n=abs(n);p=2;out=[]
    while p*p<=n:
        if n%p==0:
            out.append(p)
            while n%p==0:n//=p
        p+=1 if p==2 else 2
    if n>1:out.append(n)
    return out
def form_support(f,g):return support(f[0]*g[1]-f[1]*g[0])
def pa(*ps):
    r=[Q(0)]*max(map(len,ps))
    for p in ps:
        for i,x in enumerate(p):r[i]+=x
    while len(r)>1 and r[-1]==0:r.pop()
    return r
def ps(p,c):return [x*c for x in p]
def pm(p,q):
    r=[Q(0)]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):r[i+j]+=x*y
    return r

def verify(c):
    assert c['S']==DEFAULT['S']
    S=c['S'];B=prod(S);EB=prod(Q(p+1,p) for p in S)
    G=prod(11**4-11**i for i in range(4));V=[vp(576*G,p) for p in (2,3,5,7)]
    assert V==[15,4,4,1]
    ram=[V[0]+2]+V[1:];cond=[2+4*v for v in ram]
    assert cond==[70,18,18,6]
    CN=prod(p**(v-2) for p,v in zip((2,3,5,7),cond))
    assert CN==2**68*3**16*5**16*7**4
    L,U=log_interval(B); assert B==1857890364330 and L>28 and U<29
    k=Q(c['kUpper']);K0=(hi(12)+3*hi(CN))/2+hi(2)+Q(3,2)
    assert 4+K0/L<k
    assert hi(2304)<L and hi(4*k)+hi(CN)<4*L
    assert hi(14)<3 and 768<28*L
    assert 4*k*CN*B*B>2
    delta=Q(1,10**6);coeff=8*k+delta
    assert 216+128/L<delta*CN*B*B
    assert 1708*B+128<coeff*CN*B*B*L
    C2upper=coeff*CN*B*B*EB*U
    cb=Q(c['C2Bits'])
    assert C2upper**cb.denominator<2**cb.numerator
    theta=hi(Q(20,19))/lo(19)+1/L
    a=Q(c['alpha']);assert 2+theta<a and a<3
    return {'status':'PASS','scope':'H0–H4 exact finite rational logarithm and conductor arithmetic only; no arithmetic theorem or independent acceptance.',
      'B':B,'CN':CN,'conductorExponents':cond,'kUpper':str(k),'coefficient_c':str(coeff),
      'C2Log2StrictUpper':str(cb),'alpha':str(a),'arithmeticAccepted':False}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=HERE/'NUMERIC_CERTIFICATE_H4.json')
    ap.add_argument('--self-test',action='store_true');args=ap.parse_args()
    out=verify(copy.deepcopy(DEFAULT));bad=[]
    if args.self_test:
        for name,key,value in [('false C2bits','C2Bits','236'),('false k bound','kUpper','9'),
          ('wrong alpha','alpha','2'),('missing support prime','S',[2,3,5,7,11,13,17,37,41])]:
            c=copy.deepcopy(DEFAULT);c[key]=value
            try:verify(c)
            except AssertionError:bad.append(name)
            else:raise AssertionError('corruption accepted: '+name)
    out['negativeControlsRefused']=bad
    args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()

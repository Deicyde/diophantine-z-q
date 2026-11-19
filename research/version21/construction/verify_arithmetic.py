"""Exact finite constants for the Version21 N=15 proof, independently computed."""
from fractions import Fraction as F
from functools import reduce
from itertools import combinations
from math import prod
import json


def factors(n):
    n=abs(n)
    if not n: raise ValueError('zero factorization input')
    result=set();p=2
    while p*p<=n:
        if n%p==0:
            result.add(p)
            while n%p==0:n//=p
        p=3 if p==2 else p+2
    if n>1:result.add(n)
    return result


def log_unit(q,terms=80):
    assert 1<=q<=2
    t=(q-1)/(q+1); value=F(0)
    for j in range(terms):value+=2*t**(2*j+1)/(2*j+1)
    error=2*t**(2*terms+1)/((2*terms+1)*(1-t*t))
    return value,value+error


def log_bounds(q):
    q=F(q);assert q>0;k=0
    while q>=2:q/=2;k+=1
    while q<1:q*=2;k-=1
    a,b=log_unit(q);c,d=log_unit(F(2))
    return (a+k*c,b+k*d) if k>=0 else (a+k*d,b+k*c)


def main():
    S={2,3,5,7,11,13,17,37,41,2399}
    gamma=S|{79,89,647,3593}
    theta=[F(0),F(-1,2),F(-1),F(1,2399),F(-32,407)]
    center=F(3,11); midpoint=center/2
    contacts=theta+[center-t for t in theta]
    assert len(set(contacts))==10 and max(contacts)-min(contacts)==F(25,11)
    support=set()
    for t in contacts:
        support|=factors(t.denominator)
        delta=midpoint-t;support|=factors(delta.numerator)|factors(delta.denominator)
    for a,b in combinations(contacts,2):
        delta=a-b;support|=factors(delta.numerator)|factors(delta.denominator)
    assert support<=gamma
    source_contacts=[F(0),F(1),F(2401),F(-343,32)]
    finite_collision=set()
    for a,b in combinations(source_contacts,2):
        delta=a-b;finite_collision|=factors(delta.numerator)|factors(delta.denominator)
    assert finite_collision<={2,3,5,7}
    residues=[]
    for t in source_contacts:
        q=(t-2504)/51
        residue=q.numerator*pow(q.denominator,-1,149)%149
        assert pow(residue,74,149)==148
        residues.append(residue)
    assert residues==[59,97,109,108]
    c0=F(74712001,10**6);C0=2**68*3**16*5**16*7**4
    BS=prod(S);J=prod(gamma)
    def euler(primes):return prod((F(p+1,p) for p in primes),start=F(1))
    scalar_constant=c0*C0*BS**2*euler(S)*log_bounds(BS)[1]
    assert scalar_constant<2**237
    reflected_constant=c0*C0*J**2*euler(gamma)
    assert J==30366775457346956958330 and J<2**75
    assert reflected_constant<2**300 and c0*C0<2**149
    assert log_bounds(J)[1]+log_bounds(14)[1]/6<53
    assert reflected_constant*log_bounds(J)[0]>120*log_bounds(33)[1]+2425
    primes=[p for p in range(2,1001) if factors(p)=={p}]
    product=euler(set(primes)-gamma)
    assert product<F(21,10)
    # x log(x) is increasing for x>=1000; the first excluded integer suffices.
    assert 1001*log_bounds(1001)[0]>6006
    log149=log_bounds(149);log2=log_bounds(2)
    assert 5<log149[0] and log149[1]<F(501,100)
    assert log2[1]<F(173287,250000)
    assert log_bounds(500)[1]<F(25,4) and log_bounds(274)[1]<F(45,8)
    assert 53+44*F(501,100)<274
    lower=220*F(6005,6006)
    upper=F(25,4)+300*F(173287,250000)+F(45,8)
    assert lower>F(219963,1000)>upper
    exponent=F(1,3)+F(1,36036)
    # Verify the logarithmic comparison for the factor 500 without numerical powers.
    assert log_bounds(121)[1]+log_bounds(F(21,10))[1]/2+exponent*log_bounds(14)[1]<log_bounds(500)[0]
    assert F(23,22)*log_bounds(256036*2**304)[1]<240
    assert 149**66>2**239 and 149**66>600
    assert 66*log149[0]>330
    assert F(19,8)>F(9,4)
    return {'scope':'Exact finite products, supports, residues and rational-series bounds only.',
            'exceptional_set':sorted(gamma),'contact_support':sorted(support),'contact_diameter':'25/11',
            'nonresidues_mod_149':residues,'J':str(J),'scalar_constant_below_power_of_two':237,
            'reflected_constant_below_power_of_two':300,'euler_product_below':'21/10',
            'N':15,'L_N':(9*(2*15-1))//4+1,'contradiction_lower':str(lower),'contradiction_upper':str(upper),
            'positive_margin':str(lower-upper),'log_growth_constant_below':240}


if __name__=='__main__':
    print(json.dumps(main(),indent=2))

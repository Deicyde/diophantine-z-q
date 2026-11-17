import itertools, random
from fractions import Fraction as F
def mul(n,m):
    return [m[0]*n[0]+2*m[1]*n[1]+2*m[1]*n[3]-m[2]*n[2]+2*m[3]*n[3],
            m[0]*n[1]+m[1]*n[0]+m[1]*n[2]-m[2]*n[3]+m[3]*n[2],
            m[0]*n[2]-2*m[1]*n[3]+m[2]*n[0]+m[2]*n[2]+2*m[3]*n[1],
            m[0]*n[3]-m[1]*n[2]+m[2]*n[1]+m[2]*n[3]+m[3]*n[0]]
def conj(n): return [n[0]+n[2],-n[1],-n[2],-n[3]]
def nrd(n): return n[0]**2+n[0]*n[2]+n[2]**2-2*(n[1]**2+n[1]*n[3]+n[3]**2)
I=[0,1,0,0]; J=[-1,0,2,0]  # j = 2*(1+j)/2 - 1
print('i*i',mul(I,I),'j*j',mul(J,J), nrd(I), nrd(J))
inP2=lambda n: n[0]%2==0 and n[2]%2==0
inP3=lambda n: (n[0]-n[2])%3==0 and (n[1]-n[3])%3==0
R=range(-3,4)
for n in itertools.product(R,repeat=4):
    n=list(n)
    assert inP2(n)==(nrd(n)%2==0)
    assert inP3(n)==(nrd(n)%3==0)
    # pi^{-1} z pi - conj z in P : pi^{-1} = conj(pi)/nrd(pi); test nrd(pi)*(...) = conj(pi) z pi - nrd(pi) conj z
    for pi,inP,l in [(I,inP2,2),(J,inP3,3)]:
        a=mul(mul(conj(pi),n),pi); b=[nrd(pi)*x for x in conj(n)]
        d=[x-y for x,y in zip(a,b)]
        assert all(x% l==0 for x in d), (n,pi,d)
        d2=[x//l for x in d]  # = (conj(pi) z pi - nrd conj z)/l ; nrd(pi)=±l so this is ±(pi^-1 z pi - conj z)
        assert inP(d2),(n,pi)
for _ in range(2000):
    n=[random.randint(-9,9) for _ in range(4)]; m=[random.randint(-9,9) for _ in range(4)]
    c=[x-y for x,y in zip(mul(n,m),mul(m,n))]
    assert inP2(c) and inP3(c)
print("ok")

# Check: for n odd and a,b odd (classes mod 8), (a,b) in 2-adic image of C_n
# iff the three conics  au^2-bv^2=nt^2, au^2-abw^2=-nt^2, bv^2-abw^2=-2nt^2 are 2-adically soluble.
def v2u(x):
    k=0
    while x%2==0: x//=2;k+=1
    return k,x
def hilb2(a,b):
    al,u=v2u(a); be,w=v2u(b)
    eps=lambda t:((t-1)//2)%2
    om=lambda t:((t*t-1)//8)%2
    e=(eps(u)*eps(w)+al*om(w)+be*om(u))%2
    return 1 if e==0 else -1
T={1:{(1,1),(1,5),(7,3),(7,7)},7:{(1,1),(1,5),(7,1),(7,5)},3:{(1,1),(1,5),(7,1),(7,5)},5:{(1,1),(1,5),(7,3),(7,7)}}
ok=True
for n in (1,3,5,7):
    for a in (1,3,5,7):
        for b in (1,3,5,7):
            # use representatives that are positive to keep hilb2's formula valid for units
            c1=hilb2(a*n,(-b*n)%64 or 64) ; c2=hilb2((-a*n)%64,a*b*n); c3=hilb2((-2*b*n)%128,2*a*b*n)
            pred=(c1==1 and c2==1 and c3==1)
            if pred!=((a,b) in T[n]): ok=False; print('diff',n,a,b,c1,c2,c3)
print('three-conic criterion matches table:',ok)

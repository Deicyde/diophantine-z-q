exec(open('eta.py').read().split('res=[]')[0])
X=quot((0,2,-1,0,1,-2)); Y1=quot((0,0,-2,4,2,-4))
f=quot((0,0,2,2,0,0))  # times q^{(8+16)/24}=q^1
print('f',[int(v) for v in f[:30]])
# a_p
def leg(a,p):
    a%=p
    if a==0: return 0
    return 1 if pow(a,(p-1)//2,p)==1 else -1
def isprime(n): return n>1 and all(n%k for k in range(2,int(n**.5)+1))
ap={p:-sum(leg(x**3+4*x,p) for x in range(p)) for p in range(3,PREC) if isprime(p)}
ap[2]=0
# a_n from Euler product
a=[0]*PREC; a[1]=1
def apow(p,k):
    if k==0: return 1
    if p==2: return 0
    if k==1: return ap[p]
    return ap[p]*apow(p,k-1)-p*apow(p,k-2)
for n in range(1,PREC):
    m=n; val=1; p=2
    while m>1:
        if m%p==0:
            k=0
            while m%p==0: m//=p;k+=1
            val*=apow(p,k)
        p+=1
    a[n]=val
print('match f(q)=sum a_n q^n up to',PREC-1, all(f[n-1]==a[n] for n in range(1,PREC)))
# modular param identity: q dx/dq = c*Y1*f; x=q^-2 X(q) + 2
# q d/dq of q^-2 sum X_i q^i = sum (i-2) X_i q^{i-2}
lhs=[(i-2)*X[i] for i in range(PREC)]          # coefficient of q^{i-2}
prod=mul(Y1,f)                                 # times q^{-3+1} = q^-2
for c in (2,-2):
    print('c',c, all(lhs[i]==c*prod[i] for i in range(PREC)))

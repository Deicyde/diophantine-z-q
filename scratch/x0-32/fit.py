exec(open('eta.py').read().split('res=[]')[0])
X=quot((0,2,-1,0,1,-2))   # times q^-2
Y1=quot((0,0,-2,4,2,-4))  # times q^-3
Y2=quot((2,-1,0,-1,4,-4))
print('X',X[:12]); print('Y1',Y1[:12]); print('Y2',Y2[:12])
# Laurent series as dict shift: represent by list with offset -3
def L(s,off):  # returns list of coefficients from q^-6 ... 
    out=[0]*(PREC); 
    for i,v in enumerate(s):
        k=i+off+6
        if 0<=k<PREC: out[k]=v
    return out
def lm(a,b):
    c=[0]*PREC
    for i,x in enumerate(a):
        if x:
            for j in range(PREC-i):
                c[i+j-6] += x*b[j] if 0<=i+j-6<PREC else 0
    return c
for sx in (1,-1):
  for b in range(-8,9):
    x=L(X,-2); x=[sx*v for v in x]; x[6]+=b
    for Y in (Y1,Y2):
      for sy in (1,-1):
        y=[sy*v for v in L(Y,-3)]
        lhs=lm(y,y); x2=lm(x,x); x3=lm(x2,x)
        rhs=[x3[i]+4*x[i] for i in range(PREC)]
        if all(lhs[i]==rhs[i] for i in range(40)):
            print('FOUND sx',sx,'b',b,'Y',Y is Y1,'sy',sy)

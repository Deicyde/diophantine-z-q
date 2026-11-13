import cmath, math
def eta(t):
    q=cmath.exp(2j*math.pi*t)
    p=cmath.exp(2j*math.pi*t/24)
    s=1
    n=1
    qn=q
    while abs(qn)>1e-18:
        s*=(1-qn); qn*=q; n+=1
    return p*s
def xy(t):
    e={d:eta(d*t) for d in (2,4,8,16,32)}
    x=e[2]**2*e[16]/(e[4]*e[32]**2)+2
    y=-(e[8]**4*e[16]**2/(e[4]**2*e[32]**4))
    return x,y
for name,c in [('0',0),('1/2',0.5),('1/4',0.25),('-1/4',-0.25),('1/8',0.125),('-1/8',-0.125),('1/16',1/16)]:
    for eps in (2e-3,1e-3):
        x,y=xy(c+1j*eps)
        print(name,eps,complex(round(x.real,6),round(x.imag,6)),complex(round(y.real,6),round(y.imag,6)))
t=0.1+0.7j; x,y=xy(t); print('eq check',y*y-x**3-4*x)

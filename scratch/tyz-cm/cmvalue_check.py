# sanity check of CMValueRingClass for g = x (x0-32's eta model), level 32:
# x(tau_Q) should lie in the ring class field H_D, so deg x(tau_Q) <= 2 h(D).
import mpmath as mp
mp.mp.dps = 250
def eta(z):
    q = mp.exp(2j*mp.pi*z)
    return mp.exp(2j*mp.pi*z/24)*mp.qp(q)
def xC(z): return eta(2*z)**2*eta(16*z)/(eta(4*z)*eta(32*z)**2)+2
def yC(z): return -(eta(8*z)**4*eta(16*z)**2/(eta(4*z)**2*eta(32*z)**4))
for (A,B,C,h) in [(32,10,1,1),(32,18,3,2),(96,-8,1,None)]:
    D=B*B-4*A*C
    tau=(-B+mp.sqrt(D))/(2*A)
    x=xC(tau); y=yC(tau)
    print((A,B,C),'D=',D,'x=',mp.nstr(x,20),'curve residual',mp.nstr(abs(y**2-x**3-4*x),5))
    for deg in [1,2,4,8,16]:
        # algdep on real and imaginary structure: use findpoly on x (complex) via [Re,Im] separately is messy;
        # use mp.findpoly on the complex number by stacking real/imag parts of powers
        pw=[x**k for k in range(deg+1)]
        rows=[mp.re(p) for p in pw]+[mp.im(p) for p in pw]
        # integer relation among real and imaginary parts simultaneously: pslq on combined vector with weights
        vec=[mp.re(p)+(mp.e/mp.pi)*mp.im(p) for p in pw]
        rel=mp.pslq(vec,maxcoeff=10**40,maxsteps=10**6)
        if rel:
            val=sum(c*p for c,p in zip(rel,pw))
            if abs(val) < mp.mpf(10)**(-150):
                print('  deg',deg,'relation',rel,'|P(x)|=',mp.nstr(abs(val),5))
                break

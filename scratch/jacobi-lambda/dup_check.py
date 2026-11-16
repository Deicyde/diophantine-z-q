# numeric check of the duplication formula for Mathlib's jacobiTheta2
import cmath
def th(z,t,N=40):
    return sum(cmath.exp(2j*cmath.pi*n*z+1j*cmath.pi*n*n*t) for n in range(-N,N+1))
for (z,w,t) in [(0.3+0.1j,-0.2+0.05j,0.2+0.7j),(0.1,0.45-0.2j,-0.3+1.1j),(0.7j,0.2,0.4+0.5j)]:
    L=th(z,t)*th(w,t)
    R=th(z+w,2*t)*th(z-w,2*t)+cmath.exp(2j*cmath.pi*z+1j*cmath.pi*t)*th(z+w+t,2*t)*th(z-w+t,2*t)
    print(abs(L-R))

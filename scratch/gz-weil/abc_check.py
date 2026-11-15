import cmath
pi=cmath.pi
def th2(t, N=80): return sum(cmath.exp(pi*1j*(n+0.5)**2*t) for n in range(-N, N))
def th3(t, N=80): return sum(cmath.exp(pi*1j*n*n*t) for n in range(-N, N+1))
def th4(t, N=80): return sum((-1)**n*cmath.exp(pi*1j*n*n*t) for n in range(-N, N+1))
def ld(f, t, h=1e-6): return (f(t+h)-f(t-h))/(2*h)/f(t)
A=lambda t: ld(th2,t); B=lambda t: ld(th3,t); C=lambda t: ld(th4,t)
for t in [0.3+0.9j, -0.4+1.2j]:
    s=-1/t
    print("S:", abs(B(s)-(t*t*B(t)+t/2)), abs(A(s)-(t*t*C(t)+t/2)), abs(C(s)-(t*t*A(t)+t/2)))
    print("T:", abs(A(t+1)-A(t)), abs(B(t+1)-C(t)), abs(C(t+1)-B(t)))
    E1=B(t)-A(t)+pi*1j/4*th4(t)**4; E2=B(t)-C(t)-pi*1j/4*th2(t)**4; E3=A(t)-C(t)-pi*1j/4*th3(t)**4
    print("E:", abs(E1), abs(E2), abs(E3))

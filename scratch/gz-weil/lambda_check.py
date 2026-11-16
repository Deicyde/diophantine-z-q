import cmath
def th2(t, N=60): return sum(cmath.exp(cmath.pi*1j*(n+0.5)**2*t) for n in range(-N, N))
def th3(t, N=60): return sum(cmath.exp(cmath.pi*1j*n*n*t) for n in range(-N, N+1))
def th4(t, N=60): return sum((-1)**n*cmath.exp(cmath.pi*1j*n*n*t) for n in range(-N, N+1))
def lam(t): return th2(t)**4/th3(t)**4
for t in [0.3+0.8j, -0.2+1.1j, 0.45+0.6j]:
    h = 1e-6
    d = (lam(t+h)-lam(t-h))/(2*h)
    print(t, d, cmath.pi*1j*lam(t)*th4(t)**4, abs(d-cmath.pi*1j*lam(t)*th4(t)**4))
# (*) f th2(4tau)^2 = 2 th2(16tau) th3(16tau) th4(16tau)^4, f = eta(4tau)^2 eta(8tau)^2
def eta(t, N=200):
    q = cmath.exp(2j*cmath.pi*t); p = cmath.exp(2j*cmath.pi*t/24)
    for n in range(1, N): p *= (1-q**n)
    return p
for tau in [0.1+0.3j, -0.3+0.25j]:
    f = eta(4*tau)**2*eta(8*tau)**2
    print(abs(f*th2(4*tau)**2 - 2*th2(16*tau)*th3(16*tau)*th4(16*tau)**4))

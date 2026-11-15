"""h33-sign: numerical checks at 200 digits (PARI via cypari2); sample of 20 n (<= 30 allowed).

(1) TYZ Prop 3.5(2) (L1494-1496, proof L1563-1574) on the identity component of X_U: with
    Q^{j eps} = [Q at (j eps)^{-1} tau] = phi(tau/(1-8tau)), TYZ print Q^{j eps} = [i]Q + tau((1-i)/2),
    tau((1-i)/2) = [-1/8] = (2i, 0).  Test at 5 random tau with [i] = +I and with [i] = -I.
(2) TYZ Thm 3.6(1) third identity (L1413) z-bar = -z + tau(1), tau(1) = (0,0), at P = phi(h_n),
    h_n root of 16(n+1)h^2 - 8h + 1 in H, for z = P - [I]P (kernel tyzZn) and z = P + [I]P.
(3) Non-torsion indicator for z: elliptic logarithm of z in the period lattice, best rational
    approximation of its lattice coordinates with denominator <= 10^4 (torsion <=> rational).
"""
import cypari2, random
pari = cypari2.Pari()
pari.set_real_precision(200)
E = pari.ellinit([0, 0, 0, 4, 0])
I = pari('I')
def eta(z): return pari.eta(z, 1)
def phi(t):
    e = {d: eta(d*t) for d in (2, 4, 8, 16, 32)}
    return [e[2]**2*e[16]/(e[4]*e[32]**2) + 2, -(e[8]**4*e[16]**2/(e[4]**2*e[32]**4))]
def iP(P, s=1): return [-P[0], s*I*P[1]]
def add(P, Q): return pari.elladd(E, P, Q)
def neg(P): return pari.ellneg(E, P)
def conj(P): return [pari.conj(P[0]), pari.conj(P[1])] if P != [0] else P
def size(P): return 0 if P == [0] else abs(P[0]) + abs(P[1])
def close(P, Q):
    if P == [0] or Q == [0]: return P == Q or size(P if Q == [0] else Q) > 10**50
    return abs(P[0]-Q[0]) + abs(P[1]-Q[1]) < pari('1e-150')
out = []
def say(s): print(s); out.append(s)
T = [2*I, 0]
random.seed(1)
for k in range(5):
    t = pari(f'({random.randint(-500, 500)}/1000 + I*{random.randint(50, 300)}/1000)*1.')
    lhs = phi(t/(1 - 8*t))
    assert pari.imag(t) > 0
    r = {s: close(lhs, add(iP(phi(t), s), T)) for s in (1, -1)}
    say(f'(1) tau={pari.precision(t, 5)}: phi(tau/(1-8tau)) = [+I]phi+(2i,0): {r[1]};  = [-I]phi+(2i,0): {r[-1]}')
P00 = [0, 0]
ns = [n for n in range(5, 400, 8) if pari.issquarefree(n)][:20]
w = pari.ellperiods(E)  # [w1, w2]
for n in ns:
    h = pari(f'(8 + I*sqrt({64*n}))/(32*({n} + 1))')
    P = phi(h)
    zK = add(P, neg(iP(P)))      # P - [I]P
    zA = add(P, iP(P))           # P + [I]P
    cK = close(add(conj(zK), zK), P00)       # z-bar + z = (0,0)
    cA = close(add(conj(zA), zA), P00)
    cA2 = close(add(conj(zA), neg(zA)), P00)  # z-bar - z = (0,0)
    u = pari.ellpointtoz(E, zK)
    # lattice coordinates (a, b) with u = a w1 + b w2
    M = pari.matrix(2, 2, [pari.real(w[0]), pari.real(w[1]), pari.imag(w[0]), pari.imag(w[1])])
    ab = pari.matsolve(M, pari.matrix(2, 1, [pari.real(u), pari.imag(u)]))
    rat = [pari.bestappr(ab[i, 0], 10**4) for i in range(2)]
    err = max(abs(ab[i, 0] - rat[i]) for i in range(2))
    say(f'(2) n={n}: zK-bar + zK = (0,0): {cK};  zA-bar + zA = (0,0): {cA};  zA-bar - zA = (0,0): {cA2}'
        f';  (3) |coords(log zK) - best rational (den<=1e4)| = {pari.precision(err, 3)}')
open('cm.out', 'w').write('\n'.join(out) + '\n')

"""Heegner-point sums on X0(32) = A (32a1) for TYZ Theorem 3.3 tests.

n = 7 mod 8: P_1(n) = sum over Cl(-n) of phi(tau_Q), Q = [A,B,C], 32|A, B = delta mod 64,
             delta^2 = -n mod 128 (TYZ embedding, L1214).
n = 5 mod 8: x = f0(P_n) is the CM point tau of [16(n+1), -8, 1] (disc -64n, conductor 4);
             its K-conjugates are the forms of disc -64n with 32|A, B = -8 mod 64 (one per class
             of Cl(-64n), checked).  S_chi = sum_{t in Cl(-64n)} chi(t) phi(tau_t) for chi
             pulled back from Cl_n; then P_chi = (S_chi - i0 S_{chi psi})/4, psi = char of K(i)/K.
All points are handled as elliptic logarithms z in C / Lambda_A.
"""
import sys
import cypari2
pari = cypari2.Pari()
pari('default(realprecision, 80)')
pari.allocatemem(2 * 10**9)

E = pari('E32 = ellinit([0,0,0,4,0])')  # 32a1 = X0(32) (optimal, Manin constant 1)
NAN = 120000
OM = pari('E32.omega')
w1, w2 = OM[0], OM[1]


pari("an32 = ellan(ellinit([0,0,0,4,0]), %d)" % NAN)
pari("zphi_gp(tau) = my(q = exp(2*Pi*I*tau), qq = 1, s = 0, ok = 0); for(k = 1, #an32, qq *= q; s += an32[k]*qq/k; if(abs(qq) < 1e-75, ok = 1; break)); if(!ok, error(\"zphi: series not converged\")); s")
pari("tau_gp(A,B,C) = (-B + sqrt(B^2 - 4*A*C))/(2*A)")


def zphi(tau):
    return pari("zphi_gp")(tau)


def red_lattice(z):
    """reduce z modulo Z w1 + Z w2; return coordinates (x, y) with z = x w1 + y w2."""
    M = pari.matrix(2, 2, [pari.real(w1), pari.real(w2), pari.imag(w1), pari.imag(w2)])
    v = pari.matsolve(M, pari.matrix(2, 1, [pari.real(z), pari.imag(z)]))
    return v[0, 0], v[1, 0]


def in_lattice(z, tol=1e-25):
    x, y = red_lattice(z)
    return abs(float(x - pari.round(x))) < tol and abs(float(y - pari.round(y))) < tol


def heegner_forms(D, beta, amax=400):
    """one form per SL2(Z)-class: [A,B,C], A=32a, B=beta mod 64, disc D; smallest a first."""
    reps = {}
    allforms = {}
    for a in range(1, amax + 1):
        A = 32 * a
        for j in range(a):
            B = beta + 64 * j
            if (B * B - D) % (4 * A):
                continue
            C = (B * B - D) // (4 * A)
            if pari.gcd(pari.gcd(A, B), C) != 1 or pari.gcd(pari.gcd(a, B), 32 * C) != 1:
                continue
            key = str(pari.qfbred(pari.Qfb(A, B, C)))
            allforms.setdefault(key, []).append((A, B, C))
            if key not in reps:
                reps[key] = (A, B, C)
    return reps, allforms


def tau_of(Q):
    A, B, C = Q
    return pari("tau_gp")(A, B, C)


def represented_value(Q, D):
    A, B, C = Q
    for s in range(1, 60):
        for x in range(-s, s + 1):
            for y in (s - abs(x), -(s - abs(x))):
                m = A * x * x + B * x * y + C * y * y
                if m > 0 and pari.gcd(m, 2 * D) == 1:
                    return m
    raise ValueError


def genus_char(Dfund, Q, D):
    m = represented_value(Q, D)
    return int(pari.kronecker(Dfund, m))


def fund(d):
    """fundamental discriminant of Q(sqrt d)."""
    return int(pari.coredisc(d))


def sums_for(n, fields, beta, D):
    """S_chi for chi = character of K(sqrt f), f in fields (f = 1 means trivial)."""
    reps, allforms = heegner_forms(D, beta)
    h = int(pari.qfbclassno(D))
    out = {f: 0 for f in fields}
    for key, Q in reps.items():
        z = zphi(tau_of(Q))
        for f in fields:
            c = 1 if f == 1 else genus_char(fund(f), Q, D)
            out[f] += c * z
    # consistency: two representatives of one class give the same point
    checks = 0
    for key, L in allforms.items():
        L = [Q for Q in L if Q[0] <= 1200]
        if len(L) >= 2 and checks < 3:
            z0, z1 = zphi(tau_of(L[0])), zphi(tau_of(L[1]))
            assert in_lattice(z0 - z1), (key, L[0], L[1])
            checks += 1
    return out, len(reps), h, checks


def delta7(n):
    for d in range(1, 128, 2):
        if (d * d + n) % 128 == 0:
            return d


if __name__ == "__main__":
    pass

# Independent numerical check of PkgI1.ThetaModularity (leaf-review-a).
# thetaConst m Ω = Σ_{n∈Z²} exp(πi v^T Ω v + πi v^T b), v = n + a/2 (as in Leaves3.lean l.224).
# Sp4(Z) membership as in Mathlib: M J Mᵀ = J with J = fromBlocks 0 (-1) 1 0.
import itertools, mpmath as mp
mp.mp.dps = 30
R = 7
def theta(a, b, W):
    s = mp.mpc(0)
    for n0 in range(-R, R+1):
        for n1 in range(-R, R+1):
            v = [n0 + a[0]/2, n1 + a[1]/2]
            q = sum(v[i]*W[i][j]*v[j] for i in range(2) for j in range(2))
            s += mp.exp(mp.pi*1j*q + mp.pi*1j*(v[0]*b[0] + v[1]*b[1]))
    return s
chars = [(a, b) for a in itertools.product([0,1], repeat=2) for b in itertools.product([0,1], repeat=2)]
even = [(a, b) for (a, b) in chars if (a[0]*b[0] + a[1]*b[1]) % 2 == 0]
assert len(even) == 10
def S8(W): return sum(theta(a, b, W)**8 for (a, b) in even)
def P2(W):
    p = mp.mpc(1)
    for (a, b) in even: p *= theta(a, b, W)**2
    return p
def act(M, W):
    A = mp.matrix([[M[0][0], M[0][1]], [M[1][0], M[1][1]]]); B = mp.matrix([[M[0][2], M[0][3]], [M[1][2], M[1][3]]])
    C = mp.matrix([[M[2][0], M[2][1]], [M[3][0], M[3][1]]]); D = mp.matrix([[M[2][2], M[2][3]], [M[3][2], M[3][3]]])
    Wm = mp.matrix(W)
    X = (A*Wm + B) * mp.inverse(C*Wm + D)
    return [[X[0,0], X[0,1]], [X[1,0], X[1,1]]], mp.det(C*Wm + D)
J = [[0,0,-1,0],[0,0,0,-1],[1,0,0,0],[0,1,0,0]]
def is_symp(M):
    Mm = mp.matrix(M); Jm = mp.matrix(J)
    return mp.norm(Mm*Jm*Mm.T - Jm) == 0
gens = {
 'J': J,
 'T11': [[1,0,1,0],[0,1,0,0],[0,0,1,0],[0,0,0,1]],
 'T12': [[1,0,0,1],[0,1,1,0],[0,0,1,0],[0,0,0,1]],
 'U': [[1,1,0,0],[0,1,0,0],[0,0,1,0],[0,0,-1,1]],
 'Jpart': [[0,0,-1,0],[0,1,0,0],[1,0,0,0],[0,0,0,1]],
}
W = [[mp.mpc(0.13, 1.1), mp.mpc(0.21, 0.35)], [mp.mpc(0.21, 0.35), mp.mpc(-0.37, 0.9)]]
s0, p0 = S8(W), P2(W)
for name, M in gens.items():
    assert is_symp(M), name
    W2, f = act(M, W)
    r1 = S8(W2) / (f**4 * s0); r2 = P2(W2) / (f**10 * p0)
    print(name, mp.nstr(r1, 12), mp.nstr(r2, 12))

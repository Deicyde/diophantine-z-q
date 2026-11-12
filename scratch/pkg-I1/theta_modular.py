"""pkg-I1: numerical check of the exact form of the Sp4(Z) transformation laws used in the leaf
`ThetaModularity` of I1.lean:  Sigma(M.Om) = det(C Om + D)^4 Sigma(Om),  Pi(M.Om) = det(C Om + D)^10 Pi(Om),
with Sigma = sum of theta_m^8 and Pi = prod of theta_m^2 over the ten even characteristics
(psi4 = Sigma/4, chi10 = -Pi/2^14, Igusa).  Generators of Sp4(Z): J, translations by symmetric
integer B, and diag(A, A^-T).  Run: ~/pyenv/bin/python -I theta_modular.py"""
import mpmath as mp
mp.mp.dps = 25
def theta(ch, Om, N=22):
    (a1,a2),(b1,b2) = ch; s = mp.mpc(0)
    for n1 in range(-N, N+1):
        for n2 in range(-N, N+1):
            x1 = n1 + mp.mpf(a1)/2; x2 = n2 + mp.mpf(a2)/2
            s += mp.exp(1j*mp.pi*(x1*x1*Om[0,0] + 2*x1*x2*Om[0,1] + x2*x2*Om[1,1] + x1*b1 + x2*b2))
    return s
chars = [((a1,a2),(b1,b2)) for a1 in (0,1) for a2 in (0,1) for b1 in (0,1) for b2 in (0,1)]
even = [ch for ch in chars if (ch[0][0]*ch[1][0] + ch[0][1]*ch[1][1]) % 2 == 0]
def SP(Om):
    th = [theta(ch, Om) for ch in even]
    return mp.fsum([t**8 for t in th]), mp.fprod([t**2 for t in th])
def act(M, Om):
    A = M[0:2,0:2]; B = M[0:2,2:4]; C = M[2:4,0:2]; D = M[2:4,2:4]
    return (A*Om + B)*(C*Om + D)**-1, mp.det(C*Om + D)
Om0 = mp.matrix([[mp.mpc('0.13','1.21'), mp.mpc('0.31','0.42')], [mp.mpc('0.31','0.42'), mp.mpc('-0.22','1.07')]])
I2 = mp.eye(2); Z2 = mp.zeros(2)
def blk(A, B, C, D):
    M = mp.zeros(4)
    for r in range(2):
        for c in range(2):
            M[r,c] = A[r,c]; M[r,c+2] = B[r,c]; M[r+2,c] = C[r,c]; M[r+2,c+2] = D[r,c]
    return M
gens = {"J": blk(Z2, -I2, I2, Z2),
        "T(B=[[1,0],[0,0]])": blk(I2, mp.matrix([[1,0],[0,0]]), Z2, I2),
        "T(B=[[0,1],[1,0]])": blk(I2, mp.matrix([[0,1],[1,0]]), Z2, I2),
        "diag(A,A^-T), A=[[1,1],[0,1]]": blk(mp.matrix([[1,1],[0,1]]), Z2, Z2, mp.matrix([[1,0],[-1,1]])),
        "diag(A,A^-T), A=[[0,1],[1,0]]": blk(mp.matrix([[0,1],[1,0]]), Z2, Z2, mp.matrix([[0,1],[1,0]]))}
S0, P0 = SP(Om0)
Jst = blk(Z2, I2, -I2, Z2)
for name, M in gens.items():
    assert mp.norm(M.T*Jst*M - Jst) < 1e-20
    Om1, d = act(M, Om0)
    S1, P1 = SP(Om1)
    print(f"{name}: |S(MOm) - det^4 S(Om)|/|S| = {mp.nstr(abs(S1 - d**4*S0)/abs(S1), 4)};"
          f" |P(MOm) - det^10 P(Om)|/|P| = {mp.nstr(abs(P1 - d**10*P0)/abs(P1), 4)};"
          f" (with -det^10: {mp.nstr(abs(P1 + d**10*P0)/abs(P1), 4)})")

# Is C_d : y^2 = x^3 - d^2 x (d = 5 mod 8 squarefree) the X0(N)-optimal curve of its isogeny class?
# PARI ellweilcurve(E) = [vE, vS]: vE the isogeny class (minimal models, E's class in ellisomat order,
# E itself first), vS the Smith invariants of L_{E'} inside L_f; the optimal curve has [1,1].
import cypari2
pari = cypari2.Pari(); pari.allocatemem(10**9, 14*10**9)
def sqfree(n):
    return all(n % (p*p) for p in range(2, int(n**0.5)+1))
ds = [d for d in range(5, 200, 8) if sqfree(d)][int(__import__("sys").argv[1]):int(__import__("sys").argv[2])]
for d in ds:
    E = pari.ellinit([0, 0, 0, -d*d, 0])
    N = pari.ellglobalred(E)[0]
    vE, vS = pari.ellweilcurve(E)
    opt = [i for i in range(len(vS)) if list(vS[i]) == [1, 1]]
    # is the first curve (a minimal model of C_d) isomorphic to C_d?  ellisomat order puts E first
    iso = pari.ellisoncurve if False else None
    print(d, 'N =', N, 'smith =', [list(map(int, s)) for s in vS], 'C_d optimal:', opt == [0],
          'a4,a6 of optimal:', [(int(vE[i][3]), int(vE[i][4])) for i in opt])

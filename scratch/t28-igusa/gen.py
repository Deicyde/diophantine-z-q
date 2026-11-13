"""t28-igusa: generate Lean text for the ring-generic Igusa polynomials JnR and the explicit
coefficient formula actC of sexticAct. Reads scratch/pkg-I1/igusa_polys.txt.
Run from the repo root: ~/pyenv/bin/python -I scratch/t28-igusa/gen.py > scratch/t28-igusa/gen_out.lean"""
import sympy as sp
a = sp.symbols('a0:7')
polys = {}
for line in open('scratch/pkg-I1/igusa_polys.txt'):
    k, v = line.split(' = ')
    polys[k] = sp.sympify(v, locals={f'a{i}': a[i] for i in range(7)})
def lean_expr(P, var='a', R='R'):
    terms = []
    for mon, cf in sp.Poly(P, *a).terms():
        m = " * ".join(f"{var} {i}" + (f" ^ {e}" if e > 1 else "") for i, e in enumerate(mon) if e > 0)
        cf = sp.Integer(cf)
        terms.append(f"({cf} : {R}) * {m}")
    return " +\n    ".join(terms)
for k in ('J2', 'J4', 'J6'):
    print(f"def {k}R {{R : Type*}} [CommRing R] (a : Fin 7 → R) : R :=\n    {lean_expr(polys[k])}\n")
# J10R in chunks of 25 terms (one 246-term expression times out in elaboration)
terms = sp.Poly(polys['J10'], *a).terms()
chunks = [terms[i:i+25] for i in range(0, len(terms), 25)]
for n, ch in enumerate(chunks):
    P = sum(sp.Integer(cf) * sp.prod([a[i]**e for i, e in enumerate(mon)]) for mon, cf in ch)
    print(f"def J10R{n} {{R : Type*}} [CommRing R] (a : Fin 7 → R) : R :=\n    {lean_expr(P)}\n")
print("def J10R {R : Type*} [CommRing R] (a : Fin 7 → R) : R :=\n    " + " + ".join(f"J10R{n} a" for n in range(len(chunks))) + "\n")
# actC: coefficient i of e * sum_k f_k (A x + B)^k (C x + D)^(6-k)
A, B, C, D, E, x = sp.symbols('A B C D E x')
f = sp.symbols('f0:7')
P = sp.expand(E*sum(f[k]*(A*x+B)**k*(C*x+D)**(6-k) for k in range(7)))
def lean_gen(Q):
    out = []
    for mon, cf in sp.Poly(Q, *f, A, B, C, D, E).terms():
        parts = []
        for v, e in zip(list(f)+[A, B, C, D, E], mon):
            if e == 0: continue
            s = str(v)
            if s.startswith('f'): s = f"f {s[1:]}"
            parts.append(s + (f" ^ {e}" if e > 1 else ""))
        out.append(f"({sp.Integer(cf)} : K) * " + " * ".join(parts))
    return " + ".join(out)
print("def actC {K : Type*} [Field K] (f : Fin 7 → K) (A B C D E : K) : Fin 7 → K :=\n  ![" +
      ",\n    ".join(lean_gen(P.coeff(x, i)) for i in range(7)) + "]\n")

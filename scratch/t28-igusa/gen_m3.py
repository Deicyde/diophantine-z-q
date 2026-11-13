"""t28-igusa: Lean text for the Clebsch quadratic covariants y1,y2,y3 (coefficient vectors, as
explicit polynomials in a0..a6) and for the identities M3 (from m3_polys.txt).
Run from the repo root: ~/pyenv/bin/python -I scratch/t28-igusa/gen_m3.py > scratch/t28-igusa/gen_m3.lean"""
import itertools, sympy as sp
x, z = sp.symbols('x z')
A = sp.symbols('a0:7')
def tv(phi, psi, k):
    m = sp.Poly(phi, x, z).total_degree(); n = sp.Poly(psi, x, z).total_degree()
    s = sum((-1)**j * sp.binomial(k, j) * sp.diff(phi, x, k - j, z, j) * sp.diff(psi, x, j, z, k - j) for j in range(k + 1))
    return sp.expand(sp.factorial(m - k) * sp.factorial(n - k) / (sp.factorial(m) * sp.factorial(n)) * s)
f = sp.expand(sum(A[i] * x**i * z**(6 - i) for i in range(7)))
i4 = tv(f, f, 4); y1 = tv(f, i4, 4); y2 = tv(i4, y1, 2); y3 = tv(i4, y2, 2)
def coef(P, R='K'):
    terms = []
    for mon, cf in sp.Poly(P, *A).terms():
        m = " * ".join(f"a {i}" + (f" ^ {e}" if e > 1 else "") for i, e in enumerate(mon) if e > 0)
        cf = sp.Rational(cf)
        c = f"({cf.p} : {R})" if cf.q == 1 else f"(({cf.p} : {R}) / {cf.q})"
        terms.append(f"{c} * {m}")
    return " +\n      ".join(terms)
for n, y in enumerate((y1, y2, y3)):
    for k in range(3):
        P = sp.expand(y).coeff(x, k).coeff(z, 2 - k)
        terms = sp.Poly(P, *A).terms()
        if len(terms) <= 40:
            print(f"def y{n+1}c{k} {{K : Type*}} [Field K] (a : Fin 7 → K) : K :=\n      {coef(P)}\n")
            continue
        # chunks of 20 terms (one 86-term expression times out in elaboration)
        chunks = [terms[i:i+20] for i in range(0, len(terms), 20)]
        for m, ch in enumerate(chunks):
            Q = sum(sp.Rational(cf) * sp.prod([A[i]**e for i, e in enumerate(mon)]) for mon, cf in ch)
            print(f"def y{n+1}c{k}_{m} {{K : Type*}} [Field K] (a : Fin 7 → K) : K :=\n      {coef(Q)}\n")
        print(f"def y{n+1}c{k} {{K : Type*}} [Field K] (a : Fin 7 → K) : K :=\n  " + " + ".join(f"y{n+1}c{k}_{m} a" for m in range(len(chunks))) + "\n")
print("/-- The Clebsch quadratic covariants `y₁ = (f,i)₄`, `y₂ = (i,y₁)₂`, `y₃ = (i,y₂)₂`, `i = (f,f)₄`,\nas coefficient vectors (`c₀ + c₁x + c₂x²`). -/")
print("def yv {K : Type*} [Field K] (a : Fin 7 → K) : Fin 3 → Fin 3 → K :=\n  ![![y1c0 a, y1c1 a, y1c2 a], ![y2c0 a, y2c1 a, y2c2 a], ![y3c0 a, y3c1 a, y3c2 a]]\n")
J = sp.symbols('J2 J4 J6 J10')
P = {}
for line in open('scratch/t28-igusa/m3_polys.txt'):
    k, v = line.strip().split(' = '); P[k] = sp.sympify(v, locals={'J2': J[0], 'J4': J[1], 'J6': J[2], 'J10': J[3]})
def jexpr(Q):
    terms = []
    for mon, cf in sp.Poly(Q, *J).terms():
        m = " * ".join(f"{['j2','j4','j6','j10'][i]}" + (f" ^ {e}" if e > 1 else "") for i, e in enumerate(mon) if e > 0)
        cf = sp.Rational(cf)
        c = f"({cf.p} : K)" if cf.q == 1 else f"(({cf.p} : K) / {cf.q})"
        terms.append(f"{c} * {m}" if m else c)
    return " + ".join(terms)
for k, Q in P.items():
    print(f"def m3{k} {{K : Type*}} [Field K] (j2 j4 j6 j10 : K) : K :=\n  {jexpr(Q)}\n")
idx = lambda *t: "".join(str(s+1) for s in sorted(t))
print("/-- The Gram matrix of `yv` as a function of the Igusa invariants (identities M3). -/")
print("def gramJ {K : Type*} [Field K] (j2 j4 j6 j10 : K) : Fin 3 → Fin 3 → K :=\n  ![" + ",\n    ".join(
    "![" + ", ".join(f"m3G{idx(i, j)} j2 j4 j6 j10" for j in range(3)) + "]" for i in range(3)) + "]\n")
print("/-- The coefficients `p6 f (yᵢ yⱼ yₖ)` as functions of the Igusa invariants (identities M3). -/")
print("def cubJ {K : Type*} [Field K] (j2 j4 j6 j10 : K) : Fin 3 → Fin 3 → Fin 3 → K :=\n  ![" + ",\n    ".join(
    "![" + ", ".join("![" + ", ".join(f"m3a{idx(i, j, k)} j2 j4 j6 j10" for k in range(3)) + "]" for j in range(3)) + "]" for i in range(3)) + "]\n")

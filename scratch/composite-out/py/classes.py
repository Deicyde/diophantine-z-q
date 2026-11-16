# Unit classes of O/3O for O = Z<1, i, (1+j)/2, (i+k)/2> in B = (2,-3|Q), coordinates of LeafQM.ofInt,
# multiplication ShimuraGlue.mulCoordR (copied formula), reduced norm ShimuraGlue.N4.
import itertools
P = 3
def mul(n, m):
    return tuple(x % P for x in (
        m[0]*n[0] + 2*m[1]*n[1] + 2*m[1]*n[3] - m[2]*n[2] + 2*m[3]*n[3],
        m[0]*n[1] + m[1]*n[0] + m[1]*n[2] - m[2]*n[3] + m[3]*n[2],
        m[0]*n[2] - 2*m[1]*n[3] + m[2]*n[0] + m[2]*n[2] + 2*m[3]*n[1],
        m[0]*n[3] - m[1]*n[2] + m[2]*n[1] + m[2]*n[3] + m[3]*n[0]))
def N4(n):
    return (n[0]**2 + n[0]*n[2] + n[2]**2 - 2*(n[1]**2 + n[1]*n[3] + n[3]**2)) % P
E = (1, 0, 0, 0)
Q = [a for a in itertools.product(range(3), repeat=4) if N4(a) != 0]
assert len(Q) == 72
# associativity check
for a, b, c in itertools.product(Q, repeat=3):
    assert mul(mul(a, b), c) == mul(a, mul(b, c))
def conjC(m):  # dcy3-used's conjC: star(ofInt m) = ofInt (conjC m)
    return ((m[0] + m[2]) % P, -m[1] % P, -m[2] % P, -m[3] % P)
def inv3(a):
    s = N4(a)
    return tuple((s * x) % P for x in conjC(a))
for a in Q:
    assert mul(a, inv3(a)) == E and mul(inv3(a), a) == E, a
def pw(a, k):
    r = E
    for _ in range(k):
        r = mul(r, a)
    return r
cbar = (1, 1, 2, 0)      # c = ofInt ![1,1,-1,0]
wbar = (1, 0, 2, 0)      # omega0^{-1} = ofInt ![1,0,-1,0]
assert cbar in Q and wbar in Q
print("order c:", next(k for k in range(1, 100) if pw(cbar, k) == E))
print("order w:", next(k for k in range(1, 100) if pw(wbar, k) == E))
N8 = sorted({pw(mul(mul(a, wbar), inv3(a)), 2) for a in Q})
print("N8:", N8, len(N8))
for n in N8:
    assert n != E and pw(n, 3) == E
# also omega0 itself (if the convention gives omega0 instead of its inverse)
N8b = sorted({pw(mul(mul(a, inv3(wbar)), inv3(a)), 2) for a in Q})
print("N8 (omega):", N8b == N8)
ci = pw(cbar, 7)
table = {}
for n in N8:
    n2 = mul(mul(cbar, n), ci)
    for x in Q:
        sol = None
        for e1, e2, k in itertools.product(range(3), range(3), range(8)):
            if mul(mul(pw(n, e1), pw(n2, e2)), pw(cbar, k)) == x:
                sol = (e1, e2, k); break
        assert sol is not None, (n, x)
        table[(n, x)] = sol
print("table ok", len(table))

# Lean table tab2 : Fin 4 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ (index j of N8, then a b c d; value ![e1,e2,k])
def lean_vec(v):
    return "![" + ", ".join(str(x) for x in v) + "]"
rows = []
for j, n in enumerate(N8):
    A = []
    for a in range(3):
        B = []
        for b in range(3):
            C = []
            for c in range(3):
                D = []
                for d in range(3):
                    x = (a, b, c, d)
                    D.append(lean_vec(table[(n, x)]) if x in Q else "![0, 0, 0]")
                C.append("![" + ", ".join(D) + "]")
            B.append("![" + ", ".join(C) + "]")
        A.append("![" + ", ".join(B) + "]")
    rows.append("![" + ",\n    ".join(A) + "]")
with open("tab2.lean", "w") as f:
    f.write("def tab2 : Fin 4 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℕ :=\n  ![" + ",\n  ".join(rows) + "]\n")
    f.write("def nList : Fin 4 → Fin 4 → ZMod 3 := ![" + ", ".join(lean_vec(n) for n in N8) + "]\n")
print("written")

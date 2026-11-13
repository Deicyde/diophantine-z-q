"""rv-blueprints: numerical check of bp-qmmoduli §2.2's sign claim. B = (2,-3) embedded in M2(R)
by i -> diag(sqrt2, -sqrt2), j -> [[0,1],[-3,0]]; mu = 2j + ij; E0(x,y) = trd(mu^-1 x ybar).
Complex structures commuting with the left O-action are right multiplications by J in M2(R),
J^2 = -1, J = [[a,b],[c,-a]], a^2 + bc = -1; the two sheets are c > 0 and c < 0.
Claim: x -> E0(xJ, x) is definite on B_R = M2(R), with opposite signs on the two sheets."""
import random, math
import mpmath as mp
random.seed(1)
def mm(x, y): return [[sum(x[i][k]*y[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
def add(x, y, c=1.0): return [[x[i][j] + c*y[i][j] for j in range(2)] for i in range(2)]
def sc(c, x): return [[c*x[i][j] for j in range(2)] for i in range(2)]
def tr(x): return x[0][0] + x[1][1]
def close(x, y): return all(abs(x[i][j]-y[i][j]) < 1e-9 for i in range(2) for j in range(2))
E = [[1.0, 0.0], [0.0, 1.0]]
s2 = math.sqrt(2.0)
I = [[s2, 0.0], [0.0, -s2]]; Jq = [[0.0, 1.0], [-3.0, 0.0]]
mu = add(sc(2, Jq), mm(I, Jq))
assert close(mm(I, I), sc(2, E)) and close(mm(Jq, Jq), sc(-3, E)) and close(mm(I, Jq), sc(-1, mm(Jq, I)))
assert close(mm(mu, mu), sc(-6, E))
muinv = sc(-1/6, mu)
bar = lambda x: add(sc(tr(x), E), x, -1)
E0 = lambda x, y: tr(mm(mm(muinv, x), bar(y)))
basis = [E, I, Jq, mm(I, Jq)]
def eig(J):
    G = mp.matrix(4, 4)
    for p, u in enumerate(basis):
        for q, v in enumerate(basis):
            G[p, q] = 0.5 * (E0(mm(u, J), v) + E0(mm(v, J), u))
    ev = mp.eig(G)[0]
    return [float(mp.re(e)) for e in ev]
res = {1: [], -1: []}
for _ in range(30):
    a = random.gauss(0, 1); b = random.gauss(0, 1)
    sign = random.choice([1, -1])
    b = -sign * abs(b) - 0.1 * sign
    c = (-1 - a * a) / b
    J = [[a, b], [c, -a]]
    assert close(mm(J, J), sc(-1, E))
    ev = eig(J)
    res[1 if c > 0 else -1].append((min(ev), max(ev)))
for k, v in res.items():
    mins = [m for m, _ in v]; maxs = [M for _, M in v]
    print(f"sheet sign(c)={k:+d}: {len(v)} samples, eigenvalue range [{min(mins):.4g}, {max(maxs):.4g}]",
          "definite" if (min(mins) > 0 or max(maxs) < 0) else "INDEFINITE")

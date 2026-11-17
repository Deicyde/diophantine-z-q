#!/usr/bin/env python3
"""Exact review controls for a common-strict, rank-one determinant comparison.

No dependencies. This checks finite examples of the proved matrix identity;
it does not instantiate arithmetic Selmer complexes or prove their adjunctions.
Uses explicit exceptions, so checks remain active under python -O.
"""
from fractions import Fraction as Q
from random import Random
import json


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def eye(n):
    return [[Q(int(i == j)) for j in range(n)] for i in range(n)]


def mm(a, b):
    return [[sum((x*y for x, y in zip(row, col)), Q(0))
             for col in zip(*b)] for row in a]


def tr(a):
    return [list(row) for row in zip(*a)]


def determinant(a):
    n = len(a)
    if n == 0:
        return Q(1)
    a = [list(map(Q, row)) for row in a]
    out = Q(1)
    for j in range(n):
        row = next((i for i in range(j, n) if a[i][j]), None)
        if row is None:
            return Q(0)
        if row != j:
            a[row], a[j] = a[j], a[row]
            out = -out
        pivot = a[j][j]
        out *= pivot
        for i in range(j + 1, n):
            q = a[i][j]/pivot
            for k in range(j + 1, n):
                a[i][k] -= q*a[j][k]
    return out


def inverse(a):
    n = len(a)
    a = [list(map(Q, row)) + tail for row, tail in zip(a, eye(n))]
    for j in range(n):
        row = next((i for i in range(j, n) if a[i][j]), None)
        need(row is not None, 'singular inverse input')
        a[row], a[j] = a[j], a[row]
        p = a[j][j]
        a[j] = [x/p for x in a[j]]
        for i in range(n):
            if i != j:
                q = a[i][j]
                a[i] = [x-q*y for x, y in zip(a[i], a[j])]
    return [row[n:] for row in a]


def adjugate(a):
    n = len(a)
    return [[(-1)**(i+j)*determinant([
        [a[r][c] for c in range(n) if c != i]
        for r in range(n) if r != j])
        for j in range(n)] for i in range(n)]


def coordinate(d, z, lam):
    n = len(d)
    need(mm(d, z) == [[0] for _ in range(n)], 'class not closed')
    need(mm(lam, d) == [[0]*n], 'functional not closed')
    adj, tensor = adjugate(d), mm(z, lam)
    nonzero = [(i, j) for i in range(n) for j in range(n) if adj[i][j]]
    need(bool(nonzero), 'rank below n-1')
    i, j = nonzero[0]
    u = tensor[i][j]/adj[i][j]
    need(all(tensor[i][j] == u*adj[i][j]
             for i in range(n) for j in range(n)), 'adjugate tensor mismatch')
    return u


def unimodular(n, rng):
    a = eye(n)
    for _ in range(8):
        i, j = rng.sample(range(n), 2)
        c = rng.randrange(-3, 4)
        a[i] = [x+c*y for x, y in zip(a[i], a[j])]
        if rng.randrange(3) == 0:
            a[i], a[j] = a[j], a[i]
    need(abs(determinant(a)) == 1, 'not unimodular')
    return a


def source_change(m, v, rng):
    a = eye(m+2)
    for i in range(m):
        for j in range(2):
            a[i][m+j] = Q(rng.randrange(-3, 4))
    for i in range(2):
        for j in range(2):
            a[m+i][m+j] = v[i][j]
    return a


def v2(x):
    x = Q(x)
    need(x != 0, 'valuation of zero')
    a, b = abs(x.numerator), x.denominator
    out = 0
    while a % 2 == 0:
        a //= 2; out += 1
    while b % 2 == 0:
        b //= 2; out -= 1
    return out


def main():
    rng = Random(40120261108)
    total, matched, mismatched, divisible = 0, 0, 0, 0
    dimensions = set()
    for m in range(4):
        n = m + 2
        for i in range(75):
            af, bs = Q(2**rng.randrange(8)), Q(2**rng.randrange(8))
            scale = Q(2**rng.randrange(9))
            dF0 = [[Q(0)]*n for _ in range(n)]
            dS0 = [[Q(0)]*n for _ in range(n)]
            for j in range(m):
                dF0[j][j] = dS0[j][j] = Q(2**rng.randrange(8))
            dF0[m][m+1], dS0[m+1][m+1] = af, bs
            p = unimodular(n, rng)
            vf, vs = unimodular(2, rng), unimodular(2, rng)
            hf, hs = source_change(m, vf, rng), source_change(m, vs, rng)
            dF, dS = mm(mm(p, dF0), hf), mm(mm(p, dS0), hs)
            need([r[:m] for r in dF] == [r[:m] for r in dS], 'strict factor changed')
            J0 = [[Q(1), Q(0)], [Q(0), Q(-1)]]
            J = mm(mm(inverse(vs), J0), vf)
            z0 = [[scale if j == m else Q(0)] for j in range(n)]
            zF, zS = mm(inverse(hf), z0), mm(inverse(hs), z0)
            v, x = zF[m:], mm(inverse(vf), [[Q(0)], [1/scale]])
            need(zS[m:] == mm(J, v), 'derivative local vector mismatch')
            eta = determinant([[v[k][0], x[k][0]] for k in range(2)])
            need(abs(eta) == 1, 'nonunit complement volume')
            UF, US = [r[m:] for r in dF], [r[m:] for r in dS]
            a, b = mm(UF, x), mm(US, mm(J, x))
            W = [dF[j][:m] + [a[j][0], b[j][0]] for j in range(n)]
            theta = determinant(W)
            need(theta != 0, 'generic boundary images not independent')
            # Alternate boundary-normalized cases with arbitrary primitive choices.
            rf, rs = (af, -bs) if i % 2 == 0 else (Q(1), Q(1))
            lf0, ls0 = [[Q(0)]*n], [[Q(0)]*n]
            lf0[0][-1], ls0[0][-2] = scale*rf, scale*rs
            lf, ls = mm(lf0, inverse(p)), mm(ls0, inverse(p))
            uf, us = coordinate(dF, zF, lf), coordinate(dS, zS, ls)
            qf, qs = mm(lf, b)[0][0], mm(ls, a)[0][0]
            dj = determinant(J)
            need(uf == -eta*qf/theta, 'finite coordinate formula')
            need(us == dj*eta*qs/theta, 'singular coordinate formula')
            ratio = dj*uf/us
            need(ratio == -qf/qs, 'boundary scalar comparison')
            need(v2(ratio) == v2(qf)-v2(qs), 'valuation defect formula')
            if i % 2 == 0:
                need(qf == qs and ratio == -1, 'normalized unit comparison')
                matched += 1
            elif af != bs:
                need(v2(ratio) != 0, 'unequal-scale negative control escaped')
                mismatched += 1
            if scale > 1: divisible += 1
            dimensions.add(n); total += 1
    # Explicit primitive counterexample: common strict R^2[-2], no strict torsion.
    f, s = [[Q(0), Q(2)], [Q(0), Q(0)]], [[Q(0), Q(0)], [Q(0), Q(4)]]
    z = [[Q(1)], [Q(0)]]
    uf = coordinate(f, z, [[Q(0), Q(1)]])
    us = coordinate(s, z, [[Q(1), Q(0)]])
    need(uf == Q(-1, 2) and us == Q(1, 4), 'primitive negative example')
    need(-uf/us == 2, 'primitive mismatch factor')
    return {'status':'PASS', 'scope':'finite controls, not arithmetic Selmer verification',
            'randomized_common_strict_cases':total, 'matrix_sizes':sorted(dimensions),
            'equal_cross_pairing_cases':matched, 'unequal_scale_negative_controls':mismatched,
            'divisible_local_vector_cases':divisible,
            'primitive_counterexample':{'u_F':str(uf),'u_S':str(us),'Phi_ratio':'2'},
            'formula':'Phi(tau_F)/tau_S = -q_F/q_S in the declared adjugate convention'}


if __name__ == '__main__':
    print(json.dumps(main(), indent=2, sort_keys=True))

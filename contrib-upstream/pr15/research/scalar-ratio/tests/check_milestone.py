#!/usr/bin/env python3
"""Exact rational controls for the common-strict theorem and cup adapter.

Reuses exact_matrix.py from the previous packet as arithmetic utilities.
These are deterministic finite checks, not a Lean build or an independent
review. Explicit exceptions keep all checks active under Python -O.
"""
from fractions import Fraction as Q
from math import lcm
from random import Random
import json
from exact_matrix import (need, eye, mm, inverse, determinant,
                          coordinate, unimodular, main as previous_controls)


def column(a, j):
    return [[row[j]] for row in a]


def pair(v, w):
    return [[v[i][0], w[i][0]] for i in range(len(v))]


def area(v, w):
    return determinant(pair(v, w))


def scaled(c, a):
    return [[c * x for x in row] for row in a]


def plus(a, b):
    return [[x+y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def vp(x, p):
    x = Q(x)
    need(x != 0, 'valuation undefined at zero in this helper')
    a, b, v = abs(x.numerator), x.denominator, 0
    while a % p == 0:
        a //= p
        v += 1
    while b % p == 0:
        b //= p
        v -= 1
    return v


def unit_related(a, b, p):
    """Equality up to a unit of Z_(p), including the (0,0) case."""
    if a == 0 or b == 0:
        return a == b == 0
    return vp(a/b, p) == 0


def raw_frame(n, z, x):
    m = n - 2
    return [[Q(int(i == j)) for j in range(m)] + [z[i][0],
             Q(0) if i < m else x[i-m][0]] for i in range(n)]


def value(lam, vec):
    return mm(lam, vec)[0][0]


def run():
    rng = Random(20261108181242)
    totals = dict(adapter_cases=0, full_basis_adjunction_checks=0,
                  unit_criterion_checks=0, complement_change_checks=0,
                  equal_normalization_cases=0, zero_functional_cases=0,
                  nonunit_common_clearings=0, wrong_functional_rejections=0,
                  non_eigenvector_local_cases=0)
    sizes = set()
    for m in range(5):
        n = m + 2
        for trial in range(36):
            U = unimodular(n, rng)
            V, W = unimodular(2, rng), unimodular(2, rng)
            J = mm(mm(W, [[Q(1), Q(0)], [Q(0), Q(-1)]]), inverse(W))
            need(mm(J, J) == eye(2) and determinant(J) == -1, 'J is not an involution')
            scale = Q(2 ** rng.randrange(6))
            v = scaled(scale, column(V, 0))
            x = scaled(1/scale, column(V, 1))
            Jv, Jx = mm(J, v), mm(J, x)
            if Jv != v and Jv != scaled(-1, v):
                totals['non_eigenvector_local_cases'] += 1
            ds = [Q(2 ** rng.randrange(5) * 3 ** rng.randrange(3)) for _ in range(m)]
            D0 = [[U[i][j] * ds[j] for j in range(m)] for i in range(n)]
            hf0 = [Q(rng.randrange(-3, 4)) for _ in range(m)]
            hs0 = [Q(rng.randrange(-3, 4)) for _ in range(m)]
            vf = [[-sum((D0[i][j] * hf0[j] for j in range(m)), Q(0))] for i in range(n)]
            vs = [[-sum((D0[i][j] * hs0[j] for j in range(m)), Q(0))] for i in range(n)]
            tf, ts = Q(2 ** rng.randrange(5)), Q(3 ** rng.randrange(4))
            AF = mm(pair(vf, scaled(tf, column(U, m))), inverse(V))
            AS = mm(pair(vs, scaled(ts, column(U, m+1))), inverse(mm(J, V)))
            DF = [D0[i] + AF[i] for i in range(n)]
            DS = [D0[i] + AS[i] for i in range(n)]
            zF = [[scale*h] for h in hf0] + v
            zS = [[scale*h] for h in hs0] + Jv
            a, b = mm(AF, x), mm(AS, Jx)
            T = [D0[i]+[a[i][0], b[i][0]] for i in range(n)]
            TF = [D0[i]+[b[i][0], a[i][0]] for i in range(n)]
            eta, theta, delta = area(v, x), determinant(T), determinant(J)
            need(eta != 0 and theta != 0, 'invalid generic frame')
            BF, BS = raw_frame(n, zF, x), raw_frame(n, zS, Jx)
            N = eye(n)
            N[m][m] = Q(0)
            need(mm(DF, BF) == mm(TF, N), 'finite raw frame identity')
            need(mm(DS, BS) == mm(T, N), 'singular raw frame identity')
            need(determinant(BF) == eta and determinant(BS) == delta*eta,
                 'source frame determinant')
            need(determinant(TF) == -theta, 'target swap sign')
            c = Q(2**rng.randrange(5), 3**rng.randrange(3))
            cF, cS = [(c, c), (-3*c, c), (2*c, c), (0, c), (0, 0), (c, 0)][trial % 6]
            epsilon = Q(5)
            rF, rS = [[Q(0)]*n], [[Q(0)]*n]
            rF[0][m+1], rS[0][m] = cF*epsilon*eta, cS*epsilon*eta
            lamF, lamS = mm(rF, inverse(T)), mm(rS, inverse(T))
            clear = lcm(*(q.denominator for row in lamF+lamS for q in row))
            lamF, lamS = scaled(clear, lamF), scaled(clear, lamS)
            cF, cS = clear*cF, clear*cS
            need(all(q.denominator == 1 for row in lamF+lamS for q in row),
                 'common clearing factor did not clear both rows')
            if clear > 1:
                totals['nonunit_common_clearings'] += 1
            # Test each entire local linear map, on a basis, not just the chosen complement.
            for j in range(2):
                e = column(eye(2), j)
                need(value(lamF, mm(AS, e)) == cF*epsilon*area(v, mm(J, e)),
                     'finite full boundary-cup identity')
                need(value(lamS, mm(AF, e)) == -cS*epsilon*area(e, mm(J, Jv)),
                     'singular full boundary-cup identity')
                totals['full_basis_adjunction_checks'] += 2
            uf, us = coordinate(DF, zF, lamF), coordinate(DS, zS, lamS)
            qf, qs = value(lamF, b), value(lamS, a)
            need(qf == cF*epsilon*eta and qs == cS*epsilon*eta, 'cross evaluations')
            need(uf == -eta*qf/theta and us == delta*eta*qs/theta, 'coordinate formula')
            need(qs*(delta*uf) + qf*us == 0, 'division-free scalar identity')
            if qs:
                need(delta*uf/us == -qf/qs == -cF/cS, 'normalization defect')
            for p in (2, 3, 5):
                need(unit_related(uf, us, p) == unit_related(qf, qs, p), 'integral unit iff')
                totals['unit_criterion_checks'] += 1
            if cF == cS:
                need(delta*uf == -us and uf == us, 'common normalization exact equality')
                totals['equal_normalization_cases'] += 1
            if not cF or not cS:
                totals['zero_functional_cases'] += 1
            # Complement can be shifted by the class, or rescaled by a NONUNIT.
            alpha, beta = Q(3, 4), Q(rng.randrange(-5, 6))
            xp = plus(scaled(alpha, x), scaled(beta, v))
            ap, bp = mm(AF, xp), mm(AS, mm(J, xp))
            Tp = [D0[i]+[ap[i][0], bp[i][0]] for i in range(n)]
            etap, thetap = area(v, xp), determinant(Tp)
            qfp, qsp = value(lamF, bp), value(lamS, ap)
            need(etap == alpha*eta and thetap == alpha*alpha*theta, 'complement determinants')
            need(qfp == alpha*qf and qsp == alpha*qs, 'complement scalar covariance')
            need(uf == -etap*qfp/thetap and us == delta*etap*qsp/thetap,
                 'complement independence')
            totals['complement_change_checks'] += 1
            if cF and cS:
                wrong = scaled(2, lamS)
                uwrong = coordinate(DS, zS, wrong)
                need(uwrong == 2*us, 'wrong functional does not move coordinate')
                need(value(wrong, a) != cS*epsilon*eta,
                     'wrong functional escaped unchanged adjunction contract')
                totals['wrong_functional_rejections'] += 1
            totals['adapter_cases'] += 1
            sizes.add(n)
    need(not unit_related(Q(2), Q(1), 2), 'field-unit trap')
    need(unit_related(Q(0), Q(0), 2) and not unit_related(Q(0), Q(1), 2), 'zero relation cases')
    return {
      'status':'PASS', 'scope':'finite exact algebra; not Lean compilation or arithmetic realization',
      'shared_arithmetic_implementation':'exact_matrix.py reused from preceding review; not an independent checker',
      'matrix_sizes':sorted(sizes), **totals,
      'field_unit_trap_rejected':True,
      'previous_regression':previous_controls(),
      'lean_compilation':'NOT_RUN', 'arithmetic_boundary_cup_identity':'UNESTABLISHED'
    }


if __name__ == '__main__':
    print(json.dumps(run(), sort_keys=True, indent=2))

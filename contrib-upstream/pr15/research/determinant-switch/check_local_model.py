#!/usr/bin/env python3
"""Exact negative controls for the derivative-switch abstract interface.

Python stdlib only. This tests concrete algebra; it is not a Selmer-complex
proof or a substitute for compiling the accompanying Lean module.
"""
from fractions import Fraction
from math import gcd
from random import Random


def mul(a, v):
    x, y = v
    return (a[0][0] * x + a[0][1] * y,
            a[1][0] * x + a[1][1] * y)


def det(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def area(v, w):
    return v[0] * w[1] - v[1] * w[0]


def assert_generic_countermodel(a=3):
    # F, S, H are 2-dimensional over Q. J=diag(1,-1).
    j = ((1, 0), (0, -1))
    d_f = ((0, a), (0, 0))
    d_s = ((0, 0), (0, a))
    assert det(j) == -1
    assert mul(d_f, (1, 0)) == mul(d_s, (1, 0)) == (0, 0)
    # Both generic kernels = Q*(1,0); combined boundary rank 2.
    assert det(((a, 0), (0, a))) == a * a
    # An identity-on-strict/J-on-quotient square is impossible.
    assert mul(d_f, (0, 1)) != mul(d_s, mul(j, (0, 1)))
    # Nevertheless H^1(old) and H^1(new) each have dimension 1.
    return True


def random_unimodular(rng):
    # Compose integral elementary row operations on the identity.
    a = [[1, 0], [0, 1]]
    for _ in range(20):
        i, j = rng.choice(((0, 1), (1, 0)))
        q = rng.randrange(-5, 6)
        a[i][0] += q * a[j][0]
        a[i][1] += q * a[j][1]
        if rng.randrange(5) == 0:
            a[i], a[j] = a[j], a[i]
    if det(a) == 1:
        a[0][0] *= -1
        a[0][1] *= -1
    assert det(a) == -1
    return a


def local_volume_trials():
    rng = Random(20261108)
    count = 0
    for exponent in range(19):
        scale = 2 ** exponent
        # v0=(2,3) is primitive; x0=(-1,-1) gives area(v0,x0)=1.
        v = (2 * scale, 3 * scale)
        x = (Fraction(-1, scale), Fraction(-1, scale))
        assert area(v, x) == 1
        for _ in range(200):
            j = random_unimodular(rng)
            jv, jx = mul(j, v), mul(j, x)
            assert area(jv, jx) == -1
            assert gcd(abs(jv[0]), abs(jv[1])) == scale
            count += 1
    return count


def tensor_normalization_control():
    # Common strict complex [R -> R^3], differential (a,0,0)^t.
    # Both plane quotients are R^2[-1]; strict torsion R/(a) is retained.
    def product(d, z):
        return tuple(sum(x * y for x, y in zip(row, z)) for row in d)

    def coordinate(d, z, functional):
        # Check every cofactor and every zero entry in z*functional=u*adj(d).
        adj = [[(-1) ** (i + j) * det([
            [d[r][c] for c in range(3) if c != i]
            for r in range(3) if r != j]) for j in range(3)] for i in range(3)]
        values = {Fraction(z[i] * functional[j], adj[i][j])
                  for i in range(3) for j in range(3) if adj[i][j]}
        assert len(values) == 1
        u = values.pop()
        assert all(z[i] * functional[j] == u * adj[i][j]
                   for i in range(3) for j in range(3))
        return u

    for m in range(1, 12):
        a = 2 ** m
        d_f = ((a, 0, 0), (0, 0, 0), (0, 0, 1))
        d_s = ((a, 0, 0), (0, 0, 1), (0, 0, 0))
        j = ((1, 0), (0, -1))
        assert tuple(row[0] for row in d_f) == tuple(row[0] for row in d_s) == (a, 0, 0)
        for k in range(0, 12):
            scale = 2 ** k
            z = (0, scale, 0)
            lambda_f, lambda_s = (0, scale, 0), (0, 0, scale)
            assert product(d_f, z) == product(d_s, z) == (0, 0, 0)
            assert all(sum(lambda_f[i] * d_f[i][c] for i in range(3)) == 0
                       and sum(lambda_s[i] * d_s[i][c] for i in range(3)) == 0
                       for c in range(3))
            assert mul(j, z[1:]) == z[1:]
            u_f = coordinate(d_f, z, lambda_f)
            u_s = coordinate(d_s, z, lambda_s)
            assert u_f == Fraction(scale * scale, a)
            assert u_s / u_f == -1
            # Local J + the exact triangles do not force the normalization
            # of the *actual* duality-defined functional.
            wrong_s = coordinate(d_s, z, tuple(2 * x for x in lambda_s))
            assert wrong_s / u_f == -2  # not a 2-adic unit
    return 132


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run without Python -O: validation assertions must be enabled')
    assert assert_generic_countermodel()
    n = local_volume_trials()
    m = tensor_normalization_control()
    print(f'PASS: generic equal-rank no-go; {n} exact local-volume trials; '
          f'{m} normalization controls')

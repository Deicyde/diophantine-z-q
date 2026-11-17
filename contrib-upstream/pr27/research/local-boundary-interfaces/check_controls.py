#!/usr/bin/env python3
"""Bounded exact diagnostics for the four local-interface source modules.

Adapted algorithms and source blobs are listed in CONTROLS_PROVENANCE.json.
These are finite models, not Lean checking or arithmetic Selmer instances.
"""
import sys

if not __debug__:
    raise SystemExit("Refusing optimized Python: these controls require assertions")

from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import hashlib
import json
import platform
import random

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cochain_controls():
    """Alexander--Whitney cups on the same oriented torus as the source test."""
    n = 3
    vertices = list(range(n * n))
    vertex = lambda x, y: x % n + n * (y % n)
    parity = lambda xs: (-1) ** sum(xs[i] > xs[j] for i in range(len(xs))
                                   for j in range(i + 1, len(xs)))
    triangles = {}
    for x in range(n):
        for y in range(n):
            a, b, c, d = vertex(x, y), vertex(x + 1, y), vertex(x + 1, y + 1), vertex(x, y + 1)
            for t in ((a, b, c), (a, c, d)):
                triangles[tuple(sorted(t))] = parity(t)
    faces = sorted(triangles)
    edges = sorted({e for t in faces for e in combinations(t, 2)})
    d0 = lambda q: {e: q[e[1]] - q[e[0]] for e in edges}
    d1 = lambda a: {t: a[t[1], t[2]] - a[t[0], t[2]] + a[t[0], t[1]] for t in faces}
    cup10 = lambda a, q: {e: a[e] * q[e[1]] for e in edges}
    cup01 = lambda q, a: {e: q[e[0]] * a[e] for e in edges}
    cup11 = lambda a, b: {t: a[t[0], t[1]] * b[t[1], t[2]] for t in faces}
    cup20 = lambda z, q: {t: z[t] * q[t[2]] for t in faces}
    cup02 = lambda q, z: {t: q[t[0]] * z[t] for t in faces}
    trace = lambda z: sum(triangles[t] * z[t] for t in faces)
    add = lambda a, b: {i: a[i] + b[i] for i in a}
    sub = lambda a, b: {i: a[i] - b[i] for i in a}
    scale = lambda c, a: {i: c * a[i] for i in a}
    zero = lambda a: all(x == 0 for x in a.values())
    wrap = lambda d: (d + 1) % n - 1
    dx = {e: wrap(e[1] % n - e[0] % n) for e in edges}
    dy = {e: wrap(e[1] // n - e[0] // n) for e in edges}
    assert (len(vertices), len(edges), len(faces)) == (9, 27, 18)
    for v in vertices:
        assert zero(d1(d0({u: int(u == v) for u in vertices})))
    for e in edges:
        assert trace(d1({f: int(f == e) for f in edges})) == 0
    assert zero(d1(dx)) and zero(d1(dy))
    pairing = [[trace(cup11(a, b)) for b in (dx, dy)] for a in (dx, dy)]
    assert pairing == [[0, 9], [-9, 0]]
    rng = random.Random(20261109)
    controls = {}
    corrections = 0
    for trial in range(64):
        p = {v: rng.randrange(-7, 8) for v in vertices}
        q = {v: rng.randrange(-7, 8) for v in vertices}
        raw = {e: rng.randrange(-7, 8) for e in edges}
        l = add(add(scale(rng.randrange(-5, 6), dx), scale(rng.randrange(-5, 6), dy)), d0(p))
        m = add(scale(rng.randrange(-5, 6), dx), scale(rng.randrange(-5, 6), dy))
        local_condition = add(m, d0(q))
        correction = d1(cup10(l, q))
        actual, global_cup = cup11(l, local_condition), cup11(l, m)
        assert actual == sub(global_cup, correction)
        assert trace(actual) == trace(global_cup)
        assert d1(cup10(raw, q)) == sub(cup20(d1(raw), q), cup11(raw, d0(q)))
        assert d1(cup01(q, raw)) == add(cup11(d0(q), raw), cup02(q, d1(raw)))
        assert trace(cup11(d0(q), m)) == trace(cup11(m, d0(q))) == 0
        if not zero(correction):
            corrections += 1
            if "wrong_correction_sign" not in controls:
                t = next(t for t in faces if correction[t])
                controls["wrong_correction_sign"] = {
                    "trial": trial, "triangle": t, "actual": actual[t],
                    "wrong_plus": global_cup[t] + correction[t]}
                assert actual[t] != global_cup[t] + correction[t]
            if "non_chain_trace" not in controls:
                t = next(t for t in faces if actual[t] != global_cup[t])
                controls["non_chain_trace"] = {
                    "trial": trial, "trace_replaced_by_simplex_evaluation": t,
                    "actual": actual[t], "global_cup": global_cup[t],
                    "nonzero_evaluation_on_boundary": correction[t]}
        omitted = sub(cup11(raw, local_condition), sub(cup11(raw, m), d1(cup10(raw, q))))
        if not zero(omitted) and "nonclosed_local_direction" not in controls:
            t = next(t for t in faces if omitted[t])
            assert not zero(d1(raw))
            controls["nonclosed_local_direction"] = {
                "trial": trial, "triangle": t, "unaccounted_term": omitted[t],
                "direction_is_not_closed": True}
    assert corrections and len(controls) == 3
    return {"trials": 64, "seed": 20261109, "nonzero_corrections": corrections,
            "torus": {"vertices": 9, "edges": 27, "triangles": 18,
                      "closed_direction_trace_pairing": pairing},
            "negative_controls": controls,
            "scope": "Exact finite cochains; neither this torus nor its trace is an arithmetic Galois object"}


def cone_and_inverse_controls():
    rng = random.Random(20261109)
    cone_cases, bad_sign_cases, witness = 0, 0, None
    for modulus in (2, 4, 8, 16, 32):
        for _ in range(32):
            dG, dU, dL, loc, incp, a1, h0, h1 = [rng.randrange(modulus) for _ in range(8)]
            a0 = rng.choice([x for x in range(modulus) if x % 2])
            dV = a1 * dU * pow(a0, -1, modulus) % modulus
            inc = (incp * a0 + dL * h0 + h1 * dU) % modulus
            for _ in range(4):
                g, u, q = [rng.randrange(modulus) for _ in range(3)]
                left = (dG * g % modulus, dV * a0 * u % modulus,
                        (loc * g - incp * a0 * u - dL * (q + h0 * u)) % modulus)
                right = (dG * g % modulus, a1 * dU * u % modulus,
                         (loc * g - inc * u - dL * q + h1 * dU * u) % modulus)
                assert left == right
                wrong = (loc * g - incp * a0 * u - dL * (q - h0 * u)) % modulus
                if wrong != right[2]:
                    bad_sign_cases += 1
                    if witness is None:
                        witness = {"modulus": modulus, "dU": dU, "dL": dL,
                                   "loc": loc, "incp": incp, "inc": inc,
                                   "a0": a0, "a1": a1, "h0": h0, "h1": h1,
                                   "g": g, "u": u, "q": q,
                                   "correct_third": right[2], "wrong_third": wrong}
                cone_cases += 1
    assert bad_sign_cases and witness is not None
    homotopy_cases = 0
    for modulus in (2, 4, 8, 16):
        for differential in range(modulus):
            boundaries = {differential * x % modulus for x in range(modulus)}
            for h in range(modulus):
                k = (1 + differential * h) % modulus
                for y in range(modulus):
                    difference = (k * y - y) % modulus
                    assert difference == differential * h * y % modulus
                    assert difference in boundaries
                    for local in (0, 1, 3):
                        assert local * difference % modulus in {local * b % modulus for b in boundaries}
                    homotopy_cases += 1
    # A genuine inverse pair is insufficient without the common-projection premise.
    modulus, j, k, y = 8, 3, 3, 1
    assert j * k % modulus == 1
    assert (k * y - y) % modulus not in {0}  # zero-differential complex
    arbitrary_inverse = {"modulus": modulus, "differential": 0, "comparison": j,
                         "genuine_inverse": k, "class": y, "localized_inverse_class": k * y % modulus,
                         "missing_premise": "common global/local projection; abstract equivalence alone does not preserve this coordinate"}
    # Actual precision-two coefficient ring: (Z/4)[t]/(t^2).
    candidates = [(a, b) for a in range(4) for b in range(4)]
    products = [(0, a) for a, _ in candidates]  # t*(a+b*t)
    assert all(product != (1, 0) for product in products)
    assert products[candidates.index((0, 1))] == (0, 0)
    return {"degreewise_cone_cases": cone_cases, "wrong_cone_sign_cases": bad_sign_cases,
            "top_cohomology_homotopy_cases": homotopy_cases,
            "negative_controls": {"wrong_cone_sign": witness,
                                  "inverse_without_projection_compatibility": arbitrary_inverse,
                                  "nilpotent_t_inverse": {"ring": "(Z/4)[t]/(t^2)",
                                                          "all_candidates_rejected": len(candidates)}},
            "scope": "Cone checks are degreewise identities; homotopy checks use two-term finite complexes, not Selmer models"}


def coefficient_controls():
    modulus, order = 32, 8
    rho = lambda g: pow(3, g % order, modulus)
    gamma = lambda g: -g % order
    p = lambda g: (rho(g) - 1) % modulus
    pulled = lambda g: p(gamma(g))
    assert pow(3, order, modulus) == 1 and rho(1) != rho(gamma(1))
    mismatch = None
    for g in range(order):
        for h in range(order):
            gh = (g + h) % order
            assert p(gh) == (p(g) + rho(g) * p(h)) % modulus
            assert pulled(gh) == (pulled(g) + rho(gamma(g)) * pulled(h)) % modulus
            wrong = (pulled(g) + rho(g) * pulled(h)) % modulus
            if mismatch is None and wrong != pulled(gh):
                mismatch = {"g": g, "h": h, "actual_pulled_value": pulled(gh),
                            "wrong_original_action_value": wrong,
                            "original_action": rho(g), "conjugate_action": rho(gamma(g))}
    assert mismatch is not None
    # p is a coboundary, so its class is zero, but evaluation at g=1 is nonzero.
    assert p(1) == 2
    for m in range(modulus):
        assert (rho(0) * m - m) % modulus == 0  # valid trivially acting guard
        for g in range(order):
            coboundary_pulled = (rho(gamma(g)) * m - m) % modulus
            assert coboundary_pulled == (rho(gamma(g)) - 1) * m % modulus
    return {"group": "C8", "coefficient_ring": "Z/32", "action_generator": 3,
            "cocycle": "p(g)=rho(g)-1", "pullback": "gamma(g)=-g",
            "crossed_equations_checked": 2 * order * order,
            "coboundary_pullbacks_checked": modulus * order,
            "negative_controls": {"coefficient_carrier_mismatch": mismatch,
                                  "evaluation_without_trivial_action": {
                                      "element": 1, "coboundary_value": p(1),
                                      "cohomology_class": 0,
                                      "conclusion": "evaluation would not be well-defined on the quotient"}},
            "scope": "Finite representation/cochain model; the actual Mathlib H1 theorem is checked separately by Lean"}


def functional_controls():
    area = lambda x, y: x[0] * y[1] - x[1] * y[0]
    mv = lambda m, v: tuple(sum(a * b for a, b in zip(row, v)) for row in m)
    scale = lambda c, v: tuple(c * x for x in v)
    dot = lambda x, y: sum(a * b for a, b in zip(x, y))
    j = ((Q(0), Q(1)), (Q(1), Q(0)))
    v, x, zero = (Q(1), Q(0)), (Q(0), Q(1)), (Q(0), Q(0))
    transport, trace, epsilon = Q(3), Q(5), Q(2)
    def cup(left, right):
        f, s = left
        fp, sp = right
        return epsilon * (area(f, mv(j, sp)) - area(s, mv(j, fp)))
    partner_f = (scale(transport, v), zero)
    partner_s = (zero, scale(-transport, mv(j, v)))
    qf = trace * cup((zero, mv(j, x)), partner_f)
    qs = trace * cup((x, zero), partner_s)
    assert qf == -qs == -trace * transport * epsilon
    row_f, row_s = (Q(0), qf), (qs, Q(0))
    a, b = v, x
    assert dot(row_f, a) == dot(row_s, b) == 0
    assert dot(row_f, b) == qf and dot(row_s, a) == qs
    scaled_s = scale(2, row_s)
    assert dot(scaled_s, b) == 0
    assert dot(scaled_s, a) != -qf
    def v2(q):
        assert q
        n, d, value = abs(q.numerator), q.denominator, 0
        while n % 2 == 0:
            n //= 2
            value += 1
        while d % 2 == 0:
            d //= 2
            value -= 1
        return value
    assert v2(dot(scaled_s, a)) == v2(qf) + 1
    twice_j = trace * cup((zero, mv(j, x)), (mv(j, partner_f[0]), zero))
    omitted_tame = trace * cup((x, zero), (zero, scale(transport, mv(j, v))))
    assert twice_j == 0 != qf
    assert omitted_tame == -qs != qs
    return {"J": j, "v": v, "x": x, "transport_unit": transport,
            "common_trace": trace, "common_pairing_scalar": epsilon,
            "qF": qf, "qS": qs,
            "negative_controls": {"extra_coefficient_J": {"correct": qf, "wrong": twice_j},
                                  "omitted_tame_sign": {"correct": qs, "wrong": omitted_tame},
                                  "independent_functional_times_two": {
                                      "closedness_preserved": True, "original": qs,
                                      "rescaled": dot(scaled_s, a),
                                      "original_v2": v2(qs), "rescaled_v2": v2(dot(scaled_s, a))}},
            "scope": "Local cup/row diagnostic only; no determinant-coordinate or arithmetic normalization theorem"}


def encode(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, dict):
        return {k: encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def main():
    origin = json.loads((HERE / "ORIGIN.json").read_text())
    modules = {}
    assert len(origin["modules"]) == 4
    for entry in origin["modules"]:
        actual = sha(ROOT / entry["path"])
        assert actual == entry["sha256"], "candidate module bytes differ: " + entry["path"]
        modules[entry["path"]] = actual
    result = {"status": "PASS", "python": platform.python_version(),
              "optimized": not __debug__, "script_sha256": sha(Path(__file__)),
              "input_sha256": {name: sha(HERE / name) for name in
                               ("CHECK_DESIGN.md", "CONTROLS_PROVENANCE.json", "ORIGIN.json", "TARGETS.json")},
              "candidate_modules": modules,
              "cochains": cochain_controls(), "cone_and_inverse": cone_and_inverse_controls(),
              "coefficients": coefficient_controls(), "functionals": functional_controls(),
              "scope": "Finite diagnostic models, separate from native Lean evidence and all actual arithmetic applications"}
    print(json.dumps(encode(result), indent=2))


if __name__ == "__main__":
    main()

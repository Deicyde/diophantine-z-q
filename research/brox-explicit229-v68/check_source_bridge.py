#!/usr/bin/env python3
"""Exact, small independent source-table bridge for PR #158.

Verifies table-level relationships which are not covered by the compact
normalization checker: helper isolation, reciprocal-pair component signs,
and the full field secant components for three pairs.
No producer imports, external network, or SymPy required.
"""
from collections import defaultdict
from hashlib import sha256
from pathlib import Path
from fractions import Fraction
import argparse
import json

ROOT = Path(__file__).resolve().parent
SHA195 = "304f94843c1a4ac94fcd5f1295fee8b532e7f0424e638314d892c556e2fbfdf9"
SHA229 = "f0e6fc3f62525d7b251a10fc5f4cf0e6663c3f6f08beeef3cb28092b2e1555a8"
SHATRANS = "5ac9fdcb6becd504d5e698373f52a5bddc99afe9c93614705b07efd3ff4f4e2f"


def read_pinned(path, digest):
    data = path.read_bytes()
    assert sha256(data).hexdigest() == digest, str(path)
    return json.loads(data)


def poly(row):
    out = defaultdict(Fraction)
    for t in row["terms"]:
        key = (int(t["parameterPower"]), tuple(sorted(t["monomial"])))
        out[key] += Fraction(t["coefficient"])
    return {k: v for k, v in out.items() if v}


def add(d, power, x, y, c):
    key = (power, tuple(sorted((x, y))))
    d[key] += Fraction(c)


def secant_components(f0, f1, g0, g1, s0, s1, h0, h1, k0, k1, fp):
    # Field multiplication of s*(g-C^fp*f), with rho^2=2.
    out = [defaultdict(Fraction), defaultdict(Fraction)]
    for f, power, sign in ((f0, fp, -1), (g0, 0, 1)):
        add(out[0], power, f, s0, sign)
        add(out[1], power, f, s1, sign)
    for f, power, sign in ((f1, fp, -1), (g1, 0, 1)):
        add(out[0], power, f, s1, 2*sign)
        add(out[1], power, f, s0, sign)
    for k in (h0, k0):
        add(out[0], 1, 77, k, 1)
    for k in (h1, k1):
        add(out[1], 1, 77, k, 1)
    return [{k: v for k, v in d.items() if v} for d in out]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, default=None)
    ap.add_argument("--upstream-parent", type=Path, default=None,
                    help="Optional direct byte comparison to the receiving Version 19 parent table")
    args = ap.parse_args()
    p195 = ROOT / "source/quadratic195.json"
    p229 = ROOT / "source/quadratic229-v62.json"
    ptr = ROOT / "source/transformation195.json"
    old = read_pinned(p195, SHA195)
    new = read_pinned(p229, SHA229)
    read_pinned(ptr, SHATRANS)
    if args.upstream_parent:
        assert p195.read_bytes() == args.upstream_parent.read_bytes()

    assert old["variables"] == 195 and new["variables"] == 229
    assert old["inputCoordinate"] == new["inputCoordinate"] == 1
    assert len(old["residuals"]) == 175 and len(new["residuals"]) == 207
    assert len(new["coordinates"]) == 229
    assert [r["id"] for r in new["residuals"]] == list(range(1, 208))
    assert [c["id"] for c in new["coordinates"]] == list(range(1, 230))

    # Verify all nine contact helpers are confined to the four contact rows
    # of their detector (not one of the later trace, pole, or height rows).
    helpers = ((0, (74, 75, 76), (22, 23, 24, 25)),
               (1, (87, 88, 89), (34, 35, 36, 37)),
               (2, (201, 202, 203), (176, 177, 178, 179)))
    use_counts = []
    for detector, coords, allowed in helpers:
        for coord in coords:
            uses = {r["id"] for r in new["residuals"]
                    if any(coord in t["monomial"] for t in r["terms"])}
            assert uses and uses <= set(allowed), (detector, coord, sorted(uses))
            use_counts.append([coord, sorted(uses)])
        for idx, word in zip(coords, ("contactSquare", "contactFourthPower",
                                      "contactCombination")):
            assert new["coordinates"][idx-1]["name"] == (
                "additive.detector%d.%s" % (detector, word))

    # Bind all six Q(sqrt(2)) components of the three secant rows.
    # In blocks 3,4 only the f component carries the family parameter C.
    pair_data = [
        (111, 112, 152, 153, 156, 157, 160, 161, 154, 155, 158, 159, 0),
        (127, 128, 162, 163, 166, 167, 170, 171, 164, 165, 168, 169, 1),
        (143, 144, 172, 173, 176, 177, 180, 181, 174, 175, 178, 179, 1),
    ]
    for row0, row1, *coordinates in pair_data:
        real, imag = secant_components(*coordinates)
        assert poly(new["residuals"][row0-1]) == real, row0
        assert poly(new["residuals"][row1-1]) == imag, row1

    # The imaginary inverse-Vieta coordinate x193 must be the rho
    # component of the same field product as the real coordinate x192,
    # not merely a similarly named free variable.
    product_real = {(0, (112, 192)): Fraction(1),
                    (1, (182, 184)): Fraction(-1),
                    (1, (183, 185)): Fraction(-2)}
    product_imag = {(0, (112, 193)): Fraction(1),
                    (1, (182, 185)): Fraction(-1),
                    (1, (183, 184)): Fraction(-1)}
    assert poly(new["residuals"][154]) == product_real
    assert poly(new["residuals"][155]) == product_imag

    # The inverse Vieta r components also use 1 and 2 with the
    # correct rho^2=2 sign; both p coordinates actually occur.
    r_real = {(0, (77, 190)): Fraction(1),
              (1, (186, 192)): Fraction(-1),
              (1, (187, 193)): Fraction(-2)}
    r_imag = {(0, (77, 191)): Fraction(1),
              (1, (186, 193)): Fraction(-1),
              (1, (187, 192)): Fraction(-1)}
    assert poly(new["residuals"][156]) == r_real
    assert poly(new["residuals"][157]) == r_imag

    names = {c["id"]: c["name"] for c in new["coordinates"]}
    for pair in (1, 3, 4):
        for component in (0, 1):
            assert any(name == "pair%d.s.%d" % (pair, component)
                       for name in names.values())
    assert names[192] == "scalar.inverseVieta.p.0"
    assert names[193] == "scalar.inverseVieta.p.1"
    assert new["residuals"][174]["name"].endswith("component0")
    assert new["residuals"][206]["name"].endswith("component1")
    assert (0, (77, 192)) in poly(new["residuals"][174])
    assert (0, (77, 193)) in poly(new["residuals"][206])

    report = {
        "status": "PASS", "scope": "Exact source-table and field-component checks only",
        "source195_sha256": SHA195, "source229_sha256": SHA229,
        "parent_transformation_sha256": SHATRANS,
        "verified_helper_isolation": use_counts,
        "field_secant_rows_checked": [111, 112, 127, 128, 143, 144],
        "inverse_vieta_product_rows_checked": [155, 156],
        "inverse_vieta_r_rows_checked": [157, 158],
        "rational_imaginary_components": True,
        "all_229_rows": 207, "variables": 229,
        "global_arithmetic_proof_audited": False
    }
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

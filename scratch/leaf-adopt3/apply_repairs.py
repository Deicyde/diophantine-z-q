#!/usr/bin/env python3
"""Apply the docstring/comment repairs of rv-leaves48 (scratch/rv-leaves48/Repairs.md) and the
Leaves.lean items of docs/research/factcheck-w34b.md to scratch/h-decomposition/Leaves.lean.

Usage: python3 apply_repairs.py path/to/Leaves.lean

Every repair is an exact string replacement. Each old string must occur exactly once in the
file, otherwise the script prints the offending repair and exits nonzero without writing.
Only docstring / comment text changes; where an old string includes a code line (for
uniqueness), the same code line appears verbatim in the new string.

The anchors were located by content in the leaf-adopt3 Leaves.lean (Repairs.md's line numbers
refer to the older base 01267822).
"""
import sys

REPAIRS = [
    # ---------------------------------------------------------------- rv-leaves48 P1
    ("rv-leaves48 P1 (bundle field r19)",
     """  /-- R19-R21 over def-faltings' `stableFaltingsHeight` (not yet known non-vacuous: AN3 open). -/
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
""",
     """  /-- R19-R21 over def-faltings' `stableFaltingsHeight`. Its value is `⊤` (no metrized model) or
  the stable Faltings height in Faltings' normalization, so R19-R21 are true for the definition;
  they say something only together with `h5` (`StableHeightFinite`), which is where a defect of
  the definition would surface, as a false leaf (rv-leaves48, `RvLeaves48D`). -/
  r19 : ZInQ.DefFaltings.R19_GaudronRemond
"""),
    ("rv-leaves48 P1, extended (module header)",
     """input folded into each leaf because polarizations cannot be stated in Lean yet; the height
leaves (R18-R22, H5) are not yet known to be non-vacuous (AN3 open); see the docstrings,
""",
     """input folded into each leaf because polarizations cannot be stated in Lean yet; the height
leaves (R18-R22) say something only together with H5: where the height is `⊤` (no metrized
model) R19, R20, R22 are vacuous and R21 is trivial, so a defect of the definition surfaces as a
false H5 (`StableHeightFinite`) or a false R18 (which asserts `h < ⊤`), not as vacuity
(rv-leaves48 P1, compiled for R19-R21 and H5); see the docstrings,
"""),
    ("rv-leaves48 P1, extended (section 2 comment on R19-R21)",
     """as an explicit leaf `LeafAdopt.H5` (rv-blueprints F2). **Not yet known to be non-vacuous**: the
three Props `AnalyticUniformizationExists`, `AnalyticUniformizationUnique`,
`HodgeLatticeTheorem` (node AN3 and the Hodge lattice) are open, and until they are proved the
index set of the infimum may be empty (`h = ⊤`): then R21 holds trivially and R19, R20 have no
instance. R19""",
     """as an explicit leaf `LeafAdopt.H5` (rv-blueprints F2). **The height may be `⊤`** (formerly
worded "not yet known to be non-vacuous"; rv-leaves48 P1): the
three Props `AnalyticUniformizationExists`, `AnalyticUniformizationUnique`,
`HodgeLatticeTheorem` (node AN3 and the Hodge lattice) are open, and until they are proved the
index set of the infimum may be empty (`h = ⊤`): then R21 holds trivially and R19, R20 have no
instance. So R19-R21 are true for the definition, and a defect of it would surface as a false H5
(`StableHeightFinite`), not as vacuity. R19"""),
    # ---------------------------------------------------------------- rv-leaves48 P3
    ("rv-leaves48 P3 (bundle field r1r2)",
     """  Premise Lemma P of rv-qm-polar (type-`μ` polarization exists and is unique), see the definition. -/
  r1r2 : LeafAdopt.R1R2fpRep
""",
     """  Premise (rv-qm-polar Lemma P): for a QM pair `(A, ι)` in characteristic 0 there is exactly one
  principal polarization whose Rosati involution is `x ↦ μ⁻¹x̄μ` on `ι(𝒪)` (`μ = 2j + ij`, the
  type fixed by the PEL datum); see the definition. Checked by model reviews (rv-qm-polar), no
  human review. -/
  r1r2 : LeafAdopt.R1R2fpRep
"""),
    # ---------------------------------------------------------------- rv-leaves48 P4
    ("rv-leaves48 P4 (T23 docstring)",
     """that the leaf is basis-free. Exact. -/
def T23_FontaineClosure : Prop :=
""",
     """that the leaf is basis-free. Consequence (matrix form of the published statement). -/
def T23_FontaineClosure : Prop :=
"""),
    ("rv-leaves48 P4, extended (hsyn-fold comment listing T23)",
     """`PkgI4.T23_FontaineClosure` (exact, matrix form, `ℚ_p` coefficients),
""",
     """`PkgI4.T23_FontaineClosure` (consequence: matrix form of the published statement, `ℚ_p`
coefficients; rv-leaves48 P4),
"""),
    # ---------------------------------------------------------------- rv-leaves48 P5
    ("rv-leaves48 P5 (LocalReciprocityUpper / t16b docstring)",
     """theory* in Cassels–Fröhlich, §§2.8, 4.? (UNVERIFIED locators).  The canonical reciprocity map
is one such `θ`, so this ∃-form is a consequence of the published theorem. -/
""",
     """theory* in Cassels–Fröhlich, §§2.8, 4.? (UNVERIFIED locators).  The reciprocity map normalized
to send uniformizers to arithmetic Frobenius elements (Serre's convention) is one such `θ`; its
inverse normalization does not satisfy clause 3 (rv-leaves48 P5). So this ∃-form is a
consequence of the published theorem. -/
"""),
    # ---------------------------------------------------------------- fact-check w34b
    ("fact-check w34b item 1 (fibre_conjugates_isomorphic docstring; docs fix, statement kept)",
     """/-- **Glue (compiled): A4 + A7 from the leaves alone.** From `R1R2fp`: for every rational
`j₀`, there is an object `P` over `ℚ̄` at a point of `Y₃` over `j₀`, and every Galois conjugate of
`P` (its base change `Q` along any `σ ∈ Aut(ℚ̄/ℚ)`) has abelian surface isomorphic to that of `P`
(through an `Aut(𝒪)`-twisted QM isomorphism). This is pkg-I1's (I1-out)(ii) for the fibre over
`J(u) = j₀`. -/
theorem fibre_conjugates_isomorphic""",
     """/-- **Glue (compiled): A4 + A7 from the leaves alone.** From `R1R2fp`: there is an object
`P : QML3 ℚ̄` such that every Galois conjugate of `P` (its base change `Q` along any
`σ ∈ Aut(ℚ̄/ℚ)`) is an `Aut(𝒪)`-twist of `P` (so its abelian surface is isomorphic to that of
`P`). The statement does not link `P` to `j₀`: the proof chooses `P` at a point of `Y₃` over `j₀`
(`exists_fibre_object`), but the conclusion only asserts some `P`. For the linked form, pkg-I1's
(I1-out)(ii) for the fibre over `J(u) = j₀`, use `exists_fibre_object` with
`conj_twist_of_rational` (fact-check w34b item 1). -/
theorem fibre_conjugates_isomorphic"""),
    ("fact-check w34b item 4 = rv-qm-polar repair 3 (R1hecke parenthesis)",
     """`α(μ) ∈ ℚ^×μ`; a matching `λ' = ±λ∘ι(μ⁻¹μ')`, `μ'` rescaled to norm 6, is defined in families, so
the twist is still a functor automorphism.""",
     """`α(μ) ∈ ℚ^×μ`; a matching `λ' = λ∘ι(εv)`, `v = μ⁻¹α(μ) ∈ 𝒪¹` `†`-symmetric (`twist_type`),
`ε = sign trd v`, is defined in families (for the Atkin–Lehner generators `i`, `j + k`, `v = −1`
and `λ' = λ`; rv-qm-polar repair 3, fact-check w34b item 4), so
the twist is still a functor automorphism."""),
    ("fact-check w34b item 3, extended (R1fp docstring: compiled scope of Lemma P)",
     """§1.2 with the lattice core and sign step compiled, class number one and the descent from `ℂ`
not in Lean).""",
     """§1.2 with the lattice core and sign step compiled for N5's `μ` on `Λ = 𝒪` only; the `E0R`/`E0`
identification, `Λ = 𝒪v`, Riemann forms ↔ polarizations, class number one and the descent from
`ℂ` are not in Lean; fact-check w34b item 3)."""),
    ("fact-check w34b item 3, extended (R1R2fpRep docstring: compiled scope of Lemma P)",
     """§1.2; lattice core and sign step compiled: `eq_pm_E0_of_principal`, `type_eq_mu_mul`,
`lemmaP_lattice`; class number one and the descent from `ℂ` not in Lean); its published locators
""",
     """§1.2; lattice core and sign step compiled for N5's `μ` on `Λ = 𝒪` only: `eq_pm_E0_of_principal`,
`type_eq_mu_mul`, `lemmaP_lattice`; the `E0R`/`E0` identification, `Λ = 𝒪v`, Riemann forms ↔
polarizations, class number one and the descent from `ℂ` not in Lean; fact-check w34b item 3);
its published locators
"""),
    ("fact-check w34b nit (DefFaltingsSec header: AbVar has five fields)",
     """second copy of the kernel's abelian-variety structure (same four fields as `PkgI3.AbVar`), so
""",
     """second copy of the kernel's abelian-variety structure (same five fields as `PkgI3.AbVar`: `X`
and four instances; fact-check w34b), so
"""),
]


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: apply_repairs.py path/to/Leaves.lean", file=sys.stderr)
        return 2
    path = sys.argv[1]
    with open(path, encoding="utf-8") as f:
        text = f.read()
    bad = []
    for rid, old, new in REPAIRS:
        n = text.count(old)
        if n != 1:
            bad.append((rid, n))
    if bad:
        for rid, n in bad:
            print(f"FAIL: {rid}: old string occurs {n} times (expected exactly 1)")
        print("No changes written.")
        return 1
    for rid, old, new in REPAIRS:
        n = text.count(old)
        if n != 1:  # an earlier replacement interfered; abort without writing
            print(f"FAIL: {rid}: old string occurs {n} times after earlier repairs")
            print("No changes written.")
            return 1
        text = text.replace(old, new, 1)
        print(f"applied: {rid}")
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)
    print(f"{len(REPAIRS)} repairs applied to {path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

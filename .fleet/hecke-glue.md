# hecke-glue (fleet summary)

**Verdict.** Of hecke-pin's three open inputs to the Hecke dictionary of the r16 rows, two are now proved
outright: `ConstOnTauPoints` and `X1TauPoints`. `X1TauPoints` turns out to be glue, not a leaf. The third,
`AbelJacobiX1`, is still open. New file: `ZInQKernel/Contrib/OneProof/HeckeGlue.lean` (namespace
`AfTateLam.HeckeGlue`, about 1000 lines).

**Proved (VERIFIED: builds, no sorry, standard axioms only).**
- `tauPlace`. The functions in `K(X) = ℚ(j_X, t_X)` that have a finite limit at `τ` form a valuation subring
  `O_τ`, and the limit map is local.
  - Inputs: Mathlib's `meromorphicOrderAt`, and the relations in `IsX1Gen` combined with the identity theorem.
- `exists_cpt_of_place`. Every place has a center among the complex points of the curve.
  - Inputs: the valuative criterion of properness, and CloudW07's result that local rings of a smooth
    curve are valuation rings.
- `x1TauPoints` follows from the two results above.
- `atTau_unique`. The point `x_τ` is unique, as the docstring of `AtTau` claims.
- `constOnTauPoints`. The proof runs over `ℚ`, so it needs neither base change to `ℂ` nor geometric
  irreducibility.
  - `x_ρ` lies over a closed point, because `j_X(x_ρ) = 0`.
  - A closed set of the curve that misses the generic point is finite, and so carries only finitely
    many complex points. But `j` takes infinitely many values.
  - So the generic point maps to `g(P₀) = 0`, whose residue field is `ℚ`.
  - Note: `ConstOnTauPoints` is unprovable without the points `x_τ` (its hypothesis would be vacuous). It
    is proved from `X1TauPoints`.

**Wired into HeckePin.**
- `isHeckeT_unique'` and `isDiamond_unique'` pin `T_p` and `⟨d⟩` with no hypothesis.
- `evF_eq_zero_of_heckeJ_eq_zero_of_abelJacobi` and `killsIf_iff_IfDS_of_abelJacobi` need only
  `AbelJacobiX1`.

**Per row.**
- `HeckeJ1DS`: the dictionary gap is closed with no remaining input.
- `AfShimura`, `AfCharpolyDS965`: closed except for `AbelJacobiX1`.

**Checks.**
- `#discharges`: `r16CoreY` is still discharged by `r16CoreY_of_ds965`, assuming the same five leaves.
- The fold dry run is unchanged: `11/18 on 29 -> 15/17 on 32`.
- The verbatim target copies check by `Iff.rfl`.
- The autofold spec adds no new leaf. It marks `X1TauPoints`, `ConstOnTauPoints` and `TauPlace` as proved
  glue.

**Remains.**
- `AbelJacobiX1` is a composite of DS Thm 6.1.2 (Abel; 2005 printing pp. 214–215, VERIFIED), DS §3.3, Milne's
  Jacobian theorems and GAGA.
- It has no printed form in Lean today, because Mathlib 4.35 has no Riemann-surface Jacobian, `H₁`, or path
  integrals.
- The report (§5) lists the five bridge steps; none is proved.
- Proposed kinds row: `consequence`, strictest `GLUE`.
- Report: `docs/research/hecke-glue.md`.

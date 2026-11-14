# curve-split — report (2026-11-14)

**Main result.** Of the six GLUE rows, H-85 `ModelGlue.CurveBijIso` is now **proved outright**
(`CurveSplit.curveBijIso`, no hypotheses), from Mathlib v4.35 and `ZInQKernel/`.
`CurveBijIso` says a morphism of proper smooth curves over ℚ that is bijective on ℚ̄-points is an
isomorphism. The proof:
- descent to ℚ̄, by fpqc descent of isomorphisms;
- the curve becomes a homeomorphism on each component (topology, plus DVR stalks of smooth
  curves);
- on affine charts, a finite flat extension of a Dedekind domain that is unramified at an isolated
  maximal ideal with trivial residue extension has rank 1. Mathlib's rank and unramified-locus API
  covers this, using the generic point in characteristic 0 and the Nullstellensatz.

Zariski's Main Theorem in its original form is also proved, from Mathlib's Stacks 03GW
(`CurveSplit.zmtOriginal`).

**Other rows.**
- H-81 `NormalCurveSmoothQ` is proved from one new leaf, `RegularSmoothPerfect` (Stacks 00TV).
- H-82 `GeomConnectedOfConstantFieldQ` is proved from the kernel leaf `ZariskiConnectedness`
  (EGA III 4.3). No finiteness theorem is needed, and normality is unused.
- H-41 `X0Transitive` follows from the kernel's Igusa leaf (`IgusaSL2X` / `IgusaGL2`). The
  modular-equation form cannot be stated: Mathlib has no `j`-function.
- H-79 `GenusX1Field` cannot be split: Shimura's `Γ₁(N)\ℍ*` has no Lean form. It is also
  stronger than the proof needs: the only use is `dim J₁(N) ≤ N²` (`dim_J1_le`). That bound,
  `DimJ1Le`, is proved by `CurveSplit.dimJ1Le_of_rh` from `DimJacobianEqGenus` (kernel),
  `X0Transitive`, and one textbook leaf, `RiemannHurwitzQj` (Stichtenoth 3.4.13 + 3.5.1).
  The fundamental identity and "places are DVRs" are proved from Mathlib's Dedekind machinery.
- H-83 `ShimuraGoodReduction` cannot be split: its published form is representability of a
  moduli functor of abelian schemes over `ℤ_(p)`, and neither Mathlib nor the kernel defines
  abelian schemes over a base. Shown in Lean: the guard clause is redundant given `R1R2fp`.

No row was found false or vacuous; no row statement changed.

**What compiles.** `scratch/curve-split/{X0Split,CurvesGSplit,CurveBij,GenusBound,ShimuraGR}.lean`,
about 3100 lines. All five compile with `lake env lean`, with no errors and no `sorry`, and
`#print axioms` shows only propext, Classical.choice and Quot.sound. Report:
`docs/research/curve-split.md` (verdict, table, row-by-row). Log: `scratch/curve-split/log.md`.

**What remains.**
- Adopt `CurveBij.lean` into `ZInQKernel/Contrib/` and discharge `CurveBijIso` in model-glue.
- Switch the consumers of `dim_J1_le` to `DimJ1Le`, so that T34's second half (H-79) leaves the
  proof.
- Leaves still needed for these rows: Igusa, Riemann–Hurwitz, Stacks 00TV, Zariski connectedness,
  and the H-83 representability (not stateable yet).
- Every theorem number for a printed source is from memory (UNVERIFIED).
- A human check is needed on the printed form of Springer Cor. 5.2.8. It only matters for the
  superseded leaf `BijToNormalIsIso`.

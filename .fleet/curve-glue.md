# curve-glue (2026-11-13)

**Verdict.** Both assigned Props are reduced, and the CM-point gap in `MobiusGlue` is closed. All
of it is compiled Lean with the standard axioms. The kernel's `MobiusGlue` now rests on
**(L0) `FiniteGlobalSections`**, **(G1') `ImagePlaneCurveClosed`** and **T5 `TorsionStructure`**
(`scratch/curve-glue/MobiusFinal.lean`, `mobiusGlue_of_L0_G1'_T5`). C1b `SmoothStalkDimOne` is now
proved, by infra-smooth-dim, whose branch was merged and whose proof is copied verbatim.

- **C2K `ConstOrOntoAlgClosed`: proved** from (L) `GlobalFunctionsConst`, i.e. regular functions on
  a connected component of a proper smooth curve over `K̄` are constant up to nilpotents (`C2K.lean`).
  (L) is in turn **proved** from (L0) `FiniteGlobalSections`, the finiteness theorem for proper
  morphisms (EGA III 3.2.1, a textbook leaf, numbering UNVERIFIED), together with Lean algebra:
  Artinian rings with trivial idempotents, and idempotent sections over connected opens (`L0.lean`).
- **C3K `RatFactorAlgClosed`: proved** from (G1) `ImagePlaneCurve`, and (G1) is **proved** from C2K
  and the glue (G1') `ImagePlaneCurveClosed`. (G1') says: an irreducible `P` with `P(σ, ρ) = 0`,
  closure control at `ρ = ∞`, and the affine image of the component is Zariski closed. The rest is
  Lean-proved algebra (`C3K.lean`): resultant, Gauss lemma and char-0 separability give two roots
  in some fibre when `deg_y P ≥ 2`, and a Bezout-type finiteness lemma handles the rest.
- **CM-point gap: closed** (`CMPoints.lean`). `MobiusGlue` already carries the CM objects as a
  premise. CM points over `0, ∞, −16/27` exist on every triple because `Φ` is bijective; only the
  one-way R2fp clauses are needed. The objects come from `CMExists` and `X6Surj` (level-3
  structures exist): `cm_points_of_R1R2fp`, and `cm_points_of_R1R2fpRep` for the repaired bundle.
  `mobiusGlue_noCM_of : MobiusGlue → R1R2fp → MobiusGlueNoCM`. No hypothesis needs to be added.
- **Statements.** No statement was changed. Copies are byte-identical (`py/verbatim.py`); the one
  exception is a single destructuring line in mobius-glue's proof, adapted to the kernel's
  `R1fpProps` clause order.
- **Independent model check.** It found (L) and (G1) TRUE and not vacuous. (L0) and (G1') came
  later and were not checked by it.

**Compiles** (0 errors, axioms `[propext, Classical.choice, Quot.sound]`): `CMPoints.lean`,
`C2K.lean`, `C3K.lean`, `L0.lean`, `CurveGlueAll.lean`, `MobiusEnd.lean`, `MobiusFinal.lean`.

**Remains.**
- (L0), a textbook leaf, is not in Mathlib.
- (G1'), the geometric glue, needs `P¹ × P¹`, function fields of curves (transcendence degree 1)
  and the fact that plane curves are hypersurfaces (Hartshorne I.1.13). None of these is in
  Mathlib v4.35.
- T5 (existing leaf).
- Kernel integration of `MobiusFinal.lean`.

Report: `docs/research/curve-glue.md`.

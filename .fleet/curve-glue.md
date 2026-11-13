# curve-glue (2026-11-13)

**Verdict.** Both assigned Props are reduced, and the CM-point gap in `MobiusGlue` is closed. All
of it is compiled Lean with the standard axioms.

The kernel's `MobiusGlue` now follows from five named statements
(`scratch/curve-glue/MobiusFinal.lean`, `mobiusGlue_of_L0_CI_AD_IC_T5`):
- **(L0) `FiniteGlobalSections`** (textbook leaf): finiteness of `Γ(W, 𝒪)` for `W` clopen in a
  proper `K`-scheme, EGA III 3.2.1.
- **T5 `TorsionStructure`** (existing textbook leaf).
- **(CI) `ComponentIrreducible`** (glue): components of a smooth curve are irreducible.
- **(AD) `AlgDep`** (glue): `σ, ρ` are algebraically dependent; transcendence degree 1.
- **(IC) `ImageClosed`** (glue): the affine image of a component under `(σ, ρ)` is Zariski closed;
  properness.

C1b `SmoothStalkDimOne` was proved by infra-smooth-dim. I merged that branch and copied its proof
verbatim.

- **C2K: proved** from (L) "global functions on a component are constant" (`C2K.lean`), and (L) is
  proved from (L0) (`L0.lean`). The proof uses values of sections at `K`-points, units via
  Jacobson, gluing `1/(f−a)` with `g/(1−ag)`, and Artinian algebra.
- **C3K: proved** from C2K, (CI), (AD) and (IC), through the intermediate statements (G1'') → (G1')
  → (G1), all compiled. The Lean algebra covers:
  - two roots in some fibre when `deg_y P ≥ 2` (Gauss lemma, char-0 separability, resultant);
  - Bezout-type finiteness;
  - choice of an irreducible factor on an irreducible open;
  - the leading-coefficient clause, by density.
- **CM-point gap: closed** (`CMPoints.lean`). `MobiusGlue` already assumes the CM objects. CM
  points over `0, ∞, −16/27` exist on every triple because `Φ` is bijective, and only the one-way
  R2fp clauses are used. The objects come from `CMExists` and `X6Surj` (level-3 structures exist):
  `cm_points_of_R1R2fp`, `cm_points_of_R1R2fpRep`, and
  `mobiusGlue_noCM_of : MobiusGlue → R1R2fp → MobiusGlueNoCM`. No hypothesis needs to be added.
- **No statement was changed.** Copies are byte-identical (`py/verbatim.py`), except one
  destructuring line in mobius-glue's proof, adapted to the kernel's `R1fpProps` clause order.
- **Independent model checks** (two fresh agents) found (L), (G1), (L0) and (G1') TRUE and not
  vacuous. (CI), (AD) and (IC) were added after those checks and were not reviewed independently.

**Compiles** (0 errors, axioms `[propext, Classical.choice, Quot.sound]`): `CMPoints.lean`,
`C2K.lean`, `L0.lean`, `C3K.lean`, `CurveGlueAll.lean`, `MobiusEnd.lean`, `MobiusFinal.lean`.

**Remains.**
- (L0) is not in Mathlib.
- (CI) needs "regular local ⇒ domain" on top of infra-smooth-dim's regular stalks.
- (AD) needs function fields of curves.
- (IC) needs `P¹ × P¹` and closedness of images under proper maps.
- T5.
- Kernel integration of `MobiusFinal.lean`.

Report: `docs/research/curve-glue.md`.

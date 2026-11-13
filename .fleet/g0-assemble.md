# g0-assemble (2026-11-13)

**Result.** Wave 26 is assembled into one Lean file, `scratch/g0-assemble/G0Assemble.lean`.
It is `scratch/h-decomposition/Leaves.lean`, unchanged except for three added non-HDecomp kernel
imports, plus `parts/*.lean`. It proves:
- `HSyn.gluePieces_of_gluePieces2 (r) (t) (gp2 : GluePieces2) : GluePieces`;
- `HSyn.sixContactMin_of_leaves2 (r) (t) (gp2) : ZInQ.SixContactMin`.

Every one of the ten `GluePieces` fields is a wave-26 theorem applied to fields of `GluePieces2`,
`r` or `t`. This includes `ModularConstituent`: the three ranges G2-G7, G8-G12 and G13-G16 are
composed, with the bridges G7→G8 and G12→G13 built here (`G0AssembleMod.afterG7_of`).

**What compiles (VERIFIED).** `lake env lean scratch/g0-assemble/G0Assemble.lean` exits 0 with
0 errors and no `sorry`, and all 180 `#print axioms` lines are `[propext, Classical.choice,
Quot.sound]` (41 970 lines, 548 s).

**`GluePieces2`: 28 fields.**
- 5 LEAF: `MulIsogeny`, `RigidityHom`, `BurnsideAbsIrred`, `R14Det` (R14 with its published
  determinant clause, as g0-mod-galois found), `CarayolR17'` (concrete R17; the bundle's `r17` is
  still opaque and unused here).
- 1 LEAF candidate: `ThetaRatiosAlgebraic`, a composite of published results.
- 22 GLUE. Four are blocked on qm-pin: FS5 `FibreComTrivial`, `FibreQMPeriod`,
  `KernelFieldExists`, and the new `ModelG3G6` (its G6 half is NoCM).

**New in this task.**
- Two joint glue Props, `ModelG3G6` and `LinkedTateData`. `LinkedTateData` must tie the ℓ = 5 and
  ℓ = 3 Tate data to one descent datum: `TateBridge` is `∀ℓ ∃data`, and g0-mod-newform showed that
  `G14TraceCompat` is false for unrelated constituents.
- `G15RamG`'s clause (iii) is derived from G11 (`g15RamG_of_wild`).
- g0-mod-galois' `ResQFiniteIndex` is proved (`resQFiniteIndex`).
- The layer caveat is checked: `abVarEquiv` commutes with `baseChange` by `rfl`.

**Statement change (reported).** `G0Galois.G10Glue` had the hypotheses `HSyn.T11_RiemannGAGA →
HSyn.T12_ArtinComparison →`. These are opaque placeholders that leaf-adopt2 removed. They are
replaced by the bundle's concrete `T11a_RiemannEnd → T11b_Rigidity`; T12 is glue. All other
copies are verbatim, up to name opens.

**Remains.**
- The 22 glue Props, 4 of them waiting on qm-pin.
- `HeightCopiesAgree`: no task has worked on it.
- Not folded:
  - h5-glue. It reduces the leaf `r.h5` and proves `NeronModelMinimal`; its file is over the
    kernel's `PkgI3.AbVar` layer.
  - g4-weilres, inertia-homs and morph-descend. They give G4's Hom field, part of
    `KernelFieldExists`, through a different interface.

Report: `docs/research/g0-assemble.md`. Log: `scratch/g0-assemble/log.md`.

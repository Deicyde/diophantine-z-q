# coarse-factor results log

## Step 1: reduction (Reduction.lean)
- Copied verbatim from scratch/qm-glue/ModuliCompare.lean: `CoarseFactor`, `CanonicalCoarseX6` (python substring check True, VERIFIED).
- New Props: `PairsLift` (every QM pair over Q̄ is iso to P.forget for some QML3 P), `FactorThroughSurj` (AG glue:
  proper smooth curves Y,X,X' over ℚ, f : Y→X onto X(Q̄), f' constant on Q̄-fibres of f ⇒ ∃ h, f ≫ h = f').
- COMPILED (lake env lean, 15 s, imports ZInQKernel.OneProof.H.LPrefix; standard axioms):
  `coarseFactor_of : PairsLift → FactorThroughSurj → CoarseFactor`,
  `pairsLift_of_canonical : CanonicalCoarseX6 → PairsLift`, `pairsLift_of_rep : R1R2fpRep → PairsLift`,
  `coarseFactor_of_canonical`, `coarseFactor_of_rep`.
- Finding: X6Props alone does not give surjectivity of fY on Q̄-points; it needs that every QM pair has a level-3
  structure (PairsLift). PairsLift is not a new leaf: it follows from the leaf-forms qm-glue already uses.
- Build note: lean/.lake/build copied from ~/dzq-wt/leaf-fold7 (lean/ZInQ sources identical, diff -rq).

# height-split results log

Task height-split (2026-11-14). Base cba8157f. Lean files: scratch/height-split/*.lean, each checked
with `lake env lean` (one process at a time). Marks: VERIFIED / STANDARD / SPECULATIVE / UNVERIFIED.

## Setup
- 03:15 `lake build ZInQKernel.HDecomp.Faltings.Leaves ZInQKernel.HDecomp.LeafPush2.Bridge
  ZInQKernel.Contrib.HeightBC.Main ZInQKernel.HDecomp.QM.Leaves`: success (VERIFIED).
- Rows located (VERIFIED, read): R18 `ZInQKernel/HDecomp/LeafPush2/R18.lean`, R22 `.../R22.lean`,
  R20/R21 `ZInQKernel/HDecomp/Faltings/Leaves.lean`, StableHeightFinite `.../Faltings/Height.lean`,
  R5fpCount `ZInQKernel/HDecomp/QM/Leaves.lean`. All rows live under ZInQKernel/, so they are imported.
- Existing H5 infrastructure (VERIFIED, read): kernel leaves N1 `H5Neron.NeronModelExists`,
  N2 `H5Neron.SemistableNeronIdentityComponent`; theorems `Contrib.HeightBC.modelHeightBaseChange`,
  `openSubgroupHeight`, `neronModelMinimal`, `H5Neron.groupModelBaseChangeExists`,
  `stableFaltingsHeight_eq_neron_of_N1N2`.

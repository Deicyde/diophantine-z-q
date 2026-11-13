# g0-heightadd results log

Start 2026-11-13 01:44 PST. Base 883c4ddf; merged origin/wip/g0-split (c20fa62b) and
origin/wip/h5-neron (b7c1dc21), neither was in the base.

## Run 1: HeightAdd.lean — COMPILED 01:55 (47 s; 0 errors; axioms propext, Classical.choice, Quot.sound)
- `Prefix.lean` = `import Mathlib` + `Split.lean` l. 16667-18603 verbatim (def-faltings section:
  `ZInQ.DefFaltings.AbVar`, `GroupModel`, `MetrizedModel`, `stableFaltingsHeight : EReal`,
  `NeronModelMinimal`). Compiles standalone (93 s). VERIFIED.
- h5-neron parts A, E copied with `open PkgI3 (AbVar)` dropped (so over `DefFaltings.AbVar`):
  compiled unchanged. VERIFIED.
- `LeafAdopt.H5`, `G0Split.IsProductOf`, `G0Split.HeightAdditivity` copied verbatim. VERIFIED.
- proved `isProductAbVar_of_isProductOf`, and
  `heightAdditivity_of (hN1 : NeronModelExists) (h5 : LeafAdopt.H5) (hH : ProductModelHeight) :
  HeightAdditivity`. VERIFIED (compiled).
- FINDING (gap check): h5-neron's `stableFaltingsHeight_add_le'` is NOT literally the piece:
  (i) it is over `PkgI3.AbVar` (kernel Objects.lean), the piece over `DefFaltings.AbVar` (the
  proofs transfer verbatim); (ii) `IsProductAbVar` vs `IsProductOf` (bridge proved);
  (iii) EReal vs the real-valued form (proved). Remaining hypotheses: N1 (leaf, not in the
  bundles), `NeronModelMinimal` = `r.h5.2` (bundle), `ProductModelHeight` (glue P2, unproved).

## Run 2: P2 split — COMPILED 02:10 (0 errors; 5 #print axioms all [propext, Classical.choice, Quot.sound])
- new glue Props (namespace `ZInQ.G0HeightAdd`): `ProductMetrization` (P2a, product of
  metrizations, height = sum), `MetrizationExists` (every group model has a metrization),
  `MetrizationDimUnique` (two metrizations of one model have the same g).
- proved `height_le_of_model`, `le_height_of_model` (from `AnalyticUniformizationUnique`,
  `MetrizationDimUnique`), `productModelHeight_of : U → DimUnique → Exists → P2a →
  ProductModelHeight`, and `HSyn.G0Split.heightAdditivity_of_split : N1 → LeafAdopt.H5 → U →
  DimUnique → Exists → P2a → HeightAdditivity`. VERIFIED (compiled).

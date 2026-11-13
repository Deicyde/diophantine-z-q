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

## Run 3: integration check SplitIntegrated.lean — COMPILED (3 min 26 s; 0 errors)
- `build_integrated.sh`: g0-split's `Split.lean` + h5-neron parts A, E after l. 18603 + bridge,
  P2 split and `example (hN1) (r : HSyn.ResearchLeaves) (hU) (hD) (hE) (hP) :
  HSyn.G0Split.HeightAdditivity := heightAdditivity_of_split hN1 r.h5 hU hD hE hP` at the end.
  All `#print axioms` (incl. g0-split's `glueOutputs_of_leaves`, `sixContactMin_of_leaves`, and
  `heightAdditivity_of_split`): [propext, Classical.choice, Quot.sound]. VERIFIED.
- needed first: `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` (13 s).

## Run 4: dimension-0 check (part_zero.lean) — COMPILED (HeightAdd.lean, 53 s; 0 errors)
- first attempt failed: missing instance `GeometricallyIntegral (𝟙 (Spec K))`; copied
  `PkgI3.AbVar.geometricallyIntegral_id_spec` from Objects.lean, `zero` marked noncomputable.
- `metrizationExists_zero`, `metrizationDimUnique_zero`, `productMetrization_zero` for
  `A = B = C = AbVar.zero K`: all [propext, Classical.choice, Quot.sound]. VERIFIED.

## Run 5: P2a split (part_prod.lean) — COMPILED (HeightAdd.lean; 0 errors; all axioms standard)
- first attempt: parse errors, `η` is a token under `open MonObj` (η[M] notation); renamed to `s`.
- proved `modelHeight_add_of`: Hodge data `D` (dim g₁+g₂), `D₁`, `D₂` with nonzero sections
  `s, s₁, s₂` whose `secIndex`, `coeff σ` and `ZLattice.covolume (periods σ)` are multiplicative
  ⇒ `D.modelHeight = D₁.modelHeight + D₂.modelHeight`. VERIFIED.
- new glue `ProductMetrizationGeo` (P2a-geo: the product metrization with a product section);
  proved `productMetrization_of_geo : ProductMetrizationGeo → ProductMetrization` and
  `HSyn.G0Split.heightAdditivity_of_geo : N1 → LeafAdopt.H5 → U → DimUnique → Exists → P2a-geo →
  HeightAdditivity`. VERIFIED.

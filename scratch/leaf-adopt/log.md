# leaf-adopt results log

## 2026-11-12 19:4x  baseline
- `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` (needed first; JHeight imports package `ZInQ`): OK.
- Baseline `lake env lean scratch/h-decomposition/Leaves.lean` (8512506d): 0 errors, one `declaration uses sorry` (L12366, `HSyn.glueOutputs_of_leaves`), 2m02s wall.
- Placeholders used only in the bundles `ResearchLeaves`, `TextbookLeaves` (grep: no other use of R01_/R02_/R05_/R16_/R19_-R21_, T32a_/T32b_ outside the bundles). `glueOutputs_of_leaves` ignores its arguments, so no glue step type-checks against a placeholder.
- Import plan: the report files import kernel modules (`ZInQKernel.HDecomp.A6.A6`, `.Objects`, `.C10.C10`) whose namespaces (`PkgI2`, `PkgI3`, `ObjBridge`, `GlueC10`) are also defined in Leaves.lean, so they cannot be imported there; their bodies are copied (scratch/leaf-adopt/fold.py).
- run1 (fold.py inserted T32a.lean, QMLeaves.lean, ModCurveLeaves.lean, Faltings.lean bodies; one rename GlueA6Alg.goodReduction_of_QM_rational3' -> PkgI2.goodReduction_of_QM_rational3'): 0 errors, one sorry (glueOutputs_of_leaves), 3m29s wall. 19104 lines.
- run2/run3 (HSyn §2-§3 edited by hand; section LeafAdoptSec added): 0 errors, one `declaration uses sorry` (`HSyn.glueOutputs_of_leaves`), 3m13s wall (run3), 19.2k lines. All new `#print axioms` (t32a_glue, t32b_glue, leafB3a_glue, LeafAdopt.r2X6PropsIff_of, cmExists_of_iff, R1R2fp_of_rep, R5fp_iff_R5fpStrong, abVarEquiv_dim, and the adopted glue of the four reports): [propext, Classical.choice, Quot.sound]; only HSyn.sixContactMin_of_leaves has sorryAx.
- Diff of each copied section against its source (python difflib): T32a: only header; QMLeaves: header + the rename (2 lines) + closing `end`; ModCurveLeaves: header + two docstrings (MC9 -> citation chain, M1) + closing `end`; Faltings: header only. Dropped LeafPush blocks of T32a.lean: bodies identical to Leaves.lean's LeafPush (checked).

## Changes to the bundles (HSyn §2-§3)
- Removed placeholders: R01_ShimuraDeligne, R02_BabaGranath, R05_GonzalezRotger, R16_EichlerShimuraJ1, R19_GaudronRemond, R20_FaltingsHeightLemma, R21_Bost.
- New placeholder: R01b_ComplexUniformization (R1(b), family form, Q3).
- ResearchLeaves: r1r2 : LeafAdopt.R1R2fpRep (Q4 + Q5 repaired R1R2fp); r1an : R01b (placeholder); r1rec : LeafQM.AV.R1rec; r5 : LeafQM.AV.R5fp (= R5fpStrong, proved iff); r5count : LeafQM.AV.R5fpCount; r16 : LeafModCurves.R16_EichlerShimuraJ1'; r19-r21 : ZInQ.DefFaltings.R19_GaudronRemond, R20_FaltingsLemma5, R21_Bost; h5 : LeafAdopt.H5 (new leaf, F2).
- TextbookLeaves: t32a, t32b removed (now theorems HSyn.t32a_glue, t32b_glue); t33 : LeafModCurves.JacobianExists ℚ, t34 : LeafModCurves.DimJ1Genus added.
- Glue: no glue step consumed the removed placeholders (glueOutputs_of_leaves ignores its arguments), so no glue changed. X1ModelExists is a glue target (unproved), not put in the leaf bundle.

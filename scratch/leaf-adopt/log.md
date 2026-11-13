# leaf-adopt results log

## 2026-11-12 19:4x  baseline
- `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` (needed first; JHeight imports package `ZInQ`): OK.
- Baseline `lake env lean scratch/h-decomposition/Leaves.lean` (8512506d): 0 errors, one `declaration uses sorry` (L12366, `HSyn.glueOutputs_of_leaves`), 2m02s wall.
- Placeholders used only in the bundles `ResearchLeaves`, `TextbookLeaves` (grep: no other use of R01_/R02_/R05_/R16_/R19_-R21_, T32a_/T32b_ outside the bundles). `glueOutputs_of_leaves` ignores its arguments, so no glue step type-checks against a placeholder.
- Import plan: the report files import kernel modules (`ZInQKernel.HDecomp.A6.A6`, `.Objects`, `.C10.C10`) whose namespaces (`PkgI2`, `PkgI3`, `ObjBridge`, `GlueC10`) are also defined in Leaves.lean, so they cannot be imported there; their bodies are copied (scratch/leaf-adopt/fold.py).
- run1 (fold.py inserted T32a.lean, QMLeaves.lean, ModCurveLeaves.lean, Faltings.lean bodies; one rename GlueA6Alg.goodReduction_of_QM_rational3' -> PkgI2.goodReduction_of_QM_rational3'): 0 errors, one sorry (glueOutputs_of_leaves), 3m29s wall. 19104 lines.

# t25-newform results log

## Step 0. Setup
- merged origin/main into wip/t25-newform (32f021cc). VERIFIED.
- Leaf T25 `PkgI4.NewformOfEigenform` is stated in ZInQKernel/HDecomp/ModCurves/C9.lean:384
  (also scratch/h-decomposition/Leaves.lean:4592); its defs `CF`, `coeff`, `HasNebentypus`,
  `IsNormalizedEigenform`, `oldSpace`, `IsNewform` are in ZInQKernel/HDecomp/Conductor/LadicCond.lean
  (namespace PkgI4). VERIFIED (read).

## Step 1. Vendoring
- closure of TauCeti.NumberTheory.ModularForms.Newforms.Decomposition at ~/tc-oct16: 216 modules,
  204 new (list: vendor-new.txt). Added Newforms.FullEigenform (Newform.toEigenform: newforms are
  eigen at the bad primes too, needed for the leaf's IsNormalizedEigenform at all m, n): 205 new.
  VERIFIED.
- One fix: ModularForms/Basic.lean, `IsSMulApply R (ModularForm Γ k)` → explicit
  `... UpperHalfPlane ℂ` (Mathlib 56a00585 makes α β explicit outParams), 3 places. VERIFIED.
- `lake build ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform`:
  Build completed successfully (4197 jobs). VERIFIED (compiled).

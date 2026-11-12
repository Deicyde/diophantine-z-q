# loc-fix results log

## Step 1-2 (Lean side), 2026-11-12
- scratch/rv-loc-leaves/patch_leaves.py applied to scratch/h-decomposition/Leaves.lean (unchanged since
  6988c7fe): 16 edits, output byte-identical to scratch/rv-loc-leaves/LeavesPatched.lean (VERIFIED, diff).
- scratch/loc-fix/t27_fix.py applied to ZInQKernel/HDecomp/Objects.lean and Leaves.lean:
  - PkgI3: old `QMDichotomy` (no "indefinite") removed; `QuatIndefinite`, `QMDichotomyYu` (dated docstring),
    `quatIndefinite_two_neg_three`, `qmDichotomy_B6` (old conclusion at B = (2,-3) from Yu + indefiniteness).
  - `qmDichotomyYu_of_qmDichotomy` removed from Leaves.lean (its hypothesis no longer exists).
  - ObjBridge: `QMDichotomy`, `qmDichotomy_iff` replaced by `QMDichotomyYu`, `qmDichotomyYu_iff`;
    both `I3Leaves` fields and `i3Leaves_iff` switched; HSyn bundle field `t27 : PkgI3.QMDichotomyYu` (patch).
  - Consumers of the leaf in ZInQKernel and Leaves.lean: only the `I3Leaves` structures, `i3Leaves_iff`, the
    HSyn bundle (VERIFIED by grep).
- Docstrings: HDecomp/Repo/PRArith.lean (A2 source of (4,6,2)); Leaves.lean R03 (Example 30 → v1 Example 29),
  dated notes on R2/R5/R16/R17/R22; LadicCond.lean CarayolR17, CarayolR17'.

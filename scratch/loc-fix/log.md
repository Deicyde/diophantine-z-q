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

## Step 2-3 (notes), 2026-11-12
- h-decomposition.md: R2, R5 replaced by rv-nocm §3.2/§3.1 exact texts (history kept); §0 items 2, 5; T27 row
  (Lean `PkgI3.QMDichotomyYu`); §6 R1/R2 update notes; R16, R17, R22 adoption notes (rv-loc-leaves (j), (f), (c)).
- glue-repo.md: rows L2, L14, A10 count row + case-split row (rv-nocm §3.1 inserted sentence), PR(i) paragraph.
- hdec-elementary.md (A2, L2(a) note, L2 ref, L3(i), L2 row of the leaf list), hdec-faithful.md (A2, L2, L3 ref, L5),
  hdec-alt.md (A2, L1, L27).
- h-trust.md: A2 Content (rv-nocm text) + review note; A5 review note; A10 supplier count + review note with the
  `D(R) ≠ 1` sentence; history item "Example 30".
- pkg-I1, rv-leaves-a, wk-h, h-v14, h-b1 (M4 = rv-nocm text), tyz-t1 (Lemma 3.8 → 3.14, 6 places): header notes.
- TYZ numbering VERIFIED by environment count in Period7.tex §3: char' = Lemma 3.14 (L1868), multiples1 = 3.15 (L1919).
- scripts/print_axioms.lean: +2 entries (ObjBridge.qmDichotomyYu_iff, PkgI3.qmDichotomy_B6): 180 → 182.

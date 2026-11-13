# gz-decomp results log

Base: wip/tc-port 443ece10 + `git merge origin/main` (ee3e746f).

## Step 0: vendoring (2026-11-13 04:40-05:00 PST)
- Module list `scratch/gz-decomp/tc-modules.txt`: oct16 import closure of
  `ModularForms.LFunction.Sign`, `ModularForms.Twist.Basic`, `EllipticCurve.CanonicalHeight.Basic`,
  `EllipticCurve.MordellWeil.NaiveHeight`, `EllipticCurve.GaloisDescent` (257 modules; 243 new,
  14 already vendored). Copied by `tcport.py ~/tc-oct16` (commit 5a01f5fe3621).
- Port fixes (2 files, Mathlib 56a00585):
  - `ModularForms/Basic.lean` L342, L394, L431: `IsSMulApply R (ModularForm Γ k)` → explicit
    `… ℍ ℂ` outParams (same fix as tc-port 312eaee4).
  - `ModularForms/LFunction/Sign.lean` L137-141: `ModularForm.L_apply_of_ne_zero` does not exist
    at our Mathlib; replaced by unfolding `ModularForm.L` (= `Λ · 2/Γ_ℂ`).
- `lake build` of the five roots: success (4151 jobs), no `sorry` warning. VERIFIED.

## Step 1: scope
- Uses of `Literature.GrossZagier` (git grep): `CR3Literature.lean:110`
  (`certifiedRankTYZClRk_of_literature`, applies it to `shortCurve (-(d:ℚ)^2)`, `d % 8 = 5`,
  squarefree, only), `MainLiterature.lean` (passes it to that theorem), `GaussFE/Headline.lean`,
  `HeckeFE/Basic.lean:2186, 2760` (pass it to `certifiedRankTYZClRk_of_literature`),
  scratch copies. VERIFIED by reading: every use is at `C_d`, `d ≡ 5 (8)` squarefree.
- `scratch/gz-decomp/Scope.lean` compiles (`lake env lean`). Axioms of
  `frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagierCd`,
  `frozenTarget_of_sixContactMin_tyzInputs_grossZagierCd`, `grossZagierCd_of_grossZagier`:
  [propext, Classical.choice, Quot.sound]. VERIFIED.

## Steps 2-3: leaves, glue, assembly (`scratch/gz-decomp/Decomp.lean`)
- Compiles with `lake env lean` (7 s). Objects: TC `HeckeRing.GL2.Newform`, `Newform.frickeSign`,
  Mathlib `qExpansion`, `LSeries`, `jacobiSym`, `Affine.Point.map`, `AdjoinRoot`.
- Leaves stated: `HeckeThetaNewform` (L1), `FHNonvanishing` (L2), `GrossZagierHeegner` (L3).
- Glue proved: `modular_cd` (G1), `isEntireCont_of_isLContinuation` (G2),
  `exists_rat_point_of_heegner` (G4, with TC `exists_baseChange_eq_of_map_eq`),
  `exists_quadratic_field` (G5, `AdjoinRoot (X² − D)`), `grossZagierCd_of_leaves` (G0 assembly).
- Glue open: `SignOfSimpleZero` (G3), hypothesis of the assembly.
- `#print axioms grossZagierCd_of_leaves`, `modular_cd`, `exists_rat_point_of_heegner`:
  [propext, Classical.choice, Quot.sound]. VERIFIED.

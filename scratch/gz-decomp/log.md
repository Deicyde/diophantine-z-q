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
- (G3) `signOfSimpleZero : SignOfSimpleZero` PROVED (TC `Newform.frickeCompletedL_sub_eq`,
  `I_zpow_mul_frickeSign_eq_one_or_neg_one`, `frickeCompletedL_eq_cpow_mul_Λ`,
  `CuspForm.eq_strictWidthInfty_cpow_mul_L`; Mathlib `differentiable_Gammaℂ_inv`).
- `grossZagierCd_of_leaves' (hL1 : HeckeThetaNewform) (hL2 : FHNonvanishing)
  (hL3 : GrossZagierHeegner) : GrossZagierCd`: axioms [propext, Classical.choice, Quot.sound].
  VERIFIED (lake env lean, 2026-11-13 ~06:00 PST).

## Move to Contrib modules
- `ZInQKernel/Contrib/GZDecomp/Scope.lean`, `ZInQKernel/Contrib/GZDecomp/Decomp.lean` (new files;
  the scratch drafts are replaced by `scratch/gz-decomp/Check.lean`, which imports them).
- `lake build ZInQKernel.Contrib.GZDecomp.Decomp`: success (10109 jobs). `lake env lean
  scratch/gz-decomp/Check.lean`: every listed declaration depends on
  [propext, Classical.choice, Quot.sound]. VERIFIED.
- New: `frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves (hH : SixContactMin)
  (hA : TYZThm35ReadingA) (hL1 : HeckeThetaNewform) (hL2 : FHNonvanishing)
  (hL3 : GrossZagierHeegner) : FrozenTarget`.

## Numerical checks
- `check_chiD.py` (pure Python): `jacobi(n, |D|) = kronecker(D, n)` for 30 odd fundamental
  `D ∈ [−199, −7]`, `n ≤ 200` (6000 pairs), and `jacobi(2, |D|) = 1 ⇔ D ≡ 1 (8)`: 0 mismatches.
  VERIFIED (`out_check_chiD.txt`).
- PARI checks (conductor, root number, twist ranks) BLOCKED: `~/pyenv/bin/python` does not exist
  on this host, `cypari2` is not in the uv cache, and network installs are not allowed. Earlier
  evidence reused: rv-cr3-trust §2.1 (`N(C_d) = 32d²` and `ε(C_d) = −1` on 30 values; a Heegner `D`
  with `L(C_d^D, 1) ≠ 0`, `|D| ≤ 455`, for 16 values; `out_indep_check.txt`).

## Report
- `docs/research/gz-decomp.md` written (main result, leaf/glue tables, scope answer, review).
- Review item: nebentypus of L1 checked by hand from `HeckeFE/Basic.lean:443-475`
  (`unitOf(α mod 4)·α` = primary associate; `ψ_d((m)) = χ_{−4}(m) m`; Miyake's character
  `χ_{−4}ω_ψ` trivial). VERIFIED by reading.
- TC `cuspFormsNew` = Petersson orthogonal complement of the level raises (`Newforms/Basic.lean:105,
  202`). VERIFIED by reading.
- tc-main: `ModularCurve/Gamma/Zero.lean` (moduli problem `[Γ₀(N)]`), no coarse `X₀(N)`; lattice
  theta series only (`ModularForms/ThetaSeries/`); no Gross–Zagier/Waldspurger/Friedberg–Hoffstein
  (grep). VERIFIED.

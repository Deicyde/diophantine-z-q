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
- Also vendored HeckeSlash.Nebentypus.CoefficientFormula (divisor-sum formula for a_m(T_n F));
  its closure adds no other module. Builds. VERIFIED. Total vendored: 206 modules.

## Step 2. Bridge (ZInQKernel/Contrib/T25/Bridge.lean) — compiles, no sorry. VERIFIED.
- Leaf's `CF N k` = `CuspForm ((Gamma1 N).map (mapGL ℝ)) k` (Mathlib's `Coe` is `map (mapGL ℝ)`),
  i.e. Tau Ceti's type: no coercion bridge needed. VERIFIED (compiled).
- SL(2,ℤ) slash = slash by `mapGL ℝ γ` (`ModularForm.SL_slash` + rfl). VERIFIED.
- HasNebentypus f χ ⇒ f ∈ cuspFormCharSpace k (MulChar.toUnitHom χ); and conversely
  cuspFormCharSpace k χ₀ ⇒ HasNebentypus f (MulChar.ofUnitHom χ₀), via TC
  `mem_cuspFormCharSpace_iff_nebentypus` (Gamma0Map = lower-right entry, same convention as leaf).
  VERIFIED.
- IsNormalizedEigenform g χ ⇒ T_p g = a_p(g) g for p ∤ M (TC
  heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul). VERIFIED.
- Newform f (TC) ⇒ a_m a_n = Σ_{d|(m,n)} χ_f(d) d^{k-1} a_{mn/d²} for all m, n ≥ 1 (TC
  Newform.toEigenform + qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0). VERIFIED.
- leaf `oldSpace N k` ≤ image of TC `cuspFormsOld N k` (generators τ ↦ f(dτ) are levelRaise d f;
  leaf's (M<N, d*M|N) = TC's (M≠N, d*M|N)); with TC disjoint_cuspFormsOld_cuspFormsNew a nonzero
  TC newform is not in the leaf's oldSpace. VERIFIED.
- Notion comparison: TC Newform = nonzero, a₁=1, in Petersson-orthogonal complement of
  cuspFormsOld, good-prime eigen; leaf IsNewform = full coefficient identities + not in oldSpace.
  TC newform ⇒ leaf newform (proved above). No statement change needed. VERIFIED.

## Step 3. Leaf closed (ZInQKernel/Contrib/T25/NewformOfEigenform.lean). VERIFIED.
- `theorem T25.newformOfEigenform_leaf : PkgI4.NewformOfEigenform` (imports C9.lean for the leaf def).
- `lake build ZInQKernel.Contrib.T25.NewformOfEigenform`: Build completed successfully (9277 jobs).
- #print axioms (scratch/t25-newform/Axioms.lean, output axioms-out.txt): every theorem
  depends on [propext, Classical.choice, Quot.sound]. VERIFIED.

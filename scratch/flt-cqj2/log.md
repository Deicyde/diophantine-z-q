# flt-cqj2 results log

## 2026-11-15 03:30 PST setup
- Fresh start (no earlier log). Base 0d8105c7. Build tree: reflink copy of ~/dzq-wt/flt-cqj/.lake/build and lean/.lake/build.
- FLT source: ~/flt-src (read-only, 6e837e75 per task; toolchain v4.33.1, Mathlib db584cd6). VERIFIED (lakefile, lean-toolchain).
- Import cone of Theorems.Thm_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j
  (scratch/flt-cqj2/tools/cone.py, cone.json): 661 FLT modules + P2M.Util. 247 of them already vendored by Cloud Worker 14
  (SOURCE_MANIFEST.json); 414 new (new_modules.txt, topological order). VERIFIED.
- The MapsTo half has no smaller cone in FLT's proof: P2M/Sol/S_..._of_transcendental_j.lean proves the bijection by
  induction on N (bijOn_one, bijOn_step via bijOn_core for N = ℓM), using injectivity/counting at level M to get MapsTo at
  level ℓM. The heaviest import is Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j
  (461-module cone, 294 not yet vendored), needed already for prime N. So the full cone is ported. VERIFIED (read).
- tools/port.py copies each module into ZInQKernel/Contrib/CloudB2X0Transitive/Vendor/AnthropicFLT/<same path>, relocating
  imports, adding a 'Modified for the Z-in-Q kernel' header and the upstream lakefile options (maxHeartbeats 4000000,
  synthInstance.maxHeartbeats 400000, backward.isDefEq.respectTransparency.types false, autoImplicit false) as set_option lines.

## 2026-11-15 03:35-05:00 port builds (lake build of the Thm module; logs build1..4.log)
- build1: 240 of 414 new modules built, 11 failed. build2/3: fixes, new failures in modules unblocked. build4:
  `Build completed successfully (9708 jobs)` for
  ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j.
  VERIFIED. No 'declaration uses sorry' in any build log; no sorry/axiom/native_decide/extern/implemented_by in the 414 files (grep). VERIFIED.
- Port changes (each marked `-- [port]` in the file), all forced by Lean/Mathlib v4.33 → v4.35:
  1. `Finsupp.mapDomain_apply` (injective form) → `Finsupp.mapDomain_apply_of_injective` (Def_Compat_Mathlib430, Def_AlgebraicCurve_BaseChangeGalois,
     Def_ModularCurve_CharLFrobeniusGeomLevel, 2 S_ velu_map_equation files).
  2. `ModularForm.translate`/`CuspForm.translate` moved to Mathlib.NumberTheory.ModularForms.NormTrace (import added; S_ModularForm_exists_degeneracy_Gamma0).
  3. `Ideal.inertiaDeg'` moved to Mathlib.NumberTheory.RamificationInertia.Inertia (import added; S_AlgebraicCurve_relNorm_eq_pow_...).
  4. `List.TFAE.out` 1-indexed: `.out 0 4` → `.out 1 5` (S_..._CoordinateRing_isDedekindDomain).
  5. `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := _)` → `..._under` (3 files).
  6. `Ideal.eq_bot_of_comap_eq_bot` now states its hypothesis with `Ideal.under`: `rw [Ideal.under_def, ...]` (14 occurrences, 13 files).
  7. `Int.subgroup_cyclic` restated as `IsAddCyclic H`: the v4.33 form re-proved locally as `int_subgroup_cyclic_port` (S_PeriodPair_exists_mem_primCosetReps...).
  8. `(W.map f).IsElliptic` instance not found by `infer_instance` after dsimp: named `WeierstrassCurve.instIsEllipticMap` (Def_EllipticCurve_FunctionFieldPullback).
  9. `IsDedekindDomainDvr` removed: `isDedekindDomain_iff_isDiscreteValuationRing_atPrime` (S_..._CoordinateRing_isDedekindDomain).
  10. auto-generated instance names changed: the 3 instances of Def_WeierstrassCurve_FunctionFieldQuadratic given their v4.33 names explicitly
      (`inst..._definitions`, referenced by `attribute [-instance]` downstream).
  11. tensor-product `induction_eliminator` lost its `zero` case: `induction t using TensorProduct.induction_on with` (5 files).
  12. `continuous_add_right` → `continuous_add_const` (S_PeriodPair_exists_differentiable_toPoint_...).
  No statement of any declaration changed (all changes inside proofs, imports, or instance names).

## 2026-11-15 04:08-04:20 Tau Ceti clash
- `lake build ZInQKernel.Contrib.OneProof.ModularEquationGeneric` (new file: cyclicQuotientJBijOn_proof, modularEquationGeneric_proof,
  x0Transitive_proof) failed: `import ...Def_WeierstrassCurve_EDSEngine failed, environment already contains
  'WeierstrassCurve.Coeff.ctorIdx' from ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Universal` (build5.log). VERIFIED.
  (ModularEquation.lean imports RLeaf.T36Torsion, which imports Tau Ceti.)
- clash/DumpFLT.lean, clash/DumpMain.lean (Main + ModularEquation): 70 constants of the new vendored modules are also in Main's closure
  (clash/clashes.txt), all from Tau Ceti; 24 user-level names (the rest: constructors/recursors of `WeierstrassCurve.Coeff`, and two
  `congr_simp` lemmas `QuotientAddGroup.map.congr_simp`, `WeierstrassCurve.Jacobian.Point.fromAffine.congr_simp`). VERIFIED.
  Defining modules: Def_WeierstrassCurve_EDSEngine (19 names, an FLT copy of Tau Ceti's EDS / universal-curve code),
  Def_EllipticCurve_FunctionFieldPullback (5), Thm_WeierstrassCurve_Affine_CoordinateRing_XYIdeal_ne_bot (1).
- tools/rename_clash.py: token rename `t` → `t_aflt` of the 24 last components in the 414 new files (75 files changed; header line
  `[port] Tau Ceti name clash: renamed ...` in each). A wrong rename cannot change meaning silently (fresh names fail to elaborate).
- One follow-on: the auto-generated instance name `WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve`
  (referenced by name downstream) changed with `Coeff`; given its old name explicitly (`-- [port]`, EDSEngine) (build6.log).

## 2026-11-15 04:16-04:29 ModularEquationGeneric proved
- build7.log: `lake build ZInQKernel.Contrib.OneProof.ModularEquationGeneric` → `Build completed successfully (9990 jobs)`; no
  'declaration uses sorry'. VERIFIED.
- Statement.lean (verbatim copies of CyclicQuotientJBijOn, X0Transitive, ModularEquationGeneric, each `Iff.rfl` against the constant;
  copies proved): compiles; `#print axioms` of all three proofs: [propext, Classical.choice, Quot.sound] (Statement-output.txt). VERIFIED.
- Vendor/AnthropicFLT/NOTICE (upstream NOTICE + 'Modified for the Z-in-Q kernel' paragraph) and SOURCE_MANIFEST.flt-cqj2.json
  (414 modules, upstream path + sha256 of the ~/flt-src file) added.

## 2026-11-15 04:30-04:45 checks and fold
- DischargesCheck.lean (Main + Discharges + new module): compiles (so no clash with Main left); "65 open hypotheses, 1203 theorems
  checked, 3 discharge one" (the three pre-existing ones; none from this file: no open field has type X0Transitive/ModularEquationGeneric;
  igusaGL2 is the stronger IgusaGL2). VERIFIED.
- FoldProved.lean = gen_bypass.py mode `proved` + fold_check.part: compiles; `frozenTarget_cqj2` and `sixContactMin_of_open26_cqj`:
  [propext, Classical.choice, Quot.sound]; OpenTextbookLeavesKCqj fields = original minus igusaGL2, same types (K=7..11: 19/20,
  16/17, 14/15, 13/14, 12/13); signatures of frozenTarget and frozenTarget_cqj2 printed: equal except t's bundle. VERIFIED.
- FoldBypassModEq.lean regenerated by the copied generator: identical to scratch/flt-cqj/FoldBypassModEq.lean. VERIFIED.
- audit_diff.py over the 414 files vs ~/flt-src: import 1806, set_option 1656, `_aflt`-rename 1326, [port]-block 94, other 21 (two
  upstream copyright comments moved after the vendoring header). No statement change except the rename. VERIFIED.
- grep of the 414 files for sorry/axiom/native_decide/extern/implemented_by (whole word): no hits. VERIFIED.

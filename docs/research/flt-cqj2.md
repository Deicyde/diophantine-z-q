# flt-cqj2: FLT's cyclic-quotient bijection ported; the modular equation and `X0Transitive` proved

## Main result

1. **`FltCqj.ModularEquationGeneric` is proved, with standard axioms only.** The proof is in
   `ZInQKernel/Contrib/OneProof/ModularEquationGeneric.lean`, in namespace `FltCqj2`:
   * `cyclicQuotientJBijOn_proof : ZInQ.Contrib.CloudB2X0Transitive.CyclicQuotientJBijOn`. This is Anthropic FLT's
     `WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j` at universe 0.
   * `modularEquationGeneric_proof : FltCqj.ModularEquationGeneric`, the `MapsTo` half, obtained through
     flt-cqj's `modularEquationGeneric_of_bijOn`.
   * `x0Transitive_proof : ZInQ.RLeaf.X0Transitive` (row H-41), obtained through flt-cqj's
     `x0Transitive_of_modularEquationGeneric`.

   `#print axioms` on each of the three gives `[propext, Classical.choice, Quot.sound]`. They were checked on
   verbatim copies of the three statements, each matched to its constant by `Iff.rfl`
   (`scratch/flt-cqj2/Statement.lean`, output in `Statement-output.txt`). VERIFIED.
2. **Igusa's theorem leaves the single proof, and no leaf replaces it.** The fold is
   `scratch/flt-cqj2/FoldProved.lean`, written by `gen_bypass.py … proved` with the check `fold_check.part`
   appended. It is the bypass fold of flt-cqj, except that the field `igusaGL2 : ZInQ.RLeaf.IgusaGL2` is deleted
   from the textbook bundles of generations 7–11 instead of being replaced by a leaf. Its one consumer, the field
   `x0Transitive` of `OpenTextbookLeaves6`, is filled by `FltCqj2.x0Transitive_proof`.
   * It compiles against `ZInQKernel.OneProof.Main`.
   * `frozenTarget_cqj2 : ZInQ.FrozenTarget` takes exactly the binders of `ZInQ.OneProof.frozenTarget`, except that
     `t` has type `OpenTextbookLeaves11Cqj` instead of `OpenTextbookLeaves11`. Both signatures are printed in
     `FoldProved-output.txt`.
   * A metaprogram in the same file checks every copied bundle `OpenTextbookLeavesKCqj` (K = 7..11): its fields
     are the original's in the same order, minus `igusaGL2`, with the same types (19/20, 16/17, 14/15, 13/14 and
     12/13 fields).
   * `#print axioms frozenTarget_cqj2` gives the standard three. VERIFIED.

   **Effect on the counts:** one fewer published LEAF (Igusa 1959, row `igusaGL2`), no new leaf, no new GLUE.
3. **The port.** The import cone of the FLT theorem is 661 FLT modules plus `P2M.Util`. Cloud Worker 14 had
   vendored 247 of them. This task ported the other 414 from `~/flt-src` (6e837e75, Lean 4.33.1, Mathlib db584cd6)
   to Lean 4.35.0 / Mathlib v4.35.0, under `ZInQKernel/Contrib/CloudB2X0Transitive/Vendor/AnthropicFLT/`, keeping
   the upstream paths. All 414 build. No module failed to port. The `MapsTo` half has no smaller cone (§2).
   VERIFIED.

## 1. What changed in the vendored files

Every one of the 414 files carries a header naming the upstream module and the commit, followed by the line
"Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2)". The changes:

* **Imports relocated.** Each import points to its local copy. `P2M.Util` is the copy that Cloud Worker 2
  published under `CloudW02Connectedness`.
* **Lakefile options as `set_option` lines.** The upstream lakefile options are set at the top of each file:
  * `maxHeartbeats 4000000`
  * `synthInstance.maxHeartbeats 400000`
  * `backward.isDefEq.respectTransparency.types false`
  * `autoImplicit false`
* **Twelve kinds of Lean/Mathlib API change, each marked `-- [port]`, all inside proofs, imports or instance
  names.** They are listed in `scratch/flt-cqj2/log.md`, section "port builds":
  * `Finsupp.mapDomain_apply` became `Finsupp.mapDomain_apply_of_injective`.
  * `ModularForm.translate` moved to another module, and so did `Ideal.inertiaDeg'`.
  * `List.TFAE.out` is now 1-indexed.
  * `isMaximal_of_isIntegral_of_isMaximal_comap` became `…_under`.
  * `Ideal.eq_bot_of_comap_eq_bot` now states its hypothesis with `Ideal.under` (14 sites).
  * `Int.subgroup_cyclic` is restated; the old form is re-proved locally.
  * A `(W.map f).IsElliptic` instance is now passed by name.
  * `IsDedekindDomainDvr` was removed; the proof uses `isDedekindDomain_iff_isDiscreteValuationRing_atPrime`.
  * Three auto-generated instance names changed in Lean 4.35; the old names are now given explicitly.
  * The tensor-product `induction_eliminator` lost its `zero` case (5 sites).
  * `continuous_add_right` became `continuous_add_const`.
* **The Tau Ceti clash: 24 names renamed with the suffix `_aflt`.**
  * The first build of the deliverable failed with `environment already contains 'WeierstrassCurve.Coeff.ctorIdx'
    from ZInQKernel.Contrib.TauCeti…Universal` (`build5.log`). `ModularEquation.lean` imports Tau Ceti through
    T36.
  * Dumping the constants of the vendored tree and of `Main` + `ModularEquation` (`scratch/flt-cqj2/clash/`)
    gives 70 shared constants (`clash/clashes.txt`), all from Tau Ceti. They come down to 24 user-level names in
    three modules:
    * `Def_WeierstrassCurve_EDSEngine`, FLT's copy of Tau Ceti's EDS / universal-curve code: `Coeff`,
      `addXYZ_smulEval`, `cusp`, `dblXYZ_smulEval`, `invar`, `map_invar`, `map_specialize`, `map_ψc`,
      `preΨ₄_add_Ψ₂Sq_sq`, `preΨ₄_add_ψ₂_pow_four`, `smulEval`, `specialize`, `φ_mul_ψ`, `ψc`, `ψc_neg`,
      `normEDS_mul_complEDS`, `normEDS_mul_complEDS_div`, `universalNormEDS_ne_zero`.
    * `Def_EllipticCurve_FunctionFieldPullback`: `XYIdeal_isMaximal`, `genericPoint`, `genericX`, `genericY`,
      `infinite_point`.
    * `Thm_…XYIdeal_ne_bot`: `XYIdeal_ne_bot`.
  * `scratch/flt-cqj2/tools/rename_clash.py` renames the last name component token by token in the 414 files
    (75 files changed; each names its renames in its header). A wrong rename cannot change meaning silently,
    because the new names are fresh and would fail to elaborate.
  * One follow-on fix: the auto-generated instance name
    `WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve` contains `Coeff`
    and is referred to downstream, so it is now given explicitly (`-- [port]`).
  * The two shared `congr_simp` lemmas did not block the import.
  * After the rename, `Main` + the deliverable import together without error (`DischargesCheck.lean` compiles).
* **Diff audit** (`tools/audit_diff.py`, output in `audit_diff-output.txt`). Every line that differs from the
  `~/flt-src` file was classified:
  * 1806 import lines;
  * 1656 `set_option` lines;
  * 1326 lines equal to upstream once `_aflt` is deleted;
  * 94 lines inside `[port]`-marked blocks;
  * 21 other lines, all from two files whose upstream copyright comment now follows the vendoring header
    (moved, not changed).

  No declaration statement changed except by the `_aflt` rename. VERIFIED.
* **Licence files.** `Vendor/AnthropicFLT/LICENSE` is unchanged (Apache-2.0, byte-identical to upstream).
  * New file `Vendor/AnthropicFLT/NOTICE`: upstream's NOTICE followed by a "Modified for the Z-in-Q kernel"
    paragraph.
  * `NOTICE.upstream` and `ATTRIBUTION.upstream.md` are kept.
  * New file `SOURCE_MANIFEST.flt-cqj2.json`: the 414 modules, each with its upstream path and sha256.
  * The source is untrusted input: `grep` finds no `sorry`, `axiom`, `native_decide`, `extern` or
    `implemented_by` in the 414 files, and no build log has "declaration uses sorry". VERIFIED.

## 2. Why the whole cone and not a "MapsTo-only" sub-cone

FLT proves the bijection by induction on `N` (`P2M/Sol/S_WeierstrassCurve_bijOn_…_of_transcendental_j.lean`:
`bijOn_one`, and `bijOn_step` through `bijOn_core` for `N = ℓM`). The `MapsTo` half at level `ℓM` uses
injectivity and the counting at level `M`. Its heaviest import,
`Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j` (a 461-module cone), is needed even
for prime `N`. So the `MapsTo` half does not have a smaller cone. VERIFIED (read).

## 3. Checks (all VERIFIED)

| check | outcome |
|---|---|
| `lake build ZInQKernel.Contrib.OneProof.ModularEquationGeneric` (`build7.log`) | `Build completed successfully (9990 jobs)` |
| `Statement.lean`: three verbatim copies, `Iff.rfl`, proofs, `#print axioms` | `[propext, Classical.choice, Quot.sound]` ×3 |
| `DischargesCheck.lean` (`Main` + `Discharges` + the new module), `#discharges` | "65 open hypotheses, 1203 theorems checked, 3 discharge one"; none of the 3 comes from this file (see §4) |
| `FoldProved.lean` (imports `Main` + the new module) | compiles; `frozenTarget_cqj2` standard axioms; bundle field check passes |

## 4. For the integrator (deliverable notes)

* **`#discharges` output.** None of the three theorems discharges an open hypothesis directly. This is expected:
  the open field is `OpenTextbookLeaves11.igusaGL2 : ZInQ.RLeaf.IgusaGL2`, which is Igusa's full
  `GL₂(ℤ/N)` image. That is strictly stronger than `X0Transitive`, and the chain uses it only to fill
  `x0Transitive` (flt-cqj §Verdict 2). So `autofold.py` cannot fold this contribution, since it fills a field
  only with a term of that field's type.
* **The fold is a bundle generation without `igusaGL2`, i.e. `FoldProved.lean`.**
  * Its 48 copied declarations (suffix `_cqj`, structures `OpenTextbookLeavesKCqj`) become the new TailZ
    module.
  * `textbookLeaves6_of_open7` gets `x0Transitive := FltCqj2.x0Transitive_proof`.
  * **Main.lean edit:** `frozenTarget` switches to the body of `frozenTarget_cqj2`, which is the same except
    that `t : OpenTextbookLeaves11Cqj` and `sixContactMin_of_open26_cqj` are used. No top-level hypothesis is
    added or removed. One bundle field (`igusaGL2`) disappears.
  * OPEN.md row `igusaGL2` (T2–T3, LEAF): closed by proof. No new printed leaf.
* `Main` would import `ZInQKernel.Contrib.OneProof.ModularEquationGeneric`, and through it the 661-module
  vendored cone: 9990 Lake jobs in this build, with Mathlib prebuilt. The renamed modules rebuilt in about
  13 minutes here. Several vendored solution files are large (up to about 9000 lines). They are vendored text,
  not contribution files, and the 150 KB guideline concerns the latter.

## 5. New leaves

None. `ModularEquationGeneric`, which flt-cqj introduced as a leaf candidate, is now proved, so the rating
question is moot.

## 6. Files

* `ZInQKernel/Contrib/OneProof/ModularEquationGeneric.lean` (new; the deliverable).
* `ZInQKernel/Contrib/CloudB2X0Transitive/Vendor/AnthropicFLT/`: 414 new modules, `NOTICE`,
  `SOURCE_MANIFEST.flt-cqj2.json`.
* `scratch/flt-cqj2/`:
  * `log.md`;
  * `tools/` (`cone.py`, `port.py`, `fix.py`, `errs.py`, `rename_clash.py`, `occ.py`, `audit_diff.py`);
  * `new_files.txt`, `new_modules.txt`, `cone.json`;
  * `clash/` (dumps and `clashes.txt`);
  * `Statement.lean`;
  * `DischargesCheck.lean`;
  * `gen_bypass.py` (flt-cqj's generator with mode `proved`), `fold_check.part`, `FoldProved.lean`,
    `FoldBypassModEq.lean` (identical to flt-cqj's);
  * the `*-output.txt` files and `build*.log`.

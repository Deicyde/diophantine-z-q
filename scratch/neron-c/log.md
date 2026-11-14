# neron-c results log

Base: 8ec80711 + merge of origin/wip/leaf-fold3 (f7951690). Targets: leaf-fold3 fields
`t3 : PkgI2.NeronMappingAbelianScheme.{0}` and `t41 : ZInQ.H5Neron.NeronModelExists`.

## T3 (I2-NMP)

- `ZInQKernel/Contrib/NeronC/NMPInjective.lean`: `lake env lean` exits 0, no sorry (VERIFIED, ~30 s).
  - `ext_of_isSchemeTheoreticallyDominant_of_isSeparated` (Mathlib-level; equalizer is a closed
    immersion with kernel ⊆ ker ι = ⊥, hence iso).
  - `pullback_map_injective` (base change along qc sch.-dominant `j`, flat source, separated target).
  - `isSchemeTheoreticallyDominant_spec_map` (Spec of injective map out of a reduced ring).
  - `neronMappingAbelianScheme_injective`: injective half of T3, proved.
  - `NeronMappingAbelianSchemeSurj` (LEAF, BLR §1.2 Prop. 8, UNVERIFIED locator): surjective half.
  - `neronMappingAbelianScheme_of_surj : NeronMappingAbelianSchemeSurj.{u} → PkgI2.NeronMappingAbelianScheme.{u}`.
  - all four `#print axioms`: [propext, Classical.choice, Quot.sound] (VERIFIED).

## T41 (Néron models exist)

- `ZInQKernel/Contrib/NeronC/NeronGroupAbstract.lean` (Mathlib only; compiles in ~2 s, VERIFIED):
  `grpObjOfNeron` (a `GrpObj` on `N` from bijections `Hom(Y,N) ≅ Hom(F Y, A)` for test objects `Y`
  in a class closed under `⊗` and containing `𝟙_`), `isMonHom_of_neron` (`e : F N ≅ A` is a
  homomorphism for `Functor.grpObjObj`, `F` monoidal). Axioms: standard three (VERIFIED).
- `ZInQKernel/Contrib/NeronC/NeronGroup.lean` (imports kernel `H5Neron`; VERIFIED compile):
  - `NeronSchemeModelExists` (LEAF: BLR §1.4 Thm 3 + §1.2 Def 1, scheme-level, no group law;
    locators UNVERIFIED) and `neronModelExists_of_scheme : NeronSchemeModelExists → ZInQ.H5Neron.NeronModelExists`.
  - `NeronSchemeExtensionExists` (LEAF: same, existence of extensions only) and
    `neronModelExists_of_extension`; uniqueness from `neron_extension_injective`
    (flat source, scheme-theoretically dominant `Spec L → Spec 𝓞_L`, separated target).
  - converses `neronSchemeModelExists_of_neronModelExists`, `neronSchemeExtensionExists_of_neronModelExists`.
  - all `#print axioms`: [propext, Classical.choice, Quot.sound] (VERIFIED).

## Single-file check

- `scratch/neron-c/assemble.py` writes `scratch/neron-c/Check.lean`: verbatim slices of the kernel
  defs of T3 and T41 in fresh namespaces; `t3_of_surj`, `t41_of_scheme`, `t41_of_extension`, `t3_iff`,
  `t41_iff` (Iff.rfl to the kernel constants). `lake env lean scratch/neron-c/Check.lean` exit 0,
  no sorry, all 9 `#print axioms` standard (output `scratch/neron-c/check_out.txt`; VERIFIED).
- `scratch/neron-c/py/verbatim_check.py`: T3, T41 and their dependencies (`IsAbelianScheme`,
  `GroupModel`, `genericFibre`, `GroupModel.IsNeronModel`, `AbVar`) occur verbatim in leaf-fold3's
  `Leaves3.lean`; T3, T41 verbatim in `Check.lean`: ALL OK (VERIFIED).
- Use of T3 in leaf-fold3: only `(hN L (Ow L v) 𝒜 ℬ).2` in `fExtendGen_of_nmp` (surjective half;
  VERIFIED by reading `scratch/leaf-fold3/olean/TailH.lean`).

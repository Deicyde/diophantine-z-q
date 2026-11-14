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

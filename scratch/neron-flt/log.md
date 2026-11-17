# neron-flt results log

## 2026-11-16 16:06 setup
- Fresh start. Base wip/neron-ext 901a0efd; merged origin/main (c1e4ed1b) cleanly. Build tree: reflink copy of
  ~/dzq-wt/neron-ext/.lake/build and lean/.lake/build.
- FLT source ~/flt-src @ 6e837e75 (Lean 4.33.1). Target theorem (VERIFIED, read):
  `GoodReductionJacobian.RelativeGroupLaw.exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing`
  (Theorems/Thm_...of_henselianLocalRing.lean). Hypotheses: `R` domain, `IsDiscreteValuationRing R`, `HenselianLocalRing R`
  (henselian, NOT strictly henselian; no hypothesis on the residue field), `K` fraction field, `AK → Spec K` with a
  `RelativeGroupLaw K gK` and `AbelianSchemePropertyBundle K gK` (smooth, proper, connected fibres, has a group law).
  Conclusion: `B → Spec R` with a commutative `RelativeGroupLaw`, `NeronModelPropertyBundle R K g` (smooth, separated,
  LFT, qc, and `genericFibreRestrict` bijective for every smooth `T → Spec R` in the same universe = BLR 1.2 Def. 1),
  and an isomorphism `e` of the generic fibre with `AK` respecting the group laws.
- Import closure: 577 FLT modules (scratch/neron-flt/closure.txt; tools/closure.py): 40 Definitions, 268 P2M.Sol,
  268 Theorems, P2M.Util. VERIFIED.
- Overlap with vendorings in the tree (by module name): 70 modules are in CloudW03NeronSurj/Vendor (wrapped in namespace
  ZInQ.Contrib.CloudW03NeronSurj.FLT, so not reusable by unwrapped code); P2M.Util is CloudW02's copy (reused); none in
  CloudB2X0Transitive or CloudB3W16Cartier. VERIFIED.
- Henselian is used (grep, VERIFIED) only in the group-law step
  (`exists_relativeGroupLaw_genericFibre_iso_nhds_twist_extension_of_catchesIndexOnePoints_of_henselianLocalRing_of_isCommutative`
  and its finite-étale-descent subtree: Hensel lifting of smooth points, finite étale local DVR extensions,
  `DescentAction.effective_of_finiteEtale`). The proper model (`exists_modelFamily_finite_catchesIndexOnePoints_of_isProper`)
  and smoothening (`exists_smooth_hom_isIso_genericFibre_lift_of_isIndexOneExtension`) take any DVR.

## 2026-11-16 16:15 port batch 1
- tools/port.py (flt-cqj2's, retargeted): 576 modules copied to ZInQKernel/Contrib/OneProof/NeronFLT/Vendor/AnthropicFLT/
  with header, relocated imports, upstream lakefile options as set_option lines. Original FLT namespaces kept (as the
  CloudB2/CloudW02 FLT vendorings do; FLT names are disjoint across its modules).
- build1 (lake build of the Thm module): 554 of 576 new modules built, 20 failed (build1.log). VERIFIED.
  * 8 failures are among the 70 modules CloudW03NeronSurj had already ported: their bodies replaced by CloudW03's
    Lean-4.35 versions with the namespace wrapper removed (tools/unwrap.py; marked `-- [port]`).
  * PresheafOfModules defs (PullbackMonoidal, InternalHom, ExteriorPower): Mathlib v4.35 moved the monoidal API to
    `PresheafOfModulesOfCommRing` (tools/fix.py renames + `open PresheafOfModulesOfCommRing`), and instance search no
    longer sees `CommRing ((T ⋙ forget₂ CommRingCat RingCat).obj X)`: `instanceSearchTypes false` flag (as Mathlib's
    own Presheaf/Monoidal.lean) and a file-local instance (tools/patch_pm.py). Two proof lines adjusted (`-- [port]`).
    The three files compile alone (lake env lean). VERIFIED.

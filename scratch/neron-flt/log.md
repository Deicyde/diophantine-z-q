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
- build2..5: remaining Lean 4.35 repairs (all `-- [port]`): TFAE `.out` 1-indexed (tools/tfae.py),
  `isMaximal_comap_of_isIntegral_of_isMaximal` → `isMaximal_under_...`, `isMaximal_of_isIntegral_of_isMaximal_comap`
  → `..._under`, `Ideal.bot_prime` → `Ideal.isPrime_bot`, `ULift.ext` implicit points, `MvPolynomial.coeff` is a
  projection, `PresheafOfModules.DifferentialsConstruction` → `PresheafOfModulesOfCommRing.…`, three trailing
  `rfl` removed (goal closed by `rw`), one `try simp only`, backward-compatibility flags
  (`backward.isDefEq.respectTransparency false`, `backward.defeqAttrib.useBackward true`, `…instanceSearchTypes false`)
  in the files that needed them, file-local `CommRing ((T ⋙ forget₂ CommRingCat RingCat).obj X)` instances.
- build5: `Build completed successfully (9623 jobs)` for the FLT target theorem's module. VERIFIED. No `sorry`
  in any vendored source (grep), none reported by build4/5.
- NOTICE (upstream NOTICE + modification paragraph), NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE and
  SOURCE_MANIFEST.neron-flt.json (576 modules with upstream sha256) added under Vendor/AnthropicFLT/.

## 2026-11-16 17:05 clash scan
- Main/Discharges rebuilt after the origin/main merge (build-main.log, `Build completed successfully (14106 jobs)`,
  frozenTarget axioms standard). VERIFIED.
- clash/DumpFLT.lean (9714 constants of the vendored modules), clash/DumpMain.lean (197382 non-library constants of
  Main + Discharges + NeronSchemeExtensionExists + StrictHenselizationPair): 58 common names (clash/clashes.txt).
  7 are realized equation/congr lemmas (`.eq_1`, `.congr_simp`), which do not block imports (flt-cqj2). The others
  clash with CloudW07JacobiansCurves (Scheme.Modules monoidal/tensor-power API, SheafOfModules monoidal instances,
  GeometricallyIrreducible.geometricallyConnected, Smooth.isRegularLocalRing_stalk, IsRegularLocalRing.isDomain) and
  CloudB3W16Dimension's Stacks depth (Module.depth, Module.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes).
  VERIFIED.
- tools/rename_clash.py: token rename `t` → `t_nflt` of 18 last components in 44 vendored files, plus the qualified
  `IsRegularLocalRing.isDomain` → `..._nflt` (5 files); each file's header records it.
- build7: all vendored modules rebuilt after the renames; `NeronFLT/Henselian.lean` compiles after one fix
  (`@asIso _ _ _ _ e.1 he`). VERIFIED.

## 2026-11-16 17:20 contributor file
- `ZInQKernel/Contrib/OneProof/NeronDVRLocalSH.lean` (namespace NeronFLT): new leaf `NeronDescentSH`;
  `exists_neron_of_descentSH`, `neronDVRLocal_of_descentSH : NeronDescentSH → NeronExt.NeronDVRLocal`,
  `extension_of_descentSH`, `neronSchemeExtensionExists_of_descentSH : NeronDescentSH → NeronSchemeExtensionExists`
  (EGA IV 8.10.5 (xii) from the tree's `ZInQ.Contrib.EGAProperLimit.egaIV_8_10_5_xii_proof`). Builds. VERIFIED.
- `#discharges` (scratch/neron-flt/Discharges.lean → discharges.txt): 
  `DISCHARGES [OpenTextbookLeaves13.neronSchemeExtensionExists] by NeronFLT.neronSchemeExtensionExists_of_descentSH
  still assumes: [NeronFLT.NeronDescentSH] axioms: [propext, Classical.choice, Quot.sound]`;
  `#discharges: 45 open hypotheses, 13605 theorems checked, 16 discharge one`. `#print axioms` standard for
  extension_of_descentSH, neronSchemeExtensionExists_of_descentSH, neronDVRLocal_of_descentSH,
  exists_neron_of_henselian, exists_neron_of_descentSH. VERIFIED.
- autofold.json: discharges `neronSchemeExtensionExists`, adds leaf `neronDescentSH` (published, flag locator
  UNVERIFIED). `autofold.py --dry-run`: `strict count: 16/21 on 37 -> 16/21 on 37; strictest 16/21 -> 16/21`
  (count-neutral). Its module with line 1 stripped (AutofoldDry.lean) compiles; `sixContactMin_of_open39` axioms
  standard. VERIFIED.
- audit (tools/audit_diff.py → audit.txt): differences from upstream are 1965 import lines, 2282 set_option lines,
  855 `_nflt` rename lines, 105 lines in `-- [port]` blocks, 9 files with CloudW03NeronSurj bodies; the 14 lines
  flagged "OTHER" are all inside `-- [port]` blocks (the file-local CommRing instance definitions and one `rfl⟩`).
  No statement of a vendored declaration changed except the `_nflt` renames. VERIFIED (script).
- A doubled `-- [port]` comment (fix.py run twice over its own comment) removed; fix.py now skips comment lines.

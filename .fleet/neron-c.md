# neron-c (group C fields `t3`, `t41` of leaf-fold3)

**Main result.** Both fields are reduced, by Lean proofs, to strictly smaller published statements.
Each reduction is an equivalence; the converses are proved too.
- **T3** (`PkgI2.NeronMappingAbelianScheme`): the injective half is proved outright from Mathlib
  (`ZInQ.Contrib.NeronC.neronMappingAbelianScheme_injective`). What remains is the surjective half,
  `NeronMappingAbelianSchemeSurj` (BLR §1.2 Prop. 8, locator UNVERIFIED). It is the only half that
  leaf-fold3 uses (`fExtendGen_of_nmp` uses `.2`).
- **T41** (`ZInQ.H5Neron.NeronModelExists`): the group law of the Néron model, `gen` being a group
  isomorphism, and the uniqueness of extensions are proved. What remains is
  `NeronSchemeExtensionExists`: a smooth, separated, quasi-compact `𝓞_L`-scheme `N` with
  `N_L ≅ A_L` into which maps from smooth `Y` extend (BLR §1.4 Thm. 3 with §1.2 Def. 1, locators
  UNVERIFIED).

**Declarations proved** (all `#print axioms` = `[propext, Classical.choice, Quot.sound]`, no `sorry`):
- `ZInQKernel/Contrib/NeronC/NMPInjective.lean`:
  - `ext_of_isSchemeTheoreticallyDominant_of_isSeparated`, `pullback_map_injective`,
    `isSchemeTheoreticallyDominant_spec_map`;
  - `neronMappingAbelianScheme_injective`;
  - `neronMappingAbelianScheme_of_surj : NeronMappingAbelianSchemeSurj.{u} → PkgI2.NeronMappingAbelianScheme.{u}`
    and its converse `neronMappingAbelianSchemeSurj_of_nmp`.
- `ZInQKernel/Contrib/NeronC/NeronGroupAbstract.lean` (Mathlib only): `grpObjOfNeron` (a group
  object from a mapping property on test objects closed under `⊗`), `isMonHom_of_neron`.
- `ZInQKernel/Contrib/NeronC/NeronGroup.lean`:
  - `neronModelExists_of_extension : NeronSchemeExtensionExists → ZInQ.H5Neron.NeronModelExists`;
  - `neronModelExists_of_scheme`, `neron_extension_injective`;
  - the converses `neronSchemeExtensionExists_of_neronModelExists` and
    `neronSchemeModelExists_of_neronModelExists`;
  - the non-vacuity check `neronSchemeExtension_zero`.

**What compiles.**
- The three modules build with `lake build`.
- `scratch/neron-c/Check.lean` (written by `assemble.py`; verbatim copies of T3 and T41 with the
  reductions applied) exits 0 under `lake env lean`; all 9 axiom lines are standard.
- `scratch/neron-c/py/verbatim_check.py` prints `ALL OK`: T3, T41 and the declarations they use
  appear verbatim in leaf-fold3's `Leaves3.lean`.

**What remains.** The two published leaves above.
- T3-surj needs the valuative criterion at codimension-one points and Weil's extension theorem
  (BLR §4.4 Thm. 1). Neither is in Mathlib v4.35.
- T41's existence half needs neron-lg's gluing glue (`NeronGlueAway`, `NeronNearBadPoint`), which
  is unproved.

**Proposed statement change** (not applied; report §4): in leaf-fold3's `OpenTextbookLeaves3`, use
`NeronMappingAbelianSchemeSurj.{0}` for `t3` and `NeronSchemeExtensionExists` for `t41`.

Report: `docs/research/neron-c.md`. Log: `scratch/neron-c/log.md`.

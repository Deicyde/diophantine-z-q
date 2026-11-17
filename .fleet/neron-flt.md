# neron-flt (2026-11-16)

**Verdict.** The target (remove `neronSchemeExtensionExists`, −1, no new leaf) is **not** reached: the fold is
count-neutral (`16/21 on 37 -> 16/21 on 37`). What is proved (VERIFIED, standard axioms, no sorry):
* **Néron models over henselian DVRs**: `NeronFLT.exists_neron_of_henselian` (any henselian DVR, any residue field,
  `PkgI3.AbVar`, `CToPrinted.IsNeronModelOver` + generic-fibre iso), from the FLT development's theorem
  `…exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing`, ported:
  576 modules under `ZInQKernel/Contrib/OneProof/NeronFLT/Vendor/AnthropicFLT/` (Lean 4.35 fixes marked `-- [port]`,
  19 names clashing with CloudW07/Stacks renamed `_nflt`, NOTICE/LICENSE/manifest added).
* neron-ext's leaf `NeronDVRLocal`, hence `neronSchemeExtensionExists`, from **one new leaf `NeronFLT.NeronDescentSH`**
  (BLR §7.2 Thm 1 / §6.5: Néron models descend from `R^sh` to `R`, "if" half, `R^sh` pinned by `IsSHSep`; printed form
  as recalled, locator UNVERIFIED): `neronSchemeExtensionExists_of_descentSH` (EGA 8.10.5 (xii) is proved in the tree).
* group-law-dvr's leaf `NeronSchemeExtensionDVR` (verbatim copy) from the same leaf:
  `NeronFLT.GLD.neronSchemeExtensionDVR_of_descentSH`, so after integration one leaf covers both Néron leaves.

**What compiles.** `ZInQKernel/Contrib/OneProof/NeronDVRLocalSH.lean` (contributor file),
`NeronSchemeExtensionDVRSH.lean`, `NeronFLT/Henselian.lean`, the 576 vendored modules. `#discharges`:
`DISCHARGES [OpenTextbookLeaves13.neronSchemeExtensionExists] by NeronFLT.neronSchemeExtensionExists_of_descentSH,
still assumes [NeronFLT.NeronDescentSH]`. Autofold spec `scratch/neron-flt/autofold.json`: dry-run module compiles.

**What remains.** `NeronDescentSH`: effective descent along the non-finite `R → R^sh` for `R = (𝓞_L)_v`. FLT's
descent is finite étale only (henselian bases); BLR use quasi-projectivity (§6.4) + descent with an ample bundle
(§6.1), neither in Mathlib 4.35, the tree or the FLT closure. Report: docs/research/neron-flt.md.

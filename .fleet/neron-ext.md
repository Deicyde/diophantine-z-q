# neron-ext (2026-11-16)

**Verdict.** The textbook field `neronSchemeExtensionExists` (BLR 1.4/3 over 𝓞_L) is **proved**, VERIFIED:
`NeronExt.extension_of_dvrLocal : EGAIV_8_10_5_xii → NeronDVRLocal → NeronSchemeExtensionExists`.
* `EGAIV_8_10_5_xii` is the chain's existing leaf.
* `NeronExt.NeronDVRLocal` is a new leaf: BLR 1.4/3 over the DVRs (𝓞_L)_v. It is in printed form and not
  stronger than the field: the converse `dvrLocal_of_extension` is proved.
* The fold is count-neutral (34/11 → 34/11). The global textbook leaf becomes a local one.

**Why no narrowing to abelian schemes.** The consumers need Néron models where reduction is bad (VERIFIED):
* r6 (Raynaud's criterion) and SS1, through `GapNeron.neronSchemeModelExistsNF`;
* the height rows R18–R22 and height additivity, through T41, at every finite L.

**What compiles.** `ZInQKernel/Contrib/OneProof/NeronSchemeExtensionExists.lean` and the helpers `NeronExtGlue`,
`NeronExtLocal`, `NeronExtAb`, `NeronExtSpread`. About 1,700 lines in total, no sorry, standard axioms only.
* Zariski gluing of Néron models (Mathlib `RelativeGluingData`).
* The Néron property over an open is local at its maximal ideals.
* BLR 1.2/8 over a DVR without fibre connectedness (vendored FLT argument).
* Spreading out with separatedness (Stacks 01ZP on the diagonal) and of generic morphisms (01ZC).
* A Néron model near a closed point from the local one; the good model from AbVarSpreadsOut.
* `#discharges`: `DISCHARGES [OpenTextbookLeaves12.neronSchemeExtensionExists] by NeronExt.extension_of_dvrLocal`,
  still assumes `[EGAIV_8_10_5_xii, NeronExt.NeronDVRLocal]`.
* The autofold spec `scratch/neron-ext/autofold.json` works: its dry-run module compiles.

**What remains.** `NeronDVRLocal` itself (BLR's local existence). The FLT development (`~/flt-src`, Lean 4.33.1)
proves Néron existence over *henselian* DVRs (577-file closure). Discharging the leaf would need that port plus
descent from the henselization. Locators are UNVERIFIED, and a locators.md row is still to add.
Report: docs/research/neron-ext.md. Log: scratch/neron-ext/log.md.

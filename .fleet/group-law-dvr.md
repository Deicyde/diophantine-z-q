# group-law-dvr (fleet summary)

**Verdict.** `MumfordGroupLawDVR` (*GIT* Thm 6.14 over a DVR) is **not** proved outright, so `mumfordGroupLawConn`
is not removed: no −1. `neronSchemeExtensionExists` gives Néron models only over `𝓞_L` for number fields `L`. The
chain needs the group law over DVRs containing ℚ (local rings of curves over ℚ), so that field cannot supply the
extension. No other open field gives Néron models over a general DVR.

**Main result (VERIFIED, no `sorry`, standard axioms).** The new file `ZInQKernel/Contrib/OneProof/MumfordGroupLawNeron.lean`
proves `mumfordGroupLawDVR_of_neron : NeronSchemeExtensionDVR → NeronGoodModelIso → MumfordGroupLawDVR`. Its two
inputs:
* **`NeronSchemeExtensionDVR`** (LEAF, printed form): BLR §1.4 Thm 3 over a DVR, the DVR case of
  **`NeronSchemeExtensionDedekind`** (any affine Dedekind scheme). The Dedekind form also proves the textbook field
  `neronSchemeExtensionExists` (`neronSchemeExtensionExists_of_dedekind`; `#discharges` reports this discharge).
* **`NeronGoodModelIso`** (GLUE): a proper smooth model with abelian fibres maps isomorphically onto any smooth
  separated model under a map that is an isomorphism on generic fibres. It is true by van der Waerden purity, but
  purity and fibre-dimension theory are missing from Mathlib, so the glue is not proved here.

How the proof works: the Néron model's group law (`grpObjOfNeron`) is transported along `ψ : F ≅ N`, and the identity
is `e` by schematic density of the generic fibre. The file also gives `qmFamilyGroupLaw_of_neron(Dedekind)` and
`dvr_of_conn`.

**Folds (manual, both VERIFIED in an olean overlay; 42 downstream modules recompiled):**
* **F1 (narrowing, count 0):** `mumfordGroupLawConn` becomes `mumfordGroupLawDVR : MumfordGroupLawDVR`; the
  generations 14–27 are retyped to the DVR form. This is group-law's patch updated to TailZ45.
* **F2 (Néron):** `mumfordGroupLawConn` is replaced by `neronSchemeExtensionDedekind` (LEAF) and
  `neronGoodModelIso` (GLUE). *GIT* 6.14 leaves the list. A follow-up fold can delete the textbook field
  `neronSchemeExtensionExists` (net: −1 leaf, +1 glue).

In both, `frozenTarget` has standard axioms, and `MumfordGroupLawConn` and `MumfordGroupLaw` are out of the closure.
Files: scratch/group-law-dvr/fold/ (make_patch.py, the two patches, autofold-F1/F2.json marked manual, FoldCheck.lean,
foldcheck-F1/F2.txt).

**Remains.**
* The glue `NeronGoodModelIso` in Lean. With it, F2 removes GIT 6.14 at the cost of only widening BLR 1.4 Thm 3 to
  its printed generality.
* The cross-bundle follow-up of F2 (neron-ext also works on that field).
* An integration build and the kinds.tsv / OPEN.md rows.

Report: docs/research/group-law-dvr.md. Log: scratch/group-law-dvr/log.md.

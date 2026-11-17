# dedekind-free: manual fold spec (count-neutral: `neronSchemeExtensionDedekind` -> `neronDVRLocal`)

Autofold cannot express it (the new top theorem enters the chain at generation `OpenResearchLeaves27GM`, below the
generations that carry the old field). Edits for the integrator:

1. Add `ZInQKernel/OneProof/H/TailZ56.lean` = `scratch/dedekind-free/fold/TailZ56.lean.txt` (drop the final
   `#print axioms` line if the tree's convention keeps it out). It imports `TailZ55` and the contribution
   `ZInQKernel.Contrib.OneProof.MumfordGroupLawDescent`, and defines
   * `HDec.HSyn.OpenResearchLeaves32` = `OpenResearchLeaves31` with the field
     `neronSchemeExtensionDedekind : GroupLawNeron.NeronSchemeExtensionDedekind` replaced by
     `neronDVRLocal : NeronExt.NeronDVRLocal`;
   * `openResearchLeaves27GM_of_OpenResearchLeaves32` (the composite 31 -> 29GM -> 28GM -> 27GM, field by field, with
     `mumfordGroupLaw := GroupLawDescent.mumfordGroupLawDVR_proof`);
   * `openTextbookLeaves13HF_of_open16_22_df` (= `..._pz` with
     `neronSchemeExtensionExists := GroupLawDescent.neronSchemeExtensionExists_of_dvrLocal h`);
   * `sixContactMin_of_open49 (r : OpenResearchLeaves32) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves25)`, through
     the existing `sixContactMin_of_open37_hf_gm_pz`.
   No existing declaration is copied or changed.
2. `ZInQKernel/OneProof/Main.lean`: `import ZInQKernel.OneProof.H.TailZ56`; `frozenTarget` takes
   `(r : HDec.HSyn.OpenResearchLeaves32)` and calls `HDec.HSyn.sixContactMin_of_open49 r t l` (the rest unchanged; this is
   `ZInQ.OneProof.frozenTarget_df` of FoldCheck.lean).
3. kinds.tsv / OPEN.md: the row `neronSchemeExtensionDedekind` goes; the row `neronDVRLocal` comes in (kind `published`,
   flag `locator UNVERIFIED (BLR 1.4 Thm 3 at S = Spec of the DVR (O_L)_v)`, neron-ext's proposal). locators.md row
   (neron-ext's proposal): *BLR, Néron Models (1990), §1.4 Thm. 3, specialised to a DVR; and §1.2 Def. 1.*

Check (VERIFIED, `FoldCheck.lean` -> `foldcheck.txt`): `sixContactMin_of_open49` and `frozenTarget_df` use only
`[propext, Classical.choice, Quot.sound]`; in `frozenTarget_df`'s closure `NeronSchemeExtensionDedekind`,
`NeronSchemeExtensionDVR`, `NeronGoodModelIso`, `mumfordGroupLawDVR_of_dedekind` are absent and
`GroupLawDescent.mumfordGroupLawDVR_proof`, `NeronFLT.exists_neron_of_henselian`, `NeronExt.NeronDVRLocal` present;
the bundles have 24 + 3 + 2 = 29 fields, as before (count-neutral). `TailZ56.lean.txt` compiled as a scratch file.

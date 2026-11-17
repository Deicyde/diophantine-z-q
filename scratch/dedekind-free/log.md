# dedekind-free results log

Base wip/leaf-fold33b c0f3d085, merged origin/main (up to date) and origin/wip/neron-flt (286b326c).
Build: .lake/build copied from ~/dzq-wt/leaf-fold33b (identical Main.lean); NeronFLT oleans copied from
~/dzq-wt/neron-flt; `lake build ...NeronDVRLocalSH ...NeronSchemeExtensionDVRSH ...NeronGoodModelIso` OK (13479 jobs).

## 1. Readers of `neronSchemeExtensionDedekind` in the closure of `frozenTarget` (VERIFIED, Readers.lean -> readers.txt)
* closure size 271552.
* (a) `MumfordGroupLawDVR` via `GoodModelIso.mumfordGroupLawDVR_of_dedekind` -> `LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr`,
  `GroupLaw.mumfordGroupLawCurve_of_dvr` (OpenResearchLeaves14GM..27GM.mumfordGroupLaw).
* (b) `NeronSchemeExtensionExists` via `neronSchemeExtensionExists_of_dedekind` (in `openTextbookLeaves13HF_of_open16_22_pz`) ->
  * `HSyn.t41_of_extension5` -> `H5Neron.NeronModelExists` (T41) -> `HeightSplit.r18_of_leaves, r19_of_leaves, r20Lower_of_leaves',
    r21_of_leaves('), r22_of_upper, exists_semistable_neron, stableFaltingsHeight_eq_of_semistable, stableFaltingsHeight_ne_bot,
    stableFaltingsHeight_ne_top, stableHeightFinite_of('), isStableFaltingsHeight_iff, H5Neron.stableFaltingsHeight_add_le('),
    G0Split.heightAdditivity_of_h5neron, HDec.ZInQ.H5Neron.heightAdditivity_unfolded`;
  * `GapNeron.neronSchemeModelExistsNF` -> `NeronSchemeModelExistsDVRNF` -> `raynaudCriterion_*NF, ss1_ss3_of_cpNF,
    semistablePersists_*NF, semistableReductionThm_*NF, hasSemistableReduction_ofNF, exists_neron_groupModelNF`.

## 2. Verdict on (b) (VERIFIED by reading the readers)
* T41 readers need a *global* Néron model over `Spec 𝓞_L`: `GroupModel A L` (HDecomp/Faltings/Models.lean L31) is a smooth
  separated qc group scheme over `Spec 𝓞_L`; `stableFaltingsHeight_eq_iInf_height` is an infimum over such global models;
  `stableFaltingsHeight_eq_of_semistable` (TailY L163) and `exists_semistable_neron` (TailY L199) take the global Néron model
  `hN1 K A L'` and feed it to the leaves `hSS2` (SemistableNeronBaseChange) and `hMet` (NeronMetrizable), whose statements are
  about global `GroupModel`s with `IsNeronModel` over `𝓞_L`. So these readers cannot be fed local models over `(𝓞_L)_v^h`.
* A global model over `𝓞_L` from local ones is neron-ext's gluing (proved), but it needs Néron models over the
  *non-henselian* `(𝓞_L)_v` (`NeronDVRLocal`), i.e. effective descent from `R^sh` (neron-flt's leaf `NeronDescentSH`).
* Hence: the height readers do not move; the field cannot go with no new leaf. Target -1 NOT reached.

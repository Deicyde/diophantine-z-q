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

## 3. (a) proved: `MumfordGroupLawDVR` with no Néron leaf (VERIFIED, compiled 11-16 ~23:55)
File scratch/dedekind-free/GroupLawDescent.lean (one file; S1Local/S3Descent/S4Fibre are its earlier drafts).
`#print axioms DedekindFree.mumfordGroupLawDVR_proof` : [propext, Classical.choice, Quot.sound].
Steps (all compiled):
* `mumfordGroupLawAt_of_henselian`: GIT 6.14 at one henselian DVR, from `NeronFLT.exists_neron_of_henselian` (vendored FLT) and
  copies of goodmodel-iso's `neronGoodModelIso_of_dvr` / group-law-dvr's `mumfordGroupLawDVR_of_neron` with `R` fixed
  (`NeronExtAt R`, `GoodModelIsoAt R`).
* `map_injective`, `descend`: base change along a flat surjective qc `p` is injective on `Over` morphisms; a morphism of base
  changes descends if it coequalizes (Mathlib `EffectiveEpi` instance for fpqc maps, Stacks 023Q).
* `grpObjOfDescent`: a `GrpObj` on `F` from descended `μ, ι, η` (group structure on `T ⟶ F` transported along the injective
  base change map; `GrpObj.ofRepresentableBy`).
* `isAbVarFibre₁`, `inv_fibre` (rigidity, copy of the first half of `isGrpFibre_of_rigidity`), `gen_inv`, `gen_mul`: at points
  over the generic point `Spec E → Spec O₁`, the inverse/multiplication of `F₁` are computed by those of `A = F_K` over `K`.
* `cocycle_of_generic`: the descent condition from generic data (kernel pair flat over `S`, its `K`-fibre schematically
  dense, `F` separated; `IsPullback (Spec E) (Spec O₁) (Spec K) (Spec R)`).
* `mumfordGroupLawAt_of_cover`: GIT 6.14 descends along `R → O₁` (flat, surjective on Spec, `E = O₁ ⊗_R K`).
* `mumfordGroupLawAt_all`: cover = gt-shpair's strict henselization `O₁ = wE w` in the inertia field `E ⊆ K̄`
  (`isSHSep_inertia`): `R → O₁` faithfully flat (torsion-free over a PID + local), `E` the localization of `O₁` at `φ(R⁰)`
  (`assoc_pow`), `CommRingCat.isPushout_of_isLocalization` + `isPullback_SpecMap_of_isPushout`.

## 4. Contribution, #discharges, fold (VERIFIED)
* `ZInQKernel/Contrib/OneProof/MumfordGroupLawDescent.lean` (namespace `ZInQ.Contrib.GroupLawDescent`): `lake build` OK.
  Adds `neronDVRLocal_of_dedekind : NeronSchemeExtensionDedekind → NeronExt.NeronDVRLocal` and
  `neronSchemeExtensionExists_of_dvrLocal`. No `sorry`, no build-time code; the one instance is `attribute [local instance]`.
* `#discharges` (Discharges.lean -> discharges.txt): `35 open hypotheses, 16784 theorems checked, 33 discharge one`; no line for
  `neronSchemeExtensionDedekind` (expected: no theorem has its type; the field is narrowed, not discharged).
* Fold (fold/SPEC.md, fold/TailZ56.lean.txt, fold/FoldCheck.lean -> fold/foldcheck.txt): `sixContactMin_of_open49`,
  `frozenTarget_df` standard axioms; NeronSchemeExtensionDedekind out of the closure, NeronDVRLocal in; 29 bundle fields before
  and after. Count-neutral.

## 5. r6/SS1/SS3 readers (VERIFIED, read NeronDVR.lean)
`HasSemistableReduction A O` is `∃ 𝒩 Néron model over O, semistable` (`hasSemistableReduction_ofNF`), O a DVR of a number field
(non-henselian): these readers need existence over O itself; moving them to `O^sh` would change that definition. Not pursued
since T41 blocks anyway.

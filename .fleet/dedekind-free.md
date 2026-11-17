# dedekind-free (fleet note)

**Verdict: target −1 not reached; `neronSchemeExtensionDedekind` narrowed to `neronDVRLocal` (count-neutral, strictly
weaker leaf).** Report: docs/research/dedekind-free.md.

* **(a) proved, no Néron leaf (VERIFIED):** `ZInQ.Contrib.GroupLawDescent.mumfordGroupLawDVR_proof : MumfordGroupLawDVR`
  (GIT 6.14 over every DVR), in `ZInQKernel/Contrib/OneProof/MumfordGroupLawDescent.lean` (builds; axioms propext,
  Classical.choice, Quot.sound). Néron models over the strict henselization `O₁` (vendored FLT,
  `NeronFLT.exists_neron_of_henselian`) + goodmodel-iso's argument at `O₁`, then fpqc descent of μ, ι, η along
  `R → O₁` (Mathlib `EffectiveEpi`), cocycle from the generic fibre (rigidity + schematic density), axioms by injectivity
  of base change (`GrpObj.ofRepresentableBy`).
* **(b) does not move:** T41 height rows need global Néron models over `Spec 𝓞_L` (GroupModel; inf over global models;
  leaves hSS2/hMet on global models); r6/SS1/SS3 need models over non-henselian DVRs (definition of
  HasSemistableReduction). Missing step: `NeronExt.NeronDVRLocal` (BLR 1.4/3 over `(𝓞_L)_v`, printed form) = effective
  descent from `(𝓞_L)_v^sh` (BLR §6.1/6.4), not in Mathlib/tree.
* **Fold (manual, checked):** scratch/dedekind-free/fold/ (SPEC.md, TailZ56.lean.txt, FoldCheck.lean → foldcheck.txt):
  `OpenResearchLeaves32` (Dedekind field → `neronDVRLocal`), `sixContactMin_of_open49` via the existing
  `sixContactMin_of_open37_hf_gm_pz`; standard axioms; Dedekind leaf out of the closure; 29 fields before/after.
  `neronDVRLocal_of_dedekind` certifies the new leaf is a case of the old one.
* `#discharges`: 35 open, 33 discharge one; no line for the field (narrowed, not discharged).
* Reusable: `map_injective`, `descend`, `grpObjOfDescent`, `cocycle_of_generic` (descent of morphisms/group laws along
  any flat surjective qc base change).

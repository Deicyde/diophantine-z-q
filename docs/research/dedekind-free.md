# dedekind-free: GIT 6.14 over a DVR proved with no Néron leaf; `neronSchemeExtensionDedekind` narrowed to `neronDVRLocal`, not removed

Task dedekind-free, 2026-11-16/17. Base: wip/leaf-fold33b c0f3d085, merged with origin/main (already up to date) and
origin/wip/neron-flt. Results log: `scratch/dedekind-free/log.md`. This is model work and has had no human review.

Marks used below:
* **VERIFIED**: compiled, or read in a named file on this host.
* **STANDARD**: published mathematics, with a reference.
* **SPECULATIVE**: a judgement that has not been checked.
* **UNVERIFIED**: a theorem number recalled without a source (there is no network here).

## 1. Verdict

**Target not reached: the field cannot be removed with no new leaf.** The research leaf `neronSchemeExtensionDedekind`
has two kinds of reader:
* **(a) moves.** This is GIT Thm 6.14 over a DVR, `ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR`. It is now proved with
  no Néron leaf (VERIFIED, no `sorry`, axioms `[propext, Classical.choice, Quot.sound]`).
* **(b) does not move.** These are the readers of `neronSchemeExtensionExists`, BLR 1.4 Thm 3 over `𝓞_L`:
  * the height rows through T41 (`H5Neron.NeronModelExists`) need a Néron model over `Spec 𝓞_L` itself;
  * r6, SS1 and SS3 need Néron models over the non-henselian DVRs of number fields. Their notion
    `HasSemistableReduction A O` is defined through one.

  None of these can work with models over henselizations alone (§3).

**What changes instead.** The field is narrowed from the Dedekind form to neron-ext's local leaf `NeronExt.NeronDVRLocal`
(BLR 1.4 Thm 3 over the DVRs `(𝓞_L)_v`):
* The fold is count-neutral. It is manual (§4) and passes its check (VERIFIED).
* The new leaf is **strictly weaker** than the old one: `neronDVRLocal_of_dedekind` proves it from the old leaf
  (VERIFIED).
* The DVR reading of the old leaf, over arbitrary DVRs such as local rings of curves over `ℚ`, is no longer needed.
  That was the reading behind GIT 6.14.

```lean
-- ZInQKernel/Contrib/OneProof/MumfordGroupLawDescent.lean (namespace ZInQ.Contrib.GroupLawDescent)
theorem mumfordGroupLawDVR_proof : ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
theorem mumfordGroupLawAt_all (R) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] : MumfordGroupLawAt R
theorem mumfordGroupLawAt_of_henselian (R) [...] [HenselianLocalRing R] : MumfordGroupLawAt R
theorem mumfordGroupLawAt_of_cover (R) {O₁} (φ : R →+* O₁) [Flat (Spec.map φ)] [Surjective (Spec.map φ)] (E)
    (ι₁ : O₁ →+* E) (hsq : IsPullback (Spec ι₁) (Spec (K → E)) (Spec φ) (Spec (R → K))) :
    MumfordGroupLawAt O₁ → MumfordGroupLawAt R
theorem neronDVRLocal_of_dedekind : NeronSchemeExtensionDedekind → NeronExt.NeronDVRLocal
theorem neronSchemeExtensionExists_of_dvrLocal : NeronExt.NeronDVRLocal → ZInQ.Contrib.NeronC.NeronSchemeExtensionExists
```

**The smallest missing step** is `NeronExt.NeronDVRLocal` itself, or neron-flt's `NeronFLT.NeronDescentSH`, which implies
it:
* What it says: the existence of Néron models over the non-henselian DVRs `(𝓞_L)_v`.
* Rating: **printed form** (BLR 1.4 Thm 3 at `S = Spec (𝓞_L)_v`; locator UNVERIFIED, neron-ext's rating).
* Why it stays a leaf: the Néron model over `(𝓞_L)_v^sh` exists in the tree (vendored FLT), but descending it to
  `(𝓞_L)_v` needs *effective* descent of schemes along a non-finite flat map. BLR do this through Raynaud's
  quasi-projectivity of Néron models (§6.4) and descent of quasi-projective schemes (§6.1), both UNVERIFIED. Neither
  is in Mathlib or the tree. Descent of *morphisms* is not enough, and it is all that this task needed for (a).
* Of the two candidate leaves, `NeronDVRLocal` is preferred. `NeronDescentSH` holds over every DVR and yields Néron
  models over every DVR, whereas `NeronDVRLocal` asks only for the DVRs of number fields.

## 2. (a): GIT 6.14 over every DVR from the FLT Néron models over the strict henselization (all VERIFIED: compiled)

**Notation.**
* `R` is a DVR with `K = Frac R`.
* `F → Spec R` is proper and smooth, with geometrically connected fibres, a section `e`, and every field fibre an
  abelian variety. These are the hypotheses of `MumfordGroupLawDVR`.
* `A` is the generic fibre, with `g : A → F` (from the hypothesis at `Spec K → Spec R`).
* `O₁ = wE w` is gt-shpair's strict henselization: the valuation ring of the inertia field `E ⊆ K̄`.
* `p : Spec O₁ → Spec R`; `F₁ = F ×_R O₁`; `η₁ : Spec E → Spec O₁`.

| step | Lean (file `MumfordGroupLawDescent.lean`) | content | ingredients |
| --- | --- | --- | --- |
| henselian case | `neronExtAt_of_henselian`, `goodModelIsoAt`, `mumfordGroupLawAt_of`, `mumfordGroupLawAt_of_henselian` | GIT 6.14 at one henselian DVR | `NeronFLT.exists_neron_of_henselian` (vendored FLT, any residue field). goodmodel-iso's `neronGoodModelIso_of_dvr` and group-law-dvr's `mumfordGroupLawDVR_of_neron` are copied with `R` fixed: both read the Néron leaf only at `R` itself |
| base change | `e₁`, `isAbVarFibre_bc` | `F₁` satisfies the hypotheses over `O₁`: its fibres at `s` are those of `F` at `s ≫ p` | `IsPullback.of_right` (pasting) |
| injectivity | `map_injective` | `Hom_R(T, F) → Hom_{O₁}(T₁, F₁)` is injective for every `T` | `pullback.fst T.hom p` is an effective epimorphism. Mathlib's instance: flat, surjective and quasi-compact maps are effective epis, Stacks 023Q |
| descent of morphisms | `descend` | `b : X₁ → Y₁` descends if it coequalizes the kernel pair of `X₁ → X` | `EffectiveEpi.desc` |
| group law from descended data | `homGroup`, `homFunctor`, `grpObjOfDescent`, `grpObjOfDescent_one` | descended `μ, ι, η` give a `GrpObj F` with identity `η` | the group structure on `T ⟶ F` is pulled back along the injective base change (`Group.ofLeftAxioms`); then `GrpObj.ofRepresentableBy` |
| generic fibre of `F₁` | `isAbVarFibre₁`, `AE` | `A_E → F₁` is the fibre at `η₁`, given `Spec E → Spec O₁ → Spec R = Spec E → Spec K → Spec R` | pasting |
| rigidity | `inv_fibre` (with the tree's `isGrpFibre_of_rigidity` for `μ`) | the fibre identification commutes with `ι` (and with `μ`) | copy of the first half of `R1UnivRigid.isGrpFibre_of_rigidity`; `G0FibreSimple.rigidityHom`, `GrpObj.inv_comp` |
| generic values | `gen_inv`, `gen_mul` | at points over `η₁`, `ι₁` and `δ ≫ μ₁` followed by `F₁ → F` equal `w ≫ ι_A ≫ g`, resp. `w ≫ μ_A ≫ g`; here `w` depends only on the image in `F` and in `Spec K` | `Over.μ_pullback_left_*`, `δ_fst/snd` |
| cocycle | `cocycle_of_generic` | the descent condition. The kernel pair is flat over `R`, so its `K`-fibre is schematically dense; `F` is separated; the two points over `η₁` have the same images in `F` and in `Spec K` | `NeronC.ext_of_isSchemeTheoreticallyDominant_of_isSeparated`; `Spec E = Spec O₁ ×_R Spec K` |
| descent of the group law | `mumfordGroupLawAt_of_cover` | GIT 6.14 at `O₁` implies GIT 6.14 at `R`, for any flat `R → O₁` surjective on `Spec` with `E = O₁ ⊗_R K` | the rows above |
| the cover | `mumfordGroupLawAt_all` | `R → O₁` is faithfully flat. `E` is the localization of `O₁` at `φ(R \ 0)`, so the square is a pullback | Flatness: `O₁` is torsion-free over the PID `R` (`flat_iff_torsion_eq_bot_of_isBezout`). Locality: `comapHom_isLocalHom`, then `FaithfullyFlat.of_flat_of_isLocalHom` and `flat_and_surjective_SpecMap_iff`. Localization: `assoc_pow` (e = 1). Pullback: `CommRingCat.isPushout_of_isLocalization` and `isPullback_SpecMap_of_isPushout` |

`#print axioms ZInQ.Contrib.GroupLawDescent.mumfordGroupLawDVR_proof` gives `[propext, Classical.choice, Quot.sound]`.
* Checked in `scratch/dedekind-free/GroupLawDescent.lean`, the same content as the contribution file.
* `lake build ZInQKernel.Contrib.OneProof.MumfordGroupLawDescent`: 13479 jobs, OK.

**What the proof uses from the tree:**
* the vendored FLT port (neron-flt);
* goodmodel-iso's lemmas (`isIso_of_grp` and the lemmas behind it);
* gt-shpair (`exists_comap_eq`, `isSHSep_inertia`, `assoc_pow`);
* the rigidity of FrobChain;
* NeronC (density lemmas).

**What it uses from Mathlib:** the fpqc effective-epi instance, `GrpObj.ofRepresentableBy`, and the monoidal structure
of `Over.pullback`.

**The proof is not specific to `ℚ`.** It needs no characteristic hypothesis and no condition on the residue field.
It proves the statement exactly as stated, over every DVR.

## 3. (b): the readers of `neronSchemeExtensionExists` (VERIFIED: closure scan and reading)

`scratch/dedekind-free/Readers.lean` → `readers.txt` scans the closure of `ZInQ.OneProof.frozenTarget` (271552
constants). It lists every declaration whose type mentions the Néron statements.

| reader | Lean | what it needs | moves? |
| --- | --- | --- | --- |
| GIT 6.14 | `GoodModelIso.mumfordGroupLawDVR_of_dedekind` → `qmFamilyGroupLaw_of_dvr`, `mumfordGroupLawCurve_of_dvr` | group law over any DVR | **yes** (§2) |
| height rows via T41 | `t41_of_extension5` → `H5Neron.NeronModelExists` → `HeightSplit.r18_of_leaves, r19_of_leaves, r20Lower_of_leaves', r21_of_leaves('), r22_of_upper, exists_semistable_neron, stableFaltingsHeight_eq_of_semistable, stableFaltingsHeight_ne_bot/top, stableHeightFinite_of('), isStableFaltingsHeight_iff`, `H5Neron.stableFaltingsHeight_add_le(')`, `G0Split.heightAdditivity_of_h5neron` | a `GroupModel A L` over `Spec 𝓞_L` (HDecomp/Faltings/Models.lean L31) with `IsNeronModel` over `𝓞_L`, at every finite `L` (the stable height is an infimum over global models, `stableFaltingsHeight_eq_iInf_height`). The model is passed to the leaves `hSS2` (`SemistableNeronBaseChange`) and `hMet` (`NeronMetrizable`), which are stated for global models (TailY L163–205, L390) | **no** |
| r6, SS1, SS3 | `GapNeron.neronSchemeModelExistsNF` → `NeronSchemeModelExistsDVRNF` → `raynaudCriterion_leavesNF`, `ss1_ss3_of_cpNF`, `semistable*NF`, `hasSemistableReduction_ofNF` | Néron models over a DVR `O` of a number field (not henselian). `HasSemistableReduction A O` *is* "some Néron model over `O` is semistable" (NeronDVR.lean L129) | **no**, unless that definition is restated (which is not useful while T41 blocks) |

**Why the height rows cannot use local models (SPECULATIVE in its last step).**
* The height of a model is the Arakelov degree of `det ω` over `𝓞_L`. The local terms do depend only on the
  completions.
* But the chain's height is defined as an infimum over global group models.
* Every use of T41 needs a global model that attains the infimum: `exists_semistable_neron`,
  `stableFaltingsHeight_add_le`, `ne_top`.
* Building such a model from local data is neron-ext's gluing (proved). It needs Néron models over the
  non-henselian `(𝓞_L)_v`, which brings back the descent of §1.
* Restating the heights locally would change the statements of the height leaves (Bost, Pazuki, Gaudron–Rémond,
  Javanpeykar, `NeronMetrizable`, `SemistableNeronBaseChange`). That is outside this task.

## 4. The fold (manual; `scratch/dedekind-free/fold/`)

Autofold cannot express it, because the new route enters the chain below the generations that carry the old field.
* **Spec:** `fold/SPEC.md`.
* **Module text:** `fold/TailZ56.lean.txt`, to become `ZInQKernel/OneProof/H/TailZ56.lean`.
* **Check:** `fold/FoldCheck.lean` → `fold/foldcheck.txt`.

The module adds four declarations; none is copied or changed:
* `HDec.HSyn.OpenResearchLeaves32`: `OpenResearchLeaves31` with `neronSchemeExtensionDedekind` replaced by
  `neronDVRLocal : NeronExt.NeronDVRLocal`.
* `openResearchLeaves27GM_of_OpenResearchLeaves32`: the composite 31 → 29GM → 28GM → 27GM, with
  `mumfordGroupLaw := GroupLawDescent.mumfordGroupLawDVR_proof`.
* `openTextbookLeaves13HF_of_open16_22_df`: `neronSchemeExtensionExists := neronSchemeExtensionExists_of_dvrLocal h`.
* `sixContactMin_of_open49`, which enters through the existing `sixContactMin_of_open37_hf_gm_pz` (as
  `sixContactMin_of_open45_pz` does).

`Main.lean` then takes `r : OpenResearchLeaves32` and calls `sixContactMin_of_open49`.

**Check (VERIFIED).**
* Axioms: `sixContactMin_of_open49` and `frozenTarget_df` (Main's `frozenTarget` with the new signature) depend on
  `[propext, Classical.choice, Quot.sound]`.
* Absent from `frozenTarget_df`'s closure: `NeronSchemeExtensionDedekind`, `NeronSchemeExtensionDVR`,
  `NeronGoodModelIso`, `mumfordGroupLawDVR_of_dedekind`.
* Present: `mumfordGroupLawDVR_proof`, `NeronFLT.exists_neron_of_henselian`, `NeronDVRLocal`.
* Bundle fields: 24 + 3 + 2 = 29, before and after (count-neutral).
* `TailZ56.lean.txt` compiles as a scratch file.

**`#discharges`** (`scratch/dedekind-free/Discharges.lean` → `discharges.txt`, VERIFIED): `35 open hypotheses, 16784
theorems checked, 33 discharge one`.
* There is no line for `neronSchemeExtensionDedekind`, as expected: the field is narrowed, not discharged, and no
  theorem has its type.
* The new route shows only in the fold check.

## 5. Statements, rated

* **`NeronExt.NeronDVRLocal`** (new research field; neron-ext's statement, unchanged). **Printed form:** BLR,
  *Néron models* (1990), §1.4 Thm 3 at `S = Spec (𝓞_L)_v`, with §1.2 Def. 1 (numbers UNVERIFIED).
  * It is over genuine definitions: `PkgI3.AbVar`, Mathlib schemes, and `CToPrinted.IsNeronModelOver`.
  * It is a case of the old leaf (`neronDVRLocal_of_dedekind`, VERIFIED), so the fold weakens the hypothesis set.
  * Proposed kinds flag: `locator UNVERIFIED (BLR 1.4 Thm 3 at S = Spec of the DVR (O_L)_v)`.
  * Proposed locators.md row: *BLR, Néron Models (1990), §1.4 Thm 3, specialised to a DVR; and §1.2 Def. 1*.
* **`MumfordGroupLawDVR`**: GLUE, **proved** (§2).
* **`MumfordGroupLawAt R`, `NeronExtAt R`, `GoodModelIsoAt R`**: auxiliary per-ring forms, all proved where they are
  used. None is a field.
* No new leaf and no new glue Prop is introduced.

## 6. Files

* `ZInQKernel/Contrib/OneProof/MumfordGroupLawDescent.lean`: the contributor file (873 lines).
  * It imports `NeronGoodModelIso`, which defines `MumfordGroupLawDVR` through `MumfordGroupLawRed`, and
    `NeronDVRLocalSH` (FLT, gt-shpair, ega-limit). It never imports `OneProof.Main`.
  * It has no `sorry` and no build-time code. Its one instance is `attribute [local instance]`.
* `scratch/dedekind-free/`:
  * `log.md`;
  * `GroupLawDescent.lean`, the checked draft, with its stages `S1Local.lean`, `S3Descent.lean` and `S4Fibre.lean`;
  * `Readers.lean`, `readers.txt`;
  * `Discharges.lean`, `discharges.txt`;
  * `fold/` (`SPEC.md`, `TailZ56.lean.txt`, `FoldCheck.lean`, `foldcheck.txt`).

## 7. Remarks for the integrator

* **Order with neron-flt.**
  * neron-flt's `NeronDescentSH` implies `NeronDVRLocal` (`neronDVRLocal_of_descentSH`). So swapping in
    `neronDescentSH` would also be count-neutral, but with a stronger leaf. Keep `neronDVRLocal`.
  * The FLT port must be built for this contribution, as for neron-flt's files. The 576 vendored modules take about
    10 minutes.
* **goodmodel-iso's theorems stay valid, and its leaf is no longer needed by the chain.** `NeronGoodModelIso` is still
  proved from the DVR leaf. The per-ring copies here (`goodModelIsoAt`) are its proof with `R` fixed.
* **The descent machinery is reusable.** `map_injective`, `descend`, `grpObjOfDescent` and `cocycle_of_generic` are
  stated over arbitrary schemes, for any flat, surjective, quasi-compact base change. Any future "construct it over
  `R^sh`, descend it" argument for *morphisms* can use them. Effective descent of *objects* is what remains missing
  for `NeronDVRLocal`.

# neron-dvr results log

Base: 3782dac8e (wip/leaf-fold18 head; newest generation sixContactMin_of_open25, TailZ31).
Field `neronSchemeModelExistsDVR` lives in `OpenResearchLeaves19` (TailZ29 L41).

## Statements
- `GapNeron.NeronSchemeModelExistsDVRNF`: the field `ReductSplit.NeronSchemeModelExistsDVR` (TailZ7 L238) with
  `[NumberField K]` added after `[Field K]`; otherwise verbatim.
- `GapNeron.neronSchemeModelExistsDVRNF_of_field`: `fun K _ _ O _ A => h K O A`.
- `GapNeron.neronSchemeModelExistsNF (hN1 : NeronSchemeExtensionExists)`: no `hB` needed —
  `GapBLR.neronLocalizesDVR_proved : ReductGlue.NeronLocalizesDVR` (BLRLocalizes.lean L848) has no hypotheses.

## Compile outcomes
- 2026-11-15 03:4x scratch/neron-dvr/Draft.lean: `neronSchemeModelExistsNF` compiles, axioms
  [propext, Classical.choice, Quot.sound] (VERIFIED). Proof: N1 →(neronModelExists_of_extension, L := K) group model
  over 𝓞_K → `GapBLR.neronLocalizesDVR_proved` → `ReductGlue.toO 𝒩 O` Néron over O → compose gen with
  `bcSelfIso A : (A.baseChange K).X ≅ A.X`.
- Pitfall (VERIFIED): with `bcSelfIso` a plain `def` (eqToIso inside), the bijectivity step hits a kernel
  deterministic timeout; `noncomputable irreducible_def bcSelfIso` fixes it. `CToPrinted.bijective_comp_iso`
  needs both Hom types in one category, so a two-category variant `bijective_comp_iso'` was added.

## Consumers of the field (live chain at base)
- Field passing only: TailZ29 L105, TailZ28 L108, TailZ27 L109, TailZ26 L115, TailZ25 L119 (down to OpenResearchLeaves14).
- TailZ23 L766 `ss1_ss3_of14` → `ReductB.ss1_ss3_of_cp` (uses hN only through `hasSemistableReduction_of` at number
  fields L, F O, L₀) — NF suffices (VERIFIED by reading TailZ23 L441-589).
- TailZ23 L780-781 `researchLeaves9_of_open14.r6 := raynaudCriterion_leaves … r.neronSchemeModelExistsDVR …`
  (TailZ14 L243): conclusion `PkgI2.RaynaudCriterion` over EVERY field (Objects.lean L1436).
- TailZ23 L803 `neronSchemeModelExistsDVR := r.neronSchemeModelExistsDVR` into `OpenResearchLeaves9`, read at
  TailZ9 L100-101 `r8 := grothendieckMonodromy_final' … r.neronSchemeModelExistsDVR …` (TailZ7 L1496): conclusion
  `PkgI2.GrothendieckMonodromy` over EVERY field (Objects.lean L1416).

## Contributor file
- ZInQKernel/Contrib/OneProof/NeronDVR.lean: `lake env lean` clean (no errors, no warnings) and
  `lake build ZInQKernel.Contrib.OneProof.NeronDVR` succeeds (VERIFIED, 03:47).

## Where r6 / r8 are applied (downstream of the old bundles)
- r8 (`PkgI2.GrothendieckMonodromy`): no theorem in ZInQKernel takes it as a hypothesis; the only uses are
  bundle-field copies (TailD L98, TailE L6578, LPrefix L13695, TailZ4 L192, TailX L201) and the transport
  `grothendieckMonodromy_ofK5` (TailM L463-467, `exact h K O w hw A`) (VERIFIED by grep for
  `GrothendieckMonodromy`, `.r8`, `r8 :=`). So r8 is a dead field of the old bundles.
- r6 (`PkgI2.RaynaudCriterion`) applications (subagent trace, sites re-read VERIFIED):
  * TailC L5947-5959 `good_of_QML3`: `K : IF` with `[FiniteDimensional ℚ K]`, `haveI : NumberField K` (L5954),
    → `LeafQM.AV.QML3.goodReduction` (HDecomp/QM/Structures.lean L619) → `GlueA6Alg.goodReduction_of_QM_rational3'`
    → A6.lean L692 `hRay K O w hw A …` at the same K.
  * TailF L2293-2297 `qmModelG3_of`: same `QML3.goodReduction` at `K : IF` with `K ≤ L ≤ L'`,
    `[FiniteDimensional ℚ L']` (TailF L2263); no NumberField instance on K in scope, but K is finite over ℚ.
  * TailH L2659 `raynaudPlace_of_R6`: `hR6 F O₁ …` with `haveI : NumberField F := ⟨⟩` (TailH L2601).
  * Not traced to the end: which copy (A6.lean vs LPrefix L833) the chain resolves; other TailH users were
    reported by the subagent to funnel into `raynaudPlace_of_R6` (SPECULATIVE until re-read).
  Conclusion: r6 is applied only at number fields (SPECULATIVE for completeness of the list, VERIFIED per site).

## Checks against the built single proof (Main built 03:54, frozenTarget axioms standard)
- Discharges.lean: `#discharges: 66 open hypotheses, 1228 theorems checked, 3 discharge one` — the 3 are pre-existing
  contributions; no GapNeron theorem matches (expected: NF is weaker). All GapNeron axioms standard. The replacement
  `example` for `ss1_ss3_of14` over OpenResearchLeaves14 compiles (VERIFIED).
- Reach.lean (closure of frozenTarget; reach.txt) VERIFIED:
  * field consumers: exactly ss1_ss3_of_cp chain, raynaudCriterion_leaves (+raynaudCriterion_final/_of_leaves),
    grothendieckMonodromy_final' (+final/_of_leaves), exists_neron_groupModel, hasSemistableReduction_of; bundles
    OpenResearchLeaves14–19 and 9. TailZ15/17/19/22 generations unreachable.
  * r8: only bundles 2,5,7,8, ResearchLeaves3, transport grothendieckMonodromy_ofK5, producers. `.r8` read only by
    bundle maps. Dead.
  * r6 applied only at LPrefix L833 (QML3 field: TailC good_of_QML3 NumberField K; TailF qmModelG3_of K ≤ L' finite)
    and TailH L2659 (NumberField F). Other consumers pass it on.
- Conclusion: the field cannot be dropped by a fold: r6 (OpenResearchLeaves9.r6) and r8 (OpenResearchLeaves8.r8)
  need every field; dropping needs new copies of old generations 9..2/ResearchLeaves3 with NF r6/r8.

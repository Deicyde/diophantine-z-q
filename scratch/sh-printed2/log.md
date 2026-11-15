# sh-printed2 results log

Base b5ff0474. Build tree copied from ~/dzq-check2 (same commit). Prefix olean: `mkolean.sh` compiles
Head (`import ZInQKernel.OneProof.H.TailZ19`) + sh-route's Top, CA1, CA2, CA3, Final (verbatim copies of
origin/wip/sh-route:scratch/sh-route/*.lean as SR_*.lean, import lines dropped) to `olean/ShRG.olean`
(24 s). Parts are checked with `chk1.sh Part.lean`.

## Step 0 (VERIFIED, compiled)
- sh-route copy over the kernel's TailZ19: `ShPrinted2.lean` (mk.sh) compiles, 24.6 s, 8.8 GB, all 14
  `#print axioms` standard.

## Step 1: Part B (BLR 1.2/4) — VERIFIED, compiled (PartB.lean, 5 s over ShRG)
- `SHPrinted2.BLR_1_2_4_SH` (LEAF, strict-henselization reading, UNVERIFIED locator): `K` char 0;
  Néron over `R` ↔ ∀ maximal 𝔭, ∀ valuation subring `O` = `R_𝔭` (IsLocalization.AtPrime), ∀ `O₁` with
  `ShRoute.IsSHUnram O O₁ hO`, `X ⊗_R O₁` Néron over `O₁`.
- `SHPrinted2.BLR_1_2_4_0` = `CToPrinted.BLR_1_2_4` + `[CharZero K]`; `blr_1_2_4_0_of_field` (specialization).
- `blr_1_2_4_0_of_SH : BLR_1_2_4_SH → BLR_1_2_4_0` — PROVED; uses only the SH leaf (applied over `R` and
  over the Dedekind domain `R_𝔭`), localization-of-localization lemmas from Mathlib, and invariance of
  `IsNeronModelOver` under isomorphism. No NeronBaseChangeSH, no perfect-residue hypothesis.
- `neronLocalizesDVR_of_printed0 : BLR_1_2_4_0 → ReductGlue.NeronLocalizesDVR` (c-to-printed's proof
  verbatim; the use is at a number field) and `neronLocalizesDVR_of_SH` — PROVED, standard axioms.

## Step 2: Part S (SGA 7 IX 3.3) — VERIFIED, compiled (PartS.lean)
- `SHPrinted2.SGA7_IX_3_3_SH` (LEAF): the field statement with `IsStrictlyHenselianDVR O`, `IsStrictlyHenselianDVR O'`
  and `[CharZero K]`; `sga7_IX_3_3_SH_of_field` (specialization of the field statement).
- `SHPrinted2.SGA7_IX_3_3_0` = field statement + `[CharZero K]` + `[PerfectField κ(O)]`; `sga7_IX_3_3_0_of_field`.
- `sga7_IX_3_3_0_of_SH : SGA7_IX_3_3_SH → NeronBaseChangeSH → SGA3_VIB_3_10 → AVGlue.GeomConnOfRationalPoint →
  SGA7_IX_3_3_0` — PROVED. Ingredients: sh-route `strictHenselizationPair0_final` (proved CA), reduct-glue
  `isSemistable_bcDVR_iff`, `bcbcIso` transport, `pbCompIso_natural'` (generic iso), Mathlib fpqc descent
  `MorphismProperty.of_isPullback_of_descendsAlong (P := IsOpenImmersion)`, `Scheme.Pullback.range_fst`,
  c-to-printed `idComp_baseChange` (three times for `U₁ = q⁻¹U`, once for the image).
- Helpers proved: `pbCompIso_fst`, `pbCompIso_inv_fst` (projection compatibility; uses a copy of the vendored
  `pullbackComp_hom_app_left_fst_fst`), `flat_surjective_gD` (`Spec O₁ → Spec O` flat + surjective: torsion-free
  over a Bezout domain, local flat ⇒ faithfully flat), `isPullback_bc`, `isPullback_bc_iso`, `descend_openImm`.

## Step 3: Part U (uses) — VERIFIED, compiled (PartU.lean)
- Uses of the two fields in TailZ19: `blr_1_2_4` only via `neronLocalizesDVR_of_printed` (number field `L`);
  `sga7_IX_3_3` only via `identityComponentBaseChangeDVRRange_of`, whose result is used only in
  `semistableNeronBaseChange_of_printed_full` at `(L, O)`, `L` a number field, `O` a DVR of `L`.
- `finite_residueField`, `perfectField_residueField` (DVR of a number field) — PROVED.
- `identityComponentBaseChangeDVRRange0_of`, `semistableNeronBaseChange_of_printed_full0` — verbatim copies with
  the `…0` hypotheses (+ intro pattern, + one `haveI` for `PerfectField κ(O)`) — PROVED.

## Step 4: Part F (bundle) — VERIFIED, compiled (PartF.lean)
- `HDec.HSyn.OpenResearchLeaves12SH` (33 fields): leaf-fold12's 32 with `blr_1_2_4 ↦ blr_1_2_4_SH`,
  `sga7_IX_3_3 ↦ sga7_IX_3_3_SH`, `+ neronBaseChangeSH`. Diff vs TailZ19 checked: only these lines change.
- `researchLeaves11_of_open12SH`, `sixContactMin_of_open15SH` — PROVED.
- `shUnram_exists_numberField` (sanity: SH extensions exist at every DVR of a number field) — PROVED.

## Full check (VERIFIED)
- `chk.sh`: `ShPrinted2.lean` = Head + SR_* + PartB + PartS + PartU + PartF; `lake env lean`: 29.9 s, 8.8 GB,
  0 errors, 22/22 `#print axioms` = [propext, Classical.choice, Quot.sound] (axioms.txt). No sorry/axiom in parts.
- SR_* files are byte-identical to origin/wip/sh-route (diff -q).

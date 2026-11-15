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

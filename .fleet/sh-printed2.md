# sh-printed2 (2026-11-14): summary

**Result.** Both c-to-printed fields assigned to this task are now Lean theorems from their strictly
henselian forms. The setting is characteristic 0, plus a perfect residue field for SGA 7. No glue is left.
- `blr_1_2_4_0_of_SH : BLR_1_2_4_SH → BLR_1_2_4_0`. The leaf is BLR §1.2 Prop. 4 over strict henselizations
  `IsSHUnram`, which is `O^sh` in characteristic 0 (sh-route §3). The proof uses no other leaf: it applies the SH
  form over `R` and over `R_𝔭`.
- `sga7_IX_3_3_0_of_SH : SGA7_IX_3_3_SH → NeronBaseChangeSH → SGA3_VIB_3_10 → GeomConnOfRationalPoint →
  SGA7_IX_3_3_0`. It uses:
  - sh-route's strict-henselization pair, which is proved;
  - Néron base change and semistability over `P`, `P'`;
  - Mathlib's fpqc descent of open immersions along the faithfully flat `Spec P' → Spec O'`;
  - descent of the image through `idComp_baseChange`.
- `…_0` means the field statement word for word with `[CharZero K]` added, and for SGA 7 also
  `[PerfectField κ(O)]`. Every use is at a number field, and a DVR of a number field has a finite residue field
  (proved). The two consuming proofs, copied with only these hypotheses changed, compile.
- The new bundle `HDec.HSyn.OpenResearchLeaves12SH` has 33 fields:
  - `blr_1_2_4` becomes `blr_1_2_4_SH`;
  - `sga7_IX_3_3` becomes `sga7_IX_3_3_SH`;
  - sh-route's `neronBaseChangeSH` is added.

  `sixContactMin_of_open15SH` gives `ZInQ.SixContactMin` from this bundle and the unchanged textbook, added and
  glue bundles.

**What compiles.** `scratch/sh-printed2/chk.sh` builds `ShPrinted2.lean` and checks it with one Lean process:
30 s, 8.7 GB, 0 errors. The file is `import TailZ19`, plus sh-route's Top, CA1–3 and Final (verbatim), plus
PartB, PartS, PartU and PartF. All 22 `#print axioms` are standard, and there is no sorry or axiom. Report:
`docs/research/sh-printed2.md`; log: `scratch/sh-printed2/log.md`.

**What remains.**
1. All locators are UNVERIFIED (no network).
2. `SGA7_IX_3_3_SH` is never stronger than the print, whichever base SGA 7 IX is printed over.
3. `BLR_1_2_4_SH` is the printed form only in the strict-henselization reading. If BLR 1.2/4 is printed with
   `𝒪_{S,s}`, keep c-to-printed's `BLR_1_2_4`. Both routes feed the same use (`blr_1_2_4_0_of_field`,
   `blr_1_2_4_0_of_SH`).
4. The `IsSHUnram ≅ O^sh` argument (sh-route §3) is on paper only.

# rv-cr3-trust log

Target: docs/research/cr3-trust.md (base of that note: 14b28b23; this worktree: 8b71bfdf).

## Step 0
- Read cr3-trust.md in full (621 lines).

## Step 1: Lean implication graph (read at 8b71bfdf)
- Rank/Statements.lean: CertifiedRankRk:43, TYZRk:59, TYZClRk:72 (same lines as cr3-trust). Conclusion
  `∃ P : (shortCurve (-(d:ℚ)^2)).toAffine.Point, ¬IsOfFinAddOrder P`. VERIFIED by reading.
- certifiedRankTYZ_of_certifiedRankTYZRk' (RankVariants.lean), Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk
  (FourRank.lean:367), certifiedRank5b_of_certifiedRankTYZ (Sec3/TYZ.lean:130),
  certifiedRankTYZCl_of_certifiedRankTYZClRk' all exist with no extra hypotheses.
- FINDING F1 (error in cr3-trust §0.2, Summary 1, §3 TYZClRk docstring): TYZClRk DOES imply TYZ, TYZCl, 5b in Lean:
  TYZClRk -> TYZRk (Redei) -> TYZ (RK9+MW, primed thm) -> 5b (Thm 3.6). The premise #Sel2=8 is a premise of the
  target forms, which only weakens them. So TYZClRk implies all 13 forms (+ DLAdmRk). The sentence
  "Those three are not implied by it in Lean as stated, because of the extra premise #Sel2 = 8" is false;
  so is the draft docstring clause "It implies every other form of CR3 except the three ...".
- FINDING F2 (§0.3 out of date): new variants exist:
  exists_..._of_sixContactMin_certifiedRank5b (Rank5bSec3.lean:51, no 22P) and
  exists_..._of_sixContactMin_certifiedRankDLAdmRk (RankDL.lean:232). cr3-trust §0.3 says DLAdmRk has no
  variant and recommends adding the 5b one; both are done. Line numbers in Rank5bSec3 shifted
  (TYZ 54->64, TYZCl 67->77).
- CertifiedRank5b docstring (Row5b.lean ~195) still cites "Gross–Zagier and Kolyvagin (manuscript Lemma 5.5)";
  CertifiedRankRk docstring lists Kriz first. cr3-trust §4 already lists aligning these (consistent).
- DLAdmRk docstring (RankDL.lean:182) has no trust paragraph of its own; fine (points to DLRk).

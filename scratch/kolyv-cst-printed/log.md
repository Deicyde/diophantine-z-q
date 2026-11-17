# kolyv-cst-printed results log

## 2026-11-17
- Merged origin/wip/pc-from-rc (5404a9fe) into d435851d: clean (merge commit 91c35ba97).
- Read: docs/research/pc-from-rc.md, PoleRC/CRM.lean, PoleS12/Leaves.lean, SelmerTwoPower.lean.
- Existing: IsModular (L-series form, written fresh by pc-s12), BCDTThmA, KolyvaginThm1 (r=1 only),
  kolyvaginRankOne_of_printed, KolyvaginRankOne (CRM.lean), AnalyticRankOne (PoleManuscript.lean).
- Manuscript lines (VERIFIED, read in diophantine_zq.tex on this base): lem:forward-rank L1086-1109,
  Kolyvagin cite L1093, BCDT cite L1092, Kato L1103-1108; uses L1111-1113 (r=1), L4020 (r=1),
  L2386, L7626, L7780, L8267 (r=0); L6803 table row "Forward finiteness \cite{gz,kolyvagin}".
  CST cites L2428 (applies twice; conditions L2429-2432), L8268-8272 (unaveraged height formula,
  Rankin derivative L'(E^(D_w),1)L(E^(h_*),1) != 0), uncited uses "explicit height formula"
  L2464, "conductor-one height formula" L4345, "the height formula" L9439, table L6797.
  Bibitems: kolyvagin L11163-11166, cst L11181-11183, bcdt L11150-11154.
- Page text in repo: none of Kolyvagin or CST. Secondhand summaries (NOT the print):
  docs/theorem-application-audit/evidence/parallel-forward-modularity-report.md (A020: Kolyvagin
  printed p.3 modular = weak Weil parametrization X0(N)->E, N conductor; Thm 1 p.4: rank = an. rank
  and Sha finite when an. rank <= 1; proof chain Thms 2-5 pp.4-5), and
  docs/theorem-application-audit/evidence/applications.md §6 (CST 1.1, printed pp. 2524-2525 of
  ANT 8:10 (2014) 2523-2572: hypotheses listed). Both UNVERIFIED by this task.
- New file ZInQKernel/Contrib/OneProof/KolyvCST/Kolyvagin.lean: AnalyticRank, KolyvaginThm1Printed
  (r <= 1), ForwardRank, KummerCorank (GLUE), ForwardCorank, bridges.
- Kolyvagin.lean: lake env lean, no errors, no warnings (1m20s). VERIFIED compile.
- CaiShuTian.lean: compiles (lake env lean, no errors/warnings, after fixes: Λ token -> Lat; open Classical for decidability). VERIFIED compile.
- CaiShuTian.lean revision (heightK factored out; deriv_ne_zero_iff_heightK_ne_zero, conductor_factor_ratio added):
  lake env lean, no errors/warnings. lake build of both KolyvCST modules: success. VERIFIED compile.
- scratch/kolyv-cst-printed/Axioms.lean: 33 declarations, all [propext, Classical.choice, Quot.sound]
  or a subset (IsHeegnerForm: [propext]); output in axioms-out.txt. No sorry. VERIFIED.
- Height normalization (VERIFIED, read in source): Tau Ceti canonicalHeight = lim h_x(2^n P)/4^n with
  h_x = Mathlib logHeight of xRep over the field (relative: infinite places with multiplicity,
  FinitePlace normalized absolute values); neronTatePairing = associated' (⟨P,P⟩ = canonicalHeight P).
  So heightK is relative to K, in the h_x ("2ĥ") convention; constant factors absorbed by ∃ C.
- Manuscript fixes E non-CM (VERIFIED: tex L1013, L1807, L2836, L6835): CSTThm11Split's non-CM
  restriction costs nothing for the manuscript's uses.

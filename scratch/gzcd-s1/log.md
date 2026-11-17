# gzcd-s1 results log

## Setup
- Base HEAD 08ca9c44 (wip/leaf-fold33b + origin/main, main is ancestor). Merged origin/wip/h33-d1 (4b12a442;
  contains origin/wip/eps-splitting 5e3d65de and hgz-steps) as 06f3b5c0: 42 added files, no conflicts, no
  modified files.
- h33-d1 already proved (per its report, docs/research/h33-d1.md): S1 model uniqueness
  (CurveModel.exists_iso_of_functionField, GZUnique.model_transfer), G4(b) (H33D1.not_mem_chartZ_iff), and the
  merge of eps-splitting (GZSplitUnique.GrossZagierCurveCdSplitSome). Not duplicated here.
- Left for gzcd-s1: discriminant bridge (disc K = D <-> K contains sqrt D), equivalence of hGZ's current type
  with the printed one-model form, fold dry-run, rating.

## Builds and checks (all VERIFIED)
- build1.txt: lake build Main Discharges GrossZagierSplitUnique GrossZagierModelUnique after merge: no errors (52 min,
  stale .lake).
- Discr.lean (scratch, then Contrib/OneProof/GrossZagierCdPrinted/Discr.lean): compiles, no warnings after fixes
  (repr of 1 via rw [← h0]; nonZeroDivisors ℤ instead of ℤ⁰; IntermediateField.bot_eq_top_iff_finrank_eq_one;
  linear_combination coefficients; generalize det before push_cast).
  Statements: discr_basis_two (disc{1,w} = A²+4B if w² = Aw+B); discr_eq_of_sq (δ²=D, D<0 fundamental,
  [K:ℚ]=2 ⇒ NumberField.discr K = D); exists_sq_eq_discr ([K:ℚ]=2 ⇒ ∃ δ, δ² = discr K).
- GrossZagierCdPrinted.lean: needed [CharZero K] in exists_sqrt_embedding; compiles. Statements:
  GZPrintedBody (π(∞) = H33D1.ptO E, discr K = D, any ιK), GrossZagierCurveAtPrinted (some model),
  GrossZagierCurveCdPrinted; gzPrintedBody_iff (↔ GZSplitBody), grossZagierCurveCdPrinted_iff
  (↔ GZSplitUnique.GrossZagierCurveCdSplitSome), grossZagierCurveCd_iff_printed (↔ GZSch.GrossZagierCurveCd),
  grossZagierCurveCd_of_printed, grossZagierAlgOptCd_of_printed.
- build3.txt: lake build Main Discharges GrossZagierCdPrinted: Build completed successfully (16091 jobs).
- FoldCheck-output.txt: frozenTarget_printed (current top, hGZ retyped) and 9 others: [propext, Classical.choice,
  Quot.sound]; frozenTarget_printed_eq by rfl.
- Discharges-output.txt: DISCHARGES [hGZ] by ZInQ.GZCdPrinted.grossZagierCurveCd_of_printed, still assumes
  [GrossZagierCurveCdPrinted], standard axioms; 39 open, 13888 checked, 0 sorry.
- G10 (ĥ normalization): Tau Ceti Point.canonicalHeight = lim naiveHeight(2ⁿP)/4ⁿ over K (read); reading point,
  absorbed by ∃ κ > 0 if a positive multiple (SPECULATIVE on GZ's convention).

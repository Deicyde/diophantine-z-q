# sga735-finish log

Base: c0f3d085 (main) + merge of origin/wip/sga735-narrow (a83c9b93; adds SGA7IX35ForwardAC.lean, scratch).

## Findings
- VERIFIED (read): live readers of r6's square-zero conclusion: `HDec.G15Ram.raynaudPlace_of_R6` (TailH L2577; feeds
  `fixed_of_unipSq_of_iterate'` for wild σ with p-power period) and `HDec.PkgI2.goodReduction_of_QM_rational3_of_alg`
  (LPrefix; feeds `quatUnipotentTrivial`, (S-1)²=0 on G[3^{2k}] ⇒ S=1 on G[3^k]).
- Both need only: σ-1 nilpotent on A[ℓ^n] with ONE exponent N for all n (from nilpotence on T_ℓ).
  - wild: (σ-1)^N x = 0 and σ^{p^a} x = x ⇒ σx = x (downward induction, square-zero core at (σ-1)^{j-1}x).
  - QM: (S-1)^{2^{i+1}}=0 on all G[3^k] ⇒ (S-1)^{2^i}=0 on all G[3^k], by quatUnipotentTrivial applied to 1+(S-1)^{2^i}.
  So no new valuation algebra is needed (shorter than sga735-narrow §6's c^4 plan).

## Compiles (VERIFIED, lake env lean, standard axioms)
- ZInQKernel/Contrib/OneProof/SGA7IX35Unip.lean: leaf `SGA735Nil.SGA7_IX_3_5_ForwardUnipAC` (conclusion
  IsNilpotent (galTΩ σ - 1)); `forwardUnipAC_of_forwardGeom(AC)` (specialization); `SemistableUnipotentNilCP` from it;
  `RaynaudCriterionNFNil` and `raynaudCriterionNFNil_of_forwardUnipAC`; `fixed_of_nil_of_iterate`.
- ZInQKernel/Contrib/OneProof/SGA7IX35UnipReaders.lean: `nilQuat_trivial` [propext, Quot.sound];
  `HDec.G15Ram.raynaudPlace_of_R6Nil` (same type RaynaudPlace) and
  `HDec.PkgI2.goodReduction_of_QM_rational3_of_alg_nil`: [propext, Classical.choice, Quot.sound].

## Fold (VERIFIED)
- R6Taint.lean on closure of sixContactMin_of_open48 (242,333): tA 60, tB 710, 25 carrier structures, copy 735 (127 decls).
- gen.py -> FoldCheck.lean (127 blocks, 325 KB): 0 errors, `sixContactMin_of_open49` [propext, Classical.choice, Quot.sound].
  Fixes needed: copylib CTX + `attribute [-instance]` (else typeclass timeouts in TailH copies); HDec namespace wrap for
  LPrefix LeafQM block; stale olean of Readers (rebuild before lake env lean).
- ClosureCheck: closure of open49 has no UnipotentForward.SGA7_IX_3_5_ForwardGeom, ReductSplit.SemistableUnipotent,
  RaynaudCriterionNF (both), UnipSq, raynaudPlace_of_R6; contains ForwardUnipAC, RaynaudCriterionNFNil, raynaudPlace_of_R6Nil.
- OpenResearchLeaves32 vs 31: one field changed (diff computed).
- Statement.lean rfl copy OK; #discharges: 33 lines, none from new files (bypass, as expected).
- Counts (kinds.tsv, 29 H): strict/strictest 11/18 -> 12/17 with kinds-row-proposed.tsv (LEAF/LEAF); row passes kinds_row_problems.

# gz-statements results log

## 2026-11-13 step 1: restricted leaves (Contrib/GZStatements/Weak.lean)
- Read: Contrib/GZDecomp/{Scope,Decomp}.lean, docs/research/gz-decomp.md, atkin-li.md (VERIFIED read).
- Definitions checked (VERIFIED read): TC `Newform` = EigenformAwayFromLevel (eigen for all
  T_n, (n,N)=1, nonzero) + isNew (cuspFormsNew) + a₁=1 (Newforms/Newform.lean:85-111);
  `frickeSign` = choice of ε ∈ {±1} with 𝒲_N f = ε f (Newforms/Fricke.lean:221-233);
  `frickeCompletedL_sub_eq`: Λ_N(k−s) = i^k ε_N Λ_N(s) (LFunction/Sign.lean:186);
  Mathlib `WeierstrassCurve.LFunction`: Euler product over all primes of local factors of the
  MINIMAL model (EllipticCurve/LFunction.lean:41-81): genuine.
- Glue trace (VERIFIED read): FHNonvanishing used once, `hL2 N f hχ hw 4`, f from modular_cd for
  d%8=5; GrossZagierHeegner used once with E = C_d.
- Defined FHNonvanishingCd, GrossZagierHeegnerCd, GrossZagierRankCd; proved 10 theorems.
  `lake build ZInQKernel.Contrib.GZStatements.Weak` OK (VERIFIED). Axioms of all 10: [propext,
  Classical.choice, Quot.sound] (VERIFIED, scratch/gz-statements/out_check_axioms.txt).
- Finding: GrossZagierHeegnerCd and GrossZagierRankCd are implied by GZDecomp.GrossZagierCd
  (hence by Literature.GrossZagier): L3's conclusion is satisfied by any rational point of
  infinite order (VERIFIED, compiled).

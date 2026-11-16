# pazuki-alg results log

## 2026-11-16 15:00 PST start
- Base: wip/pazuki-dict 37b70108; merged origin/main (e41a7169) and origin/wip/integrate-w82 (5e235a40): clean.
- kinds.tsv (after merge): pazukiCor13Upper = consequence/GLUE (11-16 re-rating); gagaMorphism = consequence/GLUE;
  uniformizationLeafAll no longer a field (ZInQKernel/Contrib/OneProof/UniformizationLeafAll.lean, PR #35). VERIFIED (read).
- gaga-serre (origin/wip/gaga-serre 1d7687e7) is NOT merged into main. VERIFIED (git merge-base).

## 2026-11-16 16:30 analysis (no Lean)
- Finding (VERIFIED by reading the statements): GAGAMorphism (TailQ:875) only algebraizes holomorphic homomorphisms
  between abelian varieties; exists_closedImmersion_projectiveSpace / SerreGAGAMorphism only maps to P^N. Neither produces
  a line bundle with h0 = 1 (theta maps give nTheta, n >= 2, as pullbacks of O(1)); nothing in the fold descends a line
  bundle from A_C to A_{K'} (needs NS(A_Qbar) = NS(A_C)). So AnalyticPPAlgebraic is not provable from those inputs.
- Plan: ThetaDivisorAlgebraicC <= RiemannPPAV (per-Omega algebraicity of the ppav of Omega) + GAGAMorphism (twice:
  iso B ~ B0) + SymmPrincipalTransport (proved). SymmPrincipalDescends (arithmetic half) kept as composite GLUE.
- Lean file: ZInQKernel/Contrib/OneProof/PazukiAlg.lean (namespace PazukiAlg).

## 2026-11-16 15:50 compile 1
- (log time correction: the "16:30" entry above was written at ~15:25.)
- `lake build ZInQKernel.Contrib.OneProof.PazukiCor13Upper`: Build completed successfully (12811 jobs). VERIFIED.
- `lake env lean ZInQKernel/Contrib/OneProof/PazukiAlg.lean` (without the UniformizationLeafAll import): 0 errors. VERIFIED.
  Proved: discreteTopology_periodLattice; riemannTheta_add_int / _add_period / _add_mem_eq_zero_iff (consistency of the
  leaf); tensorPowPullbackIso, support_zeroLocus_pullbackSec, isAmple_map, finrank_map, symmPrincipalTransport;
  thetaDivisorAlgebraicC_of_riemann (RiemannPPAV + GAGAMorphism + SymmPrincipalTransport => ThetaDivisorAlgebraicC).

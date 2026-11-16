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

## 2026-11-16 16:05 compile 2
- `lake build ZInQKernel.Contrib.OneProof.UniformizationLeafAll`: Build completed successfully (9136 jobs). VERIFIED.
- PazukiAlg.lean with final theorems: 0 errors; `#print axioms` (temporary, removed after) for pazukiCor13Upper_of_riemann,
  symmPrincipalTransport, thetaDivisorAlgebraicC_of_riemann: [propext, Classical.choice, Quot.sound]. VERIFIED.
- RiemannPPAV now allows a translate theta(. + c) (weaker than the print, which has c = 0).
- Verbatim.lean (AnalyticPPAlgebraic copy, rfl): compiles, no output. VERIFIED.

## 2026-11-16 15:55 full build, #discharges, autofold dry run
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.PazukiAlg`:
  Build completed successfully (14103 jobs); frozenTarget axioms standard. VERIFIED.
- `#discharges` (scratch/pazuki-alg/Discharges.lean, output discharges-output.txt):
  DISCHARGES [OpenResearchLeaves28.pazukiCor13Upper] by PazukiAlg.pazukiCor13Upper_of_riemann
    still assumes: [ZInQ.HomLattice.GAGAMorphism, PazukiDict.PazukiCor13UpperPP, PazukiAlg.RiemannPPAV,
    PazukiDict.SymmPrincipalDescends]; axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 45 open hypotheses, 6725 theorems checked, 15 discharge one. VERIFIED.
- autofold dry run without --allow-rise: refused, "strict count: 16/21 on 37 -> 17/22 on 39; strictest 16/21 -> 17/22".
  With --allow-rise: output (line 1 stripped) = scratch/pazuki-alg/FoldCheck.lean, compiles;
  HDec.HSyn.sixContactMin_of_open39 axioms [propext, Classical.choice, Quot.sound]. VERIFIED.

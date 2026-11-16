# gaga-chart results log

## Setup (11-16 02:50)
- Base aa37ef8ab (wip/sga1-etale). Build tree copied from ~/dzq-wt/nv-local (differs only in Contrib files);
  `lake build ZInQKernel.Contrib.OneProof.SmoothComplexManifoldEtale ZInQKernel.OneProof.H.TailQ`: success (9082 jobs). VERIFIED.
- Target statement: `ZInQ.HomLattice.GAGAMorphism` (ZInQKernel/OneProof/H/TailQ.lean:875). VERIFIED (read).
- Rating context: origin/wip/leaf-fold32 kinds.tsv re-rates gagaMorphism `consequence` (GLUE), 11-16 dictionary
  ruling: hypothesis reached from IsStrongUnif/IsAnalyticHom only through the holomorphic inverse function theorem;
  same step as `ShimuraThm54` (origin/wip/hcm-g1, ZInQKernel/Contrib/OneProof/ShimuraMainCMG1.lean:469). VERIFIED (read).

## Plan
- New leaf `GAGAChart.GAGAChart`: for abelian varieties A, B over ℂ, analytic manifold structures on A(ℂ), B(ℂ)
  (analyticTopology) satisfying `IsAnStr` (= the three clauses of `SmoothComplexManifoldAn`), every map
  F : A(ℂ) → B(ℂ) holomorphic (ContMDiff ω) in these charts is `P ↦ P ≫ f` for a morphism f.
- Glue: GAGAMorphism from GAGAChart + UniformizationLeafAll (B's uniformization, for analyticity of ψ)
  + SmoothComplexManifoldAn (existence of the charts; proved by sga1-etale from SGA1_XII_3_1_Etale).

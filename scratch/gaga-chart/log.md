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

## A.lean (11-16 03:40) — COMPILES (VERIFIED, `lake env lean scratch/gaga-chart/A.lean`)
- `GAGAAn.IsAnStr X n` (def, the three clauses of SmoothComplexManifoldAn), leaf `GAGAAn.GAGAChart`.
- glue: `contMDiffAt_of_regular` (holomorphy into X(ℂ) from regular functions + continuity),
  `continuous_analyticHom` (IsAnalyticHom ⇒ continuous, classical topology), `continuousAt_symm` (φ⁻¹ continuous).
- `GAGAAn.gagaMorphism_of_chart (hU : UniformizationLeafAll) (hMan : SmoothComplexManifoldAn) (hG : GAGAChart) :
  ZInQ.HomLattice.GAGAMorphism` — axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
  Inverse function step: Mathlib `ContDiffAt.localInverse`/`to_localInverse` at ω (analytic IFT) on
  Θ∘φ∘proj (clause (ii) of the uniformization gives the invertible derivative).
- added `contMDiff_id_of_isAnStr` (two IsAnStr structures over a topology with open U(ℂ): identity holomorphic
  both ways), `isAnStr_of_etale`, `gagaMorphism_of_chart_etale (hU) (hL : SGA1_XII_3_1_Etale) (hG)`. All compile,
  standard axioms. VERIFIED.
- ShimuraThm54 (hcm-g1): `IsAnalyticIso` = surjective hom, kernel L, Weierstrass coordinates holomorphic off L; no
  derivative/inverse clause, objects are Mathlib Weierstrass points (no analyticTopology/CPt). The chart restatement
  here does not apply verbatim (different objects, and no coords clause to feed the IFT). VERIFIED (read).

## Contribution module v1 (11-16 04:15)
- `ZInQKernel/Contrib/OneProof/GAGAChart.lean` (A.lean + docs): `lake build ZInQKernel.Contrib.OneProof.GAGAChart` OK.
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges` OK (12994 jobs);
  `lake env lean scratch/gaga-chart/DischargesCheck.lean` → scratch/gaga-chart/discharges.txt. VERIFIED:
  DISCHARGES [OpenTextbookLeaves11.gagaMorphism] by GAGAAn.gagaMorphism_of_chart
    still assumes: [UniformizationLeafAll, SmoothComplexManifoldAn, GAGAAn.GAGAChart]; standard axioms
  DISCHARGES [OpenTextbookLeaves11.gagaMorphism] by GAGAAn.gagaMorphism_of_chart_etale
    still assumes: [UniformizationLeafAll, SGA1Etale.SGA1_XII_3_1_Etale, GAGAAn.GAGAChart]; standard axioms
  #discharges: 63 open hypotheses, 1926 theorems checked, 13 discharge one

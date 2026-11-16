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

## v2: charts from the uniformization (11-16 05:00) — COMPILES (VERIFIED)
- B.lean: `RChart` (chart by regular functions with analytic representation), `rChartedSpace`,
  `isManifold_rChart`, `contMDiffOn_xevalAt_rChart`, `isAnStr_rChart`; `uPt`, `continuous_uPt`, `continuous_symm`,
  `exists_rChart` (IFT at v₀ on a nbhd S where dG invertible; chart Q ↦ Θ Q on φ(proj S); inverse φ∘proj∘G⁻¹;
  regular functions analytic via `OpenPartialHomeomorph.contDiffAt_symm` at each point of G(S)).
- Module now proves `GAGAAn.gagaMorphism_of_gagaChart (hU : UniformizationLeafAll) (hG : GAGAChart) : GAGAMorphism`
  (no SmoothComplexManifoldAn / SGA1 leaf needed); `exists_isAnStr_of_unif`; core theorem over named glue
  `IsAnStrExists`. C.lean = module copy.
- `#discharges` (scratch/gaga-chart/discharges.txt), VERIFIED:
  DISCHARGES [OpenTextbookLeaves11.gagaMorphism] by GAGAAn.gagaMorphism_of_gagaChart
    still assumes: [BPAnalytic.Uniformization.UniformizationLeafAll, GAGAAn.GAGAChart]; axioms standard
  (plus rows for gagaMorphism_of_chart, _core, _etale); #discharges: 63 open hypotheses, 1951 theorems checked, 15 discharge one

## Autofold spec (11-16 05:10)
- scratch/gaga-chart/autofold.json: gagaMorphism := GAGAAn.gagaMorphism_of_gagaChart {n}.uniformizationLeafAll {n}.gagaChart;
  new leaf gagaChart (kind published, flag "unread: new printed leaf, no reading recorded; locator UNVERIFIED").
- `python3 scripts/one_proof/autofold.py scratch/gaga-chart/autofold.json --dry-run`: exit 0,
  "strict count: 46/10 on 56 -> 46/10 on 56; strictest 45/11 -> 45/11" (this base rates gagaMorphism LEAF;
  under leaf-fold32's re-rating, consequence/GLUE, the fold is -1 GLUE). VERIFIED.
- FoldDryRun.lean (dry-run module minus line 1) compiles; `HDec.HSyn.sixContactMin_of_open30` axioms
  [propext, Classical.choice, Quot.sound]. VERIFIED.
- added `GAGAChartSome` (GAGA for some IsAnStr charts) and `gagaChart_of_some : GAGAChartSome → GAGAChart`
  (the ∀ over charts in the leaf adds nothing). Module rebuilt; #discharges rerun: same gagaMorphism rows,
  "63 open hypotheses, 1952 theorems checked, 15 discharge one"; all listed axioms standard. VERIFIED.

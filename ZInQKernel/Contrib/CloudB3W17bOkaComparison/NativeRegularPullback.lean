import ZInQKernel.Contrib.CloudB3W17GAGA.CanonicalModels
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.ReindexedAffineGamma
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Analytic.ParametricCircleIntegral

/-!
# Actual regular pullbacks of a native manifold-differentiable map in its fixed algebraic étale chart

The source chart is exactly `ComplexPoint.localChart`, hence the same algebraic
étale chart that defines the unchanged native Hodge atlas.  Only native
MDifferentiability of F is used.  The genuine finite-dimensional scalar Cauchy
theorem gives actual Oka sections; H103 or an algebraic F witness is not used.
-/

open scoped Manifold ContDiff Topology
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ZInQ.Contrib.CloudB3W17GAGA

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (X Y : Over (Spec (CommRingCat.of ℂ))) (d e : ℕ)
variable [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Y.hom]
variable (F : ComplexPoint X → ComplexPoint Y)
variable (hF : MDifferentiable 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ) F)
variable (p : ComplexPoint X)

/-- The fixed original canonical algebraic étale source chart. -/
abbrev nativeMapSourceChart := ComplexPoint.localChart X d p

/-- The genuine open domain on which a target regular section can be pulled back in this chart. -/
def nativeMapRegularOpen (U : Y.left.Opens) : Opens (Fin d → ℂ) :=
  ⟨(nativeMapSourceChart X d p).target ∩
      (fun w => F ((nativeMapSourceChart X d p).symm w)) ⁻¹' Point.overOpen U,
    (nativeMapSourceChart X d p).isOpen_inter_preimage_symm
      ((Point.isOpen_overOpen U).preimage hF.continuous)⟩

/-- Native regular-section pullbacks along F are scalar analytic in this actual source chart. -/
theorem analyticAt_nativeMap_regular (U : Y.left.Opens) (s : Γ(Y.left, U))
    {w : Fin d → ℂ} (hw : w ∈ nativeMapRegularOpen X Y d e F hF p U) :
    AnalyticAt ℂ (fun v => Point.evaluate U s (F ((nativeMapSourceChart X d p).symm v))) w := by
  let c := nativeMapSourceChart X d p
  have hc : MDifferentiableOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) c.symm c.target :=
    (mdifferentiable_chart (I := 𝓘(ℂ, Fin d → ℂ)) p).2
  have hm : MDifferentiableOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin e → ℂ)
      (fun v => F (c.symm v)) (nativeMapRegularOpen X Y d e F hF p U) :=
    (hF.mdifferentiableOn (s := Set.univ)).comp (hc.mono inter_subset_left)
      (fun _ _ => Set.mem_univ _)
  have hs := (canonicalPoint_holo Y e U s).mdifferentiableOn (by simp)
  have hd : MDifferentiableOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, ℂ)
      (fun v => Point.evaluate U s (F (c.symm v))) (nativeMapRegularOpen X Y d e F hF p U) :=
    hs.comp hm (fun _ h => h.2)
  exact analyticAt_of_differentiableOn (nativeMapRegularOpen X Y d e F hF p U).isOpen
    hd.differentiableOn hw

/-- An actual Oka section, not just an analytic scalar formula. -/
def nativeMapRegularSection (U : Y.left.Opens) (s : Γ(Y.left, U)) :
    OkaRing (nativeMapRegularOpen X Y d e F hF p U) :=
  OkaRing.mk (fun v => Point.evaluate U s (F ((nativeMapSourceChart X d p).symm v.1)))
    (okaAnalytic_restrict fun _ hv => analyticAt_nativeMap_regular X Y d e F hF p U s hv)

/-- The true value of the constructed section is the original native pullback value. -/
theorem nativeMapRegularSection_eval (U : Y.left.Opens) (s : Γ(Y.left, U))
    (w : nativeMapRegularOpen X Y d e F hF p U) :
    OkaRing.evalHom w.2 (nativeMapRegularSection X Y d e F hF p U s) =
      Point.evaluate U s (F ((nativeMapSourceChart X d p).symm w.1)) := rfl

/-- The original centre lies in the actual pulled-back regular-section chart domain. -/
theorem nativeMapRegularOpen_centre (U : Y.left.Opens) (hp : F p ∈ Point.overOpen U) :
    nativeMapSourceChart X d p p ∈ nativeMapRegularOpen X Y d e F hF p U := by
  let c := nativeMapSourceChart X d p
  have hc : p ∈ c.source := ComplexPoint.mem_localChart_source X d p
  refine ⟨c.map_source hc, ?_⟩
  exact (congrArg (fun q => F q ∈ Point.overOpen U) (c.left_inv hc)).mpr hp

end ZInQ.Contrib.CloudB3W17bOkaComparison

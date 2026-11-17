import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AffineChartLRS
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.OpenGermEvaluation

/-!
# Original native point and evaluation realization of the constructed affine chart LRS map

This proves the genuine Γ–Spec point dictionary for the constructed chart,
using the actual residue evaluation on the actual open Oka source.  The point
is the inverse of the SAME native canonical algebraic étale chart.  No
homeomorphism/model compatibility or algebraic F/H witness is assumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (z : ComplexPoint X) (w : actualEtaleOkaSource X d z)

local instance pointAffine : IsAffine (actualEtaleNativeScheme X d z).left :=
  (actualEtaleDatum X d z).isAffine

local instance pointComplexAlgebra : Algebra ℂ Γ((actualEtaleDatum X d z).neighborhood.toScheme, ⊤) :=
  (actualEtaleDatum X d z).coordinateRingComplexAlgebra

/-- The actual source global-section values composed with μ are the actual native inverse-chart values. -/
theorem affineChartGlobalValue_comp_pullback :
    (openOkaGlobalValue (actualEtaleOkaOpen X d z) w).comp (actualEtaleOkaGlobalPullback X d z) =
      ((actualEtaleDatum X d z).pointAlgHomHomeomorph
        (actualEtaleChartPoint X d z ((affineCoordinateULift d).symm w.1))).toRingHom := by
  apply RingHom.ext
  intro s
  let U := actualEtaleOkaOpen X d z
  have h₁ := openOkaGermEval_germ U w ⊤ trivial (actualEtaleOkaGlobalPullback X d z s)
  have hle : openOkaSectionImage U ⊤ ≤ U :=
    LocallyRingedSpace.imOpen_le (X := _root_.complexAffineSpace d) U ⊤
  have h₂ := OkaRing.evalHom_restrict hle
    (openOkaMemSectionImage U w ⊤ trivial) (actualEtaleOkaRingPullback X d z s)
  have h₃ := actualEtaleOkaRingPullback_eval X d z s w
  exact h₁.trans (h₂.trans (h₃.trans
    ((actualEtaleDatum X d z).pointAlgHomHomeomorph_apply _ s).symm))

/-- The actual native affine point's Γ coordinates identify its genuine scheme map. -/
theorem actualEtalePointAlgHom_spec
    (q : ComplexPoint (actualEtaleNativeScheme X d z)) :
    Spec.map (CommRingCat.ofHom
      ((actualEtaleDatum X d z).pointAlgHomHomeomorph q).toRingHom) =
        q.left ≫ (actualEtaleNativeScheme X d z).left.toSpecΓ := by
  let D := actualEtaleDatum X d z
  letI := D.coordinateRingComplexAlgebra
  have H := congrArg (fun p : ComplexPoint (Over.mk
      (ComplexPoint.affineSpecStructureMap Γ(D.neighborhood.toScheme, ⊤))) => p.left)
    ((ComplexPoint.affineSpecEquiv Γ(D.neighborhood.toScheme, ⊤)).symm_apply_apply
      (D.affineSpecPointHomeomorph q))
  exact H

/-- The constructed LRS chart map has the ORIGINAL inverse-chart point on its underlying carrier. -/
theorem affineChartToNativeLRS_base :
    (affineChartToNativeLRS X d z).base w =
      (actualEtaleChartPoint X d z ((affineCoordinateULift d).symm w.1)).underlying := by
  let U := actualEtaleOkaOpen X d z
  let Z := actualEtaleOkaSource X d z
  let V := actualEtaleNativeScheme X d z
  let D := actualEtaleDatum X d z
  let q := actualEtaleChartPoint X d z ((affineCoordinateULift d).symm w.1)
  let e := asIso V.left.toSpecΓ
  let μ := actualEtaleOkaGlobalPullback X d z
  let v := openOkaGlobalValue U w
  let a := (D.pointAlgHomHomeomorph q).toRingHom
  have hvalue : v.comp μ = a := affineChartGlobalValue_comp_pullback X d z w
  have hspec : Spec.map (CommRingCat.ofHom v) ≫ Spec.map (CommRingCat.ofHom μ) =
      Spec.map (CommRingCat.ofHom a) := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hvalue)
  have hpoint : Spec.map (CommRingCat.ofHom v) ≫ Spec.map (CommRingCat.ofHom μ) ≫ e.inv = q.left := by
    calc
      _ = Spec.map (CommRingCat.ofHom a) ≫ e.inv :=
        (Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ e.inv) hspec)
      _ = (q.left ≫ e.hom) ≫ e.inv :=
        congrArg (fun m => m ≫ e.inv) (actualEtalePointAlgHom_spec X d z q)
      _ = q.left := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change e.inv (Spec.map (CommRingCat.ofHom μ) (Z.toLocallyRingedSpace.toΓSpec.base w)) = q.underlying
  have hbase := openOka_toΓSpec_base U w
  exact (congrArg (fun y => e.inv (Spec.map (CommRingCat.ofHom μ) y)) hbase).trans
    (congrArg (fun f : Spec (CommRingCat.of ℂ) ⟶ V.left => f (IsLocalRing.closedPoint ℂ)) hpoint)

end ZInQ.Contrib.CloudB3W17bOkaComparison

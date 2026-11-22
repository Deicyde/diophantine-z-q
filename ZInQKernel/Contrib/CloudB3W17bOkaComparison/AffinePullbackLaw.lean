import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AffineChartLRS

/-!
# The actual Γ pullback law for the constructed affine chart morphism

This computes all regular-section pullbacks of the genuine Γ–Spec construction,
not just its underlying point map or its values.  Naturality of the actual
Γ–Spec unit and the actual affine scheme isomorphism prove the equality.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

/-- The genuine Γ–Spec affine construction pulls back EVERY regular section by μ. -/
theorem affine_lrs_gamma_pullback (V : Scheme) [IsAffine V] (Z : LocallyRingedSpace)
    (μ : Γ(V, ⊤) →+* Z.presheaf.obj (op ⊤)) :
    (LocallyRingedSpace.Γ.map
      (Z.toSpecOfAlgMap μ ≫ (asIso V.toSpecΓ).inv.toLRSHom).op).hom = μ := by
  let e := asIso V.toSpecΓ
  let F := Z.toSpecOfAlgMap μ ≫ e.inv.toLRSHom
  have he : e.inv.toLRSHom ≫ e.hom.toLRSHom = 𝟙 _ :=
    congrArg Scheme.Hom.toLRSHom e.inv_hom_id
  have hf : F ≫ V.toLocallyRingedSpace.toΓSpec = Z.toSpecOfAlgMap μ :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m => Z.toSpecOfAlgMap μ ≫ m) he).trans (Category.comp_id _))
  apply LocallyRingedSpace.toSpecOfAlgMap_injective Z
  exact (LocallyRingedSpace.toΓSpec_naturality F).symm.trans hf

/-- Morphisms from a genuine locally ringed space into an actual affine scheme
are determined by their actual regular-ring pullbacks. -/
theorem affine_lrs_hom_ext (V : Scheme) [IsAffine V] (Z : LocallyRingedSpace)
    (f g : Z ⟶ V.toLocallyRingedSpace)
    (h : (LocallyRingedSpace.Γ.map f.op).hom = (LocallyRingedSpace.Γ.map g.op).hom) : f = g := by
  let e := asIso V.toSpecΓ
  have H : f ≫ e.hom.toLRSHom = g ≫ e.hom.toLRSHom :=
    (LocallyRingedSpace.toΓSpec_naturality f).trans
      ((congrArg (fun μ => Z.toSpecOfAlgMap μ) h).trans
        (LocallyRingedSpace.toΓSpec_naturality g).symm)
  have he : e.hom.toLRSHom ≫ e.inv.toLRSHom = 𝟙 _ :=
    congrArg Scheme.Hom.toLRSHom e.hom_inv_id
  have HH := congrArg (fun m => m ≫ e.inv.toLRSHom) H
  simpa only [Category.assoc, he, Category.comp_id] using HH

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (z : ComplexPoint X)

local instance affineChartAffine : IsAffine (actualEtaleNativeScheme X d z).left :=
  (actualEtaleDatum X d z).isAffine

/-- The constructed original-chart LRS morphism has literally the proved Γ pullback. -/
theorem affineChartToNativeLRS_gamma_pullback :
    (LocallyRingedSpace.Γ.map (affineChartToNativeLRS X d z).op).hom =
      actualEtaleOkaGlobalPullback X d z :=
  affine_lrs_gamma_pullback (actualEtaleNativeScheme X d z).left
    (actualEtaleOkaSource X d z).toLocallyRingedSpace (actualEtaleOkaGlobalPullback X d z)

end ZInQ.Contrib.CloudB3W17bOkaComparison

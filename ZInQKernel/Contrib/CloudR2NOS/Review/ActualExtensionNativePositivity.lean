/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

CONSTRUCT the actual invertible model line M and literal original generic
beta from the GIVEN original generic line, then prove its actual special
native H0/chi positivity. No M/beta existence or special-positivity premise.
The generic line's positivity is intermediate DATA to be supplied by the
original-A/K line constructor/comparison, not a final NOS assumption.
Replay only after a parent-owned consistent Source/native stage view exists;
no private old-4b/new-AE21 provider mixture is authorized by this source.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.StageNativePositivity
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.GenericLineExtension
import ZInQKernel.Contrib.CloudR2NOS.Review.AmpleCoefficientBridge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ZInQ.Contrib.CloudR2NOS.Spreadout.GenericCohomologyTransport

namespace ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension

/-- Genuine extension and original beta are constructed by C3; native
invertibility and special positivity follow for that SAME constructed M. -/
theorem exists_actual_extension_special_positive_of_originalLine
    {O Bs : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing Bs] [IsDomain Bs] [IsDiscreteValuationRing Bs] [Algebra O Bs]
    (hinj : Function.Injective (algebraMap O Bs))
    (V : (Spec (CommRingCat.of O)).Opens)
    (hV : ∀ z : Spec (CommRingCat.of O), z ∉ V → z = IsLocalRing.closedPoint O)
    {K : Type u} [Field K] (iV : V.toScheme ≅ Spec (CommRingCat.of K))
    (G : Grp (Over (Spec (CommRingCat.of Bs)))) [PkgI2.IsAbelianScheme G]
    (A₀ : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A₀]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ⁻¹ᵁ V).ι).mapGrp.obj G ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ∣_ V)).mapGrp.obj
        ((Over.pullback iV.hom).mapGrp.obj A₀))
    (L₀ : A₀.X.left.Modules)
    (hL : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.IsInvertible L₀)
    (h0 : 0 < L₀.hFiber A₀.X.hom 0 (IsLocalRing.closedPoint K))
    (hχ : L₀.eulerCharFiber A₀.X.hom (IsLocalRing.closedPoint K) ≠ 0) :
    ∃ M : G.X.left.Modules,
      ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.IsInvertible M ∧
      ∃ β : (Scheme.Modules.pullback
            (G.X.hom ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ⁻¹ᵁ V)).ι).obj M ≅
          (Scheme.Modules.pullback (ZInQ.Contrib.CloudR2NOS.GoodDescent.genericModelOfGroupIso
            (Spec.map (CommRingCat.ofHom (algebraMap O Bs))) V G
              ((Over.pullback iV.hom).mapGrp.obj A₀) e).q).obj (pullbackLine iV A₀ L₀),
        M.IsInvertible ∧ 0 < M.hFiber G.X.hom 0 (IsLocalRing.closedPoint Bs) ∧
          M.eulerCharFiber G.X.hom (IsLocalRing.closedPoint Bs) ≠ 0 := by
  have hLV : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.IsInvertible
      (pullbackLine iV A₀ L₀) :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.IsInvertible.pullback
      (pullback.fst A₀.X.hom iV.hom) hL
  obtain ⟨M, hM, ⟨β⟩⟩ :=
    ZInQ.Contrib.CloudR2NOS.Spreadout.InvertibleExtension.exists_extension_on_genericOpen
      (Spec.map (CommRingCat.ofHom (algebraMap O Bs))) V G
      ((Over.pullback iV.hom).mapGrp.obj A₀) e (pullbackLine iV A₀ L₀) hLV
  haveI : L₀.IsInvertible := (source_isInvertible_iff_sheaf L₀).mp hL
  haveI hMn : M.IsInvertible := (source_isInvertible_iff_sheaf M).mp hM
  exact ⟨M, hM, β, hMn, special_positive_of_originalLine hinj V hV iV G A₀ e M L₀ β h0 hχ⟩

#print axioms exists_actual_extension_special_positive_of_originalLine

end ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension

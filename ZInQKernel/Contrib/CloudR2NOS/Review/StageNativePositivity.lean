/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Native positivity at the ACTUAL special point of the stage DVR, from the
ORIGINAL generic line and the actual generic-open beta/q. Generic field
positivity is constructed by C1 and transported by C3; relative flatness,
finite presentation and quasi-coherence are derived for the same model M.
This supplies H0/chi only, NOT finite stabilizer, ampleness, relative VA or NOS.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.AmpleH0
import ZInQKernel.Contrib.CloudR2NOS.SingleOrder.GenericLinePositivity
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.GenericLineCohomology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open ZInQ.Contrib.CloudR2NOS.Spreadout.GenericCohomologyTransport

namespace ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension

variable {O Bs : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
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

include hinj hV

/-- The ORIGINAL line's positive H0/nonzero chi give actual special H0/chi
for ANY genuine native invertible extension with the actual original beta. -/
theorem special_positive_of_originalLine
    (M : G.X.left.Modules) [M.IsInvertible]
    (L₀ : A₀.X.left.Modules) [L₀.IsInvertible]
    (β : (Scheme.Modules.pullback
        (G.X.hom ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ⁻¹ᵁ V)).ι).obj M ≅
      (Scheme.Modules.pullback (GoodDescent.genericModelOfGroupIso
        (Spec.map (CommRingCat.ofHom (algebraMap O Bs))) V G
          ((Over.pullback iV.hom).mapGrp.obj A₀) e).q).obj (pullbackLine iV A₀ L₀))
    (h0 : 0 < L₀.hFiber A₀.X.hom 0 (IsLocalRing.closedPoint K))
    (hχ : L₀.eulerCharFiber A₀.X.hom (IsLocalRing.closedPoint K) ≠ 0) :
    0 < M.hFiber G.X.hom 0 (IsLocalRing.closedPoint Bs) ∧
      M.eulerCharFiber G.X.hom (IsLocalRing.closedPoint Bs) ≠ 0 := by
  haveI : IsProper G.X.hom := PkgI2.IsAbelianScheme.proper
  haveI : Smooth G.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : IsProper A₀.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : M.IsFinitePresentation := isFinitePresentation_of_invertible M
  haveI : L₀.IsFinitePresentation := isFinitePresentation_of_invertible L₀
  haveI : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  haveI : L₀.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData L₀).choose.isQuasicoherent
  letI : A₀.X.left.Over (Spec (CommRingCat.of K)) := ⟨A₀.X.hom⟩
  have hg0 := hFiber_genericPoint_originalLine hinj V hV iV G A₀ e M L₀ β 0
  have hgχ := eulerCharFiber_genericPoint_originalLine hinj V hV iV G A₀ e M L₀ β
  have hf0 : L₀.hFiber A₀.X.hom 0 (IsLocalRing.closedPoint K) = L₀.finrankH K 0 :=
    Scheme.Modules.hFiber_eq_finrankH A₀.X.hom L₀ 0 (IsLocalRing.closedPoint K)
  have hfχ : L₀.eulerCharFiber A₀.X.hom (IsLocalRing.closedPoint K) = L₀.eulerChar K := by
    simp only [Scheme.Modules.eulerCharFiber, Scheme.Modules.eulerChar,
      Scheme.Modules.hFiber_eq_finrankH A₀.X.hom L₀]
  have hη0 : 0 < M.hFiber G.X.hom 0 (genericPoint (Spec (CommRingCat.of Bs))) := by
    rw [hg0, ← hf0]
    exact h0
  have hηχ : M.eulerCharFiber G.X.hom (genericPoint (Spec (CommRingCat.of Bs))) ≠ 0 := by
    rw [hgχ, ← hfχ]
    exact hχ
  have hsp : genericPoint (Spec (CommRingCat.of Bs)) ⤳ IsLocalRing.closedPoint Bs :=
    (genericPoint_spec _).specializes (Set.mem_univ _)
  have hflat := Scheme.Modules.isFlatOver_of_isInvertible G.X.hom M
  refine ⟨h0_pos_of_specializes G.X.hom M hflat hsp hη0, ?_⟩
  rw [← eulerCharFiber_eq_over_domain G.X.hom M hflat
    (genericPoint (Spec (CommRingCat.of Bs))) (IsLocalRing.closedPoint Bs)]
  exact hηχ

/-- Construct ORIGINAL generic field positivity without a positivity premise.
The returned original L₀ can be fed to the genuine extension supplier; every
actual invertible M/beta extending it has positive special H0/nonzero chi. -/
theorem exists_originalLine_with_special_positive_extensions :
    ∃ L₀ : A₀.X.left.Modules, L₀.IsInvertible ∧
      ∀ (M : G.X.left.Modules) [M.IsInvertible]
        (β : (Scheme.Modules.pullback
            (G.X.hom ⁻¹ᵁ (Spec.map (CommRingCat.ofHom (algebraMap O Bs)) ⁻¹ᵁ V)).ι).obj M ≅
          (Scheme.Modules.pullback (GoodDescent.genericModelOfGroupIso
            (Spec.map (CommRingCat.ofHom (algebraMap O Bs))) V G
              ((Over.pullback iV.hom).mapGrp.obj A₀) e).q).obj (pullbackLine iV A₀ L₀)),
        0 < M.hFiber G.X.hom 0 (IsLocalRing.closedPoint Bs) ∧
          M.eulerCharFiber G.X.hom (IsLocalRing.closedPoint Bs) ≠ 0 := by
  obtain ⟨L₀, hL, h0, hχ⟩ :=
    ZInQ.Contrib.CloudR2NOS.SingleOrder.GenericLinePositivity.exists_line_hFiber_pos_eulerCharFiber_ne_zero A₀
  haveI := hL
  refine ⟨L₀, hL, ?_⟩
  intro M hM β
  exact special_positive_of_originalLine hinj V hV iV G A₀ e M L₀ β h0 hχ

#print axioms special_positive_of_originalLine
#print axioms exists_originalLine_with_special_positive_extensions

end ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension

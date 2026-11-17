/-
Copyright (c) 2026 H5 contributors. Apache-2.0.
EXACT C3 K-a CodimOneLocalizationsDetermine.{u}, SOURCE ONLY / UNCOMPILED.
I/J and every affine/stalk/height-one ring map stay literal original objects.

The proof does NOT assume an affine open has a global UFD ring: only the
ACTUAL stalk is UFD, derived from native A2 and A1. On an actual common affine
neighbourhood where the given invertible ideals are regular principal, their
stalk ideals are regular principal. Original height-one affine data pull to
the stalk's height-one data by actual nested-localization algebra maps and
height-under invariance. Native reduced fractions then detect equality.
Affine ideal/stalk extensionality glues equality of the ORIGINAL ideals.
No Krull/valuation/normal/rank/Picard or ideal-support Factory is added.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.KeyPlan
import I0RegularLocalUFD
import I0SmoothFieldStalkRegular
import CodimOneRingIdeals
import Mathlib.AlgebraicGeometry.FunctionField

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped nonZeroDivisors

namespace H5OriginalDVR.Lane5.I0Native

/-- The ideal-germ map is the SAME on nested actual affine neighbourhoods. -/
theorem ideal_germ_map_of_affine_le
    {X : Scheme.{u}} (I : X.IdealSheafData) (U V : X.affineOpens)
    (hVU : V.1 ≤ U.1) (x : X) (hxV : x ∈ V.1) :
    (I.ideal U).map (X.presheaf.germ U.1 x (hVU hxV)).hom =
      (I.ideal V).map (X.presheaf.germ V.1 x hxV).hom := by
  rw [← I.map_ideal hVU, Ideal.map_map, ← CommRingCat.hom_comp,
    X.presheaf.germ_res]

/-- EXACT C3 K-a; no proof-bearing assumption beyond the consumer inputs. -/
theorem codimOneLocalizationsDetermine :
    ZInQ.Contrib.CloudR2NOS.Step2B1.CodimOneLocalizationsDetermine.{u} := by
  intro K _ _ A _ I J hI hJ hloc
  letI : Smooth A.X.hom := PkgI2.IsAbelianVariety.smooth
  letI : GeometricallyIntegral A.X.hom := PkgI2.IsAbelianVariety.geomIntegral
  letI : IsIntegral A.X.left :=
    GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  apply Scheme.IdealSheafData.ext
  funext U
  rw [U.2.ideal_ext_iff]
  intro x hxU
  let S : Type u := A.X.left.presheaf.stalk x
  letI : IsRegularLocalRing S := smoothFieldStalkRegular A.X.hom x
  letI : UniqueFactorizationMonoid S := regularLocalUFD S
  letI : IsDomain S := inferInstance
  obtain ⟨V_I, hxI, f, hf, hIf⟩ := hI x
  obtain ⟨V_J, hxJ, g, hg, hJg⟩ := hJ x
  letI : Nonempty V_I.1 := ⟨⟨x, hxI⟩⟩
  letI : Nonempty V_J.1 := ⟨⟨x, hxJ⟩⟩
  obtain ⟨W₀, hW₀, hxW, hWsub⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (U.1 ⊓ V_I.1) ⊓ V_J.1 from ⟨⟨hxU, hxI⟩, hxJ⟩)
  let W : A.X.left.affineOpens := ⟨W₀, hW₀⟩
  have hWU : W.1 ≤ U.1 := fun z hz => (hWsub hz).1.1
  have hWI : W.1 ≤ V_I.1 := fun z hz => (hWsub hz).1.2
  have hWJ : W.1 ≤ V_J.1 := fun z hz => (hWsub hz).2
  let ψ : Γ(A.X.left, W.1) →+* S :=
    (A.X.left.presheaf.germ W.1 x hxW).hom
  letI : Algebra Γ(A.X.left, W.1) S :=
    TopCat.Presheaf.algebra_section_stalk A.X.left.presheaf ⟨x, hxW⟩
  let p : Ideal Γ(A.X.left, W.1) := (W.2.primeIdealOf ⟨x, hxW⟩).asIdeal
  letI : p.IsPrime := inferInstance
  letI : IsLocalization.AtPrime S p := W.2.isLocalization_stalk ⟨x, hxW⟩
  let fW : Γ(A.X.left, W.1) :=
    A.X.left.presheaf.map (homOfLE hWI).op f
  let gW : Γ(A.X.left, W.1) :=
    A.X.left.presheaf.map (homOfLE hWJ).op g
  have hIW : I.ideal W = Ideal.span {fW} := by
    rw [← I.map_ideal hWI, hIf, Ideal.map_span, Set.image_singleton]
    rfl
  have hJW : J.ideal W = Ideal.span {gW} := by
    rw [← J.map_ideal hWJ, hJg, Ideal.map_span, Set.image_singleton]
    rfl
  have hfGerm : ψ fW = A.X.left.presheaf.germ V_I.1 x hxI f :=
    A.X.left.presheaf.germ_res_apply (homOfLE hWI) x hxW f
  have hgGerm : ψ gW = A.X.left.presheaf.germ V_J.1 x hxJ g :=
    A.X.left.presheaf.germ_res_apply (homOfLE hWJ) x hxW g
  have hfψ : ψ fW ≠ 0 := by
    rw [hfGerm]
    intro hz
    apply nonZeroDivisors.ne_zero hf
    apply germ_injective_of_isIntegral A.X.left x hxI
    simpa only [map_zero] using hz
  have hgψ : ψ gW ≠ 0 := by
    rw [hgGerm]
    intro hz
    apply nonZeroDivisors.ne_zero hg
    apply germ_injective_of_isIntegral A.X.left x hxJ
    simpa only [map_zero] using hz
  have hIψ : ((I.ideal W).map (algebraMap Γ(A.X.left, W.1) S)).IsRegularPrincipal := by
    change ((I.ideal W).map ψ).IsRegularPrincipal
    rw [hIW, Ideal.map_span, Set.image_singleton]
    exact Ideal.isRegularPrincipal_span_singleton (mem_nonZeroDivisors_of_ne_zero hfψ)
  have hJψ : ((J.ideal W).map (algebraMap Γ(A.X.left, W.1) S)).IsRegularPrincipal := by
    change ((J.ideal W).map ψ).IsRegularPrincipal
    rw [hJW, Ideal.map_span, Set.image_singleton]
    exact Ideal.isRegularPrincipal_span_singleton (mem_nonZeroDivisors_of_ne_zero hgψ)
  have heqS : (I.ideal W).map ψ = (J.ideal W).map ψ :=
    localized_regular_principal_eq_of_height_one p (I.ideal W) (J.ideal W)
      hIψ hJψ (hloc W)
  calc (I.ideal U).map (A.X.left.presheaf.germ U.1 x hxU).hom
      = (I.ideal W).map (A.X.left.presheaf.germ W.1 x hxW).hom :=
        ideal_germ_map_of_affine_le I U W hWU x hxW
    _ = (J.ideal W).map (A.X.left.presheaf.germ W.1 x hxW).hom := heqS
    _ = (J.ideal U).map (A.X.left.presheaf.germ U.1 x hxU).hom :=
      (ideal_germ_map_of_affine_le J U W hWU x hxW).symm

end H5OriginalDVR.Lane5.I0Native

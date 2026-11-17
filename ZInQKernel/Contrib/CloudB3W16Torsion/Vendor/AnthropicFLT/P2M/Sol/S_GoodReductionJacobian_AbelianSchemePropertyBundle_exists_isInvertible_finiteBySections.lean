/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isInvertible_finiteBySections. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_forall_nonempty_pullback_translate_tensor_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_hom_ne_zero_finite_setOf_stabilizer
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isFinite_toProj_of_finite_setOf_forall_pullbackSection_eq_zero_iff
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_tensorPow_three_of_forall_nonempty_pullback_tensor_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isInvertible_finiteBySections

set_option autoImplicit false
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open NeronModelInfra
open GoodReductionJacobian

open scoped CategoryTheory.MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace P2mAbProj

theorem isInvertible_tensorPow {X : Scheme.{u}} {𝓛 : X.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    ∀ n : ℕ, Scheme.Modules.IsInvertible (𝓛.tensorPowFLT n)
  | 0 => Scheme.Modules.isInvertible_unitFLT X
  | n + 1 => (isInvertible_tensorPow h𝓛 n).tensor h𝓛

theorem geometricallyConnected_of_geometricallyIntegral {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyIntegral f] :
    GeometricallyConnected f := by
  have h : geometrically (IrreducibleSpace ·) f := by
    rw [← GeometricallyIrreducible.eq_geometrically]; infer_instance
  refine ⟨fun K _ y Z fst snd hp => ?_⟩
  haveI : IrreducibleSpace Z := h y fst snd hp
  infer_instance

theorem main (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) :
    ∃ 𝓛 : A.Modules, Scheme.Modules.IsInvertible 𝓛 ∧ 𝓛.FiniteBySections f := by
  haveI : IsProper f := hA.proper
  haveI : IsIntegral A := hA.isIntegral_of_field
  haveI : GeometricallyIntegral f := hA.geometricallyIntegral
  obtain ⟨G⟩ := hA.hasGroupLaw
  letI : GrpObj (Over.mk f) := G.grpObjOverMk
  haveI : IsProper (Over.mk f : Over (Spec (CommRingCat.of K))).hom := ‹IsProper f›
  haveI : GeometricallyIntegral (Over.mk f : Over (Spec (CommRingCat.of K))).hom := ‹GeometricallyIntegral f›
  haveI : IsCommMonObj (Over.mk f) := isCommMonObj_of_isProper_of_geometricallyIntegral (Over.mk f)
  have hgc : GeometricallyConnected f := geometricallyConnected_of_geometricallyIntegral f

  obtain ⟨L, hL, θ, hθ, hfin⟩ :=
    Scheme.Modules.exists_isInvertible_hom_ne_zero_finite_setOf_stabilizer K f hA.smooth

  have hsq := fun x y =>
    Scheme.Modules.forall_nonempty_pullback_translate_tensor_iso K f hA.smooth hA.proper hgc L hL x y

  obtain ⟨N, σ, U, hU, hframe⟩ :=
    Scheme.Modules.exists_isFrameOn_tensorPow_three_of_forall_nonempty_pullback_tensor_iso K f L hL hsq θ hθ
  obtain ⟨𝔓, -, -⟩ := Scheme.Modules.exists_projPresentation_of_iSup_eq_top f (L.tensorPowFLT 3) N σ U hU
    (fun i V hV => hframe i le_top hV)

  have hF : IsFinite 𝔓.toProj :=
    Scheme.Modules.ProjPresentation.isFinite_toProj_of_finite_setOf_forall_pullbackSection_eq_zero_iff K f L hL hsq θ
      hfin 𝔓
  exact ⟨L.tensorPowFLT 3, isInvertible_tensorPow hL 3, N, 𝔓, hF⟩

end P2mAbProj

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) :
    ∃ 𝓛 : A.Modules, Scheme.Modules.IsInvertible 𝓛 ∧ 𝓛.FiniteBySections f :=
  P2mAbProj.main K f hA

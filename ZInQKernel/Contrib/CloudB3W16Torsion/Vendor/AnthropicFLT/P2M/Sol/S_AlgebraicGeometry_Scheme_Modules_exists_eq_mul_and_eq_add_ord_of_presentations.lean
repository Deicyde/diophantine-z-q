/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_eq_mul_and_eq_add_ord_of_presentations. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_forall_eq_mul_of_presentations
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_place_range_stalk_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_eq_mul_and_eq_add_ord_of_presentations

set_option autoImplicit false

universe u
open CategoryTheory
open AlgebraicGeometry
-- Deferred synthetic P2M scope: root namespace remains open.
open Opposite
open TopologicalSpace

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (SmoothOfRelativeDimension IsProper IsAffine.of_isIso IsAffine Spec IsIntegral Scheme IsAffineOpen Scheme.Modules Scheme.Modules.exists_forall_eq_mul_of_presentations not_isAffine_of_isProper_of_smoothOfRelativeDimension_one)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (Γ topIso functionField isBasis_affineOpens Modules Opens Modules.exists_forall_eq_mul_of_presentations)
namespace Modules
export _root_.AlgebraicGeometry.Scheme.Modules (presheaf exists_forall_eq_mul_of_presentations)
namespace PresUniq
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme
open AlgebraicGeometry
open AlgebraicCurve TopologicalSpace WithZero

theorem exists_not_mem_placesOf {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (U : X.Opens) (hU : IsAffineOpen U) [hUne : Nonempty U] :
    letI := (baseToFunctionField x).toAlgebra
    ∃ v₀ : Place K X.functionField, v₀ ∉ placesOf x U := by
  letI := (baseToFunctionField x).toAlgebra
  have hNA := not_isAffine_of_isProper_of_smoothOfRelativeDimension_one x
  have hne : U ≠ ⊤ := by
    intro h
    apply hNA
    have hT : IsAffineOpen (⊤ : X.Opens) := h ▸ hU
    haveI : IsAffine (⊤ : X.Opens) := hT
    exact IsAffine.of_isIso X.topIso.inv
  obtain ⟨y, hy⟩ : ∃ y : X, y ∉ U := by
    by_contra hall
    exact hne (eq_top_iff.mpr fun z _ => by_contra fun hz => hall ⟨z, hz⟩)
  have hUne' : ((U : Set X)).Nonempty := let ⟨⟨z, hz⟩⟩ := hUne; ⟨z, hz⟩
  have hη : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hUne')
  have hyη : y ≠ genericPoint X := fun h => hy (h ▸ hη)
  obtain ⟨v₀, hv₀⟩ := exists_place_range_stalk_eq x y (isClosed_singleton_of_ne_genericPoint x y hyη)
  refine ⟨v₀, ?_⟩
  rintro ⟨y', hy'U, -, hv₀'⟩
  have : y' = y := eq_of_range_stalk_eq x y' y (hv₀'.trans hv₀.symm)
  exact hy (this ▸ hy'U)

theorem exp_eq_mul_exp_of_forall_mem_iff {K F : Type*} [Field K] [Field F] [Algebra K F]
    (S : Set (Place K F)) (D D' : Divisor K F) (g : F)
    (hiff : ∀ f : F, f ∈ lSpaceOn S D' ↔ ∃ f₀ ∈ lSpaceOn S D, f = g * f₀)
    (v : Place K F) (hv : v ∈ S)
    (hatt : ∃ f : F, f ∈ lSpaceOn S D ∧ v.adicValuation f = exp (D v))
    (hatt' : ∃ f : F, f ∈ lSpaceOn S D' ∧ v.adicValuation f = exp (D' v)) :
    exp (D' v) = v.adicValuation g * exp (D v) := by
  apply le_antisymm
  · obtain ⟨f', hf', hval'⟩ := hatt'
    obtain ⟨f₀, hf₀, rfl⟩ := (hiff f').mp hf'
    rw [← hval', Valuation.map_mul]
    exact mul_le_mul_right (hf₀ v hv) _
  · obtain ⟨f, hf, hval⟩ := hatt
    have hgf : g * f ∈ lSpaceOn S D' := (hiff (g * f)).mpr ⟨f, hf, rfl⟩
    have := hgf v hv
    rwa [Valuation.map_mul, hval] at this

end AlgebraicGeometry.Scheme.Modules.PresUniq

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper IsAffine.of_isIso IsAffine Spec IsIntegral Scheme IsAffineOpen Scheme.Modules Scheme.Modules.exists_forall_eq_mul_of_presentations not_isAffine_of_isProper_of_smoothOfRelativeDimension_one" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Γ topIso functionField isBasis_affineOpens Modules Opens Modules.exists_forall_eq_mul_of_presentations" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf exists_forall_eq_mul_of_presentations" end AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules in
open AlgebraicGeometry.Scheme.Modules.PresUniq AlgebraicCurve in

theorem AlgebraicGeometry.Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations'
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (M : X.Modules)
    (D D' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ φ' : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ' V (M.presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField))
    (hsec : ∃ (U : X.Opens) (m : Γ(M, U)), m ≠ 0) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ g : X.functionField, g ≠ 0 ∧
      (∀ (U : X.Opens) [Nonempty U] (m : Γ(M, U)), φ' U m = g * φ U m) ∧
      (∀ v : AlgebraicCurve.Place K X.functionField, D v = D' v + v.ord g) ∧
      AlgebraicCurve.Divisor.IsPrincipal (D - D') := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra

  haveI hcurve : IsCurveOver K X.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one x (RingEquiv.refl _) (fun _ => rfl)
  haveI : Algebra.EssFiniteType K X.functionField := essFiniteType_functionField x

  obtain ⟨g, hg, hmul⟩ :=
    Scheme.Modules.exists_forall_eq_mul_of_presentations M φ φ' hnat hnat' hsmul hsmul' hinj hinj' hsec
  have hord : ∀ v : Place K X.functionField, D v = D' v + v.ord g := by
    intro v

    obtain ⟨y, hy, hvy⟩ := exists_closedPoint_range_stalk_eq x v
    obtain ⟨U, hUaff, hyU, -⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (Opens.mem_top y)
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
    have hvS : v ∈ placesOf x U := ⟨y, hyU, hy, hvy⟩
    obtain ⟨v₀, hv₀⟩ := exists_not_mem_placesOf x U hUaff

    haveI : Nonempty (Place K X.functionField) := ⟨v⟩
    have hC : ConstantsAreBase K X.functionField :=
      constantsAreBase_of_deg_eq_one v (IsCurveOver.deg_eq_one_of_isAlgClosed v)
    obtain ⟨-, hL0, γ, D₀, hγ⟩ := stichtenothGenusExists_of_isCurveOver hC
    haveI := hL0

    have hiff : ∀ f : X.functionField,
        f ∈ lSpaceOn (placesOf x U) D' ↔ ∃ f₀ ∈ lSpaceOn (placesOf x U) D, f = g * f₀ := by
      intro f
      have hD : ∀ f₀, f₀ ∈ lSpaceOn (placesOf x U) D ↔ f₀ ∈ Set.range (φ U) := fun f₀ => by
        rw [hrange U hUaff inferInstance]; rfl
      have hD' : f ∈ lSpaceOn (placesOf x U) D' ↔ f ∈ Set.range (φ' U) := by
        rw [hrange' U hUaff inferInstance]; rfl
      rw [hD']
      constructor
      · rintro ⟨m, rfl⟩
        exact ⟨φ U m, (hD _).mpr ⟨m, rfl⟩, hmul U m⟩
      · rintro ⟨f₀, hf₀, rfl⟩
        obtain ⟨m, rfl⟩ := (hD f₀).mp hf₀
        exact ⟨m, hmul U m⟩
    have key := exp_eq_mul_exp_of_forall_mem_iff (placesOf x U) D D' g hiff v hvS
      (exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt hγ (placesOf x U) hv₀ D v hvS)
      (exists_mem_lSpaceOn_adicValuation_eq_of_riemannGenusReachedAt hγ (placesOf x U) hv₀ D' v hvS)
    rw [Place.adicValuation_eq_exp_neg_ord v hg, ← WithZero.exp_add] at key
    have := WithZero.exp_injective key
    omega
  refine ⟨g, hg, hmul, hord, g, hg, fun v => ?_⟩
  rw [Finsupp.sub_apply, hord v]
  ring

open AlgebraicGeometry.Scheme.Modules.PresUniq AlgebraicCurve in
theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (M : X.Modules)
    (D D' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ φ' : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ' V (M.presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField))
    (hsec : ∃ (U : X.Opens) (m : Γ(M, U)), m ≠ 0) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ g : X.functionField, g ≠ 0 ∧
      (∀ (U : X.Opens) [Nonempty U] (m : Γ(M, U)), φ' U m = g * φ U m) ∧
      (∀ v : AlgebraicCurve.Place K X.functionField, D v = D' v + v.ord g) ∧
      AlgebraicCurve.Divisor.IsPrincipal (D - D') :=
  AlgebraicGeometry.Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations' x M D D' φ φ' hnat hnat' hsmul hsmul'
    hinj hinj' hrange hrange' hsec

/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.RingTheory.FinitePresentation
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_genericPoint_notMem_support_zeroSchemeIdeal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_over_field
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_finite_compl_of_isOpen
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open TopologicalSpace

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    {M : (pullback f x).Modules} (hM : Scheme.Modules.IsInvertible M)
    (s : 𝟙_ (pullback f x).Modules ⟶ M) (hs : s ≠ 0) :
    ∃ (r : ℕ) (D : RelEffCartierDiv f r x), D.I = Scheme.Modules.zeroSchemeIdeal s := by
  classical

  let C : Scheme.{u} := pullback f x
  let c : C ⟶ Spec (CommRingCat.of k) := pullback.snd f x
  haveI : IsProper c := inferInstance
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 c :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) f x inferInstance
  haveI : QuasiCompact c := inferInstance

  haveI : IrreducibleSpace ↥C :=
    GeometricallyIrreducible.geometrically_irreducibleSpace (f := f) x (pullback.fst f x) c
      (IsPullback.of_hasPullback f x)
  haveI : IsReduced C :=
    isReduced_of_smooth_over_field (g := c) (SmoothOfRelativeDimension.smooth 1 c)
  haveI : IsIntegral C := isIntegral_of_irreducibleSpace_of_isReduced _

  let I : C.IdealSheafData := Scheme.Modules.zeroSchemeIdeal s
  let g : I.subscheme ⟶ Spec (CommRingCat.of k) := I.subschemeι ≫ c

  have hη : genericPoint C ∉ I.support :=
    Scheme.Modules.IsInvertible.genericPoint_notMem_support_zeroSchemeIdeal hM s hs
  have hfin : (I.support : Set C).Finite := by
    have h := AlgebraicCurve.finite_compl_of_isOpen c I.support.compl ⟨genericPoint _, hη⟩
    simpa [TopologicalSpace.Closeds.coe_compl, compl_compl] using h
  haveI : Finite ↥(I.subscheme) := by
    haveI : Finite (I.support : Set C) := hfin.to_subtype
    refine Finite.of_injective (fun z => (⟨I.subschemeι.base z, ?_⟩ : (I.support : Set C))) ?_
    · rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨z, rfl⟩
    · intro a b hab
      exact I.subschemeι.isClosedEmbedding.injective (congrArg Subtype.val hab)

  haveI : LocallyQuasiFinite g :=
    LocallyQuasiFinite.of_finite_preimage_singleton g fun y => Set.toFinite _
  haveI : IsProper g := inferInstance
  haveI hgfin : IsFinite g := IsFinite.of_isProper_of_locallyQuasiFinite g
  haveI : Flat g := inferInstance

  have hlofp : LocallyOfFinitePresentation g := by
    haveI : IsAffine I.subscheme := isAffine_of_isAffineHom g
    rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
    have hft : g.appTop.hom.Finite :=
      ((HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := g)).mp hgfin).2
    letI := g.appTop.hom.toAlgebra
    haveI : Module.Finite Γ(Spec (CommRingCat.of k), ⊤) Γ(I.subscheme, ⊤) := hft
    haveI : IsNoetherianRing Γ(Spec (CommRingCat.of k), ⊤) :=
      isNoetherianRing_of_ringEquiv k (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    exact Algebra.FinitePresentation.of_finiteType.mp inferInstance

  obtain ⟨t₀⟩ : Nonempty ↥(Spec (CommRingCat.of k)) := inferInstance
  refine ⟨g.finrank t₀, ⟨I, hgfin, inferInstance, hlofp, fun t => ?_⟩, rfl⟩
  rw [Subsingleton.elim t t₀]

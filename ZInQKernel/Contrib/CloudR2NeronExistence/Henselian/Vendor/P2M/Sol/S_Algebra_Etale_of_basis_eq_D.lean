import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_Algebra_Etale_of_basis_eq_D.lean
Original Git blob: c2a9393e5fb24f42c50ba6250252a8102391dd8a
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_Algebra_Etale_of_formallyUnramified_of_isStandardSmoothOfRelativeDimension
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_MvPolynomial_isStandardSmoothOfRelativeDimension_natCard
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "KaehlerDifferential"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_Algebra_Etale_of_basis_eq_D
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open KaehlerDifferential

universe u v

theorem solution
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    {ι : Type v} [Finite ι] (x : ι → S) (b : Module.Basis ι S Ω[S⁄R]) (hb : ∀ i, b i = D R S (x i))
    [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]
    (hx : ∀ i, algebraMap (MvPolynomial ι R) S (MvPolynomial.X i) = x i) :
    Algebra.Etale (MvPolynomial ι R) S := by
  classical
  set A := MvPolynomial ι R with hAdef
  rcases subsingleton_or_nontrivial S with hS | hS
  · infer_instance

  haveI : Algebra.IsStandardSmooth R S :=
    Algebra.IsStandardSmooth.of_basis_kaehlerDifferential b (by
      rintro _ ⟨i, rfl⟩; exact ⟨x i, (hb i).symm⟩)
  haveI hSn : Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ι) R S := by
    rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
    haveI : Fintype ι := Fintype.ofFinite ι
    rw [rank_eq_card_basis b, Nat.card_eq_fintype_card]
  haveI hAn : Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ι) R A :=
    MvPolynomial.isStandardSmoothOfRelativeDimension_natCard R ι

  have hrange : LinearMap.range (KaehlerDifferential.mapBaseChange R A S) = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨(1 : S) ⊗ₜ KaehlerDifferential.D R A (MvPolynomial.X i), ?_⟩
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D, hx, hb]
  haveI : Algebra.FormallyUnramified A S := by
    refine ⟨⟨fun ω₁ ω₂ => ?_⟩⟩
    have hzero : ∀ ω : Ω[S⁄A], ω = 0 := by
      intro ω
      obtain ⟨η, rfl⟩ := KaehlerDifferential.map_surjective R A S ω
      have hη : η ∈ LinearMap.ker (KaehlerDifferential.map R A S S) := by
        rw [(KaehlerDifferential.exact_mapBaseChange_map R A S).linearMap_ker_eq, hrange]
        trivial
      exact hη
    rw [hzero ω₁, hzero ω₂]
  exact Algebra.Etale.of_formallyUnramified_of_isStandardSmoothOfRelativeDimension (R := R) (Nat.card ι)


end P2MW.S_Algebra_Etale_of_basis_eq_D
end ZInQ.Contrib.CloudR2NeronExistence.Henselian

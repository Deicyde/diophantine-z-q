/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mTorsionCount

theorem locallyOfFinitePresentation_of_field (K : Type u) [Field K] {X : Scheme.{u}}
    (q : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType q] :
    LocallyOfFinitePresentation q := by
  haveI : IsNoetherianRing (Γ(Spec (CommRingCat.of K), ⊤) : CommRingCat.{u}) :=
    isNoetherianRing_of_ringEquiv K
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have h := (HasRingHomProperty.iff_of_source_openCover (P := @LocallyOfFiniteType)
    (f := q) X.affineCover).mp inferInstance
  exact HasRingHomProperty.of_source_openCover (P := @LocallyOfFinitePresentation)
    X.affineCover (fun i => RingHom.FinitePresentation.of_finiteType.mp (h i))

section Etale

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem etale_endKerStr_nsmul (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    [LocallyOfFiniteType f] (n : ℕ) (hn : (n : K) ≠ 0) :
    Etale (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) := by
  have hunit : IsUnit (n : K) := isUnit_iff_ne_zero.mpr hn
  haveI hfu : FormallyUnramified (L.schemeNsmul n) :=
    GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
      L (fun t x y => hc t x y) n hunit
  haveI : FormallyUnramified (L.nsmul f n RelativeGroupLaw.idPoint).1 := hfu
  haveI : LocallyOfFiniteType ((L.nsmul f n RelativeGroupLaw.idPoint).1 ≫ f) := by
    rw [(L.nsmul f n RelativeGroupLaw.idPoint).2]; infer_instance
  haveI : LocallyOfFiniteType (L.nsmul f n RelativeGroupLaw.idPoint).1 :=
    locallyOfFiniteType_of_comp _ f
  haveI : FormallyUnramified (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  haveI : LocallyOfFiniteType (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  haveI : LocallyOfFinitePresentation (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) :=
    locallyOfFinitePresentation_of_field K _
  haveI : Flat (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) := inferInstance
  exact Etale.of_formallyUnramified_of_flat _

end Etale

section Points

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem coe_nsmul_eq_comp (L : RelativeGroupLaw K f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : SchemeHomOver t f) :
    (L.nsmul t n x).1 = x.1 ≫ (L.nsmul f n RelativeGroupLaw.idPoint).1 := by
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id x.1)
  have h := L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  rw [hx] at h
  rw [← h]
  rfl

theorem isTorsionPoint_iff_schemeHomOverComp_eq (L : RelativeGroupLaw K f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : SchemeHomOver t f) :
    L.IsTorsionPoint t n x ↔
      NeronModelInfra.schemeHomOverComp x (L.nsmul f n RelativeGroupLaw.idPoint) = L.one t := by
  rw [RelativeGroupLaw.isTorsionPoint_def]
  constructor
  · intro h
    apply Subtype.ext
    rw [NeronModelInfra.schemeHomOverComp_coe, ← coe_nsmul_eq_comp, h]
  · intro h
    apply Subtype.ext
    rw [coe_nsmul_eq_comp, ← NeronModelInfra.schemeHomOverComp_coe, h]

end Points

theorem natCard_isTorsionPoint_eq_pow
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f] (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
        L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) n x} = n ^ (2 * g) := by
  haveI : IsProper f := hA.proper
  haveI : Etale (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) :=
    etale_endKerStr_nsmul L hc n hn
  obtain ⟨-, -, hcard⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
      K f L (L.nsmul f n RelativeGroupLaw.idPoint)
  have hdeg :=
    GoodReductionJacobian.RelativeGroupLaw.endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero
      K f L hc hA g n hn
  rw [← hdeg, ← hcard]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun x =>
    isTorsionPoint_iff_schemeHomOverComp_eq L (𝟙 _) n x))

theorem finite_isTorsionPoint
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f] (n : ℕ) (hn : (n : K) ≠ 0) :
    Finite {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
        L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) n x} := by
  apply Nat.finite_of_card_ne_zero
  rw [natCard_isTorsionPoint_eq_pow K f L hc hA g n hn]
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  exact pow_ne_zero _ hn0

end P2mTorsionCount

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f] (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
        L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) n x} = n ^ (2 * g) :=
  P2mTorsionCount.natCard_isTorsionPoint_eq_pow K f L hc hA g n hn

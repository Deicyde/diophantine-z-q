/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_eq_of_range_stalk_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_eq_of_range_stalk_eq

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u

theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (x y : C)
    (h : (algebraMap (C.presheaf.stalk x) C.functionField).range =
      (algebraMap (C.presheaf.stalk y) C.functionField).range) :
    x = y := by

  haveI : C.IsSeparated := ⟨by
    rw [show terminal.from C = c ≫ terminal.from _ from terminal.hom_ext _ _]
    infer_instance⟩
  set O := C.presheaf.stalk x with hOdef
  set O' := C.presheaf.stalk y with hO'def
  set F := C.functionField with hFdef
  have hinj : Function.Injective (algebraMap O F) := IsFractionRing.injective O F
  have hinj' : Function.Injective (algebraMap O' F) := IsFractionRing.injective O' F

  let eO : O ≃+* (algebraMap O F).range :=
    RingEquiv.ofBijective (algebraMap O F).rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  let eO' : O' ≃+* (algebraMap O' F).range :=
    RingEquiv.ofBijective (algebraMap O' F).rangeRestrict
      ⟨fun a b hab => hinj' (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  let eh : (algebraMap O' F).range ≃+* (algebraMap O F).range := RingEquiv.subringCongr h.symm
  let e : O' ≃+* O := eO'.trans (eh.trans eO.symm)
  have he : ∀ a : O', algebraMap O F (e a) = algebraMap O' F a := by
    intro a
    have h1 : ∀ b : (algebraMap O F).range, algebraMap O F (eO.symm b) = (b : F) := by
      intro b
      exact congrArg Subtype.val (eO.apply_symm_apply b)
    change algebraMap O F (eO.symm (eh (eO' a))) = _
    rw [h1]
    rfl

  have hηx : genericPoint C ⤳ x := (genericPoint_spec C).specializes trivial
  have hηy : genericPoint C ⤳ y := (genericPoint_spec C).specializes trivial
  have halgx : algebraMap O F = (C.presheaf.stalkSpecializes hηx).hom :=
    RingHom.algebraMap_toAlgebra _
  have halgy : algebraMap O' F = (C.presheaf.stalkSpecializes hηy).hom :=
    RingHom.algebraMap_toAlgebra _

  let α : Spec O ⟶ C := C.fromSpecStalk x
  let β : Spec O ⟶ C := Spec.map (CommRingCat.ofHom e.toRingHom) ≫ C.fromSpecStalk y
  let ι : Spec F ⟶ Spec O := Spec.map (C.presheaf.stalkSpecializes hηx)
  haveI : IsDominant ι := ⟨by
    have hpt : ∀ p : Spec F, ι.base p = genericPoint (Spec O) := by
      intro p
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      change Ideal.comap (C.presheaf.stalkSpecializes hηx).hom p.asIdeal = ⊥
      have hp : p.asIdeal = ⊥ := Ideal.eq_bot_of_prime p.asIdeal
      rw [hp, ← RingHom.ker_eq_comap_bot, ← halgx]
      exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
    have hmem : genericPoint (Spec O) ∈ Set.range ι.base :=
      ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F), hpt _⟩
    have hd : Dense ({genericPoint (Spec O)} : Set (Spec O)) :=
      dense_iff_closure_eq.mpr (genericPoint_closure (Spec O))
    exact hd.mono (Set.singleton_subset_iff.mpr hmem)⟩

  have hιe : ι ≫ Spec.map (CommRingCat.ofHom e.toRingHom)
      = Spec.map (C.presheaf.stalkSpecializes hηy) := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    change (C.presheaf.stalkSpecializes hηx).hom (e a) = (C.presheaf.stalkSpecializes hηy).hom a
    rw [← halgx, ← halgy]
    exact he a
  have hagree : ι ≫ α = ι ≫ β := by
    change ι ≫ C.fromSpecStalk x
      = ι ≫ (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ C.fromSpecStalk y)
    rw [← Category.assoc, hιe, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hαβ : α = β := ext_of_isDominant ι hagree

  haveI : IsLocalHom e.toRingHom :=
    ⟨fun a ha => (isLocalHom_equiv e).map_nonunit a ha⟩
  have hcl : (Spec.map (CommRingCat.ofHom e.toRingHom)).base (IsLocalRing.closedPoint O)
      = IsLocalRing.closedPoint O' := by
    change PrimeSpectrum.comap e.toRingHom (IsLocalRing.closedPoint O) = _
    exact IsLocalRing.comap_closedPoint e.toRingHom
  have h1 : α.base (IsLocalRing.closedPoint O) = x := Scheme.fromSpecStalk_closedPoint
  have h2 : β.base (IsLocalRing.closedPoint O) = y := by
    change (C.fromSpecStalk y).base
      ((Spec.map (CommRingCat.ofHom e.toRingHom)).base (IsLocalRing.closedPoint O)) = y
    rw [hcl]
    exact Scheme.fromSpecStalk_closedPoint
  rw [← h1, ← h2, hαβ]

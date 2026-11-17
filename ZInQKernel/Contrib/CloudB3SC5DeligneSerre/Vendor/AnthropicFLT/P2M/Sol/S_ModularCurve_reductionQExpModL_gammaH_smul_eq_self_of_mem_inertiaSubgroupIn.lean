/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn (git blob 88a2a2ddb6d6743b637d4a89f43acadfe5883d39, sha256 87fa74eb6889bc1b22e2b7f9a58ad19d99fb39e6a9f13dfaf221f22d73a48b06).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpReductionModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve
namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn.ModularCurve
end P2MW.S_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn.ModularCurve
namespace HahnSeries
end HahnSeries
namespace IntermediateField
end IntermediateField

namespace P2MW.S_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn

set_option autoImplicit false

noncomputable section

namespace ModularCurve
export _root_.ModularCurve (IsLaurentPlaceReduction laurentIntegralPrincipalDivisors LaurentPrincipalGeneratedByIntegral LaurentReductionInputs laurentReductionDegZero coe_laurentReductionDegZero laurentReduction laurentReduction_mk IsLaurentPlaceReduction.eq_or_const_of_agree ReductionInputsQExpModL reductionQExpModL qExpFunctionFieldC arithmeticGalois coe_arithmeticGalois_smul galois_smul_pic0_def coeffMap coeffMap_coeffMap coeffMap_congr laurentBaseChange coeffMap_mem_laurentBaseChange translation_mem_GammaH Gamma1_le_GammaH JH JOneES.exists_transcendental_finiteDimensional_laurentBaseChange)
namespace QExpInertRed
open _root_.ModularCurve

open _root_.AlgebraicCurve
open _root_.ModularCurve
open _root_.P2MW.S_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn.ModularCurve
open _root_.HahnSeries
open _root_.IntermediateField
open scoped Pointwise

section Generic

variable {L : Type*} [Field L] [Algebra ℚ L] {A : ValuationSubring L}
variable {k : Type*} [Field k] {π : A →+* k} {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}

abbrev FL (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Type _ :=
  laurentBaseChange L (qExpFunctionFieldC ℚ Γ)

theorem coeffMap_subtype_coeffMap (σ : L ≃ₐ[ℚ] L) (σA : A →+* A) (hσA : ∀ a : A, (σA a : L) = σ a)
    (y : LaurentSeries A) :
    coeffMap A.subtype (coeffMap σA y) = coeffMap (σ : L →+* L) (coeffMap A.subtype y) := by
  rw [coeffMap_coeffMap, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext fun a => hσA a) y

theorem mapDomain_inertia_agree
    {r : Place L (FL L Γ) → Place k (qExpFunctionFieldC k Γ)}
    (hr : IsLaurentPlaceReduction A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ) r)
    (σ : L ≃ₐ[ℚ] L) (σA : A →+* A) (hσA : ∀ a : A, (σA a : L) = σ a)
    (hπ : ∀ a, π (σA a) = π a)
    {D : Divisor L (FL L Γ)}
    (hD : D ∈ laurentIntegralPrincipalDivisors A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ)) :
    Finsupp.mapDomain r D =
      Finsupp.mapDomain (r ∘ fun P => arithmeticGalois (qExpFunctionFieldC ℚ Γ) σ • P) D := by
  obtain ⟨y, hy, hyk, hne, hDy⟩ := hD
  set g := arithmeticGalois (qExpFunctionFieldC ℚ Γ) σ with hg
  set y' : LaurentSeries A := coeffMap σA y with hy'def
  have himg : coeffMap A.subtype y' = coeffMap (σ : L →+* L) (coeffMap A.subtype y) :=
    coeffMap_subtype_coeffMap σ σA hσA y
  have hy' : coeffMap A.subtype y' ∈ laurentBaseChange L (qExpFunctionFieldC ℚ Γ) := by
    rw [himg]; exact coeffMap_mem_laurentBaseChange σ hy

  have hred : coeffMap π y' = coeffMap π y := by
    rw [hy'def, coeffMap_coeffMap]
    exact coeffMap_congr (RingHom.ext fun a => hπ a) y
  have hyk' : coeffMap π y' ∈ qExpFunctionFieldC k Γ := hred ▸ hyk
  have hne' : coeffMap π y' ≠ 0 := hred ▸ hne
  have hyeq : (⟨coeffMap π y', hyk'⟩ : qExpFunctionFieldC k Γ) = ⟨coeffMap π y, hyk⟩ := Subtype.ext hred

  have hgx : g • (⟨coeffMap A.subtype y, hy⟩ : FL L Γ) = ⟨coeffMap A.subtype y', hy'⟩ :=
    Subtype.ext (by rw [coe_arithmeticGalois_smul]; exact himg.symm)

  have hD' : ∀ P, (g • D) P = P.ord (⟨coeffMap A.subtype y', hy'⟩ : FL L Γ) := by
    intro P
    rw [SemilinearAut.divisor_smul_apply, hDy, ← hgx, ← SemilinearAut.ord_smul g (g⁻¹ • P), smul_inv_smul]

  rw [Finsupp.mapDomain_comp, ← SemilinearAut.divisor_smul_def]
  ext Q
  rw [hr.2 y hy hyk hne D hDy Q, hr.2 y' hy' hyk' hne' (g • D) hD' Q, hyeq]

theorem mapDomain_eq_zero_of_const {K F K' F' : Type*} [Field K] [Field F] [Algebra K F] [Field K'] [Field F']
    [Algebra K' F'] {r : Place K F → Place K' F'} (hconst : ∀ P Q, r P = r Q) (hdeg : ∀ P : Place K F, P.deg = 1)
    {D : Divisor K F} (hD : D ∈ Divisor.degZero (K := K) (F := F)) : Finsupp.mapDomain r D = 0 := by
  rcases isEmpty_or_nonempty (Place K F) with hE | ⟨⟨P₀⟩⟩
  · have : D = 0 := Finsupp.ext fun P => isEmptyElim P
    rw [this, Finsupp.mapDomain_zero]
  · have hmapconst : ∀ D : Divisor K F, Finsupp.mapDomain r D = Finsupp.single (r P₀) (Divisor.degree D) := by
      intro D
      induction D using Finsupp.induction with
      | zero => simp
      | single_add P n D _ _ ih =>
        rw [Finsupp.mapDomain_add, ih, Finsupp.mapDomain_single, hconst P P₀, map_add,
          Divisor.degree_single, hdeg, Nat.cast_one, mul_one, ← Finsupp.single_add, add_comm]
    rw [hmapconst D, (Divisor.mem_degZero.mp hD), Finsupp.single_zero]

set_option maxHeartbeats 3200000 in

theorem laurentReduction_smul_eq_self
    (h : LaurentReductionInputs A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ))
    (hdegL : ∀ P : Place L (FL L Γ), P.deg = 1)
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 L (FL L Γ), ∃ y : Pic0 L (FL L Γ), n • y = x)
    (σ : L ≃ₐ[ℚ] L) (σA : A →+* A) (hσA : ∀ a : A, (σA a : L) = σ a)
    (hπ : ∀ a, π (σA a) = π a)
    (x : Pic0 L (FL L Γ)) :
    laurentReduction A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ) (σ • x) =
      laurentReduction A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ) x := by
  set r := h.choose with hrdef
  have hr : IsLaurentPlaceReduction A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ) r := h.choose_spec.1
  have hgen : LaurentPrincipalGeneratedByIntegral A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ) :=
    h.choose_spec.2
  set g := arithmeticGalois (qExpFunctionFieldC ℚ Γ) σ with hg
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [galois_smul_pic0_def, SemilinearAut.pic0_smul_mk, laurentReduction_mk h, laurentReduction_mk h]

  rcases IsLaurentPlaceReduction.eq_or_const_of_agree (r₁ := r)
      (r₂ := r ∘ fun P => g • P) hgen (fun D hD => mapDomain_inertia_agree hr σ σA hσA hπ hD) hdegL hdiv with
    key | hconst
  · congr 1
    apply Subtype.ext
    rw [coe_laurentReductionDegZero, coe_laurentReductionDegZero, SemilinearAut.coe_degZeroSMulHom,
      SemilinearAut.divisor_smul_def, ← Finsupp.mapDomain_comp, ← hg, show h.choose = r from rfl, ← key]
  ·
    have h0 : ∀ E : Divisor.degZero (K := L) (F := FL L Γ),
        laurentReductionDegZero h.choose h.choose_spec.1.1 E = 0 := fun E =>
      Subtype.ext (by rw [coe_laurentReductionDegZero]; exact mapDomain_eq_zero_of_const hconst hdegL E.2)
    rw [h0, h0]

end Generic

section Modular

open ValuationSubring

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem main (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (h : ModularCurve.ReductionInputsQExpModL A Γ)
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
    (z : Pic0 (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ)) :
    ModularCurve.reductionQExpModL A Γ (τ • z) = ModularCurve.reductionQExpModL A Γ z := by

  obtain ⟨t, ht, hfd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) Γ hT
  haveI : IsCurveOver (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField ht hfd
  have hdegL : ∀ P : Place (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ), P.deg = 1 :=
    IsCurveOver.deg_eq_one_of_isAlgClosed
  have hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ),
      ∃ y : Pic0 (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ), n • y = x :=
    fun n hn x => AlgebraicCurve.Pic0.exists_nsmul_eq (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ)
      ⟨t, ht, hfd⟩ n hn x

  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hτ
  let σA : A →+* A := MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) A s
  have hσA : ∀ a : A, (σA a : AlgebraicClosure ℚ) = (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a :=
    fun a => rfl
  have hs1 : MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ) (IsLocalRing.ResidueField A) s = 1 :=
    (MonoidHom.mem_ker).mp hs
  have hπ : ∀ a : A, IsLocalRing.residue A (σA a) = IsLocalRing.residue A a := by
    intro a
    show IsLocalRing.residue A (s • a) = _
    rw [IsLocalRing.ResidueField.residue_smul]
    have h1 := RingEquiv.congr_fun hs1 (IsLocalRing.residue A a)
    simpa using h1
  exact laurentReduction_smul_eq_self h hdegL hdiv (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    σA hσA hπ z

end Modular

end ModularCurve.QExpInertRed

end

theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (h : ModularCurve.ReductionInputsQExpModL A (CohCarrier.GammaH M H))
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hτ : τ ∈ A.inertiaSubgroupIn ℚ)
    (z : ModularCurve.JH M H) :
    ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H) (τ • z) =
      ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H) z :=
  haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)
  ModularCurve.QExpInertRed.main (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H) A h τ hτ z

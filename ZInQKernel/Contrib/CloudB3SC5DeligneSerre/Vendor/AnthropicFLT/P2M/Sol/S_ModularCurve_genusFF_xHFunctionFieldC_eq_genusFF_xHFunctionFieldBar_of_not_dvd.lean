/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd (git blob cc879c286f8ce9abd40cf234fdbfb424fa631cfa, sha256 c2e1d575dcc1d58478ae2b20a0c64c1193090e93c7dcc38f4ceed8086b5e43c2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularProlongation
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Ramification
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_transcendental_jqModC
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ValuationSubring_krullDimLE_one_of_isAlgebraic_rat
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace IntermediateField
end IntermediateField
namespace AlgebraicCurve
end AlgebraicCurve
namespace ModularCurve
end ModularCurve
namespace P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.ModularCurve
end P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.ModularCurve
namespace IsLocalRing
end IsLocalRing
namespace P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.ModularCurve.IgusaGenusXH
end P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.ModularCurve.IgusaGenusXH

namespace P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped MatrixGroups
open _root_.IntermediateField
open _root_.AlgebraicCurve hiding genus
open _root_.ModularCurve
open _root_.P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.ModularCurve
open _root_.IsLocalRing

namespace ModularCurve
export _root_.ModularCurve (translation_mem_GammaH Gamma1_le_GammaH xHFunctionFieldC xHFunctionFieldBar qExpFunctionFieldC intFormRatiosC_subset coeffMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC map_jqModC exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC genusFF_qExpFunctionFieldC_eq_of_ringHom genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField jqModC_mem_intFormRatiosC transcendental_jqModC)
namespace IgusaGenusXH
open _root_.ModularCurve



section Residue

variable {ℓ : ℕ} [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))

theorem charP_residueField (hA : A.LiesOverPrime ℓ) : CharP (ResidueField A) ℓ := by
  have hmem : ((ℓ : A) : (AlgebraicClosure ℚ)) ∈ A.nonunits := by
    have : ((ℓ : A) : (AlgebraicClosure ℚ)) = (ℓ : (AlgebraicClosure ℚ)) := by simp
    rw [this]; exact hA
  have hmax : (ℓ : A) ∈ maximalIdeal A := (ValuationSubring.coe_mem_nonunits_iff).mp hmem
  have h0 : (ℓ : ResidueField A) = 0 := by
    rw [← map_natCast (residue A), residue_eq_zero_iff]
    exact hmax
  exact (CharP.charP_iff_prime_eq_zero Fact.out).mpr h0

theorem isAlgebraic_residueField [CharP (ResidueField A) ℓ] :
    letI : Algebra (ZMod ℓ) (ResidueField A) := ZMod.algebra _ ℓ
    Algebra.IsAlgebraic (ZMod ℓ) (ResidueField A) := by
  letI : Algebra (ZMod ℓ) (ResidueField A) := ZMod.algebra _ ℓ
  refine ⟨fun z => ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective z

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
  have halgQ : IsAlgebraic ℚ (x : (AlgebraicClosure ℚ)) := Algebra.IsAlgebraic.isAlgebraic _
  have halgZ : IsAlgebraic ℤ (x : (AlgebraicClosure ℚ)) := (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr halgQ
  obtain ⟨P, hP0, hPx⟩ := halgZ

  set Q : Polynomial ℤ := P.primPart with hQ
  have hQprim : Q.IsPrimitive := P.isPrimitive_primPart
  have hcont : (P.content : (AlgebraicClosure ℚ)) ≠ 0 := by
    have : P.content ≠ 0 := fun h => hP0 (Polynomial.content_eq_zero_iff.mp h)
    exact_mod_cast this
  have hQx : Polynomial.aeval (x : (AlgebraicClosure ℚ)) Q = 0 := by
    have h1 : Polynomial.aeval (x : (AlgebraicClosure ℚ)) P =
        (P.content : (AlgebraicClosure ℚ)) * Polynomial.aeval (x : (AlgebraicClosure ℚ)) Q := by
      conv_lhs => rw [P.eq_C_content_mul_primPart]
      rw [map_mul, Polynomial.aeval_C]
      congr 1
    rw [hPx] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left hcont

  have hQxA : Polynomial.eval₂ (Int.castRingHom A) x Q = 0 := by
    apply Subtype.val_injective
    change A.subtype (Polynomial.eval₂ (Int.castRingHom A) x Q) = ((0 : A) : (AlgebraicClosure ℚ))
    rw [Polynomial.hom_eval₂, ZeroMemClass.coe_zero]
    have : (A.subtype).comp (Int.castRingHom A) = algebraMap ℤ (AlgebraicClosure ℚ) := RingHom.ext_int _ _
    rw [this]
    exact hQx

  have hQbar : Polynomial.aeval (residue A x) (Q.map (Int.castRingHom (ZMod ℓ))) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have : (algebraMap (ZMod ℓ) (ResidueField A)).comp (Int.castRingHom (ZMod ℓ)) =
        (residue A).comp (Int.castRingHom A) := RingHom.ext_int _ _
    rw [this, ← Polynomial.hom_eval₂, hQxA, map_zero]

  have hQbar0 : Q.map (Int.castRingHom (ZMod ℓ)) ≠ 0 := by
    intro h0
    have hdvd : ∀ n, (ℓ : ℤ) ∣ Q.coeff n := by
      intro n
      have h1 : (Q.map (Int.castRingHom (ZMod ℓ))).coeff n = 0 := by rw [h0, Polynomial.coeff_zero]
      rw [Polynomial.coeff_map, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
      exact h1
    have hC : Polynomial.C (ℓ : ℤ) ∣ Q := (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hdvd
    have hunit : IsUnit (ℓ : ℤ) := hQprim _ hC
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hunit
    exact (Fact.out : ℓ.Prime).one_lt.ne' hunit
  exact ⟨_, hQbar0, hQbar⟩

theorem exists_ringHom_residueField [CharP (ResidueField A) ℓ]
    (k : Type*) [Field k] [IsAlgClosed k] [CharP k ℓ] :
    Nonempty (ResidueField A →+* k) := by
  letI : Algebra (ZMod ℓ) (ResidueField A) := ZMod.algebra _ ℓ
  letI : Algebra (ZMod ℓ) k := ZMod.algebra _ ℓ
  haveI : Algebra.IsAlgebraic (ZMod ℓ) (ResidueField A) := isAlgebraic_residueField A
  exact ⟨(IsAlgClosed.lift (R := ZMod ℓ) (S := ResidueField A) (M := k)).toRingHom⟩

end Residue

section DeuringLE

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime]




scoped instance finiteIndex_gammaH : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem coeffMap_jqModC_mem (A : ValuationSubring (AlgebraicClosure ℚ)) :
    coeffMap A.subtype (jqModC A) ∈ (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := by
  have h1 : coeffMap A.subtype (jqModC A) = coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) := by
    change (jqModC A).map A.subtype = (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ))
    rw [map_jqModC, map_jqModC]
  rw [h1]
  exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
    (intFormRatiosC_subset ℚ (CohCarrier.GammaH M H) (jqModC_mem_intFormRatiosC ℚ (CohCarrier.GammaH M H)))

set_option maxHeartbeats 3200000 in

theorem genusFF_residueField_le (hℓM : ¬ ℓ ∣ M) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    genusFF (ResidueField A) (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H)) ≤
      genusFF (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := by
  have hT : ModularGroup.T ∈ (CohCarrier.GammaH M H) := translation_mem_GammaH M H

  obtain ⟨R, -, hRres⟩ :=
    exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) A (CohCarrier.GammaH M H) hT

  have hjF : coeffMap A.subtype (jqModC A) ∈ (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := coeffMap_jqModC_mem M H A
  set y : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := ⟨coeffMap A.subtype (jqModC A), hjF⟩ with hydef
  have hycoe : (y : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    change (jqModC A).map A.subtype = jqModC (AlgebraicClosure ℚ)
    exact map_jqModC _
  obtain ⟨hO, hres⟩ := hRres (jqModC A) hjF
  set xb : qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H) := R.residue ⟨y, hO⟩ with hxbdef
  have hxbcoe : (xb : LaurentSeries (ResidueField A)) = jqModC (ResidueField A) := by
    rw [hxbdef, hres]
    exact map_jqModC _

  have htrL : Transcendental (AlgebraicClosure ℚ) y := by
    have h := transcendental_jqModC (AlgebraicClosure ℚ)
    rw [← hycoe] at h
    exact (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) (LaurentSeries (AlgebraicClosure ℚ)))).mp h
  have htr : Transcendental (ResidueField A) xb := by
    have h := transcendental_jqModC (ResidueField A)
    rw [← hxbcoe] at h
    exact (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H))
        (LaurentSeries (ResidueField A)))).mp h

  obtain ⟨x₁, hx₁, -, hfin₁, hle₁⟩ :=
    exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField (AlgebraicClosure ℚ) A (CohCarrier.GammaH M H) hT
  have hx₁xb : x₁ = xb := Subtype.ext (hx₁.trans hxbcoe.symm)
  subst hx₁xb
  have hle : Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({xb} : Set (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H)))) (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H)) ≤
      Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := hle₁ y hycoe

  have hge : Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ≤
      Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({xb} : Set (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H)))) (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H)) :=
    finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd M H hℓM A hA xb y hxbcoe hycoe
  have heq := le_antisymm hle hge

  haveI := hfin₁
  have hpos : 0 < Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({xb} : Set (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H)))) (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H)) :=
    Module.finrank_pos
  have hfd : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
    Module.finite_of_finrank_pos (by omega)

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
  haveI : Ring.KrullDimLE 1 A := ValuationSubring.krullDimLE_one_of_isAlgebraic_rat A

  have key := RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one
    (L := (AlgebraicClosure ℚ)) A (F := (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) (ι := Unit) (fun _ => qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H))
    (fun _ => R) (fun _ _ _ => Subsingleton.elim _ _) (y : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) (fun _ => hO) htrL hfd
    (fun _ => htr) (by rw [Fintype.sum_unique]; exact heq)
  rwa [Fintype.sum_unique] at key

end DeuringLE

section Main

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime]

set_option maxHeartbeats 3200000 in
theorem main (hℓM : ¬ ℓ ∣ M) (k : Type*) [Field k] [IsAlgClosed k] [CharP k ℓ] :
    genusFF k (xHFunctionFieldC k M H) = genusFF (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) := by

  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨ℓ, Fact.out⟩
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : CharP (ResidueField A) ℓ := charP_residueField A hA
  obtain ⟨φ⟩ := exists_ringHom_residueField A k
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H

  have hfg : ∃ x : qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H),
      Transcendental (ResidueField A) x ∧
      FiniteDimensional (IntermediateField.adjoin (ResidueField A)
        ({x} : Set (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H))))
        (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H)) := by
    obtain ⟨x, -, htr, hfin, -⟩ :=
      exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField (AlgebraicClosure ℚ) A
        (CohCarrier.GammaH M H) hT
    exact ⟨x, htr, hfin⟩

  have htrans : genusFF k (qExpFunctionFieldC k (CohCarrier.GammaH M H)) =
      genusFF (ResidueField A) (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H)) :=
    genusFF_qExpFunctionFieldC_eq_of_ringHom φ (CohCarrier.GammaH M H) hfg

  have hle := genusFF_residueField_le M H hℓM A hA

  have hge : genusFF (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) ≤
      genusFF k (qExpFunctionFieldC k (CohCarrier.GammaH M H)) :=
    genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd M H hℓM k
  change genusFF k (qExpFunctionFieldC k (CohCarrier.GammaH M H)) =
    genusFF (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
  change genusFF (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ≤ _ at hge
  exact le_antisymm (htrans.le.trans hle) hge

end Main

end ModularCurve.IgusaGenusXH
open scoped _root_.P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.ModularCurve _root_.P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.ModularCurve.IgusaGenusXH
open scoped _root_.P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.ModularCurve

end
open scoped _root_.P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.ModularCurve _root_.P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.ModularCurve.IgusaGenusXH

open _root_.AlgebraicCurve hiding genus in open  _root_.ModularCurve _root_.P2MW.S_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd.ModularCurve in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (k : Type*) [Field k] [IsAlgClosed k] [CharP k ℓ] :
    genusFF k (ModularCurve.xHFunctionFieldC k M H) =
      genusFF (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) :=
  ModularCurve.IgusaGenusXH.main M H hℓM k

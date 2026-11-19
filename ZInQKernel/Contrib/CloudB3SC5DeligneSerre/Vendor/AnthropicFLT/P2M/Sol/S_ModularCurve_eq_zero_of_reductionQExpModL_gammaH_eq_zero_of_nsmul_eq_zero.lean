/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero (git blob 88fb6f35ab3f182605a66c547967313f06a48436, sha256 1d0fbc21a9b214d438a581de45b4d8743774e9c623b64dabde43d9c67349351d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpReductionModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_ConstantReduction
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularProlongation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_transcendental_finrank_adjoin_eq_xHFunctionFieldC_of_not_dvd
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ValuationSubring_krullDimLE_one_of_isAlgebraic_rat
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve
namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero.ModularCurve
end P2MW.S_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero.ModularCurve
namespace IsLocalRing
end IsLocalRing

namespace P2MW.S_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace ModularCurve
export _root_.ModularCurve (ReductionInputsQExpModL reductionQExpModL qExpFunctionFieldC laurentBaseChange translation_mem_GammaH Gamma1_le_GammaH JH exists_constantReduction_pic0Map_eq_reductionQExpModL genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd exists_transcendental_finrank_adjoin_eq_xHFunctionFieldC_of_not_dvd JOneES.exists_transcendental_finiteDimensional_laurentBaseChange)
namespace GammaHTorsionInjective
open _root_.ModularCurve

open _root_.AlgebraicCurve hiding genus
open _root_.ModularCurve
open _root_.P2MW.S_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero.ModularCurve
open _root_.IsLocalRing

section Kummer

theorem natCast_ne_zero_of_dvd {k : Type*} [NonAssocSemiring k] {m q : ℕ}
    (hm : (m : k) ≠ 0) (hq : q ∣ m) : (q : k) ≠ 0 := by
  obtain ⟨c, rfl⟩ := hq
  intro h
  apply hm
  rw [Nat.cast_mul, h, zero_mul]

theorem ne_zero_of_natCast_ne_zero {k : Type*} [NonAssocSemiring k] {m : ℕ}
    (hm : (m : k) ≠ 0) : m ≠ 0 := by
  rintro rfl
  exact hm Nat.cast_zero

theorem eq_zero_of_forall_prime {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H) (m : ℕ) (hm : m ≠ 0)
    (h : ∀ q : ℕ, q.Prime → q ∣ m → ∀ x : G, q • x = 0 → φ x = 0 → x = 0)
    (x : G) (hmx : m • x = 0) (hx : φ x = 0) : x = 0 := by
  induction m using Nat.strong_induction_on generalizing x with
  | _ m ih =>
    rcases eq_or_ne m 1 with rfl | hm1
    · simpa using hmx
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
    obtain ⟨m', rfl⟩ := hqm
    have hm' : m' ≠ 0 := by rintro rfl; simp at hm
    have hy : m' • x = 0 := by
      refine h q hq (dvd_mul_right q m') (m' • x) ?_ ?_
      · rw [smul_smul]; exact hmx
      · rw [map_nsmul, hx, nsmul_zero]
    have hlt : m' < q * m' := lt_mul_left (Nat.pos_of_ne_zero hm') hq.one_lt
    exact ih m' hlt hm' (fun q' hq' hq'm => h q' hq' (Dvd.dvd.mul_left hq'm q)) x hy hx

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem nsmul_divisor_apply (m : ℕ) (D : Divisor L F) (P : Place L F) :
    (m • D) P = (m : ℤ) * D P := by
  simp [Finsupp.smul_apply]

theorem smul_const_ne_zero (R : ConstantReduction A F Fbar) {f : F} {c : L}
    (hc : c • f ∈ R.integers) (hres : R.residue ⟨c • f, hc⟩ ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply hres
  have : (⟨(0 : L) • f, hc⟩ : R.integers) = 0 := Subtype.ext (by simp)
  rw [this, map_zero]

theorem mk_eq_zero_of_mem_principal (D : Divisor.degZero (K := L) (F := F))
    (hD : (D : Divisor L F) ∈ Divisor.principal (K := L) (F := F)) : Pic0.mk D = 0 := by
  refine (QuotientAddGroup.eq_zero_iff D).mpr ?_
  rwa [AddSubgroup.mem_addSubgroupOf]

theorem exists_kummerDatum (R : ConstantReduction A F Fbar) (z : Pic0 L F) (m : ℕ)
    (hmz : m • z = 0) (hz : R.pic0Map z = 0) :
    ∃ D : Divisor.degZero (K := L) (F := F), Pic0.mk D = z ∧
      ∃ f : R.integers, R.residue f ≠ 0 ∧ (∀ P, (m : ℤ) * (D : Divisor L F) P = P.ord (f : F)) ∧
      ∃ g : Fbar, g ≠ 0 ∧ (∀ Q : Place (ResidueField A) Fbar,
        Finsupp.mapDomain R.placeMap (D : Divisor L F) Q = Q.ord g) ∧
      ∀ Q : Place (ResidueField A) Fbar, Q.ord (R.residue f) = (m : ℤ) * Q.ord g := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective z
  have hmD : ((m • D : Divisor.degZero (K := L) (F := F)) : Divisor L F) ∈
      Divisor.principal (K := L) (F := F) := by
    have h1 : Pic0.mk (m • D) = 0 := by
      change QuotientAddGroup.mk (m • D) = (0 : Pic0 L F)
      rw [QuotientAddGroup.mk_nsmul]
      exact hmz
    have h2 := (QuotientAddGroup.eq_zero_iff (m • D)).mp h1
    rwa [AddSubgroup.mem_addSubgroupOf] at h2
  obtain ⟨f₀, hf₀, hDf₀⟩ := hmD
  obtain ⟨c, hc, hres⟩ := R.exists_smul_mem f₀ hf₀
  have hc0 : c ≠ 0 := smul_const_ne_zero R hc hres
  have hdivf : ∀ P, (m : ℤ) * (D : Divisor L F) P = P.ord (c • f₀) := fun P => by
    rw [ConstantReduction.ord_smul P hc0, ← hDf₀ P, AddSubgroupClass.coe_nsmul, nsmul_divisor_apply]
  have hrD : (R.degZeroMap D : Divisor (ResidueField A) Fbar) ∈
      Divisor.principal (K := ResidueField A) (F := Fbar) := by
    have h1 : Pic0.mk (R.degZeroMap D) = 0 := by rw [← ConstantReduction.pic0Map_mk]; exact hz
    have h2 := (QuotientAddGroup.eq_zero_iff (R.degZeroMap D)).mp h1
    rwa [AddSubgroup.mem_addSubgroupOf] at h2
  obtain ⟨g, hg, hDg⟩ := hrD
  refine ⟨D, rfl, ⟨c • f₀, hc⟩, hres, hdivf, g, hg, fun Q => by rw [← hDg Q]; rfl, fun Q => ?_⟩
  have key := R.mapDomain_placeMap ⟨c • f₀, hc⟩ hres ((m • D : Divisor.degZero (K := L) (F := F)) :
      Divisor L F) (fun P => by rw [AddSubgroupClass.coe_nsmul, nsmul_divisor_apply, hdivf P]) Q
  rw [← key, AddSubgroupClass.coe_nsmul, Finsupp.mapDomain_smul, nsmul_divisor_apply, ← hDg Q]
  rfl

theorem ord_residue_mul_inv_pow_eq_zero (R : ConstantReduction A F Fbar) {f : R.integers}
    (hf : R.residue f ≠ 0) {g : Fbar} (hg : g ≠ 0) (m : ℕ)
    (h : ∀ Q : Place (ResidueField A) Fbar, Q.ord (R.residue f) = (m : ℤ) * Q.ord g)
    (Q : Place (ResidueField A) Fbar) : Q.ord (R.residue f * (g ^ m)⁻¹) = 0 := by
  rw [Q.ord_mul hf (inv_ne_zero (pow_ne_zero _ hg)), Q.ord_inv, h Q, ← zpow_natCast,
    Q.ord_zpow]
  ring

theorem mem_principal_of_pow_eq {q : ℕ} (hq : q ≠ 0) {D : Divisor L F} {f h : F} (hf : f ≠ 0)
    (hhf : h ^ q = f) (hD : ∀ P, (q : ℤ) * D P = P.ord f) :
    D ∈ Divisor.principal (K := L) (F := F) := by
  have hh : h ≠ 0 := by
    rintro rfl
    rw [zero_pow hq] at hhf
    exact hf hhf.symm
  refine ⟨h, hh, fun P => ?_⟩
  have h1 : (q : ℤ) * D P = (q : ℤ) * P.ord h := by
    rw [hD P, ← hhf, ← zpow_natCast, P.ord_zpow]
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hq) h1

theorem prime_case [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) [Ring.KrullDimLE 1 A]
    (F : Type*) [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) (hR : R.IsGood)
    (hreg : ∃ x : R.integers, Transcendental (ResidueField A) (R.residue x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar ∧
      Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
        Module.finrank
          (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (q : ℕ) [hqp : Fact q.Prime] (hqk : (q : ResidueField A) ≠ 0)
    (z : Pic0 L F) (hqz : q • z = 0) (hz : R.pic0Map z = 0) : z = 0 := by
  classical
  have hq0 : q ≠ 0 := hqp.out.ne_zero
  have hqpos : 0 < q := hqp.out.pos

  obtain ⟨D, hDz, f, hfres, hdivf, g, hg0, -, hordfg⟩ := exists_kummerDatum R z q hqz hz
  subst hDz
  have hf0 : (f : F) ≠ 0 := by
    intro h
    apply hfres
    rw [show f = 0 from Subtype.ext h, map_zero]

  obtain ⟨xO, hxt, hxpos, hxeq⟩ := hreg
  haveI : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue xO} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hxpos
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A

  set u : Fbar := R.residue f * (g ^ q)⁻¹ with hu
  have hu_ord : ∀ Q' : Place (ResidueField A) Fbar, Q'.ord u = 0 :=
    ord_residue_mul_inv_pow_eq_zero R hfres hg0 q hordfg
  obtain ⟨cbar, hcbar⟩ :=
    Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed (R.residue xO) hxt hu_ord
  obtain ⟨ebar, hebar⟩ := IsAlgClosed.exists_pow_nat_eq cbar hqpos
  set w : Fbar := algebraMap (ResidueField A) Fbar ebar * g with hw
  have hwq : w ^ q = R.residue f := by
    rw [hw, mul_pow, ← map_pow, hebar, hcbar, hu, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hg0), mul_one]
  have hw0 : w ≠ 0 := by
    intro h0
    apply hfres
    rw [← hwq, h0, zero_pow hq0]

  have hdvd : ∀ P : Place L F, (q : ℤ) ∣ P.ord (f : F) := fun P => ⟨_, (hdivf P).symm⟩
  have hgood : genusFF (ResidueField A) Fbar = genusFF L F := (R.isGood_iff).mp hR
  obtain ⟨h, hh⟩ := RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one
    A hF R.toRegularProlongation hgood ⟨xO, hxt, hxpos, hxeq⟩ hqk f hdvd w hw0 hwq
  exact mk_eq_zero_of_mem_principal D (mem_principal_of_pow_eq hq0 hf0 hh hdivf)

theorem of_finrank_eq [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) [Ring.KrullDimLE 1 A]
    (F : Type*) [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : ConstantReduction A F Fbar) (hR : R.IsGood)
    (hreg : ∃ x : R.integers, Transcendental (ResidueField A) (R.residue x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar ∧
      Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
        Module.finrank
          (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (m : ℕ) (hm : (m : ResidueField A) ≠ 0)
    (z : Pic0 L F) (hmz : m • z = 0) (hz : R.pic0Map z = 0) : z = 0 := by
  refine eq_zero_of_forall_prime R.pic0Map m (ne_zero_of_natCast_ne_zero hm)
    (fun q hq hqm z' hqz hz' => ?_) z hmz hz
  haveI : Fact q.Prime := ⟨hq⟩
  exact prime_case A F hF Fbar R hR hreg q (natCast_ne_zero_of_dvd hm hqm) z' hqz hz'

end Kummer

theorem natCast_residueField_ne_zero {L : Type*} [Field L] (A : ValuationSubring L) {ℓ : ℕ} [Fact ℓ.Prime]
    (hA : A.LiesOverPrime ℓ) {m : ℕ} (hm : ¬ ℓ ∣ m) : (m : IsLocalRing.ResidueField A) ≠ 0 := by
  intro h0
  have hℓ : ((ℓ : A) : L) ∈ A.nonunits := by first | exact hA | simpa [ValuationSubring.LiesOverPrime] using hA
  rw [ValuationSubring.coe_mem_nonunits_iff] at hℓ
  have hmA : (m : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]; exact h0
  have hcop : IsCoprime (ℓ : A) (m : A) :=
    Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm)
  obtain ⟨u, v, huv⟩ := hcop
  apply (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  rw [Ideal.eq_top_iff_one, ← huv]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hℓ) (Ideal.mul_mem_left _ _ hmA)

section Modular

open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem main (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (h : ModularCurve.ReductionInputsQExpModL A (CohCarrier.GammaH M H))
    (m : ℕ) (hm : ¬ ℓ ∣ m) (z : ModularCurve.JH M H) (hmz : m • z = 0)
    (hz : ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H) z = 0) :
    z = 0 := by

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _
  haveI : Ring.KrullDimLE 1 A := ValuationSubring.krullDimLE_one_of_isAlgebraic_rat A

  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : CharP (IsLocalRing.ResidueField A) ℓ := ValuationSubring.charP_residueField_of_liesOverPrime ℓ A hA

  haveI : (CohCarrier.GammaH M H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := ModularCurve.translation_mem_GammaH M H

  obtain ⟨R, -, hRpic, hRres⟩ :=
    ModularCurve.exists_constantReduction_pic0Map_eq_reductionQExpModL (CohCarrier.GammaH M H) hT A h

  have hF := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) hT

  have hgood : R.IsGood := by
    rw [ConstantReduction.isGood_iff]
    exact ModularCurve.genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd M H hℓM
      (IsLocalRing.ResidueField A)

  obtain ⟨y, hy, hyk, htr, hpos, heq⟩ :=
    ModularCurve.exists_transcendental_finrank_adjoin_eq_xHFunctionFieldC_of_not_dvd M H hℓM A hA
  obtain ⟨hO, hres⟩ := hRres y hy hyk
  have hreg : ∃ x : R.integers, Transcendental (ResidueField A) (R.residue x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} :
          Set (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))))
          (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) ∧
      Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({(x : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))} :
            Set (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))))
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) =
        Module.finrank
          (IntermediateField.adjoin (ResidueField A) ({R.residue x} :
            Set (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))))
          (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) := by
    refine ⟨⟨_, hO⟩, ?_, ?_, ?_⟩
    · rw [hres]; exact htr
    · rw [hres]; exact hpos
    · rw [hres]; exact heq

  have hz' : R.pic0Map z = 0 := by rw [hRpic]; exact hz
  exact of_finrank_eq A _ hF _ R hgood hreg m (natCast_residueField_ne_zero A hA hm) z hmz hz'

end Modular

end ModularCurve.GammaHTorsionInjective

theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (h : ModularCurve.ReductionInputsQExpModL A (CohCarrier.GammaH M H))
    (m : ℕ) (hm : ¬ ℓ ∣ m) (z : ModularCurve.JH M H) (hmz : m • z = 0)
    (hz : ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H) z = 0) :
    z = 0 :=
  ModularCurve.GammaHTorsionInjective.main M H hℓM A hA h m hm z hmz hz

end

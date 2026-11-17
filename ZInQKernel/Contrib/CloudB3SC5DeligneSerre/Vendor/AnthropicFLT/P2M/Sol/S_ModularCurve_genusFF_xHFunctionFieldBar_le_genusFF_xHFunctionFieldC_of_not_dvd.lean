/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd (git blob 082e26486d29f97e34050de983cac31b7fa825a0, sha256 63683ae09613fd1dc4dcdb0277c91a9e7acfe3180331c0035862a3cb6c1692c8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QAdicPlaceMod
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Differentials
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Ramification
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_natCard_doubleCoset_le_card_fibres_of_finrank_eq_index
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_two_mul_index_le_sum_ordDiff_D_add_natCard_doubleCoset_of_lt_five
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_isSeparable_adjoin_of_ord_eq_one
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
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
namespace P2MW.S_ModularCurve_genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd.ModularCurve
end P2MW.S_ModularCurve_genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd.ModularCurve
namespace IsLocalRing
end IsLocalRing
namespace P2MW.S_ModularCurve_genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd.ModularCurve.IgusaGenusLB
end P2MW.S_ModularCurve_genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd.ModularCurve.IgusaGenusLB

namespace P2MW.S_ModularCurve_genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped MatrixGroups
open _root_.IntermediateField
open _root_.AlgebraicCurve hiding genus
open _root_.ModularCurve
open _root_.P2MW.S_ModularCurve_genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd.ModularCurve
open _root_.IsLocalRing

namespace ModularCurve
export _root_.ModularCurve (translation_mem_GammaH Gamma1_le_GammaH GammaH_mono xHFunctionFieldC xHFunctionFieldBar qExpFunctionFieldC intFormRatiosC_subset coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC map_jqModC qInftyPlaceMod ord_qInftyPlaceMod order_jqModC_def jqModC_ne_zero_def order_inv_of_ne_zero_bar qSeriesBar two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le natCard_doubleCoset_le_card_fibres_of_finrank_eq_index card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset two_mul_index_le_sum_ordDiff_D_add_natCard_doubleCoset_of_lt_five index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField genusFF_qExpFunctionFieldC_eq_of_ringHom jqModC_mem_intFormRatiosC)
namespace IgusaGenusLB
open _root_.ModularCurve



section Groups

open CohCarrier CongruenceSubgroup

variable {M : ℕ}

theorem mem_sup_zpowers_neg_one_iff (H : Subgroup (ZMod M)ˣ) (u : (ZMod M)ˣ) :
    u ∈ H ⊔ Subgroup.zpowers (-1) ↔ u ∈ H ∨ -u ∈ H := by
  constructor
  · intro hu
    rw [Subgroup.mem_sup] at hu
    obtain ⟨y, hy, z, hz, rfl⟩ := hu
    rw [Subgroup.mem_zpowers_iff] at hz
    obtain ⟨n, rfl⟩ := hz
    rcases Int.even_or_odd n with hn | hn
    · left; rw [hn.neg_one_zpow, mul_one]; exact hy
    · right; rw [hn.neg_one_zpow, mul_neg_one, neg_neg]; exact hy
  · rintro (h | h)
    · exact Subgroup.mem_sup_left h
    · have : u = -u * -1 := by rw [mul_neg_one, neg_neg]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem GammaH_mono {H H' : Subgroup (ZMod M)ˣ} (h : H ≤ H') : GammaH M H ≤ GammaH M H' := by
  intro A hA
  obtain ⟨hA0, hAH⟩ := mem_GammaH_iff.mp hA
  exact mem_GammaH_iff.mpr ⟨hA0, h hAH⟩

theorem neg_mem_Gamma0 {γ : SL(2, ℤ)} (h : γ ∈ Gamma0 M) : -γ ∈ Gamma0 M := by
  rw [Gamma0_mem] at h ⊢
  simp [h]

theorem gamma0Units_neg (γ : SL(2, ℤ)) (h : γ ∈ Gamma0 M) :
    gamma0Units M ⟨-γ, neg_mem_Gamma0 h⟩ = -gamma0Units M ⟨γ, h⟩ := by
  ext
  simp [Gamma0Map]

theorem mem_or_neg_mem_of_mem_GammaH_sup (H : Subgroup (ZMod M)ˣ) (γ : SL(2, ℤ))
    (hγ : γ ∈ GammaH M (H ⊔ Subgroup.zpowers (-1))) : γ ∈ GammaH M H ∨ -γ ∈ GammaH M H := by
  obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp hγ
  rcases (mem_sup_zpowers_neg_one_iff H _).mp hγH with h | h
  · exact Or.inl (mem_GammaH_iff.mpr ⟨hγ0, h⟩)
  · refine Or.inr (mem_GammaH_iff.mpr ⟨neg_mem_Gamma0 hγ0, ?_⟩)
    rw [gamma0Units_neg]
    exact h

theorem neg_one_mem_GammaH_sup (H : Subgroup (ZMod M)ˣ) :
    (-1 : SL(2, ℤ)) ∈ GammaH M (H ⊔ Subgroup.zpowers (-1)) := by
  have h1 : (1 : SL(2, ℤ)) ∈ Gamma0 M := Subgroup.one_mem _
  refine mem_GammaH_iff.mpr ⟨neg_mem_Gamma0 h1, ?_⟩
  rw [gamma0Units_neg 1 h1]
  have : gamma0Units M ⟨1, h1⟩ = 1 := by
    have : (⟨1, h1⟩ : Gamma0 M) = 1 := rfl
    rw [this, map_one]
  rw [this]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem GammaH_sup_eq (H : Subgroup (ZMod M)ˣ) :
    GammaH M (H ⊔ Subgroup.zpowers (-1)) = GammaH M H ⊔ Subgroup.zpowers (-1) := by
  refine le_antisymm ?_ (sup_le (GammaH_mono le_sup_left) ?_)
  · intro γ hγ
    rcases mem_or_neg_mem_of_mem_GammaH_sup H γ hγ with h | h
    · exact Subgroup.mem_sup_left h
    · have : γ = -γ * -1 := by rw [mul_neg_one, neg_neg]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  · rw [Subgroup.zpowers_le]
    exact neg_one_mem_GammaH_sup H

end Groups

abbrev dcZero (Γ : Subgroup SL(2, ℤ)) : ℕ :=
  Nat.card (DoubleCoset.Quotient (Γ : Set SL(2, ℤ))
    (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) : Set SL(2, ℤ)))

abbrev dc1728 (Γ : Subgroup SL(2, ℤ)) : ℕ :=
  Nat.card (DoubleCoset.Quotient (Γ : Set SL(2, ℤ)) (Subgroup.zpowers ModularGroup.S : Set SL(2, ℤ)))

abbrev dcInf (Γ : Subgroup SL(2, ℤ)) : ℕ :=
  Nat.card (DoubleCoset.Quotient (Γ : Set SL(2, ℤ))
    ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ)))

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
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by convert AlgebraicClosure.isAlgebraic ℚ <;> first | exact Subsingleton.elim _ _ | with_reducible_and_instances rfl | rfl
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

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_sub_algebraMap_of_ord_neg (v : Place K F) {x : F} (c : K) (hx : v.ord x < 0) :
    v.ord (x - algebraMap K F c) = v.ord x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hc0 : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  have hxc : x - algebraMap K F c ≠ 0 := by
    intro h
    have : v.ord x = 0 := by
      rw [sub_eq_zero.mp h]; exact v.ord_algebraMap c
    omega
  have h1 := v.min_ord_le_ord_add hx0 (neg_ne_zero.mpr hc0) (by rwa [← sub_eq_add_neg])
  rw [← sub_eq_add_neg, ← map_neg, v.ord_algebraMap] at h1
  have h2 := v.min_ord_le_ord_add hxc hc0 (by rw [sub_add_cancel]; exact hx0)
  rw [sub_add_cancel, v.ord_algebraMap] at h2
  omega

theorem ord_neg_of_ord_sub_algebraMap_neg (v : Place K F) {x : F} (c : K)
    (hx : v.ord (x - algebraMap K F c) < 0) : v.ord x < 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using hx
  have hc0 : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  have hxc : x - algebraMap K F c ≠ 0 := by rintro h; rw [h] at hx; simp at hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_sub, ← map_neg, v.ord_algebraMap] at hx
    exact lt_irrefl _ hx
  have h2 := v.min_ord_le_ord_add hxc hc0 (by rw [sub_add_cancel]; exact hx0)
  rw [sub_add_cancel, v.ord_algebraMap] at h2
  by_contra h
  have h1 := v.min_ord_le_ord_add hx0 (neg_ne_zero.mpr hc0) (by rwa [← sub_eq_add_neg])
  rw [← sub_eq_add_neg, ← map_neg, v.ord_algebraMap] at h1
  omega

theorem not_ord_sub_pos_of_ord_sub_pos (v : Place K F) {x : F} {c c' : K} (hcc' : c ≠ c')
    (h : 0 < v.ord (x - algebraMap K F c)) : ¬ 0 < v.ord (x - algebraMap K F c') := by
  intro h'
  have hne : x - algebraMap K F c ≠ 0 := by rintro hh; rw [hh] at h; simp at h
  have hne' : x - algebraMap K F c' ≠ 0 := by rintro hh; rw [hh] at h'; simp at h'
  have hd : algebraMap K F (c' - c) ≠ 0 := (map_ne_zero _).mpr (sub_ne_zero.mpr hcc'.symm)
  have hsum : (x - algebraMap K F c) + -(x - algebraMap K F c') = algebraMap K F (c' - c) := by
    rw [map_sub]; ring
  have key := v.min_ord_le_ord_add hne (neg_ne_zero.mpr hne') (by rw [hsum]; exact hd)
  rw [hsum, v.ord_algebraMap] at key
  have : v.ord (-(x - algebraMap K F c')) = v.ord (x - algebraMap K F c') := by
    rw [show -(x - algebraMap K F c') = (x - algebraMap K F c') * (-1) by ring,
      v.ord_mul hne' (by norm_num), show (-1 : F) = algebraMap K F (-1) by simp,
      v.ord_algebraMap, add_zero]
  rw [this] at key
  have hmin : 0 < min (v.ord (x - algebraMap K F c)) (v.ord (x - algebraMap K F c')) := lt_min h h'
  omega

theorem degree_eq_sum_support (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
  simp [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]

theorem exists_finset_zeros [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) :
    ∃ T : Finset (Place K F), ∀ v, v ∈ T ↔ 0 < v.ord f := by
  classical
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  refine ⟨D.support.filter fun v => 0 < D v, fun v => ?_⟩
  rw [Finset.mem_filter, Finsupp.mem_support_iff, hD v]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

theorem exists_finset_poles [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) :
    ∃ T : Finset (Place K F), ∀ v, v ∈ T ↔ v.ord f < 0 := by
  classical
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  refine ⟨D.support.filter fun v => D v < 0, fun v => ?_⟩
  rw [Finset.mem_filter, Finsupp.mem_support_iff, hD v]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

theorem natCard_subtype_eq_card {γ : Type*} (T : Finset γ) (p : γ → Prop)
    (hT : ∀ v, v ∈ T ↔ p v) : Nat.card {v // p v} = T.card := by
  classical
  have e : {v // p v} ≃ {v // v ∈ T} := Equiv.subtypeEquivRight fun v => (hT v).symm
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

variable [IsAlgClosed K] [IsCurveOver K F]

theorem degree_eq_sum_support' (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v := by
  rw [degree_eq_sum_support]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed v]; simp

theorem sum_ord_sub_algebraMap_eq_finrank {x : F} (hx : Transcendental K x)
    [FiniteDimensional K⟮x⟯ F] (c : K)
    (T : Finset (Place K F)) (hT : ∀ v, v ∈ T ↔ 0 < v.ord (x - algebraMap K F c)) :
    ∑ v ∈ T, v.ord (x - algebraMap K F c) = (Module.finrank K⟮x⟯ F : ℤ) := by
  classical
  set f := x - algebraMap K F c with hf
  have hf0 : f ≠ 0 := by
    intro h
    apply hx
    rw [hf, sub_eq_zero] at h
    rw [h]; exact isAlgebraic_algebraMap c
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0

  set Dinf : Divisor K F := -(D.filter fun v => D v < 0) with hDinf
  have hDinf_apply : ∀ v, Dinf v = max 0 (-v.ord x) := by
    intro v
    rw [hDinf, Finsupp.neg_apply, Finsupp.filter_apply]
    split_ifs with h
    · rw [hD v] at h
      have hx' := ord_neg_of_ord_sub_algebraMap_neg v c h
      rw [hD v, ord_sub_algebraMap_of_ord_neg v c hx', max_eq_right (by omega)]
    · rw [hD v] at h
      have : 0 ≤ v.ord x := by
        by_contra hneg
        exact h (by rw [ord_sub_algebraMap_of_ord_neg v c (by omega)]; omega)
      rw [neg_zero, max_eq_left (by omega)]
  have hdegInf := degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental x hx Dinf
    hDinf_apply
  have hsplit : (D.filter fun v => 0 < D v) + (D.filter fun v => D v < 0) = D := by
    ext v
    rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
    split_ifs with h1 h2 <;> omega
  have hdegpos : Divisor.degree (D.filter fun v => 0 < D v) = (Module.finrank K⟮x⟯ F : ℤ) := by
    have h := congrArg Divisor.degree hsplit
    rw [map_add, hdeg] at h
    have h2 : Divisor.degree (D.filter fun v => D v < 0) = -Divisor.degree Dinf := by
      rw [hDinf, map_neg, neg_neg]
    rw [h2, hdegInf] at h
    linarith
  rw [degree_eq_sum_support', Finsupp.support_filter] at hdegpos
  have hTeq : T = D.support.filter fun v => 0 < D v := by
    ext v
    rw [hT, Finset.mem_filter, Finsupp.mem_support_iff, hD v]
    constructor
    · intro h; exact ⟨by omega, h⟩
    · intro h; exact h.2
  rw [hTeq, ← hdegpos]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finsupp.filter_apply, if_pos (Finset.mem_filter.mp hv).2, hD v]

theorem sum_neg_ord_eq_finrank {x : F} (hx : Transcendental K x)
    [FiniteDimensional K⟮x⟯ F]
    (T : Finset (Place K F)) (hT : ∀ v, v ∈ T ↔ v.ord x < 0) :
    ∑ v ∈ T, (-v.ord x) = (Module.finrank K⟮x⟯ F : ℤ) := by
  classical
  have hx0 : x ≠ 0 := by
    rintro rfl; exact hx isAlgebraic_zero
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) x hx0
  set Dinf : Divisor K F := -(D.filter fun v => D v < 0) with hDinf
  have hDinf_apply : ∀ v, Dinf v = max 0 (-v.ord x) := by
    intro v
    rw [hDinf, Finsupp.neg_apply, Finsupp.filter_apply, hD v]
    split_ifs with h
    · rw [max_eq_right (by omega)]
    · rw [neg_zero, max_eq_left (by omega)]
  have hdegInf := degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental x hx Dinf
    hDinf_apply
  rw [degree_eq_sum_support'] at hdegInf
  have hTeq : T = Dinf.support := by
    ext v
    rw [hT, Finsupp.mem_support_iff, hDinf_apply]
    constructor
    · intro h; exact (lt_max_of_lt_right (by omega)).ne'
    · intro h
      by_contra h'
      exact h (max_eq_left (by omega))
  rw [hTeq, ← hdegInf]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [hDinf_apply]
  rw [Finsupp.mem_support_iff, hDinf_apply] at hv
  rcases le_or_gt 0 (v.ord x) with h | h
  · exact absurd (max_eq_left (by omega : -v.ord x ≤ 0)) hv
  · rw [max_eq_right (by omega)]

end Generic

section Separable

variable (K : Type*) [Field K] [PerfectField K] {F : IntermediateField K (LaurentSeries K)}

theorem isSeparable_adjoin_of_coe_eq_jqModC (x : F) (hx : (x : LaurentSeries K) = jqModC K)
    [FiniteDimensional K⟮x⟯ F] : Algebra.IsSeparable K⟮x⟯ F := by
  have hF : jqModC K ∈ F := hx ▸ x.2
  haveI : Algebra.IsAlgebraic K⟮x⟯ F := Algebra.IsAlgebraic.of_finite _ _

  set v : Place K F := qInftyPlaceMod K hF with hv
  have hx0 : x ≠ 0 := by
    intro h
    have := congrArg (fun z : F => (z : LaurentSeries K)) h
    simp only [hx, ZeroMemClass.coe_zero] at this
    exact jqModC_ne_zero_def K this
  have hord : v.ord x⁻¹ = 1 := by
    rw [hv, ord_qInftyPlaceMod, qSeriesBar]
    have : ((x⁻¹ : F) : LaurentSeries K) = (jqModC K)⁻¹ := by
      rw [← hx]; simp
    rw [this, order_inv_of_ne_zero_bar (jqModC_ne_zero_def K), order_jqModC_def]
    norm_num
  have hsep : Algebra.IsSeparable K⟮x⁻¹⟯ F := Place.isSeparable_adjoin_of_ord_eq_one x v hord
  have heq : K⟮x⁻¹⟯ = K⟮x⟯ := by
    refine le_antisymm ?_ ?_
    · rw [adjoin_simple_le_iff]
      exact inv_mem (mem_adjoin_simple_self K x)
    · rw [adjoin_simple_le_iff]
      have := inv_mem (mem_adjoin_simple_self K x⁻¹)
      rwa [inv_inv] at this
  rw [heq] at hsep
  exact hsep

end Separable

section CharL

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime]
variable (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]




theorem cast_1728_ne_zero (hℓ : 5 ≤ ℓ) : ((1728 : ℕ) : K) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff K ℓ] at h
  have hp : ℓ.Prime := Fact.out
  have h1728 : (1728 : ℕ) = 2 ^ 6 * 3 ^ 3 := by norm_num
  rw [h1728] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3); omega

set_option maxHeartbeats 3200000 in

theorem charL_bound_of_five_le (hℓM : ¬ ℓ ∣ M) (hℓ : 5 ≤ ℓ) (x : (qExpFunctionFieldC K (CohCarrier.GammaH M H)))
    (hx : (x : LaurentSeries K) = jqModC K) (htr : Transcendental K x)
    [FiniteDimensional K⟮x⟯ (qExpFunctionFieldC K (CohCarrier.GammaH M H))] :
    (Module.finrank K⟮x⟯ (qExpFunctionFieldC K (CohCarrier.GammaH M H)) : ℤ) - dcInf (CohCarrier.GammaH M H) - dcZero (CohCarrier.GammaH M H) - dc1728 (CohCarrier.GammaH M H) ≤
      2 * (genusFF K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) : ℤ) - 2 := by
  classical
  haveI : IsCurveOver K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) := isCurveOver_of_transcendental_of_perfectField htr inferInstance
  haveI : Algebra.IsSeparable K⟮x⟯ (qExpFunctionFieldC K (CohCarrier.GammaH M H)) := isSeparable_adjoin_of_coe_eq_jqModC K x hx
  have hx0 : x ≠ 0 := fun h => htr (h ▸ isAlgebraic_zero)
  have hx1728 : x - algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) 1728 ≠ 0 := by
    intro h; apply htr; rw [sub_eq_zero] at h; rw [h]; exact isAlgebraic_algebraMap _

  obtain ⟨S₀, hS₀⟩ := exists_finset_zeros (K := K) hx0
  obtain ⟨S₁, hS₁⟩ := exists_finset_zeros (K := K) hx1728
  obtain ⟨Sinf, hSinf⟩ := exists_finset_poles (K := K) hx0

  have hS₁' : ∀ Q, Q ∈ S₁ ↔ 0 < Q.ord (x - 1728) := by
    intro Q; rw [hS₁]; simp [map_ofNat]
  obtain ⟨hb₀, hb₁, hbinf⟩ :=
    card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset M H hℓM K x hx S₀ S₁ Sinf
      hS₀ hS₁' hSinf

  have h1728 : (0 : K) ≠ 1728 := by
    have := cast_1728_ne_zero K hℓ
    intro h; apply this; rw [Nat.cast_ofNat]; exact h.symm
  have hdisj : Disjoint S₀ S₁ := by
    rw [Finset.disjoint_left]
    intro Q hQ0 hQ1
    rw [hS₀] at hQ0
    rw [hS₁] at hQ1
    have hQ0' : 0 < Q.ord (x - algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) 0) := by rwa [map_zero, sub_zero]
    exact not_ord_sub_pos_of_ord_sub_pos Q h1728 hQ0' hQ1

  set a : Place K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) → K := fun Q => if Q ∈ S₀ then 0 else 1728 with ha
  have hT : ∀ Q ∈ S₀ ∪ S₁, 0 < Q.ord (x - algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) (a Q)) := by
    intro Q hQ
    rcases Finset.mem_union.mp hQ with h | h
    · rw [ha]; simp only [h, if_true, map_zero, sub_zero]; exact (hS₀ Q).mp h
    · have hn : Q ∉ S₀ := Finset.disjoint_right.mp hdisj h
      rw [ha]; simp only [hn, if_false]; exact (hS₁ Q).mp h
  have hTinf : ∀ Q ∈ Sinf, Q.ord x < 0 := fun Q hQ => (hSinf Q).mp hQ
  have hRH := sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable K x htr inferInstance inferInstance
    (S₀ ∪ S₁) a hT Sinf hTinf

  have hsum₀ : ∑ Q ∈ S₀, (Q.ord (x - algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) (a Q)) - 1) =
      (Module.finrank K⟮x⟯ (qExpFunctionFieldC K (CohCarrier.GammaH M H)) : ℤ) - S₀.card := by
    have h1 : ∑ Q ∈ S₀, (Q.ord (x - algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) (a Q)) - 1) =
        ∑ Q ∈ S₀, (Q.ord (x - algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) 0) - 1) := by
      refine Finset.sum_congr rfl fun Q hQ => ?_
      rw [ha]; simp only [hQ, if_true]
    rw [h1, Finset.sum_sub_distrib, sum_ord_sub_algebraMap_eq_finrank htr 0 S₀
      (fun Q => by rw [hS₀, map_zero, sub_zero])]
    simp
  have hsum₁ : ∑ Q ∈ S₁, (Q.ord (x - algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) (a Q)) - 1) =
      (Module.finrank K⟮x⟯ (qExpFunctionFieldC K (CohCarrier.GammaH M H)) : ℤ) - S₁.card := by
    have h1 : ∑ Q ∈ S₁, (Q.ord (x - algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) (a Q)) - 1) =
        ∑ Q ∈ S₁, (Q.ord (x - algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) 1728) - 1) := by
      refine Finset.sum_congr rfl fun Q hQ => ?_
      have hn : Q ∉ S₀ := Finset.disjoint_right.mp hdisj hQ
      rw [ha]; simp only [hn, if_false]
    rw [h1, Finset.sum_sub_distrib, sum_ord_sub_algebraMap_eq_finrank htr 1728 S₁ hS₁]
    simp
  have hsuminf : ∑ Q ∈ Sinf, (-Q.ord x - 1) = (Module.finrank K⟮x⟯ (qExpFunctionFieldC K (CohCarrier.GammaH M H)) : ℤ) - Sinf.card := by
    have h1 : ∑ Q ∈ Sinf, (-Q.ord x - 1) = ∑ Q ∈ Sinf, (-Q.ord x) - ∑ Q ∈ Sinf, (1 : ℤ) := by
      rw [← Finset.sum_sub_distrib]
    rw [h1, sum_neg_ord_eq_finrank htr Sinf hSinf]
    simp
  rw [Finset.sum_union hdisj, hsum₀, hsum₁, hsuminf] at hRH
  have hb₀' : (S₀.card : ℤ) ≤ dcZero (CohCarrier.GammaH M H) := by exact_mod_cast hb₀
  have hb₁' : (S₁.card : ℤ) ≤ dc1728 (CohCarrier.GammaH M H) := by exact_mod_cast hb₁
  have hbinf' : (Sinf.card : ℤ) ≤ dcInf (CohCarrier.GammaH M H) := by exact_mod_cast hbinf
  linarith

set_option maxHeartbeats 3200000 in

theorem charL_bound_of_lt_five (hℓM : ¬ ℓ ∣ M) (hℓ : ℓ < 5) (x : (qExpFunctionFieldC K (CohCarrier.GammaH M H)))
    (hx : (x : LaurentSeries K) = jqModC K) (htr : Transcendental K x)
    [FiniteDimensional K⟮x⟯ (qExpFunctionFieldC K (CohCarrier.GammaH M H))] :
    2 * ((CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index : ℤ) - dcZero (CohCarrier.GammaH M H) - dc1728 (CohCarrier.GammaH M H) - dcInf (CohCarrier.GammaH M H) -
        (Module.finrank K⟮x⟯ (qExpFunctionFieldC K (CohCarrier.GammaH M H)) : ℤ) ≤
      2 * (genusFF K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) : ℤ) - 2 := by
  classical
  haveI : IsCurveOver K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) := isCurveOver_of_transcendental_of_perfectField htr inferInstance
  haveI : Algebra.IsSeparable K⟮x⟯ (qExpFunctionFieldC K (CohCarrier.GammaH M H)) := isSeparable_adjoin_of_coe_eq_jqModC K x hx
  have hx0 : x ≠ 0 := fun h => htr (h ▸ isAlgebraic_zero)
  have hx1728 : x - algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) 1728 ≠ 0 := by
    intro h; apply htr; rw [sub_eq_zero] at h; rw [h]; exact isAlgebraic_algebraMap _
  obtain ⟨S₀, hS₀⟩ := exists_finset_zeros (K := K) hx0
  obtain ⟨S₁, hS₁⟩ := exists_finset_zeros (K := K) hx1728
  obtain ⟨Sinf, hSinf⟩ := exists_finset_poles (K := K) hx0
  have hS₁' : ∀ Q, Q ∈ S₁ ↔ 0 < Q.ord (x - 1728) := by
    intro Q; rw [hS₁]; simp [map_ofNat]
  obtain ⟨-, -, hbinf⟩ :=
    card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset M H hℓM K x hx S₀ S₁ Sinf
      hS₀ hS₁' hSinf

  have hW := two_mul_index_le_sum_ordDiff_D_add_natCard_doubleCoset_of_lt_five M H hℓ hℓM K x hx
    S₀ hS₀

  have hT : ∀ Q ∈ S₀, 0 ≤ Q.ord x := fun Q hQ => ((hS₀ Q).mp hQ).le
  have hTinf : ∀ Q ∈ Sinf, Q.ord x < 0 := fun Q hQ => (hSinf Q).mp hQ
  have hRH := sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable K x htr inferInstance inferInstance
    S₀ hT Sinf hTinf
  have hsuminf : ∑ Q ∈ Sinf, (-Q.ord x - 1) = (Module.finrank K⟮x⟯ (qExpFunctionFieldC K (CohCarrier.GammaH M H)) : ℤ) - Sinf.card := by
    have h1 : ∑ Q ∈ Sinf, (-Q.ord x - 1) = ∑ Q ∈ Sinf, (-Q.ord x) - ∑ Q ∈ Sinf, (1 : ℤ) := by
      rw [← Finset.sum_sub_distrib]
    rw [h1, sum_neg_ord_eq_finrank htr Sinf hSinf]
    simp
  rw [hsuminf] at hRH
  have hbinf' : (Sinf.card : ℤ) ≤ dcInf (CohCarrier.GammaH M H) := by exact_mod_cast hbinf
  change 2 * ((CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index : ℤ) ≤
      _ + (dcZero (CohCarrier.GammaH M H) : ℤ) + (dc1728 (CohCarrier.GammaH M H) : ℤ) at hW
  linarith

end CharL

section CharZero

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)




theorem charZero_bound (y : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (hfull : Module.finrank (AlgebraicClosure ℚ)⟮y⟯ (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) = (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index) :
    2 * genusFF (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) + dcInf (CohCarrier.GammaH M H) + dcZero (CohCarrier.GammaH M H) + dc1728 (CohCarrier.GammaH M H) ≤ Module.finrank (AlgebraicClosure ℚ)⟮y⟯ (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) + 2 := by
  have hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ (CohCarrier.GammaH M H) := Gamma1_le_GammaH M H
  have hRH := two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le M (CohCarrier.GammaH M H) hΓ₁ y hy
  obtain ⟨h₀, h₁, hinf⟩ := natCard_doubleCoset_le_card_fibres_of_finrank_eq_index M (CohCarrier.GammaH M H) hΓ₁ y hy hfull
  change dcZero (CohCarrier.GammaH M H) ≤ _ at h₀
  change dc1728 (CohCarrier.GammaH M H) ≤ _ at h₁
  change dcInf (CohCarrier.GammaH M H) ≤ _ at hinf
  omega

end CharZero

section Main

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime]




scoped instance finiteIndex_gammaH : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem coeffEmb_jqModC_mem : coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) ∈ (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
  coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (intFormRatiosC_subset ℚ (CohCarrier.GammaH M H) (jqModC_mem_intFormRatiosC ℚ (CohCarrier.GammaH M H)))

set_option maxHeartbeats 3200000 in

theorem genusFF_le_residueField (hℓM : ¬ ℓ ∣ M) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    genusFF (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ≤ genusFF (ResidueField A) (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H)) := by
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : CharP (ResidueField A) ℓ := charP_residueField A hA
  have hT : ModularGroup.T ∈ (CohCarrier.GammaH M H) := translation_mem_GammaH M H

  set y : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := ⟨coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ), coeffEmb_jqModC_mem M H⟩ with hydef
  have hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    change (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)
    exact map_jqModC _
  obtain ⟨x, hx, htr, hfin, hle⟩ :=
    exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField (AlgebraicClosure ℚ) A (CohCarrier.GammaH M H) hT
  haveI := hfin

  have hdle : Module.finrank (AlgebraicClosure ℚ)⟮y⟯ (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ≤ (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index := by
    have h := finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) hT
      (CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1))) (GammaH_mono le_sup_left)
      (mem_or_neg_mem_of_mem_GammaH_sup H) y hy
    rwa [GammaH_sup_eq] at h
  have hμle : (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index ≤
      Module.finrank (ResidueField A)⟮x⟯ (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H)) := by
    have h := index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField M H hℓM A hA x hx
    rwa [GammaH_sup_eq] at h
  have hdbarle : Module.finrank (ResidueField A)⟮x⟯ (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H)) ≤
      Module.finrank (AlgebraicClosure ℚ)⟮y⟯ (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := hle y hy
  have hfull : Module.finrank (AlgebraicClosure ℚ)⟮y⟯ (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) = (CohCarrier.GammaH M H ⊔ Subgroup.zpowers (-1)).index := by
    omega
  have hdeq : Module.finrank (ResidueField A)⟮x⟯ (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H)) =
      Module.finrank (AlgebraicClosure ℚ)⟮y⟯ (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := by omega

  have h0 := charZero_bound M H y hy hfull
  have hp : ℓ.Prime := Fact.out
  rcases le_or_gt 5 ℓ with hℓ5 | hℓ5
  · have hL := charL_bound_of_five_le M H (ResidueField A) hℓM hℓ5 x hx htr
    rw [hdeq] at hL
    have h0' : (2 * genusFF (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) + dcInf (CohCarrier.GammaH M H) + dcZero (CohCarrier.GammaH M H) + dc1728 (CohCarrier.GammaH M H) : ℤ) ≤
        (Module.finrank (AlgebraicClosure ℚ)⟮y⟯ (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : ℤ) + 2 := by exact_mod_cast h0
    have : (genusFF (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : ℤ) ≤ genusFF (ResidueField A) (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H)) := by
      linarith
    exact_mod_cast this
  · have hL := charL_bound_of_lt_five M H (ResidueField A) hℓM hℓ5 x hx htr
    rw [hdeq, hfull] at hL
    have h0' : (2 * genusFF (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) + dcInf (CohCarrier.GammaH M H) + dcZero (CohCarrier.GammaH M H) + dc1728 (CohCarrier.GammaH M H) : ℤ) ≤
        (Module.finrank (AlgebraicClosure ℚ)⟮y⟯ (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : ℤ) + 2 := by exact_mod_cast h0
    rw [hfull] at h0'
    have : (genusFF (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : ℤ) ≤ genusFF (ResidueField A) (qExpFunctionFieldC (ResidueField A) (CohCarrier.GammaH M H)) := by
      linarith
    exact_mod_cast this

set_option maxHeartbeats 3200000 in
theorem main (hℓM : ¬ ℓ ∣ M) (k : Type*) [Field k] [IsAlgClosed k] [CharP k ℓ] :
    genusFF (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) ≤ genusFF k (xHFunctionFieldC k M H) := by

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

  have hle := genusFF_le_residueField M H hℓM A hA
  change genusFF (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ≤
    genusFF k (qExpFunctionFieldC k (CohCarrier.GammaH M H))
  rw [htrans]
  exact hle

end Main

end ModularCurve.IgusaGenusLB
open scoped _root_.P2MW.S_ModularCurve_genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd.ModularCurve _root_.P2MW.S_ModularCurve_genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd.ModularCurve.IgusaGenusLB
open scoped _root_.P2MW.S_ModularCurve_genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd.ModularCurve

end
open scoped _root_.P2MW.S_ModularCurve_genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd.ModularCurve _root_.P2MW.S_ModularCurve_genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd.ModularCurve.IgusaGenusLB

open _root_.AlgebraicCurve hiding genus in open  _root_.ModularCurve _root_.P2MW.S_ModularCurve_genusFF_xHFunctionFieldBar_le_genusFF_xHFunctionFieldC_of_not_dvd.ModularCurve in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (k : Type*) [Field k] [IsAlgClosed k] [CharP k ℓ] :
    genusFF (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) ≤
      genusFF k (ModularCurve.xHFunctionFieldC k M H) :=
  ModularCurve.IgusaGenusLB.main M H hℓM k

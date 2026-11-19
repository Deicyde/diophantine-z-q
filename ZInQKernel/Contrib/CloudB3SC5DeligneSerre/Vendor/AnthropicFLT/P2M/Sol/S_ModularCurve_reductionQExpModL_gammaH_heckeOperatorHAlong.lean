/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_reductionQExpModL_gammaH_heckeOperatorHAlong (git blob d104763e0a011b0f0e497638e4929d1dc83a9c3d, sha256 36d66a0f458ae30b7db52fd7ebe74924186d4272c46c790e290b8dcfcbb27e6d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpReductionModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpFrobeniusModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_qExpand_norm_heckeBetaHBar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace ModularCurve
end ModularCurve
namespace HahnSeries
end HahnSeries
namespace P2MW.S_ModularCurve_reductionQExpModL_gammaH_heckeOperatorHAlong.ESGammaHSol
end P2MW.S_ModularCurve_reductionQExpModL_gammaH_heckeOperatorHAlong.ESGammaHSol

namespace P2MW.S_ModularCurve_reductionQExpModL_gammaH_heckeOperatorHAlong

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open _root_.AlgebraicCurve
open _root_.ModularCurve hiding coeffMap_injective
open _root_.HahnSeries

namespace ESGammaHSol



section Along

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem pullbackAlong_apply_eq_ord [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) {f : F} {D : Divisor K F} (hD : ∀ v, D v = v.ord f)
    (w : Place K F') : Divisor.pullbackAlong φ hφ D w = w.ord (φ f) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Divisor.pullback_apply_eq_ord hD w

theorem pushforwardAlong_apply_eq_ord (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K φ) (hN : NormFormulaAlong K φ hfin) {g : F'} (hg : g ≠ 0)
    {D : Divisor K F'} (hD : ∀ w, D w = w.ord g) (v : Place K F) :
    Divisor.pushforwardAlong φ hφ D v = v.ord (letI := algebraAlong φ; Algebra.norm F g) := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  haveI : Module.Finite F F' := hfin
  exact hN g hg D hD v

end Along

section Engine

variable {L F : Type*} [Field L] [Field F] [Algebra L F]
variable {k Fb : Type*} [Field k] [Field Fb] [Algebra k Fb]

theorem int_eq_zero_of_forall_dvd {a : ℤ} (h : ∀ n : ℕ, n ≠ 0 → (n : ℤ) ∣ a) : a = 0 :=
  Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h (a.natAbs + 1) (Nat.succ_ne_zero _))
    (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)

theorem eq_of_agree (S : Set (Divisor L F))
    (hgen : Divisor.principal (K := L) (F := F) ≤ AddSubgroup.closure S)
    (Φ Ψ : Divisor L F →+ Divisor k Fb) (hagree : ∀ D ∈ S, Φ D = Ψ D)
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 L F, ∃ y : Pic0 L F, n • y = x)
    {D : Divisor L F} (hD : D ∈ Divisor.degZero (K := L) (F := F)) : Φ D = Ψ D := by
  classical
  set δ : Divisor L F →+ Divisor k Fb := Φ - Ψ with hδ
  have hδapp : ∀ E, δ E = Φ E - Ψ E := fun E => rfl

  have hδprin : ∀ E ∈ Divisor.principal (K := L) (F := F), δ E = 0 := by
    intro E hE
    have hE' := hgen hE
    clear hE
    induction hE' using AddSubgroup.closure_induction with
    | mem E hE => rw [hδapp, hagree E hE, sub_self]
    | zero => exact map_zero δ
    | add E E' _ _ hE hE' => rw [map_add, hE, hE', add_zero]
    | neg E _ hE => rw [map_neg, hE, neg_zero]

  have hδD : δ D = 0 := by
    ext Q
    rw [Finsupp.zero_apply]
    refine int_eq_zero_of_forall_dvd fun n hn => ?_
    obtain ⟨y, hy⟩ := hdiv n hn (Pic0.mk ⟨D, hD⟩)
    obtain ⟨E, rfl⟩ := Pic0.mk_surjective y
    have hmem : ((⟨D, hD⟩ : Divisor.degZero (K := L) (F := F)) - n • E :
        Divisor.degZero (K := L) (F := F)) ∈
          (Divisor.principal (K := L) (F := F)).addSubgroupOf (Divisor.degZero (K := L) (F := F)) := by
      rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.mk_nsmul]
      exact hy.symm
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_nsmul] at hmem
    have h0 := hδprin _ hmem
    rw [map_sub, map_nsmul, sub_eq_zero] at h0
    refine ⟨δ (E : Divisor L F) Q, ?_⟩
    rw [h0, Finsupp.smul_apply, nsmul_eq_mul]
  rw [hδapp] at hδD
  exact sub_eq_zero.mp hδD

end Engine

section Series

variable {R S : Type*} [CommRing R] [CommRing S]

theorem coeffMap_qTwist (f : R →+* S) (c : Rˣ) (x : LaurentSeries R) :
    coeffMap f (qTwist c x) = qTwist (Units.map (f : R →* S) c) (coeffMap f x) := by
  ext n
  rw [coeffMap_coeff, qTwist_coeff, qTwist_coeff, coeffMap_coeff, map_mul, ← map_zpow, Units.coe_map]
  rfl

theorem coeffMap_qExpand' (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

def unexpand (ℓ : ℕ) [NeZero ℓ] (P : LaurentSeries R) : LaurentSeries R where
  coeff k := P.coeff ((ℓ : ℤ) * k)
  isPWO_support' := by
    have hℓ : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
    refine (P.isPWO_support.image_of_monotone (f := fun n : ℤ => n / (ℓ : ℤ))
      (fun a b h => Int.ediv_le_ediv hℓ h)).mono ?_
    intro k hk
    refine ⟨(ℓ : ℤ) * k, hk, ?_⟩
    show (ℓ : ℤ) * k / (ℓ : ℤ) = k
    exact Int.mul_ediv_cancel_left k hℓ.ne'

theorem unexpand_coeff (ℓ : ℕ) [NeZero ℓ] (P : LaurentSeries R) (k : ℤ) :
    (unexpand ℓ P).coeff k = P.coeff ((ℓ : ℤ) * k) := rfl

theorem qExpand_unexpand (ℓ : ℕ) [NeZero ℓ] (P : LaurentSeries R)
    (hP : ∀ n : ℤ, ¬ (ℓ : ℤ) ∣ n → P.coeff n = 0) : qExpand R ℓ (unexpand ℓ P) = P := by
  ext n
  by_cases h : (ℓ : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := h
    rw [qExpand_coeff_mul, unexpand_coeff]
  · rw [qExpand_coeff_of_not_dvd ℓ _ h, hP n h]

theorem coeffMap_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (coeffMap f : LaurentSeries R → LaurentSeries S) := by
  intro x y h
  ext n
  have := congrArg (fun s : LaurentSeries S => s.coeff n) h
  simp only [coeffMap_coeff] at this
  exact hf this

end Series

section RootsOfUnity

variable {ℓ : ℕ} [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))

theorem zeta_mem {ζ : (AlgebraicClosure ℚ)} (hζ : IsPrimitiveRoot ζ ℓ) : ζ ∈ A := by
  have hprime : ℓ.Prime := Fact.out
  rcases A.mem_or_inv_mem ζ with h | h
  · exact h
  · have h2 : (ζ⁻¹) ^ (ℓ - 1) = ζ := by
      rw [inv_pow]
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ, Nat.sub_add_cancel hprime.one_le, hζ.pow_eq_one]
    rw [← h2]
    exact pow_mem h _

def zetaUnit {ζ : (AlgebraicClosure ℚ)} (hζ : IsPrimitiveRoot ζ ℓ) : Aˣ :=
  Units.ofPowEqOne (⟨ζ, zeta_mem A hζ⟩ : A) ℓ
    (Subtype.ext (by
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      exact hζ.pow_eq_one)) (NeZero.ne ℓ)

def zu {ζ : (AlgebraicClosure ℚ)} (hζ : IsPrimitiveRoot ζ ℓ) : (AlgebraicClosure ℚ)ˣ := Units.mk0 ζ (hζ.ne_zero (NeZero.ne ℓ))

theorem map_subtype_zetaUnit {ζ : (AlgebraicClosure ℚ)} (hζ : IsPrimitiveRoot ζ ℓ) :
    Units.map (A.subtype : A →* (AlgebraicClosure ℚ)) (zetaUnit A hζ) = zu hζ :=
  Units.ext rfl

theorem isPrimitiveRoot_zu {ζ : (AlgebraicClosure ℚ)} (hζ : IsPrimitiveRoot ζ ℓ) : IsPrimitiveRoot (zu hζ) ℓ :=
  IsPrimitiveRoot.coe_units_iff.mp hζ

theorem map_residue_zetaUnit [CharP (IsLocalRing.ResidueField A) ℓ]
    {ζ : (AlgebraicClosure ℚ)} (hζ : IsPrimitiveRoot ζ ℓ) :
    Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A) (zetaUnit A hζ) = 1 := by
  have hzℓ : (Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A)
      (zetaUnit A hζ)) ^ ℓ = 1 := by
    rw [← map_pow, zetaUnit, Units.pow_ofPowEqOne, map_one]
  apply Units.ext
  have h0 : ((Units.map (IsLocalRing.residue A : A →* IsLocalRing.ResidueField A)
      (zetaUnit A hζ) : IsLocalRing.ResidueField A) - 1) ^ ℓ = 0 := by
    rw [sub_pow_char, ← Units.val_pow_eq_pow_val, hzℓ, Units.val_one, one_pow, sub_self]
  rw [Units.val_one]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (NeZero.ne ℓ)).mp h0)

end RootsOfUnity

section CharL

variable {k : Type*} [Field k] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]

omit [Fact ℓ.Prime] [CharP k ℓ] in

theorem coeffMap_intSeriesC (g : k →+* k) (p : PowerSeries ℤ) : coeffMap g (intSeriesC k p) = intSeriesC k p := by
  ext n
  rw [coeffMap_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [intSeriesC, ofPowerSeries_coeff_of_neg _ hn, map_zero]
  · lift n to ℕ using hn with n
    rw [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, eq_intCast, map_intCast]

omit [Fact ℓ.Prime] [CharP k ℓ] in

theorem coeffMap_mem (g : k →+* k) {x : LaurentSeries k} (hx : x ∈ qExpFunctionFieldC k Γ) :
    coeffMap g x ∈ qExpFunctionFieldC k Γ := by
  have hx' : x ∈ (qExpFunctionFieldC k Γ).toSubfield := hx
  rw [qExpFunctionFieldC, IntermediateField.adjoin_toSubfield] at hx'
  have key : (Subfield.closure (Set.range (algebraMap k (LaurentSeries k)) ∪ intFormRatiosC k Γ)).map
      (coeffMap g) ≤ (qExpFunctionFieldC k Γ).toSubfield := by
    rw [RingHom.map_field_closure, Subfield.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with ⟨c, rfl⟩ | ⟨w, f, g', pf, pg, hf, hg, hg0, rfl⟩
    · rw [coeffMap_algebraMap]
      exact (qExpFunctionFieldC k Γ).algebraMap_mem _
    · change coeffMap g (intSeriesC k pf / intSeriesC k pg) ∈ qExpFunctionFieldC k Γ
      rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
      exact div_mem_qExpFunctionFieldC f g' hf hg hg0
  exact key ⟨x, hx', rfl⟩

theorem norm_frobenius_eq (hrank : finrankAlong k (qExpFrobeniusModL k Γ ℓ) = ℓ)
    {f g : qExpFunctionFieldC k Γ} (hg : qExpFrobeniusModL k Γ ℓ g = f ^ ℓ) :
    (letI := algebraAlong (qExpFrobeniusModL k Γ ℓ);
      Algebra.norm (qExpFunctionFieldC k Γ) f) = g := by
  letI := algebraAlong (qExpFrobeniusModL k Γ ℓ)
  haveI : CharP (qExpFunctionFieldC k Γ) ℓ :=
    charP_of_injective_algebraMap (algebraMap k (qExpFunctionFieldC k Γ)).injective ℓ
  have hpow : (Algebra.norm (qExpFunctionFieldC k Γ) f) ^ ℓ = g ^ ℓ := by
    have h3 : Algebra.norm (qExpFunctionFieldC k Γ)
        (algebraMap (qExpFunctionFieldC k Γ) (qExpFunctionFieldC k Γ) g) =
          g ^ finrankAlong k (qExpFrobeniusModL k Γ ℓ) :=
      Algebra.norm_algebraMap g
    calc (Algebra.norm (qExpFunctionFieldC k Γ) f) ^ ℓ
        = Algebra.norm (qExpFunctionFieldC k Γ) (f ^ ℓ) := (map_pow (Algebra.norm (qExpFunctionFieldC k Γ)) f ℓ).symm
      _ = Algebra.norm (qExpFunctionFieldC k Γ)
            (algebraMap (qExpFunctionFieldC k Γ) (qExpFunctionFieldC k Γ) g) := by
          rw [show algebraMap (qExpFunctionFieldC k Γ) (qExpFunctionFieldC k Γ) g =
            qExpFrobeniusModL k Γ ℓ g from rfl, hg]
      _ = g ^ finrankAlong k (qExpFrobeniusModL k Γ ℓ) := h3
      _ = g ^ ℓ := by rw [hrank]
  exact frobenius_inj (qExpFunctionFieldC k Γ) ℓ hpow

theorem coe_eq_coeffMap_frobenius_of_eq_pow {f g : qExpFunctionFieldC k Γ}
    (hg : qExpFrobeniusModL k Γ ℓ g = f ^ ℓ) :
    (g : LaurentSeries k) = coeffMap (frobenius k ℓ) (f : LaurentSeries k) := by
  haveI := charP_laurentSeriesC k ℓ
  apply qExpand_injective ℓ
  have h := congrArg (fun z : qExpFunctionFieldC k Γ => (z : LaurentSeries k)) hg
  simp only [coe_qExpFrobeniusModL] at h
  rw [h, show ((f ^ ℓ : qExpFunctionFieldC k Γ) : LaurentSeries k) = (f : LaurentSeries k) ^ ℓ from rfl,
    pow_char_eq_coeffMap_frobenius_qExpand ℓ (f : LaurentSeries k), coeffMap_qExpand']

end CharL

section Agree

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [Fact ℓ.Prime]
variable {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (IsLocalRing.ResidueField A) ℓ]






variable (A M H) in

def genSet (d : (ZMod M)ˣ) : Set (Divisor (AlgebraicClosure ℚ) (xHFunctionFieldBar M H)) :=
  {D | ∃ (y u : LaurentSeries A) (hy : coeffMap A.subtype y ∈ (xHFunctionFieldBar M H)),
      coeffMap A.subtype u = ((diamondAutHBar M H d ⟨coeffMap A.subtype y, hy⟩ : (xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) ∧
      coeffMap (IsLocalRing.residue A) y ∈ xHFunctionFieldC (IsLocalRing.ResidueField A) M H ∧
      coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
      coeffMap (IsLocalRing.residue A) u ∈ xHFunctionFieldC (IsLocalRing.ResidueField A) M H ∧
      coeffMap (IsLocalRing.residue A) u ≠ 0 ∧
      ∀ P, D P = P.ord (⟨coeffMap A.subtype y, hy⟩ : (xHFunctionFieldBar M H))}

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem agree_on_generator (hℓM : ¬ ℓ ∣ M) (hin : HeckeDiamondInputsHAll M H)
    {r : Place (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) → Place (IsLocalRing.ResidueField A) (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))}
    (hr : IsPlaceReductionQExpModL A (CohCarrier.GammaH M H) r)
    (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) M H ℓ) (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ)) (hN : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hfin)
    [HasPrincipalDivisors (IsLocalRing.ResidueField A) (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))]
    (hfin' : FiniteAlong (IsLocalRing.ResidueField A) (qExpFrobeniusModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ))
    (hN' : NormFormulaAlong (IsLocalRing.ResidueField A) (qExpFrobeniusModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ) hfin')
    (hrank : finrankAlong (IsLocalRing.ResidueField A) (qExpFrobeniusModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ) = ℓ)
    {D : Divisor (AlgebraicClosure ℚ) (xHFunctionFieldBar M H)}
    (hD : D ∈ genSet M H A (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM))) :
    Finsupp.mapDomain r (heckeDivHBar hα hβ D) =
      qExpFrobeniusDivPushforwardModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ
          (Finsupp.mapDomain r
            (SemilinearAut.ofAlgAut (diamondAutHBar M H
              (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM))) • D)) +
        qExpFrobeniusDivPullbackModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ (Finsupp.mapDomain r D) := by
  classical
  obtain ⟨y, u, hy, hu, hyk, hy0, huk, hu0, hDy⟩ := hD
  set d : (ZMod M)ˣ := ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM) with hd
  set σ : (xHFunctionFieldBar M H) ≃ₐ[(AlgebraicClosure ℚ)] (xHFunctionFieldBar M H) := diamondAutHBar M H d with hσ

  set f : (xHFunctionFieldBar M H) := ⟨coeffMap A.subtype y, hy⟩ with hf_def
  have hyk' : coeffMap (IsLocalRing.residue A) y ∈ (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) := hyk
  have huk' : coeffMap (IsLocalRing.residue A) u ∈ (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) := huk
  set fbar : (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) := ⟨coeffMap (IsLocalRing.residue A) y, hyk'⟩ with hfbar_def
  set ubar : (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) := ⟨coeffMap (IsLocalRing.residue A) u, huk'⟩ with hubar_def
  have hfbar : fbar ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  have hubar : ubar ≠ 0 := fun h => hu0 (congrArg Subtype.val h)
  have hAinj : Function.Injective (A.subtype) := fun a b hab => Subtype.ext hab
  have hy0' : y ≠ 0 := by
    rintro rfl
    exact hy0 (map_zero _)
  have hf : f ≠ 0 := by
    intro h
    apply hy0'
    have h' : coeffMap A.subtype y = 0 := congrArg Subtype.val h
    exact coeffMap_injective hAinj (by rw [h', map_zero])
  have hβf : heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f ≠ 0 := (map_ne_zero _).mpr hf

  have hu_mem : coeffMap A.subtype u ∈ (xHFunctionFieldBar M H) := by rw [hu]; exact SetLike.coe_mem _
  have hσf : σ f = ⟨coeffMap A.subtype u, hu_mem⟩ := Subtype.ext hu.symm

  have hpull : ∀ w, Divisor.pullbackAlong (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hβ D w = w.ord (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f) :=
    fun w => pullbackAlong_apply_eq_ord (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hβ hDy w
  have hT : ∀ v, heckeDivHBar hα hβ D v =
      v.ord (letI := algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ);
        Algebra.norm (xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f)) := by
    intro v
    rw [heckeDivHBar, Divisor.correspondence_apply]
    exact pushforwardAlong_apply_eq_ord (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hα hfin hN hβf hpull v

  haveI : NeZero ((ℓ : ℕ) : (AlgebraicClosure ℚ)) := NeZero.charZero
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) ℓ
  have hnorm := ModularCurve.qExpand_norm_heckeBetaHBar M H hℓM hin (zu hζ) (isPrimitiveRoot_zu hζ) f
  rw [← hσ, hσf] at hnorm

  set P : LaurentSeries A :=
    (∏ j ∈ Finset.range ℓ, qTwist (zetaUnit A hζ ^ j) u) * qExpand A ℓ (qExpand A ℓ y) with hP
  have hPQ : coeffMap A.subtype P
      = (∏ j ∈ Finset.range ℓ, qTwist (zu hζ ^ j) (coeffMap A.subtype u))
        * qExpand (AlgebraicClosure ℚ) ℓ (qExpand (AlgebraicClosure ℚ) ℓ (coeffMap A.subtype y)) := by
    rw [hP, map_mul, map_prod, coeffMap_qExpand', coeffMap_qExpand']
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [coeffMap_qTwist, map_pow, map_subtype_zetaUnit]
  have hPQ' := hPQ.trans hnorm.symm

  have hPsupp : ∀ n : ℤ, ¬ (ℓ : ℤ) ∣ n → P.coeff n = 0 := by
    intro n hn
    have h := congrArg (fun s : LaurentSeries (AlgebraicClosure ℚ) => s.coeff n) hPQ'
    simp only [coeffMap_coeff, qExpand_coeff_of_not_dvd ℓ _ hn] at h
    exact (map_eq_zero_iff A.subtype hAinj).mp h
  set y' : LaurentSeries A := unexpand ℓ P with hy'
  have hy'1 : coeffMap A.subtype y' = ((letI := algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ);
        Algebra.norm (xHFunctionFieldBar M H) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f) : (xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
    apply qExpand_injective ℓ
    rw [← coeffMap_qExpand' A.subtype ℓ (unexpand ℓ P), qExpand_unexpand ℓ P hPsupp]
    exact hPQ'
  have hy'2 : coeffMap (IsLocalRing.residue A) y' =
      coeffMap (frobenius (IsLocalRing.ResidueField A) ℓ) (coeffMap (IsLocalRing.residue A) u) *
        qExpand (IsLocalRing.ResidueField A) ℓ (coeffMap (IsLocalRing.residue A) y) := by
    apply qExpand_injective ℓ
    rw [← coeffMap_qExpand' (IsLocalRing.residue A) ℓ (unexpand ℓ P), qExpand_unexpand ℓ P hPsupp,
      hP, map_mul, map_prod, coeffMap_qExpand', coeffMap_qExpand',
      Finset.prod_eq_pow_card (b := coeffMap (IsLocalRing.residue A) u), Finset.card_range,
      map_mul, ← coeffMap_qExpand' (frobenius (IsLocalRing.ResidueField A) ℓ) ℓ, ← pow_char_eq_coeffMap_frobenius_qExpand ℓ]
    intro j _
    rw [coeffMap_qTwist, map_pow, map_residue_zetaUnit, one_pow, qTwist_one_apply]

  have hy'mem : coeffMap A.subtype y' ∈ (xHFunctionFieldBar M H) := by rw [hy'1]; exact SetLike.coe_mem _
  have hT' : ∀ v, heckeDivHBar hα hβ D v = v.ord (⟨coeffMap A.subtype y', hy'mem⟩ : (xHFunctionFieldBar M H)) := by
    intro v
    rw [hT v]
    congr 1
    exact Subtype.ext hy'1.symm

  obtain ⟨g, hg⟩ := exists_qExpFrobeniusModL_eq_pow (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ ubar
  have hgcoe : (g : LaurentSeries (IsLocalRing.ResidueField A)) = coeffMap (frobenius (IsLocalRing.ResidueField A) ℓ) (coeffMap (IsLocalRing.residue A) u) :=
    coe_eq_coeffMap_frobenius_of_eq_pow hg
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hg
    exact pow_ne_zero ℓ hubar hg.symm
  have hFr0 : qExpFrobeniusModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ fbar ≠ 0 := (map_ne_zero _).mpr hfbar
  have hprod : coeffMap (IsLocalRing.residue A) y' = ((g * qExpFrobeniusModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ fbar : (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField A)) := by
    rw [hy'2, ← hgcoe]
    rfl
  have hy'k : coeffMap (IsLocalRing.residue A) y' ∈ (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) := by
    rw [hprod]; exact SetLike.coe_mem _
  have hy'ne : coeffMap (IsLocalRing.residue A) y' ≠ 0 := by
    rw [hprod]
    exact fun h => (mul_ne_zero hg0 hFr0) (Subtype.ext h)
  have hy'eq : (⟨coeffMap (IsLocalRing.residue A) y', hy'k⟩ : (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))) = g * qExpFrobeniusModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ fbar :=
    Subtype.ext hprod

  have hup : ∀ Q, Finsupp.mapDomain r (heckeDivHBar hα hβ D) Q =
      Q.ord g + Q.ord (qExpFrobeniusModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ fbar) := by
    intro Q
    rw [hr.2 y' hy'mem hy'k hy'ne (heckeDivHBar hα hβ D) hT' Q, hy'eq, Q.ord_mul hg0 hFr0]
  have hdown : ∀ Q, Finsupp.mapDomain r D Q = Q.ord fbar := hr.2 y hy hyk' hy0 D hDy
  have hσD : ∀ w, (SemilinearAut.ofAlgAut σ • D) w = w.ord (⟨coeffMap A.subtype u, hu_mem⟩ : (xHFunctionFieldBar M H)) := by
    intro w
    rw [SemilinearAut.divisor_smul_apply, hDy, ← hσf]
    have h := SemilinearAut.ord_smul (SemilinearAut.ofAlgAut σ) ((SemilinearAut.ofAlgAut σ)⁻¹ • w) f
    rw [smul_inv_smul, SemilinearAut.ofAlgAut_smul] at h
    exact h.symm
  have hσdown : ∀ Q, Finsupp.mapDomain r (SemilinearAut.ofAlgAut σ • D) Q = Q.ord ubar :=
    hr.2 u hu_mem huk' hu0 _ hσD

  have hpush' : ∀ Q, qExpFrobeniusDivPushforwardModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ
      (Finsupp.mapDomain r (SemilinearAut.ofAlgAut σ • D)) Q = Q.ord g := by
    intro Q
    have h1 := pushforwardAlong_apply_eq_ord (qExpFrobeniusModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ) (qExpFrobeniusModL_isIntegral (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ)
      hfin' hN' hubar hσdown Q
    have h2 := norm_frobenius_eq (k := (IsLocalRing.ResidueField A)) (Γ := (CohCarrier.GammaH M H)) hrank hg
    rw [h2] at h1
    exact h1
  have hpull' : ∀ Q, qExpFrobeniusDivPullbackModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ (Finsupp.mapDomain r D) Q =
      Q.ord (qExpFrobeniusModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ fbar) := fun Q =>
    pullbackAlong_apply_eq_ord (qExpFrobeniusModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ) (qExpFrobeniusModL_isIntegral (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ) hdown Q

  ext Q
  rw [hup Q, Finsupp.add_apply, hpush' Q, hpull' Q]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem divisor_identity (hℓM : ¬ ℓ ∣ M) (hin : HeckeDiamondInputsHAll M H)
    {r : Place (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) → Place (IsLocalRing.ResidueField A) (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))}
    (hr : IsPlaceReductionQExpModL A (CohCarrier.GammaH M H) r)
    (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) M H ℓ) (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ)) (hN : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hfin)
    [HasPrincipalDivisors (IsLocalRing.ResidueField A) (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))]
    (hfin' : FiniteAlong (IsLocalRing.ResidueField A) (qExpFrobeniusModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ))
    (hN' : NormFormulaAlong (IsLocalRing.ResidueField A) (qExpFrobeniusModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ) hfin')
    (hrank : finrankAlong (IsLocalRing.ResidueField A) (qExpFrobeniusModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ) = ℓ)
    (hgen : Divisor.principal (K := (AlgebraicClosure ℚ)) (F := (xHFunctionFieldBar M H)) ≤
      AddSubgroup.closure (genSet M H A (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM))))
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 (AlgebraicClosure ℚ) (xHFunctionFieldBar M H), ∃ y : Pic0 (AlgebraicClosure ℚ) (xHFunctionFieldBar M H), n • y = x)
    {D : Divisor (AlgebraicClosure ℚ) (xHFunctionFieldBar M H)} (hD0 : D ∈ Divisor.degZero (K := (AlgebraicClosure ℚ)) (F := (xHFunctionFieldBar M H))) :
    Finsupp.mapDomain r (heckeDivHBar hα hβ D) =
      qExpFrobeniusDivPushforwardModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ
          (Finsupp.mapDomain r
            (SemilinearAut.ofAlgAut (diamondAutHBar M H
              (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM))) • D)) +
        qExpFrobeniusDivPullbackModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ (Finsupp.mapDomain r D) := by
  set g := SemilinearAut.ofAlgAut (K := (AlgebraicClosure ℚ)) (F := (xHFunctionFieldBar M H))
    (diamondAutHBar M H (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM))) with hg_def
  let mr : Divisor (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) →+ Divisor (IsLocalRing.ResidueField A) (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) := Finsupp.mapDomain.addMonoidHom r
  let Φ : Divisor (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) →+ Divisor (IsLocalRing.ResidueField A) (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) := mr.comp (heckeDivHBar hα hβ)
  let Ψ : Divisor (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) →+ Divisor (IsLocalRing.ResidueField A) (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) :=
    (qExpFrobeniusDivPushforwardModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ).comp (mr.comp (DistribSMul.toAddMonoidHom (Divisor (AlgebraicClosure ℚ) (xHFunctionFieldBar M H)) g)) +
      (qExpFrobeniusDivPullbackModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ).comp mr
  have hΦ : ∀ E, Φ E = Finsupp.mapDomain r (heckeDivHBar hα hβ E) := fun E => rfl
  have hΨ : ∀ E, Ψ E = qExpFrobeniusDivPushforwardModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ (Finsupp.mapDomain r (g • E)) +
      qExpFrobeniusDivPullbackModL (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) ℓ (Finsupp.mapDomain r E) := fun E => rfl
  have key := eq_of_agree (genSet M H A (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM)))
    hgen Φ Ψ (fun E hE => by
      rw [hΦ, hΨ]
      exact agree_on_generator hℓM hin hr hα hβ hfin hN hfin' hN' hrank hE)
    hdiv hD0
  rw [hΦ, hΨ] at key
  exact key

end Agree

section Upstairs

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

scoped instance : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

theorem exists_transcendental_bar :
    ∃ x : xHFunctionFieldBar M H, Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set (xHFunctionFieldBar M H))) (xHFunctionFieldBar M H) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)
    (translation_mem_GammaH M H)

theorem jH_divisible (n : ℕ) (hn : n ≠ 0) (x : Pic0 (AlgebraicClosure ℚ) (xHFunctionFieldBar M H)) :
    ∃ y : Pic0 (AlgebraicClosure ℚ) (xHFunctionFieldBar M H), n • y = x := by
  obtain ⟨t, htr, hfd⟩ := exists_transcendental_bar M H
  haveI : IsCurveOver (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfd
  exact AlgebraicCurve.Pic0.exists_nsmul_eq (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) ⟨t, htr, hfd⟩ n hn x

end Upstairs

end ESGammaHSol
open scoped _root_.P2MW.S_ModularCurve_reductionQExpModL_gammaH_heckeOperatorHAlong.ESGammaHSol

open ESGammaHSol in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (IsLocalRing.ResidueField A) ℓ]
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (h : ModularCurve.ReductionInputsQExpModL A (CohCarrier.GammaH M H))
    (z : ModularCurve.JH M H) :
    ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H)
        (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ z) =
      ModularCurve.qExpFrobeniusPushforwardModL (IsLocalRing.ResidueField A)
          (CohCarrier.GammaH M H) ℓ
          (ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H)
            (ModularCurve.diamondHBar M H
              (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM)) z))
        + ModularCurve.qExpFrobeniusPullbackModL (IsLocalRing.ResidueField A)
            (CohCarrier.GammaH M H) ℓ
            (ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H) z) := by

  obtain ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩ := hin.heckeInputsHAlong ℓ Fact.out
  haveI := hP
  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  have hF : ∃ x : qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H),
      Transcendental (IsLocalRing.ResidueField A) x ∧
        FiniteDimensional (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({x} : Set (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))))
          (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) :=
    (ModularCurve.exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd M H hℓM A hA).1
  obtain ⟨⟨hPk, hfin', hFI', hN'⟩, hrank⟩ :=
    ModularCurve.qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental (IsLocalRing.ResidueField A)
      (ℓ := ℓ) (CohCarrier.GammaH M H) hF
  haveI := hPk

  obtain ⟨D, rfl⟩ := Pic0.mk_surjective z
  rw [heckeOperatorHAlong_eq h0 hα hβ hFI hfin hN, heckePic0HBar, Pic0.correspondence_mk,
    diamondHBar_apply, SemilinearAut.pic0_smul_mk]
  have hred : ∀ D' : Divisor.degZero (K := AlgebraicClosure ℚ) (F := xHFunctionFieldBar M H),
      reductionQExpModL A (CohCarrier.GammaH M H) (Pic0.mk D') =
        Pic0.mk (laurentReductionDegZero (placeReductionQExpModL h)
          (isPlaceReductionQExpModL_placeReductionQExpModL h).1 D') :=
    fun D' => reductionQExpModL_mk h D'
  erw [hred, hred, hred]
  rw [qExpFrobeniusPushforwardModL_mk hfin' hFI' hN', qExpFrobeniusPullbackModL_mk hfin' hFI' hN',
    ← Pic0.mk_add]
  refine congrArg Pic0.mk (Subtype.ext ?_)

  exact divisor_identity hℓM hin (isPlaceReductionQExpModL_placeReductionQExpModL h) hα hβ hfin hN hfin' hN'
    hrank (ModularCurve.principal_le_closure_divisor_laurentIntegral_diamondAutHBar M H hℓM A hA hin _)
    (jH_divisible M H) D.2

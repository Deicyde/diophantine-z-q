/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus (git blob 4e37e1505ba9baeebc19dc960d852324a84bbb48, sha256 d297c69133d1312d5b24cdd336951f041e60d427e1ecffd42439d8c5c729880a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RiemannRochRows
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_ratFunc
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus.AlgebraicCurve
end P2MW.S_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus.AlgebraicCurve
namespace KaehlerDifferential
end KaehlerDifferential
namespace IntermediateField
end IntermediateField

namespace P2MW.S_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus

set_option autoImplicit false

noncomputable section

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus.AlgebraicCurve
open _root_.KaehlerDifferential
open _root_.IntermediateField

namespace AlgebraicCurve
export _root_.AlgebraicCurve (IsCurveOver IsCurveOver.finrank_kaehler Place Divisor HasCanonicalDivisor canonicalDivisorOf canonicalDivisorOf_apply genus Place.ordDifferential regularDifferentials mem_regularDifferentials_iff FunctionFieldRiemannRoch LSpace ell mem_lSpace_iff_ord ConstantsAreBase ell_zero_eq_one_of_constantsAreBase dCoordGenerates_of_isCurveOver IsCurveOver.exists_separating_transcendental isCurveOver_ratFunc essFiniteType_of_transcendental_of_finiteDimensional functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver constantsAreBase_of_isAlgClosed finiteDimensional_lSpace)
open _root_.AlgebraicCurve

namespace RegularDifferentialsFinrank

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem_valuationSubring (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg Subtype.val hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_valuationSubring_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0)
    (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem differentialCoeff_ne_zero {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) [v.DCoordGenerates] :
    v.differentialCoeff ω ≠ 0 := by
  intro h
  apply hω
  rw [← v.differentialCoeff_smul_dCoord ω, h, zero_smul]

theorem exists_smul_eq [IsCurveOver K F] {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (ω : Ω[F⁄K]) :
    ∃ h : F, h • ω₀ = ω :=
  (finrank_eq_one_iff_of_nonzero' ω₀ hω₀).mp IsCurveOver.finrank_kaehler ω

section Comparison

variable [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates]

theorem smul_mem_regularDifferentials_iff {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (h : F) :
    h • ω₀ ∈ regularDifferentials K F ↔ h ∈ LSpace (canonicalDivisorOf hω₀) := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp only [zero_smul, Submodule.zero_mem]
  rw [mem_regularDifferentials_iff, mem_lSpace_iff_ord, or_iff_right hh]
  refine forall_congr' fun v => ?_
  have hc : v.differentialCoeff ω₀ ≠ 0 := differentialCoeff_ne_zero hω₀ v

  have hdec : h • ω₀ = (h * v.differentialCoeff ω₀) • v.dCoord := by
    rw [mul_smul, v.differentialCoeff_smul_dCoord]
  have hprod : h * v.differentialCoeff ω₀ ≠ 0 := mul_ne_zero hh hc
  rw [canonicalDivisorOf_apply, Place.ordDifferential]
  constructor
  · rintro ⟨g, hg, hEq⟩

    have hgu : g = h * v.differentialCoeff ω₀ := by
      rw [← v.differentialCoeff_unique hEq, v.differentialCoeff_unique hdec]
    have h0 : 0 ≤ v.ord (h * v.differentialCoeff ω₀) :=
      hgu ▸ ord_nonneg_of_mem_valuationSubring v hg
    rw [v.ord_mul hh hc] at h0
    linarith
  · intro hle
    refine ⟨h * v.differentialCoeff ω₀, ?_, hdec⟩
    refine mem_valuationSubring_of_ord_nonneg v hprod ?_
    rw [v.ord_mul hh hc]
    linarith

def toRegular {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    LSpace (canonicalDivisorOf hω₀) →ₗ[K] regularDifferentials K F where
  toFun h := ⟨(h : F) • ω₀, (smul_mem_regularDifferentials_iff hω₀ (h : F)).mpr h.2⟩
  map_add' h₁ h₂ := by
    ext
    simp [add_smul]
  map_smul' c h := by
    ext
    simp [smul_assoc]

theorem toRegular_apply {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (h : LSpace (canonicalDivisorOf hω₀)) :
    ((toRegular hω₀ h : regularDifferentials K F) : Ω[F⁄K]) = (h : F) • ω₀ := rfl

theorem toRegular_bijective {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    Function.Bijective (toRegular (K := K) (F := F) hω₀) := by
  constructor
  · intro h₁ h₂ hEq
    have hEq' : ((h₁ : F) - (h₂ : F)) • ω₀ = 0 := by
      have := congrArg (fun x : regularDifferentials K F => (x : Ω[F⁄K])) hEq
      simp only [toRegular_apply] at this
      rw [sub_smul, this, sub_self]
    rcases smul_eq_zero.mp hEq' with h0 | h0
    · exact Subtype.ext (sub_eq_zero.mp h0)
    · exact absurd h0 hω₀
  · rintro ⟨ω, hω⟩
    obtain ⟨h, rfl⟩ := exists_smul_eq hω₀ ω
    exact ⟨⟨h, (smul_mem_regularDifferentials_iff hω₀ h).mp hω⟩, rfl⟩

def lSpaceCanonicalEquivRegular {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    LSpace (canonicalDivisorOf hω₀) ≃ₗ[K] regularDifferentials K F :=
  LinearEquiv.ofBijective (toRegular hω₀) (toRegular_bijective hω₀)

theorem ell_canonical_eq_genus (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    ell (canonicalDivisorOf hω₀) = genus K F := by
  have h := hRR hω₀ 0
  rw [sub_zero, ell_zero_eq_one_of_constantsAreBase hC] at h
  simp only [map_zero, Nat.cast_one, zero_add] at h
  exact_mod_cast (by linarith : (ell (canonicalDivisorOf hω₀) : ℤ) = genus K F)

end Comparison

theorem riemannRoch_and_constantsAreBase [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates] :
    FunctionFieldRiemannRoch K F ∧ ConstantsAreBase K F := by
  classical

  obtain ⟨t, ht, htfd, htsep⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  haveI := htfd
  haveI := htsep

  set e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht with he
  letI : Algebra (RatFunc K) F :=
    ((algebraMap K⟮t⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
        (e.symm.toRingEquiv : K⟮t⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮t⟯ F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap K⟮t⟯ F (e (e.symm a)) = algebraMap K⟮t⟯ F a
    rw [e.apply_symm_apply]
  haveI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K F a = algebraMap K⟮t⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite (RatFunc K) F

  haveI : IsCurveOver K (RatFunc K) := isCurveOver_ratFunc K
  haveI : FiniteDimensional (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
      (RatFunc K) := by
    refine Module.Finite.of_surjective
      (Algebra.linearMap (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
        (RatFunc K)) fun y => ?_
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [RatFunc.adjoin_X]
    exact IntermediateField.mem_top
  haveI : Algebra.EssFiniteType K (RatFunc K) :=
    essFiniteType_of_transcendental_of_finiteDimensional
      (RatFunc.transcendental_X (K := K)) inferInstance
  haveI : ∀ v : Place K (RatFunc K), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  refine ⟨?_, constantsAreBase_of_isAlgClosed K F⟩
  intro _ _ _ ω hω D
  exact functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver (K := K) (F := F) hω D

end RegularDifferentialsFinrank

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus.AlgebraicCurve AlgebraicCurve.RegularDifferentialsFinrank KaehlerDifferential in
theorem solution {K F : Type*} [Field K]
    [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)] :
    Module.Finite K ↥(AlgebraicCurve.regularDifferentials K F) ∧
      Module.finrank K ↥(AlgebraicCurve.regularDifferentials K F) =
        AlgebraicCurve.genus K F := by
  classical

  haveI : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver

  obtain ⟨hRR, hC⟩ := riemannRoch_and_constantsAreBase (K := K) (F := F)

  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄K])

  haveI : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) := by
    rw [show LSpace (0 : Divisor K F) = _ from hC]
    infer_instance
  haveI : FiniteDimensional K ↥(LSpace (canonicalDivisorOf hω₀)) :=
    finiteDimensional_lSpace _

  set e := lSpaceCanonicalEquivRegular (K := K) (F := F) hω₀
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq]
  exact ell_canonical_eq_genus hRR hC hω₀

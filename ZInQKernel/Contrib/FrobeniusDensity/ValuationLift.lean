import ZInQKernel.Contrib.FrobeniusDensity.ValuationAction
import ZInQKernel.HDecomp.C10.C10
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# From integral Frobenius to an actual valuation-level Frobenius

The integral closure of `ℤ` in `ℚ̄`, localized at a prime above `p`, is a
valuation ring. This is proved by passing each element to a finite number
field and using its Dedekind-domain localization. Congruences then extend
to every local fraction by Mathlib's Frobenius-localization theorem.
No density premise enters this local lift.
-/

noncomputable section

namespace ZInQ.Contrib.FrobeniusDensity

open NumberField IsLocalRing
open scoped NumberField Pointwise

/-- The integral closure of the integers in the same algebraic closure used by T18. -/
abbrev Zbar := GlueC10.Zbar

instance zbarFractionRing : IsFractionRing Zbar Qbar := by
  have : Algebra.IsAlgebraic ℤ Qbar :=
    IsFractionRing.comap_isAlgebraic_iff.mpr (inferInstance : Algebra.IsAlgebraic ℚ Qbar)
  exact integralClosure.isFractionRing_of_algebraic (A := ℤ) (L := Qbar)
    (fun x hx => (FaithfulSMul.algebraMap_injective ℤ Qbar)
      (hx.trans (map_zero (algebraMap ℤ Qbar)).symm))

/-- Every algebraic number or its inverse lies in the localization at a prime
of the integral closure above a rational prime. -/
theorem localization_integer_or_inverse (P : Ideal Zbar) [P.IsPrime] (p : ℕ)
    (hp : p.Prime) (hPp : P.under ℤ = Ideal.span {(p : ℤ)}) :
    let S := Localization.subalgebra.ofField Qbar P.primeCompl P.primeCompl_le_nonZeroDivisors
    ∀ x : Qbar, x ∈ S ∨ x⁻¹ ∈ S := by
  dsimp only
  let S := Localization.subalgebra.ofField Qbar P.primeCompl P.primeCompl_le_nonZeroDivisors
  intro x
  let E := IntermediateField.adjoin ℚ {x}
  have : FiniteDimensional ℚ E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have : NumberField E := ⟨⟩
  let Q := P.comap (GlueC10.toZbar E)
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQp : Q.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← hPp, Ideal.under, Ideal.under, Ideal.comap_comap]
    congr 1
  have hQne : Q ≠ ⊥ := by
    intro h0
    have hpin : (p : 𝓞 E) ∈ Q := by
      change algebraMap ℤ (𝓞 E) (p : ℤ) ∈ Q
      rw [← Ideal.mem_comap]
      change (p : ℤ) ∈ Q.under ℤ
      rw [hQp]
      exact Ideal.mem_span_singleton_self _
    rw [h0, Ideal.mem_bot] at hpin
    exact hp.ne_zero (by exact_mod_cast hpin)
  let W := Localization.subalgebra.ofField E Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  have : IsDiscreteValuationRing W :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) hQne W
  have : IsFractionRing W E :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl W E
  let f : W →+* S := IsLocalization.map S (M := Q.primeCompl) (T := P.primeCompl)
    (GlueC10.toZbar E) (by intro a ha; exact ha)
  have hf : (algebraMap S Qbar).comp f =
      (algebraMap E Qbar).comp (algebraMap W E) := by
    apply IsLocalization.ringHom_ext Q.primeCompl
    ext a
    change algebraMap S Qbar (f (algebraMap (𝓞 E) W a)) =
      algebraMap E Qbar (algebraMap W E (algebraMap (𝓞 E) W a))
    have hmap : f (algebraMap (𝓞 E) W a) = algebraMap Zbar S (GlueC10.toZbar E a) :=
      IsLocalization.map_eq (M := Q.primeCompl) (S := W) (T := P.primeCompl) (Q := S)
        (fun b hb => hb) a
    rw [hmap, ← IsScalarTower.algebraMap_apply Zbar S Qbar,
      ← IsScalarTower.algebraMap_apply (𝓞 E) W E]
    rfl
  let xE : E := ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩
  obtain ⟨a, ha⟩ | ⟨a, ha⟩ := ValuationRing.isInteger_or_isInteger W xE
  · left
    have heq : ((f a : S) : Qbar) = x := by
      change ((algebraMap S Qbar).comp f) a = x
      rw [hf, RingHom.comp_apply, ha]
      rfl
    exact heq ▸ (f a).2
  · right
    have heq : ((f a : S) : Qbar) = x⁻¹ := by
      change ((algebraMap S Qbar).comp f) a = x⁻¹
      rw [hf, RingHom.comp_apply, ha, map_inv₀]
      rfl
    exact heq ▸ (f a).2

end ZInQ.Contrib.FrobeniusDensity

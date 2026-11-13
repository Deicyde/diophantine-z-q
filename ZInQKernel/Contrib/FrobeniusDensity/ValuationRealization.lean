import ZInQKernel.Contrib.FrobeniusDensity.ValuationLift

/-!
# A compatible absolute arithmetic Frobenius at an actual valuation

This supplies the valuation-level output missing from the integral-only baseline
lift. The absolute automorphism is not chosen again after constructing the
valuation, so its finite restriction is preserved exactly.
-/

noncomputable section

namespace ZInQ.Contrib.FrobeniusDensity

open NumberField IsLocalRing
open scoped NumberField

/-- The actual valuation subring obtained by localizing the integral closure
of the integers at the specified prime. -/
def valuationOverIntegralPrime (P : Ideal Zbar) [P.IsPrime] (p : ℕ)
    (hp : p.Prime) (hPp : P.under ℤ = Ideal.span {(p : ℤ)}) : ValuationSubring Qbar :=
  ValuationSubring.ofSubring
    (Localization.subalgebra.ofField Qbar P.primeCompl P.primeCompl_le_nonZeroDivisors).toSubring
    (localization_integer_or_inverse P p hp hPp)

section PrimeLocalization

variable (P : Ideal Zbar) [P.IsPrime] (p : ℕ) (hp : p.Prime)
  (hPp : P.under ℤ = Ideal.span {(p : ℤ)})

local notation "V" => valuationOverIntegralPrime P p hp hPp

/-- The algebra structure is built at its actual dependent type, not by
identifying two unrelated local `let` variables. -/
instance integralPrimeAlgebra : Algebra Zbar V :=
  inferInstanceAs (Algebra Zbar
    (Localization.subalgebra.ofField Qbar P.primeCompl P.primeCompl_le_nonZeroDivisors))

instance integralPrimeScalarTower : IsScalarTower Zbar V Qbar :=
  inferInstanceAs (IsScalarTower Zbar
    (Localization.subalgebra.ofField Qbar P.primeCompl P.primeCompl_le_nonZeroDivisors) Qbar)

instance integralPrimeLocalization : IsLocalization.AtPrime V P :=
  inferInstanceAs (IsLocalization.AtPrime
    (Localization.subalgebra.ofField Qbar P.primeCompl P.primeCompl_le_nonZeroDivisors) P)

/-- The rational prime belongs to the maximal ideal of the actual valuation. -/
theorem liesOver_valuationOverIntegralPrime : LiesOver V p := by
  have hpP : (p : Zbar) ∈ P := by
    change algebraMap ℤ Zbar (p : ℤ) ∈ P
    rw [← Ideal.mem_comap]
    change (p : ℤ) ∈ P.under ℤ
    rw [hPp]
    exact Ideal.mem_span_singleton_self _
  have hmem := (IsLocalization.AtPrime.to_map_mem_maximal_iff V P (p : Zbar)).mpr hpP
  have hn := ValuationSubring.coe_mem_nonunits_iff.mpr hmem
  change (V).subtype (algebraMap Zbar V (p : Zbar)) ∈ (V).nonunits at hn
  rw [map_natCast, map_natCast] at hn
  exact hn

/-- Integral Frobenius congruences extend to every local fraction at the same
prime and force stabilization of the resulting valuation. -/
theorem isArithFrob_at_integralPrime (τ : GQ)
    (hh : ∀ x y : Zbar, (y : Qbar) = τ (x : Qbar) - (x : Qbar) ^ p → y ∈ P) :
    IsArithFrob τ V p := by
  have : Fact p.Prime := ⟨hp⟩
  let α : Zbar →ₐ[ℤ] Zbar := (galRestrict ℤ ℚ Qbar Zbar τ).toAlgHom
  have hα : α.IsArithFrobAt P := by
    intro x
    rw [hPp, GlueC10.card_quot p]
    apply hh x (α x - x ^ p)
    change algebraMap Zbar Qbar (α x) - (x : Qbar) ^ p = τ (x : Qbar) - (x : Qbar) ^ p
    have hco : algebraMap Zbar Qbar (α x) = τ (x : Qbar) :=
      algebraMap_galRestrict_apply (A := ℤ) (K := ℚ) (L := Qbar) (B := Zbar) τ x
    rw [hco]
  let e : Localization.AtPrime P ≃ₐ[Zbar] V :=
    IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) V
  have he : (V).subtype.comp (e.toRingHom.comp hα.localize.toRingHom) =
      τ.toRingHom.comp ((V).subtype.comp e.toRingHom) := by
    apply IsLocalization.ringHom_ext P.primeCompl
    ext a
    change (V).subtype (e (hα.localize (algebraMap Zbar (Localization.AtPrime P) a))) =
      τ ((V).subtype (e (algebraMap Zbar (Localization.AtPrime P) a)))
    rw [hα.localize_algebraMap, e.commutes, e.commutes]
    change algebraMap Zbar Qbar (α a) = τ (algebraMap Zbar Qbar a)
    exact algebraMap_galRestrict_apply (A := ℤ) (K := ℚ) (L := Qbar) (B := Zbar) τ a
  have hcard : Nat.card (ℤ ⧸ (maximalIdeal (Localization.AtPrime P)).under ℤ) = p := by
    rw [← Ideal.under_under (B := Zbar), Localization.AtPrime.under_maximalIdeal,
      hPp, GlueC10.card_quot p]
  apply (isArithFrob_iff_congruence hp.ne_zero).mpr
  intro x hx
  let a := e.symm ⟨x, hx⟩
  have ha : e a = ⟨x, hx⟩ := e.apply_symm_apply ⟨x, hx⟩
  have hloc := hα.isArithFrobAt_localize a
  change hα.localize a - a ^ Nat.card
    (ℤ ⧸ (maximalIdeal (Localization.AtPrime P)).under ℤ) ∈ maximalIdeal _ at hloc
  rw [hcard] at hloc
  have hmem : e (hα.localize a - a ^ p) ∈ maximalIdeal V := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hloc ⊢
    intro hu
    apply hloc
    have hunit := hu.map e.symm.toRingHom
    change IsUnit (e.symm (e (hα.localize a - a ^ p))) at hunit
    rwa [e.symm_apply_apply] at hunit
  have hgx : (V).subtype (e (hα.localize a)) = τ x := by
    have h := congrArg (fun f : Localization.AtPrime P →+* Qbar => f a) he
    change (V).subtype (e (hα.localize a)) = τ ((V).subtype (e a)) at h
    rwa [ha] at h
  have hval : (V).subtype (e (hα.localize a - a ^ p)) = τ x - x ^ p := by
    rw [map_sub, map_sub, map_pow, map_pow, hgx, ha]
    rfl
  have hn : (e (hα.localize a - a ^ p) : Qbar) ∈ (V).nonunits :=
    ValuationSubring.coe_mem_nonunits_iff.mpr hmem
  exact hval ▸ hn

end PrimeLocalization

/-- The valuation-level conversion keeps the given absolute automorphism. -/
theorem exists_valuation_of_integral_frobenius (τ : GQ) (p : ℕ) (hp : p.Prime)
    (P : Ideal Zbar) [P.IsPrime] (hPp : P.under ℤ = Ideal.span {(p : ℤ)})
    (hh : ∀ x y : Zbar, (y : Qbar) = τ (x : Qbar) - (x : Qbar) ^ p → y ∈ P) :
    ∃ v : ValuationSubring Qbar, LiesOver v p ∧ IsArithFrob τ v p :=
  ⟨valuationOverIntegralPrime P p hp hPp,
    liesOver_valuationOverIntegralPrime P p hp hPp,
    isArithFrob_at_integralPrime P p hp hPp τ hh⟩

/-- A finite unramified arithmetic Frobenius lifts to an absolute arithmetic
Frobenius at an actual valuation, with the same finite restriction.
This theorem uses only the closed baseline local lift, not Chebotarev. -/
theorem valuation_frobLift (E : IntermediateField ℚ Qbar) [FiniteDimensional ℚ E]
    [IsGalois ℚ E] (σ : E ≃ₐ[ℚ] E) (p : ℕ) (Q : Ideal (𝓞 E)) [Q.IsPrime]
    (hp : p.Prime) (hQp : Q.under ℤ = Ideal.span {(p : ℤ)})
    (hQu : Algebra.IsUnramifiedAt ℤ Q) (hσ : IsArithFrobAt ℤ σ Q) :
    ∃ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p ∧ IsArithFrob τ v p ∧ AlgEquiv.restrictNormal τ E = σ := by
  obtain ⟨τ, hτ, hres⟩ := GlueC10.frobLift E σ p Q hp hQp hQu hσ
  obtain ⟨P, hP, hPp, hh⟩ := hτ
  have : P.IsPrime := hP
  obtain ⟨v, hv, hf⟩ := exists_valuation_of_integral_frobenius τ p hp P hPp hh
  exact ⟨v, τ, hv, hf, hres⟩

end ZInQ.Contrib.FrobeniusDensity

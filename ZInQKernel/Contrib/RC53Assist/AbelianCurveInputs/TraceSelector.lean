import ZInQKernel.Contrib.RC53Assist.AbelianCurveInputs.ResidueNormalization
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Different.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# A residual trace selector for one place in a finite fiber

Chinese remainders on the integral closure of a discrete valuation ring isolate
one residue component. Its field trace has residue e times f.

Locators: Stichtenoth III.1–III.4; Mathlib integral trace and the residual
prime-component calculation in `ResidueNormalization.lean`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AbelianCurveInputs.TraceSelector

open Module TauCeti Polynomial IsLocalRing IsDedekindDomain
open scoped nonZeroDivisors

attribute [local instance 10] Place.algebraIntegersExtension Place.isScalarTowerIntegersExtension

/-- THEOREM. One place above a base place has a field element equal to one
modulo its maximal ideal, zero modulo the other maximal ideals in the fiber,
and field trace congruent to e times f modulo the base maximal ideal.
Locator: Stichtenoth III.2 and III.4; the finite normalization, Chinese
remainders, and `ResidueNormalization.primeComponent_intTrace`. -/
theorem exists_residual_trace_selector {k F F' : Type} [Field k] [Field F] [Field F']
    [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (P : Place k F') :
    ∃ b : F', P.valuation (b - 1) < 1 ∧
      (∀ P' : Place k F', P'.restrict k F = P.restrict k F → P' ≠ P →
        P'.valuation b < 1) ∧
      (P.restrict k F).valuation (Algebra.trace F F' b - algebraMap k F
        ((Place.ramificationIdx F P * Place.relativeDegree k F P : ℕ) : k)) < 1 := by
  let Q := P.restrict k F
  let A := Q.integers
  let B := integralClosure A F'
  haveI : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A F F' B
  haveI : IsFractionRing B F' := IsIntegralClosure.isFractionRing_of_finite_extension A F F' B
  haveI : Module.Finite A B := IsIntegralClosure.finite (A := A) (K := F) (L := F') B
  haveI : Module.IsTorsionFree A B := inferInstance
  haveI : IsScalarTower k A F' := .of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply A F F',
      ← IsScalarTower.algebraMap_apply k A F,
      ← IsScalarTower.algebraMap_apply k F F']
  letI : Algebra k B := ((algebraMap A B).comp (algebraMap k A)).toAlgebra
  haveI : IsScalarTower k A B := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k B F' := .of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k A F' c, IsScalarTower.algebraMap_apply A B F']
    rfl
  have hB : ∀ b : B, algebraMap B F' b ∈ P.integers :=
    P.algebraMap_mem_integers_of_mem_integralClosure k F
  let pp := P.center hB
  let p : Ideal A := maximalIdeal A
  have hp : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  haveI : pp.asIdeal.IsMaximal := pp.isPrime.isMaximal pp.ne_bot
  haveI : pp.asIdeal.LiesOver p := P.centerIntegralClosure_liesOver_maximalIdeal k F
  haveI : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B F F'
  have hpB : Ideal.map (algebraMap A B) p ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  obtain ⟨J, hcop, hfactor⟩ := Ideal.eq_prime_pow_mul_coprime hpB pp.asIdeal
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count p pp.asIdeal hpB]
    at hfactor
  let e := pp.asIdeal.ramificationIdx A
  have he0 : e ≠ 0 := (Ideal.ramificationIdx_pos A pp.asIdeal).ne'
  have hcop' : IsCoprime (pp.asIdeal ^ e) J :=
    (Ideal.isCoprime_iff_sup_eq.mpr hcop).pow_left
  have hfactor' : pp.asIdeal ^ e * J = Ideal.map (algebraMap A B) p := hfactor.symm
  obtain ⟨b, hbP, hbJ⟩ := ResidueNormalization.exists_primeComponent pp.asIdeal J e hcop'
  have hbP' : b - 1 ∈ pp.asIdeal := Ideal.pow_le_self he0 hbP
  have htr := ResidueNormalization.primeComponent_intTrace hp pp.asIdeal J e hcop'
    hfactor' b hbJ hbP'
  have hf : Module.finrank (A ⧸ p) (B ⧸ pp.asIdeal) =
      Place.relativeDegree k F P := by
    rw [← Ideal.inertiaDeg_eq_of_isMaximal p pp.asIdeal]
    exact (P.relativeDegree_eq_inertiaDeg_center (R := A) k F hB).symm
  have he : e = Place.ramificationIdx F P :=
    (P.ramificationIdx_eq_ramificationIdx_center (R := A) k F hB).symm
  rw [hf] at htr
  have htrmem : Algebra.intTrace A B b -
      (e * Place.relativeDegree k F P : ℕ) ∈ p := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_natCast, htr, Nat.cast_mul, sub_self]
  have hmaptr : algebraMap A F (Algebra.intTrace A B b) =
      Algebra.trace F F' (algebraMap B F' b) := Algebra.algebraMap_intTrace (K := F) (L := F') b
  refine ⟨algebraMap B F' b, ?_, ?_, ?_⟩
  · have h := (P.mem_center_asIdeal hB).mp hbP'
    simpa only [map_sub, map_one] using h
  · intro P' hres hne
    have hB' : ∀ z : B, algebraMap B F' z ∈ P'.integers := by
      intro z
      apply P'.mem_integers_of_isIntegral (R := A) (fun a => ?_) z.2
      rw [IsScalarTower.algebraMap_apply A F F', ← Place.mem_integers_restrict_iff k F,
        hres]
      exact a.2
    let pp' := P'.center hB'
    haveI : pp'.asIdeal.IsPrime := pp'.isPrime
    have hppne : pp'.asIdeal ≠ pp.asIdeal := by
      intro hsame
      exact hne (P'.center_injective hB' hB (HeightOneSpectrum.ext hsame))
    have hbase : ((P'.restrict k F).center
        (Place.algebraMap_mem_integers_restrict (R := A) k F P' hB')).asIdeal = p := by
      ext a
      rw [Place.mem_center_asIdeal]
      change (P'.restrict k F).valuation (a : F) < 1 ↔ a ∈ p
      rw [hres]
      exact (Q.mem_maximalIdeal_iff_valuation_lt_one).symm
    have hlies := P'.center_liesOver (R := A) k F hB'
    rw [hbase] at hlies
    have hmaple : Ideal.map (algebraMap A B) p ≤ pp'.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      change p ≤ pp'.asIdeal.under A
      rw [hlies.over]
    have hbpp' := ResidueNormalization.primeComponent_mem_otherPrime pp.asIdeal J pp'.asIdeal
      hppne e hfactor' hmaple hbJ
    exact (P'.mem_center_asIdeal hB').mp hbpp'
  · have h := (Q.mem_maximalIdeal_iff_valuation_lt_one).mp htrmem
    change Q.valuation (algebraMap A F (Algebra.intTrace A B b -
      (e * Place.relativeDegree k F P : ℕ))) < 1 at h
    rw [map_sub, hmaptr, map_natCast, he] at h
    simpa only [map_natCast] using h

end ZInQ.Contrib.RC53Assist.AbelianCurveInputs.TraceSelector

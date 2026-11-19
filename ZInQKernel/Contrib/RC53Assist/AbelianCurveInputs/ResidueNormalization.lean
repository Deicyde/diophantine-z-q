import ZInQKernel.Contrib.RC53Assist.AbelianCurveInputs.LocalFacts
import ZInQKernel.Contrib.RC53Assist.AbelianCurveInputs.LogarithmicNorm
import ZInQKernel.Contrib.TauCeti.RingTheory.Trace.QuotientPow
import Mathlib.RingTheory.Trace.Quotient

/-!
# Local logarithmic residues and residual trace components

The residue of a logarithmic differential is its local order times the residue
of a uniformizer logarithm. The integral trace of a residual prime component is
its ramification index times its residue degree. These are local steps toward
the normalization of the Kähler–Weil comparison.

Locators: Stichtenoth, *Algebraic Function Fields and Codes*, second edition,
Sections I.7 and III.4; Mathlib `Algebra.trace_quotient_eq_of_isDedekindDomain`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AbelianCurveInputs.ResidueNormalization

open Module TauCeti Polynomial KaehlerDifferential IsLocalRing
open scoped IntermediateField nonZeroDivisors

attribute [local instance] Ideal.Quotient.field

/-- THEOREM. The integral trace of an element supported on one residual prime
component and congruent to one there is e times the residue degree.
Locator: Mathlib `Algebra.trace_quotient_eq_of_isDedekindDomain`;
Tau Ceti `Algebra.trace_quotient_pow_mk`. -/
theorem primeComponent_intTrace {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]
    {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥)
    (P Q : Ideal B) [P.IsMaximal] [P.LiesOver p] (e : ℕ)
    (hPQ : IsCoprime (P ^ e) Q) (hmul : P ^ e * Q = Ideal.map (algebraMap A B) p)
    (b : B) (hbQ : b ∈ Q) (hbP : b - 1 ∈ P) :
    Ideal.Quotient.mk p (Algebra.intTrace A B b) =
      (e : A ⧸ p) * (Module.finrank (A ⧸ p) (B ⧸ P) : A ⧸ p) := by
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  have hQle : p ≤ Ideal.comap (algebraMap A B) Q := by
    rw [← Ideal.map_le_iff_le_comap, ← hmul]
    exact Ideal.mul_le_right
  have hPle : p ≤ Ideal.comap (algebraMap A B) (P ^ e) := by
    rw [← Ideal.map_le_iff_le_comap, ← hmul]
    exact Ideal.mul_le_left
  letI : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap hQle
  haveI : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  letI : Algebra (A ⧸ p) (B ⧸ P ^ e) := Ideal.Quotient.algebraQuotientOfLEComap hPle
  haveI : IsScalarTower A (A ⧸ p) (B ⧸ P ^ e) := .of_algebraMap_eq' rfl
  haveI : Module.Finite (A ⧸ p) (B ⧸ Q) := .of_restrictScalars_finite A _ _
  haveI : Module.Finite (A ⧸ p) (B ⧸ P ^ e) := .of_restrictScalars_finite A _ _
  haveI : Module.Finite (A ⧸ p) (B ⧸ P) := .of_restrictScalars_finite A _ _
  let ee : (B ⧸ Ideal.map (algebraMap A B) p) ≃ₐ[A ⧸ p] ((B ⧸ P ^ e) × B ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hmul.symm).trans
        (Ideal.quotientMulEquivQuotientProd (P ^ e) Q hPQ)
      commutes' := Quotient.ind fun _ => rfl }
  have hb₁ : (ee (Ideal.Quotient.mk _ b)).1 = Ideal.Quotient.mk (P ^ e) b := by simp [ee]
  have hb₂ : (ee (Ideal.Quotient.mk _ b)).2 = 0 := by
    simpa [ee, Ideal.Quotient.eq_zero_iff_mem] using hbQ
  have hb₃ : Ideal.Quotient.mk P b = 1 := by
    apply sub_eq_zero.mp
    rw [← map_one (Ideal.Quotient.mk P), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hbP
  rw [← Algebra.trace_quotient_eq_of_isDedekindDomain, ← Algebra.trace_eq_of_algEquiv ee,
    Algebra.trace_prod_apply, hb₁, hb₂, map_zero, add_zero,
    Algebra.trace_quotient_pow_mk hPbot e b, hb₃,
    ← map_one (algebraMap (A ⧸ p) (B ⧸ P)), Algebra.trace_algebraMap]
  simp only [nsmul_eq_mul, mul_one]

/-- THEOREM. A Chinese remainder idempotent can be lifted to one on the chosen
prime-power component and zero on its coprime complement.
Locator: Mathlib `Ideal.quotientMulEquivQuotientProd`. -/
theorem exists_primeComponent {B : Type*} [CommRing B] (P Q : Ideal B) (e : ℕ)
    (hPQ : IsCoprime (P ^ e) Q) :
    ∃ b : B, b - 1 ∈ P ^ e ∧ b ∈ Q := by
  let ee := Ideal.quotientMulEquivQuotientProd (P ^ e) Q hPQ
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (ee.symm (1, 0))
  have h := congrArg ee hb
  rw [RingEquiv.apply_symm_apply] at h
  refine ⟨b, ?_, ?_⟩
  · have h₁ : Ideal.Quotient.mk (P ^ e) b = 1 := by
      simpa [ee] using congrArg Prod.fst h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_one, h₁, sub_self]
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa [ee] using congrArg Prod.snd h

/-- THEOREM. The local logarithmic residue of a nonzero function is its order
times the logarithmic residue of a uniformizer, for every specified comparison.
Locator: the universal Kähler Leibniz rule; the proved local uniformizer basis
and normalized order-zero statement in `LocalFacts.lean`. -/
theorem logarithmicResidue_eq_order_mul {k F : Type} [Field k] [Field F] [Algebra k F]
    [CharZero k] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    {x : F} (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (P : Place k F) {t s : F} (ht : P.valuation.IsUniformizer t) (hs : s ≠ 0) :
    letI := weilDifferentialSpaceModule hF
    repartitionDualComponent (comparison hF hex hx (D k F s) :
      Module.Dual k ↥(repartitionSpace k F)) P s⁻¹ =
      (P.ord s : k) * repartitionDualComponent (comparison hF hex hx (D k F t) :
        Module.Dual k ↥(repartitionSpace k F)) P t⁻¹ := by
  letI := weilDifferentialSpaceModule hF
  have httr := uniformizer_transcendental P ht
  haveI := hF.finiteDimensional_adjoin httr
  have ht0 : t ≠ 0 := ht.ne_zero
  let n : ℤ := P.ord s
  let u : F := s / t ^ n
  have hu0 : u ≠ 0 := div_ne_zero hs (zpow_ne_zero n ht0)
  have hordu : P.ord u = 0 := by
    rw [P.ord_div hs (zpow_ne_zero n ht0), P.ord_zpow,
      P.isUniformizer_iff_ord_eq_one.mp ht, mul_one, sub_self]
  have humem : u ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by rw [hordu])
  have huinv : u⁻¹ ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr
    (by rw [P.ord_inv, hordu, neg_zero])
  let d := derivativeOfSeparating httr
  have hdt : d t = 1 := derivativeOfSeparating_self httr
  have hdu : d u ∈ P.integers :=
    LocalFacts.uniformizer_derivative_integral hF P ht ⟨u, humem⟩
  have hfrac : d u / u ∈ P.integers := by
    rw [div_eq_mul_inv]
    exact mul_mem hdu huinv
  have hsu : s = t ^ n * u := by
    dsimp only [u]
    field_simp
  have hdlog : d s / s = (n : F) * t⁻¹ + d u / u := by
    conv_lhs => rw [hsu]
    rw [d.leibniz, d.leibniz_zpow, hdt]
    simp only [smul_eq_mul, zsmul_eq_mul, mul_one]
    rw [zpow_sub₀ ht0, zpow_one]
    field_simp
    ring
  let ω := comparison hF hex hx (D k F t)
  have hω0 : (ω : Module.Dual k ↥(repartitionSpace k F)) ≠ 0 :=
    comparison_uniformizer_ne_zero hF hex hx P ht
  have hreg : RegularAt P ω :=
    (regularAt_iff_order_nonneg hF hex P ω hω0).mpr
      (by rw [LocalFacts.uniformizerResidueOrder k F hF hex x hx P t ht])
  rw [← derivativeOfSeparating_smul_D httr s, map_smul,
    coe_weilDifferentialSpaceModule_smul,
    repartitionDualComponent_repartitionDualMul, ← div_eq_mul_inv, hdlog, map_add,
    hreg _ hfrac, add_zero]
  have hn : (n : F) = algebraMap k F (n : k) := by simp
  rw [hn, ← Algebra.smul_def, map_smul, smul_eq_mul]

/-- THEOREM. A local linear functional annihilating the valuation ring evaluates
the logarithmic uniformizer-coordinate derivative as order times its value on
the inverse uniformizer. Locator: Stichtenoth I.7, the logarithmic residue rule;
`LocalFacts.uniformizer_derivative_integral`. -/
theorem logarithmicFunctional_eq_order_mul {k F : Type} [Field k] [Field F] [Algebra k F]
    [CharZero k] (hF : IsFunctionField k F) (P : Place k F) {t s : F}
    (ht : P.valuation.IsUniformizer t) (hs : s ≠ 0) (ell : Module.Dual k F)
    (hell : ∀ a : F, a ∈ P.integers → ell a = 0) :
    let httr := uniformizer_transcendental P ht
    letI := hF.finiteDimensional_adjoin httr
    ell (derivativeOfSeparating httr s / s) = (P.ord s : k) * ell t⁻¹ := by
  have httr := uniformizer_transcendental P ht
  haveI := hF.finiteDimensional_adjoin httr
  have ht0 : t ≠ 0 := ht.ne_zero
  let n : ℤ := P.ord s
  let u : F := s / t ^ n
  have hu0 : u ≠ 0 := div_ne_zero hs (zpow_ne_zero n ht0)
  have hordu : P.ord u = 0 := by
    rw [P.ord_div hs (zpow_ne_zero n ht0), P.ord_zpow,
      P.isUniformizer_iff_ord_eq_one.mp ht, mul_one, sub_self]
  have humem : u ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by rw [hordu])
  have huinv : u⁻¹ ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr
    (by rw [P.ord_inv, hordu, neg_zero])
  let d := derivativeOfSeparating httr
  have hdt : d t = 1 := derivativeOfSeparating_self httr
  have hdu : d u ∈ P.integers :=
    LocalFacts.uniformizer_derivative_integral hF P ht ⟨u, humem⟩
  have hfrac : d u / u ∈ P.integers := by
    rw [div_eq_mul_inv]
    exact mul_mem hdu huinv
  have hsu : s = t ^ n * u := by
    dsimp only [u]
    field_simp
  have hdlog : d s / s = (n : F) * t⁻¹ + d u / u := by
    conv_lhs => rw [hsu]
    rw [d.leibniz, d.leibniz_zpow, hdt]
    simp only [smul_eq_mul, zsmul_eq_mul, mul_one]
    rw [zpow_sub₀ ht0, zpow_one]
    field_simp
    ring
  dsimp only
  change ell (d s / s) = (n : k) * ell t⁻¹
  rw [hdlog, map_add, hell _ hfrac, add_zero]
  have hn : (n : F) = algebraMap k F (n : k) := by simp
  rw [hn, ← Algebra.smul_def, map_smul, smul_eq_mul]

/-- THEOREM. A lift supported on one coprime prime-power component lies in every
other prime above the same base ideal.
Locator: the prime-ideal product criterion and Chinese remainder decomposition. -/
theorem primeComponent_mem_otherPrime {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {p : Ideal A} (P Q R : Ideal B) [P.IsMaximal] [R.IsPrime] (hRP : R ≠ P)
    (e : ℕ) (hmul : P ^ e * Q = Ideal.map (algebraMap A B) p)
    (hR : Ideal.map (algebraMap A B) p ≤ R) {b : B} (hb : b ∈ Q) : b ∈ R := by
  have hnot : ¬ P ≤ R := by
    intro hle
    have heq : P = R := Ideal.IsMaximal.eq_of_le
      (inferInstance : P.IsMaximal) (Ideal.IsPrime.ne_top' (I := R)) hle
    exact hRP heq.symm
  obtain ⟨a, haP, haR⟩ := SetLike.not_le_iff_exists.mp hnot
  have hamul : a ^ e * b ∈ R := hR (hmul ▸ Ideal.mul_mem_mul
    (Ideal.pow_mem_pow haP e) hb)
  rcases Ideal.IsPrime.mem_or_mem (inferInstance : R.IsPrime) hamul with hpow | hbR
  · exact False.elim (haR (Ideal.IsPrime.mem_of_pow_mem (inferInstance : R.IsPrime) e hpow))
  · exact hbR

/-- THEOREM. Dividing an element of the maximal ideal by a uniformizer is
integral. Locator: the defining valuation of a uniformizer in a discrete
valuation ring. -/
theorem div_uniformizer_integral {k F : Type} [Field k] [Field F] [Algebra k F]
    (P : Place k F) {t z : F} (ht : P.valuation.IsUniformizer t)
    (hz : P.valuation z < 1) : z / t ∈ P.integers := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  have hpos : 0 < P.ord z := by
    rw [P.valuation_eq_exp_neg_ord hz0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hz
    omega
  apply P.mem_integers_iff_ord_nonneg.mpr
  rw [P.ord_div hz0 ht.ne_zero, P.isUniformizer_iff_ord_eq_one.mp ht]
  omega

/-- THEOREM. A comparison logarithmic differential annihilates a local maximal
ideal. This uses the actual valuation-ring lattice and does not use parameter
independence. Locator: Stichtenoth I.7; the local logarithmic functional rule. -/
theorem logarithmicComparison_kills_maximal {k F : Type} [Field k] [Field F] [Algebra k F]
    [CharZero k] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    {x : F} (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (P : Place k F) {s z : F} (hs : s ≠ 0) (hz : P.valuation z < 1) :
    letI := weilDifferentialSpaceModule hF
    repartitionDualComponent (comparison hF hex hx (D k F s) :
      Module.Dual k ↥(repartitionSpace k F)) P (s⁻¹ * z) = 0 := by
  letI := weilDifferentialSpaceModule hF
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  have httr := uniformizer_transcendental P ht
  haveI := hF.finiteDimensional_adjoin httr
  let dt := derivativeOfSeparating httr
  let ω := comparison hF hex hx (D k F t)
  have hω0 : (ω : Module.Dual k ↥(repartitionSpace k F)) ≠ 0 :=
    comparison_uniformizer_ne_zero hF hex hx P ht
  have hreg : RegularAt P ω :=
    (regularAt_iff_order_nonneg hF hex P ω hω0).mpr
      (by rw [LocalFacts.uniformizerResidueOrder k F hF hex x hx P t ht])
  have hzmem : z ∈ P.integers := P.mem_integers_iff.mpr hz.le
  let ell : Module.Dual k F := (repartitionDualComponent
    (ω : Module.Dual k ↥(repartitionSpace k F)) P).comp (LinearMap.mulLeft k z)
  have hell : ∀ a : F, a ∈ P.integers → ell a = 0 :=
    fun a ha => hreg (z * a) (mul_mem hzmem ha)
  have hellt : ell t⁻¹ = 0 := by
    change repartitionDualComponent (ω : Module.Dual k ↥(repartitionSpace k F)) P
      (z * t⁻¹) = 0
    rw [← div_eq_mul_inv]
    exact hreg _ (div_uniformizer_integral P ht hz)
  have h := logarithmicFunctional_eq_order_mul hF P ht hs ell hell
  change ell (dt s / s) = (P.ord s : k) * ell t⁻¹ at h
  rw [hellt, mul_zero] at h
  rw [← derivativeOfSeparating_smul_D httr s, map_smul,
    coe_weilDifferentialSpaceModule_smul, repartitionDualComponent_repartitionDualMul]
  change repartitionDualComponent (ω : Module.Dual k ↥(repartitionSpace k F)) P
    (dt s * (s⁻¹ * z)) = 0
  have heq : dt s * (s⁻¹ * z) = z * (dt s / s) := by
    rw [div_eq_mul_inv]
    ring
  rw [heq]
  exact h

end ZInQ.Contrib.RC53Assist.AbelianCurveInputs.ResidueNormalization

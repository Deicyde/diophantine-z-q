import ZInQKernel.Contrib.RC53Assist.AbelianCurveInputs.ResidueNormalization
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic

/-!
# Logarithmic residues on the rational function field

The rational differential with divisor -2 at infinity and value -1 on X inverse
has logarithmic residue equal to the local order times the place degree.

Locators: Stichtenoth, *Algebraic Function Fields and Codes*, second edition,
Sections I.2 and I.7, including the abstract residue theorem.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AbelianCurveInputs.RationalResidues

open Module TauCeti Polynomial KaehlerDifferential TauCeti.AlgebraicGeometry
open scoped IntermediateField WithZero

/-- THEOREM. At infinity the normalized rational Weil differential evaluates a
logarithmic derivative as its order, since the place degree is one.
Locator: Stichtenoth I.7; the local logarithmic functional identity in
`ResidueNormalization.lean` and the normalization on X inverse. -/
theorem logarithmicResidue_infty {k : Type} [Field k] [CharZero k]
    (ω : Module.Dual k ↥(repartitionSpace k (RatFunc k)))
    (hD : ω ∈ weilDifferentialFiltration
      ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k)))
    (hN : repartitionDualComponent ω (Place.infty k) (RatFunc.X : RatFunc k)⁻¹ = -1)
    {f : RatFunc k} (hf : f ≠ 0) :
    letI := (IsFunctionField.ratFunc k).finiteDimensional_adjoin
      (RatFunc.transcendental_X (K := k))
    repartitionDualComponent ω (Place.infty k)
      (derivativeOfSeparating (RatFunc.transcendental_X (K := k)) f / f) =
        ((Place.infty k).ord f : k) := by
  haveI := (IsFunctionField.ratFunc k).finiteDimensional_adjoin
    (RatFunc.transcendental_X (K := k))
  let P := Place.infty k
  let t : RatFunc k := (RatFunc.X : RatFunc k)⁻¹
  have ht : P.valuation.IsUniformizer t := Place.isUniformizer_infty
  have ht0 : t ≠ 0 := ht.ne_zero
  have httr := uniformizer_transcendental P ht
  haveI := (IsFunctionField.ratFunc k).finiteDimensional_adjoin httr
  let dX := derivativeOfSeparating (RatFunc.transcendental_X (K := k))
  let dt := derivativeOfSeparating httr
  let c : RatFunc k := -t ^ 2
  let ell : Module.Dual k (RatFunc k) :=
    (repartitionDualComponent ω P).comp (LinearMap.mulLeft k c)
  have hc0 : c ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 ht0)
  have hvc : P.valuation c = WithZero.exp (-2 : ℤ) := by
    rw [P.valuation_eq_exp_neg_ord hc0]
    change WithZero.exp (-P.ord (-t ^ 2)) = _
    rw [P.ord_neg, P.ord_pow, P.isUniformizer_iff_ord_eq_one.mp ht]
    norm_num
  have hell : ∀ a : RatFunc k, a ∈ P.integers → ell a = 0 := by
    intro a ha
    change repartitionDualComponent ω P (c * a) = 0
    apply repartitionDualComponent_apply_eq_zero_of_le hD P
    rw [WeilDivisor.coeff_zsmul]
    change P.valuation (c * a) ≤ WithZero.exp
      ((-2 : ℤ) * (WeilDivisor.ofPoint P).coeff P)
    rw [WeilDivisor.coeff_ofPoint_self, mul_one, map_mul, hvc]
    have ha' : P.valuation a ≤ 1 := P.mem_integers_iff.mp ha
    calc
      WithZero.exp (-2 : ℤ) * P.valuation a ≤ WithZero.exp (-2 : ℤ) * 1 := by gcongr
      _ = WithZero.exp (-2 : ℤ) := mul_one _
  have hellt : ell t⁻¹ = 1 := by
    change repartitionDualComponent ω P (c * t⁻¹) = 1
    have heq : c * t⁻¹ = -t := by
      dsimp only [c]
      field_simp
    rw [heq, map_neg]
    change -repartitionDualComponent ω (Place.infty k) (RatFunc.X : RatFunc k)⁻¹ = 1
    rw [hN]
    ring
  have hdXt : dX t = c := by
    change dX (RatFunc.X : RatFunc k)⁻¹ = -(RatFunc.X : RatFunc k)⁻¹ ^ 2
    rw [dX.leibniz_inv, derivativeOfSeparating_self, smul_eq_mul, mul_one]
  have hchain : dX f = c * dt f := by
    have h := dX.apply_eq_derivativeOfSeparating_smul httr f
    change dX f = dt f * dX t at h
    rw [hdXt] at h
    exact h.trans (mul_comm _ _)
  have h := ResidueNormalization.logarithmicFunctional_eq_order_mul
    (IsFunctionField.ratFunc k) P ht hf ell hell
  change ell (dt f / f) = (P.ord f : k) * ell t⁻¹ at h
  rw [hellt, mul_one] at h
  change repartitionDualComponent ω P (dX f / f) = (P.ord f : k)
  rw [hchain]
  change repartitionDualComponent ω P (c * dt f / f) = _
  rw [mul_div_assoc]
  exact h

/-- THEOREM. The separating derivation at X differentiates the polynomial
subring coefficientwise. Locator: the Kähler polynomial Leibniz rule,
`Derivation.map_aeval`. -/
theorem derivative_polynomial {k : Type} [Field k] [CharZero k] (q : k[X]) :
    letI := (IsFunctionField.ratFunc k).finiteDimensional_adjoin
      (RatFunc.transcendental_X (K := k))
    derivativeOfSeparating (RatFunc.transcendental_X (K := k))
      (algebraMap k[X] (RatFunc k) q) = algebraMap k[X] (RatFunc k) q.derivative := by
  haveI := (IsFunctionField.ratFunc k).finiteDimensional_adjoin
    (RatFunc.transcendental_X (K := k))
  let dX := derivativeOfSeparating (RatFunc.transcendental_X (K := k))
  have heval : aeval (RatFunc.X : RatFunc k) =
      IsScalarTower.toAlgHom k k[X] (RatFunc k) := by
    ext
    simp only [aeval_X, IsScalarTower.coe_toAlgHom', RatFunc.algebraMap_X]
  have h := dX.map_aeval q (RatFunc.X : RatFunc k)
  rw [heval] at h
  change dX (algebraMap k[X] (RatFunc k) q) =
    algebraMap k[X] (RatFunc k) q.derivative • dX (RatFunc.X : RatFunc k) at h
  have hself : dX (RatFunc.X : RatFunc k) = 1 :=
    derivativeOfSeparating_self (RatFunc.transcendental_X (K := k))
  rw [hself, smul_eq_mul, mul_one] at h
  exact h

/-- THEOREM. The normalized rational differential has logarithmic residue equal
to degree at the finite place of an irreducible polynomial.
Locator: Stichtenoth I.2 and I.7; the abstract residue theorem and the computed
logarithmic residue at infinity. -/
theorem logarithmicResidue_irreducible {k : Type} [Field k] [CharZero k]
    (ω : Module.Dual k ↥(repartitionSpace k (RatFunc k)))
    (hD : ω ∈ weilDifferentialFiltration
      ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k)))
    (hN : repartitionDualComponent ω (Place.infty k) (RatFunc.X : RatFunc k)⁻¹ = -1)
    {q : k[X]} (hq : Irreducible q) :
    letI := (IsFunctionField.ratFunc k).finiteDimensional_adjoin
      (RatFunc.transcendental_X (K := k))
    repartitionDualComponent ω (Place.adicOfIrreducible hq)
      (derivativeOfSeparating (RatFunc.transcendental_X (K := k))
        (algebraMap k[X] (RatFunc k) q) / algebraMap k[X] (RatFunc k) q) =
      ((Place.adicOfIrreducible hq).degree : k) := by
  haveI := (IsFunctionField.ratFunc k).finiteDimensional_adjoin
    (RatFunc.transcendental_X (K := k))
  classical
  let Q := Place.adicOfIrreducible hq
  let qF : RatFunc k := algebraMap k[X] (RatFunc k) q
  let dX := derivativeOfSeparating (RatFunc.transcendental_X (K := k))
  let v : RatFunc k := dX qF / qF
  have hqF : qF ≠ 0 :=
    (map_ne_zero_iff (algebraMap k[X] (RatFunc k))
      (IsFractionRing.injective k[X] (RatFunc k))).mpr hq.ne_zero
  have hQinf : Q ≠ Place.infty k := Place.adicOfIrreducible_ne_infty hq
  have houtside (P : Place k (RatFunc k)) (hPQ : P ≠ Q) (hPinf : P ≠ Place.infty k) :
      repartitionDualComponent ω P v = 0 := by
    obtain ⟨p, rfl⟩ := (P.eq_infty_or_exists_eq_ofPrime).resolve_left hPinf
    have hR := Place.algebraMap_mem_integers_ofPrime k (RatFunc k) p
    have hqnot : q ∉ p.asIdeal := by
      intro hqmem
      let p₀ := IsDedekindDomain.HeightOneSpectrum.ofIrreducible hq
      haveI : p₀.asIdeal.IsMaximal := p₀.isPrime.isMaximal p₀.ne_bot
      have hle : p₀.asIdeal ≤ p.asIdeal := by
        rw [IsDedekindDomain.HeightOneSpectrum.ofIrreducible_asIdeal hq]
        exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hqmem)
      have heq : p₀.asIdeal = p.asIdeal :=
        Ideal.IsMaximal.eq_of_le (inferInstance : p₀.asIdeal.IsMaximal) p.isPrime.ne_top hle
      have heqp : p₀ = p := IsDedekindDomain.HeightOneSpectrum.ext heq
      apply hPQ
      change Place.ofPrime k (RatFunc k) p = Place.ofPrime k (RatFunc k) p₀
      rw [heqp]
    have hord : (Place.ofPrime k (RatFunc k) p).ord qF = 0 := by
      have hnonneg := (Place.ofPrime k (RatFunc k) p).mem_integers_iff_ord_nonneg.mp (hR q)
      change 0 ≤ (Place.ofPrime k (RatFunc k) p).ord qF at hnonneg
      have hcenter := (Place.ofPrime k (RatFunc k) p).mem_center_asIdeal_iff_ord_pos hR hq.ne_zero
      rw [Place.center_ofPrime] at hcenter
      have hnotpos : ¬ 0 < (Place.ofPrime k (RatFunc k) p).ord qF := by
        exact fun hpos => hqnot (hcenter.mpr hpos)
      omega
    have hinv : qF⁻¹ ∈ (Place.ofPrime k (RatFunc k) p).integers :=
      (Place.ofPrime k (RatFunc k) p).mem_integers_iff_ord_nonneg.mpr
        (by rw [Place.ord_inv, hord, neg_zero])
    have hv : v ∈ (Place.ofPrime k (RatFunc k) p).integers := by
      change dX qF / qF ∈ _
      rw [derivative_polynomial, div_eq_mul_inv]
      exact mul_mem (hR q.derivative) hinv
    apply repartitionDualComponent_apply_eq_zero_of_le hD
    rw [WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_of_ne hPinf, mul_zero,
      WithZero.exp_zero]
    exact (Place.ofPrime k (RatFunc k) p).mem_integers_iff.mp hv
  have hinfty : repartitionDualComponent ω (Place.infty k) v = -(q.natDegree : k) := by
    have h := logarithmicResidue_infty ω hD hN hqF
    simpa only [qF, Place.ord_infty, RatFunc.intDegree_polynomial, Int.cast_neg,
      Int.cast_natCast] using h
  have hsum := finsum_repartitionDualComponent_eq_zero (IsFunctionField.ratFunc k)
    (weilDifferentialFiltration_le_weilDifferentialSpace _ hD) v
  have hsupp : Function.support (fun P : Place k (RatFunc k) =>
      repartitionDualComponent ω P v) ⊆ ({Q, Place.infty k} : Finset (Place k (RatFunc k))) := by
    apply Function.support_subset_iff'.mpr
    intro P hP
    apply houtside P
    · intro heq
      exact hP (by simp [heq])
    · intro heq
      exact hP (by simp [heq])
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_pair hQinf, hinfty,
    ← sub_eq_add_neg, sub_eq_zero] at hsum
  change repartitionDualComponent ω Q v = _
  rw [Place.degree_adicOfIrreducible]
  exact hsum

/-- THEOREM. Every local logarithmic residue of the normalized rational Weil
differential is the order times the place degree.
Locator: Stichtenoth I.2 and I.7; classification of rational-function places,
`logarithmicResidue_infty`, and `logarithmicResidue_irreducible`. -/
theorem logarithmicResidue_eq_order_mul_degree {k : Type} [Field k] [CharZero k]
    (ω : Module.Dual k ↥(repartitionSpace k (RatFunc k)))
    (hD : ω ∈ weilDifferentialFiltration
      ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k)))
    (hN : repartitionDualComponent ω (Place.infty k) (RatFunc.X : RatFunc k)⁻¹ = -1)
    (P : Place k (RatFunc k)) {f : RatFunc k} (hf : f ≠ 0) :
    letI := (IsFunctionField.ratFunc k).finiteDimensional_adjoin
      (RatFunc.transcendental_X (K := k))
    repartitionDualComponent ω P
      (derivativeOfSeparating (RatFunc.transcendental_X (K := k)) f / f) =
        (P.ord f : k) * (P.degree : k) := by
  haveI := (IsFunctionField.ratFunc k).finiteDimensional_adjoin
    (RatFunc.transcendental_X (K := k))
  rcases P.eq_infty_or_exists_eq_adicOfIrreducible with rfl | ⟨q, hq, rfl⟩
  · simpa only [Place.degree_infty, Nat.cast_one, mul_one] using
      logarithmicResidue_infty ω hD hN hf
  let Q := Place.adicOfIrreducible hq
  let t : RatFunc k := algebraMap k[X] (RatFunc k) q
  have ht : Q.valuation.IsUniformizer t := Place.isUniformizer_adicOfIrreducible hq
  have httr := uniformizer_transcendental Q ht
  haveI := (IsFunctionField.ratFunc k).finiteDimensional_adjoin httr
  let dX := derivativeOfSeparating (RatFunc.transcendental_X (K := k))
  let dt := derivativeOfSeparating httr
  let c : RatFunc k := algebraMap k[X] (RatFunc k) q.derivative
  let ell : Module.Dual k (RatFunc k) :=
    (repartitionDualComponent ω Q).comp (LinearMap.mulLeft k c)
  have hc : c ∈ Q.integers :=
    Place.algebraMap_mem_integers_ofPrime k (RatFunc k)
      (IsDedekindDomain.HeightOneSpectrum.ofIrreducible hq) q.derivative
  have hell : ∀ a : RatFunc k, a ∈ Q.integers → ell a = 0 := by
    intro a ha
    change repartitionDualComponent ω Q (c * a) = 0
    apply repartitionDualComponent_apply_eq_zero_of_le hD Q
    rw [WeilDivisor.coeff_zsmul,
      WeilDivisor.coeff_ofPoint_of_ne (Place.adicOfIrreducible_ne_infty hq), mul_zero,
      WithZero.exp_zero]
    exact Q.mem_integers_iff.mp (mul_mem hc ha)
  have hdXt : dX t = c := derivative_polynomial q
  have hellt : ell t⁻¹ = (Q.degree : k) := by
    have h := logarithmicResidue_irreducible ω hD hN hq
    change repartitionDualComponent ω Q (dX t / t) = (Q.degree : k) at h
    rw [hdXt, div_eq_mul_inv] at h
    exact h
  have hchain : dX f = c * dt f := by
    have h := dX.apply_eq_derivativeOfSeparating_smul httr f
    change dX f = dt f * dX t at h
    rw [hdXt] at h
    exact h.trans (mul_comm _ _)
  have h := ResidueNormalization.logarithmicFunctional_eq_order_mul
    (IsFunctionField.ratFunc k) Q ht hf ell hell
  change ell (dt f / f) = (Q.ord f : k) * ell t⁻¹ at h
  rw [hellt] at h
  change repartitionDualComponent ω Q (dX f / f) = _
  rw [hchain, mul_div_assoc]
  exact h

/-- THEOREM. A rational-function place has a uniformizer whose normalized
logarithmic residue is its degree and whose logarithmic form kills the maximal
ideal. Locator: Stichtenoth I.2 and I.7, local parameters and logarithmic residues. -/
theorem exists_uniformizer_residue_data {k : Type} [Field k] [CharZero k]
    (ω : Module.Dual k ↥(repartitionSpace k (RatFunc k)))
    (hD : ω ∈ weilDifferentialFiltration
      ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k)))
    (hN : repartitionDualComponent ω (Place.infty k) (RatFunc.X : RatFunc k)⁻¹ = -1)
    (P : Place k (RatFunc k)) :
    letI := (IsFunctionField.ratFunc k).finiteDimensional_adjoin
      (RatFunc.transcendental_X (K := k))
    ∃ t : RatFunc k, P.valuation.IsUniformizer t ∧
      (∀ z : RatFunc k, P.valuation z < 1 → repartitionDualComponent ω P
        ((derivativeOfSeparating (RatFunc.transcendental_X (K := k)) t / t) * z) = 0) ∧
      repartitionDualComponent ω P
        (derivativeOfSeparating (RatFunc.transcendental_X (K := k)) t / t) = (P.degree : k) := by
  haveI := (IsFunctionField.ratFunc k).finiteDimensional_adjoin
    (RatFunc.transcendental_X (K := k))
  let dX := derivativeOfSeparating (RatFunc.transcendental_X (K := k))
  rcases P.eq_infty_or_exists_eq_adicOfIrreducible with rfl | ⟨q, hq, rfl⟩
  · let t : RatFunc k := (RatFunc.X : RatFunc k)⁻¹
    have ht := (Place.isUniformizer_infty (k := k))
    have hd : dX t = -t ^ 2 := by
      rw [dX.leibniz_inv]
      have hself : dX (RatFunc.X : RatFunc k) = 1 :=
        derivativeOfSeparating_self (RatFunc.transcendental_X (K := k))
      rw [hself, smul_eq_mul, mul_one]
    refine ⟨t, ht, ?_, ?_⟩
    · intro z hz
      have hmem := ResidueNormalization.div_uniformizer_integral (Place.infty k) ht hz
      have hval : (Place.infty k).valuation (-t ^ 2) = WithZero.exp (-2 : ℤ) := by
        rw [(Place.infty k).valuation_eq_exp_neg_ord
          (neg_ne_zero.mpr (pow_ne_zero 2 ht.ne_zero)),
          Place.ord_neg, Place.ord_pow, (Place.infty k).isUniformizer_iff_ord_eq_one.mp ht]
        norm_num
      have heq : (dX t / t) * z = (-t ^ 2) * (z / t) := by rw [hd]; ring
      rw [heq]
      apply repartitionDualComponent_apply_eq_zero_of_le hD
      rw [WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_self, mul_one, map_mul, hval]
      have hle := (Place.infty k).mem_integers_iff.mp hmem
      calc
        WithZero.exp (-2 : ℤ) * (Place.infty k).valuation (z / t) ≤
            WithZero.exp (-2 : ℤ) * 1 := by gcongr
        _ = WithZero.exp (-2 : ℤ) := mul_one _
    · have h := logarithmicResidue_eq_order_mul_degree ω hD hN (Place.infty k) ht.ne_zero
      rw [(Place.infty k).isUniformizer_iff_ord_eq_one.mp ht, Int.cast_one, one_mul] at h
      exact h
  · let P := Place.adicOfIrreducible hq
    let t : RatFunc k := algebraMap k[X] (RatFunc k) q
    have ht : P.valuation.IsUniformizer t := Place.isUniformizer_adicOfIrreducible hq
    refine ⟨t, ht, ?_, ?_⟩
    · intro z hz
      have hmem := ResidueNormalization.div_uniformizer_integral P ht hz
      have hd : dX t = algebraMap k[X] (RatFunc k) q.derivative := derivative_polynomial q
      have heq : (dX t / t) * z = dX t * (z / t) := by ring
      rw [heq]
      apply repartitionDualComponent_apply_eq_zero_of_le hD
      rw [WeilDivisor.coeff_zsmul,
        WeilDivisor.coeff_ofPoint_of_ne (Place.adicOfIrreducible_ne_infty hq), mul_zero,
        WithZero.exp_zero]
      apply P.mem_integers_iff.mp
      rw [hd]
      exact mul_mem (Place.algebraMap_mem_integers_ofPrime k (RatFunc k)
        (IsDedekindDomain.HeightOneSpectrum.ofIrreducible hq) q.derivative) hmem
    · have h := logarithmicResidue_eq_order_mul_degree ω hD hN P ht.ne_zero
      rw [P.isUniformizer_iff_ord_eq_one.mp ht, Int.cast_one, one_mul] at h
      exact h

end ZInQ.Contrib.RC53Assist.AbelianCurveInputs.RationalResidues

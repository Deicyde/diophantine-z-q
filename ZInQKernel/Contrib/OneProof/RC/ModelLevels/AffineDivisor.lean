import ZInQKernel.Contrib.OneProof.RC.ModelLevels.Divisibility

/-! # Closed inclusions of affine torsion at divisor levels -/

namespace WeierstrassCurve.ModelLevels

open Polynomial ModelTorsion WeierstrassCurve.Affine

private theorem prePsi_dvd_over_algClosed {k : Type*} [Field k] [IsAlgClosed k]
    (W : WeierstrassCurve k) [W.IsElliptic] {d N : ℕ} (hN : IsUnit (N : k))
    (hdN : d ∣ N) : W.preΨ' d ∣ W.preΨ' N := by
  classical
  have h := xPolynomial_dvd_over_algClosed W hN hdN
  by_cases hd : Even d
  · have hNe : Even N := by
      obtain ⟨m, rfl⟩ := hdN
      exact hd.mul_right m
    have hne : W.Ψ₂Sq ≠ 0 := by
      have hs := (separable_xPolynomial W hN.ne_zero).ne_zero
      exact (mul_ne_zero_iff.mp
        (show W.preΨ' N * W.Ψ₂Sq ≠ 0 by simpa [xPolynomial, hNe] using hs)).2
    have hmul : W.preΨ' d * W.Ψ₂Sq ∣ W.preΨ' N * W.Ψ₂Sq := by
      simpa [xPolynomial, hd, hNe] using h
    obtain ⟨r, hr⟩ := hmul
    refine ⟨r, mul_right_cancel₀ hne ?_⟩
    simpa only [mul_right_comm] using hr
  · by_cases hNe : Even N
    · have hcop : IsCoprime (W.preΨ' d) W.Ψ₂Sq := by
        apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed k k (W.preΨ' d) W.Ψ₂Sq).2
        intro x
        change (W.preΨ' d).eval x ≠ 0 ∨ W.Ψ₂Sq.eval x ≠ 0
        by_cases hx : (W.preΨ' d).eval x = 0
        · right
          intro h₂
          obtain ⟨y, hP, ht⟩ := exists_torsion_ordinate W
            (show (xPolynomial W d).eval x = 0 by simpa [xPolynomial, hd] using hx)
          let P : W.toAffine.Point := Point.some x y hP
          have htwo : 2 • P = 0 := by
            rw [two_nsmul]
            exact Point.add_self_of_Y_eq ((eval_Ψ₂Sq_eq_zero_iff W hP.1).mp h₂)
          have h₁ : addOrderOf P ∣ 1 := by
            have hgd := Nat.dvd_gcd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr ht)
              (addOrderOf_dvd_iff_nsmul_eq_zero.mpr htwo)
            rwa [((Nat.coprime_two_right).2 (Nat.not_even_iff_odd.mp hd)).gcd_eq_one] at hgd
          exact Point.some_ne_zero hP
            (AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp h₁))
        · exact Or.inl hx
      exact hcop.dvd_of_dvd_mul_right (by simpa [xPolynomial, hd, hNe] using h)
    · simpa [xPolynomial, hd, hNe] using h

variable {A : Type*} [CommRing A]

/-- The division equation of the quadratic ordinate chart divides the
corresponding equation at every multiple of the level, over a domain. -/
theorem prePsi_dvd [IsDomain A] (W : WeierstrassCurve A) [W.IsElliptic]
    {d N : ℕ} (hN : IsUnit (N : A)) (hdN : d ∣ N) : W.preΨ' d ∣ W.preΨ' N := by
  let k := AlgebraicClosure (FractionRing A)
  let f : A →+* k := (algebraMap (FractionRing A) k).comp (algebraMap A (FractionRing A))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing A) k).injective.comp (IsFractionRing.injective A (FractionRing A))
  have hd : IsUnit (d : A) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hdN) hN
  have hu : IsUnit (W.preΨ' d).leadingCoeff := by
    rw [W.leadingCoeff_preΨ' hd.ne_zero]
    by_cases he : Even d
    · obtain ⟨m, rfl⟩ := he.two_dvd
      rw [ite_eq_left (even_two_mul m), Nat.mul_div_cancel_left _ two_pos]
      exact isUnit_of_mul_isUnit_right (show IsUnit ((2 : A) * m) by simpa using hd)
    · simpa [he] using hd
  refine dvd_of_map_dvd f hf hu ?_
  rw [← W.map_preΨ', ← W.map_preΨ']
  exact prePsi_dvd_over_algClosed (W.map f) (by simpa using hN.map f) hdN

private theorem mapAdjoinRoot_surjective {B C : Type*} [CommRing B] [CommRing C]
    (f : B →+* C) (hf : Function.Surjective f) (p : B[X]) (q : C[X]) (h : q ∣ p.map f) :
    Function.Surjective (AdjoinRoot.map f p q h) := by
  intro y
  obtain ⟨q', rfl⟩ := AdjoinRoot.mk_surjective y
  obtain ⟨p', rfl⟩ := Polynomial.map_surjective f hf q'
  refine ⟨AdjoinRoot.mk p p', ?_⟩
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.mk p p') = _
  rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq,
    ← Polynomial.aeval_def, AdjoinRoot.aeval_eq]

private theorem quadratic_dvd (W : WeierstrassCurve A) {d N : ℕ}
    (h : W.preΨ' d ∣ W.preΨ' N) :
    unramifiedOrdinate W d ∣ (unramifiedOrdinate W N).map
      (AdjoinRoot.algHomOfDvd A (W.preΨ' N) (W.preΨ' d) h).toRingHom := by
  let f := AdjoinRoot.algHomOfDvd A (W.preΨ' N) (W.preΨ' d) h
  change _ ∣ (unramifiedOrdinate W N).map f.toRingHom
  have hq : (unramifiedOrdinate W N).map f.toRingHom = unramifiedOrdinate W d := by
    unfold unramifiedOrdinate
    rw [map_ordinatePolynomial, WeierstrassCurve.map_map,
      show f.toRingHom.comp (algebraMap A _) = algebraMap A _ from f.comp_algebraMap]
    rw [show f.toRingHom (AdjoinRoot.root _) = AdjoinRoot.root (W.preΨ' d) from
      AdjoinRoot.algHomOfDvd_root (R := A) _ _ h]
  rw [hq]

private theorem branch_dvd (W : WeierstrassCurve A) {d N : ℕ} (hdN : d ∣ N) :
    branchPolynomial W d ∣ branchPolynomial W N := by
  by_cases he : Even d
  · obtain ⟨m, rfl⟩ := hdN
    simp [branchPolynomial, he, he.mul_right m]
  · simp [branchPolynomial, he]

/-- Restriction on each chart of nonidentity torsion. Divisibility on the
quadratic chart suffices, since the branch survives precisely at even levels. -/
noncomputable def affineDivisorMap (W : WeierstrassCurve A) {d N : ℕ} (hdN : d ∣ N)
    (h : W.preΨ' d ∣ W.preΨ' N) :
    AffineTorsionAlgebra W N →ₐ[A] AffineTorsionAlgebra W d :=
  AlgHom.prodMap
    (AdjoinRoot.mapAlgHom (AdjoinRoot.algHomOfDvd A _ _ h) _ _ (quadratic_dvd W h))
    (AdjoinRoot.algHomOfDvd A _ _ (branch_dvd W hdN))

/-- The restriction is surjective on both charts, since the coefficient and
ordinate root maps preserve their generators. -/
theorem affineDivisorMap_surjective (W : WeierstrassCurve A) {d N : ℕ} (hdN : d ∣ N)
    (h : W.preΨ' d ∣ W.preΨ' N) : Function.Surjective (affineDivisorMap W hdN h) := by
  unfold affineDivisorMap
  apply Function.Surjective.prodMap
  · refine mapAdjoinRoot_surjective _ ?_ _ _ (quadratic_dvd W h)
    exact mapAdjoinRoot_surjective (RingHom.id A) Function.surjective_id _ _ (by simpa)
  · exact mapAdjoinRoot_surjective (RingHom.id A) Function.surjective_id _ _
      (by simpa using branch_dvd W hdN)

#print axioms prePsi_dvd_over_algClosed
#print axioms prePsi_dvd
#print axioms mapAdjoinRoot_surjective
#print axioms quadratic_dvd
#print axioms branch_dvd
#print axioms affineDivisorMap_surjective

end WeierstrassCurve.ModelLevels

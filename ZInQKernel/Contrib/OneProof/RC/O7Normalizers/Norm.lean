import ZInQKernel.Contrib.OneProof.RC.O7Normalizers.Local

/-! Unramified norm factors at the level and detecting primes. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O7Normalizers

open Adelic Eichler ThetaJoin ThetaClose LocalWeights

variable {ell N m : ℕ} [Fact ell.Prime] (h : ell % 4 = 3) (hN : 0 < N)

theorem splitUnit_valuation (q : Prime) (hq : q.val ≠ ell) :
    (valHom q (localNormHom q (splitUnit (N := N) h q hq))).toAdd =
      (N.factorization q.val : ℤ) := by
  let e := N.factorization q.val
  let u := splitUnit (N := N) h q hq
  let f := splitChart ell h q hq
  change (u.val * star u.val).re.valuation = _
  rw [← (split_invariants _ _ f u.val).2]
  have hf : f u.val = (atkinMatrix q e).val := congrArg Units.val (splitUnit_chart h q hq)
  rw [hf]
  let X : Mat ℚ_[q.val] := !![0, 1; (q.val : ℚ_[q.val]) ^ e, 0]
  change X.det.valuation = _
  have hdet : X.det = -((q.val : ℚ_[q.val]) ^ e) := by
    rw [Matrix.det_fin_two]
    change 0 * 0 - 1 * (q.val : ℚ_[q.val]) ^ e = _
    rw [zero_mul, one_mul, zero_sub]
  rw [hdet]
  have hneg : (-1 : ℚ_[q.val]).valuation = 0 := by
    have h := Padic.valuation_mul (by norm_num : (-1 : ℚ_[q.val]) ≠ 0)
      (by norm_num : (-1 : ℚ_[q.val]) ≠ 0)
    rw [neg_mul_neg, one_mul, Padic.valuation_one] at h
    omega
  rw [neg_eq_neg_one_mul, Padic.valuation_mul (by norm_num)
    (pow_ne_zero _ (Nat.cast_ne_zero.mpr q.prop.ne_zero)),
    hneg, zero_add, Padic.valuation_pow, Padic.valuation_p, mul_one]

theorem divisionUnit_valuation :
    (valHom (detectingPrime ell) (localNormHom (detectingPrime ell) (divisionUnit h))).toAdd =
      1 := by
  letI : Fact (ell % 4 = 3) := ⟨h⟩
  change (DivisionJoin.reducedNorm ell (divisionUnit h).val).valuation = _
  rw [← DivisionJoin.ambient_norm, show DivisionJoin.ambientEquiv ell (divisionUnit h).val =
    LocalDivision.uniformizer.val from congrArg Units.val (divisionUnit_chart h)]
  exact LocalDivision.uniformizer_norm

/-- The supplementary law at two applies because the fixed discriminant
is 1 modulo 8. For odd q use the negative discriminant product law. -/
theorem discriminant_product (H : DiscriminantData m N ell) (p : Prime) :
    jacobiSym (-(m : ℤ)) p.val = ∏ q ∈ m.primeFactors, jacobiSym p.val q := by
  by_cases hp : p.val = 2
  · have hprod : jacobiSym 2 m = ∏ q ∈ m.primeFactors, jacobiSym 2 q := by
      conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree H.squarefree]
      set S := m.primeFactors
      have hne : ∀ q ∈ S, q ≠ 0 := fun q hq => (Nat.prime_of_mem_primeFactors hq).ne_zero
      classical
      clear_value S
      induction S using Finset.induction_on with
      | empty => simp
      | insert q T hq ih =>
        rw [Finset.prod_insert hq, Finset.prod_insert hq, jacobiSym.mul_right']
        · exact congrArg (jacobiSym 2 q * ·) (ih fun p hp => hne p (Finset.mem_insert_of_mem hp))
        · exact hne q (Finset.mem_insert_self _ _)
        · exact Finset.prod_ne_zero_iff.mpr fun p hp => hne p (Finset.mem_insert_of_mem hp)
    rw [hp, Nat.cast_two, ← hprod]
    have hm : m % 8 = 7 := by
      have hh := H.twoSplit
      change (-(m : ℤ)) % 8 = 1 % 8 at hh
      omega
    have hm' : Odd m := Nat.odd_iff.mpr (by omega)
    have hv : (-(m : ℤ)) % 2 = 1 := by omega
    rw [jacobiSym.at_two hm', ZMod.χ₈_nat_eq_if_mod_eight, hm]
    rw [jacobiSym.mod_left' (b := 2) (a₂ := 1) (by simpa using hv), jacobiSym.one_left]
    simp [Nat.odd_iff.mp hm']
  · exact negativeDiscriminant_unit_character m p.val H.odd H.squarefree (p.prop.odd_of_ne_two hp)

/-- A one-place norm idèle of valuation e, away from the ramified character
primes, has character χ(p)^e. The local unit at p is absent from the product. -/
theorem norm_single (H : DiscriminantData m N ell) {O : Type} [CommRing O]
    (C : LevelRoots O N) (hn : 2 * m * N * ell ≠ 0)
    (p : Prime) (hp : ¬ p.val ∣ m) (u : (Bp p.val (-1) (-(ell : ℚ)))ˣ) (e : ℕ)
    (hu : (valHom p (localNormHom p u)).toAdd = (e : ℤ)) :
    (levelNormCharacter h hN C hn (single (levelRing h hN) p u) : O) =
      (jacobiSym (-(m : ℤ)) p.val : O) ^ e := by
  classical
  let z := normIdeles h hN (single (levelRing h hN) p u)
  have haway (q : Prime) (hq : q ≠ p) : z.val q = 1 := by
    change localNormHom q ((single (levelRing h hN) p u).val q) = 1
    rw [single_away hq, map_one]
  have hz : rationalPart z = rationalPrime p ^ e := by
    apply div_eq_one.mp
    apply positive_rational_unit
    · rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
      refine div_pos (rationalPart_pos z) (pow_pos ?_ _)
      change 0 < (p.val : ℚ)
      exact_mod_cast p.prop.pos
    · intro q
      rw [map_div, map_div, rationalPart_valuation, div_eq_one, map_pow, map_pow]
      apply Multiplicative.toAdd.injective
      rw [Int.toAdd_pow, val_rationalPrime]
      by_cases hq : q = p
      · subst q
        change (valHom p (localNormHom p ((single (levelRing h hN) p u).val p))).toAdd =
          (if p = p then (1 : ℤ) else 0) * (e : ℤ)
        rw [single_same, hu, ite_eq_left rfl, one_mul]
      · rw [haway q hq, map_one, ite_eq_right (Ne.symm hq)]
        simp
  let S := (phaseFor C hn).places.filter fun q => q.val ∣ m
  let emb : Prime ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hS : S.map emb = m.primeFactors := by
    ext n
    simp only [Finset.mem_map, Finset.mem_filter, S, phaseFor, schwartzPhase,
      mem_exceptionalPlaces, emb, Function.Embedding.coeFn_mk, Nat.mem_primeFactors]
    constructor
    · rintro ⟨q, ⟨_, hq⟩, rfl⟩
      exact ⟨q.prop, hq, by have := H.odd; omega⟩
    · rintro ⟨hq, hqm, _⟩
      exact ⟨⟨n, hq⟩, ⟨dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hqm 2) N) ell,
        hqm⟩, rfl⟩
  rw [discriminant_product H p, ← hS, Finset.prod_map, Int.cast_prod, ← Finset.prod_pow]
  change ((∏ q ∈ S, legendreUnit q.val (localUnitPart q z) : Oˣ) : O) = _
  rw [Units.coe_prod]
  apply Finset.prod_congr rfl
  intro q hq
  have hd := (Finset.mem_filter.mp hq).2
  have hqp : q ≠ p := fun he => hp (he ▸ hd)
  have hqnd : ¬ q.val ∣ p.val := fun hdv =>
    hqp (Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.prop p.prop).mp hdv))
  let v := PhaseData.natUnit q p.val hqnd
  let f := Units.map (algebraMap ℤ_[q.val] ℚ_[q.val]).toMonoidHom
  have hv₀ : f v = rationalToLocal q (rationalPrime p) := by
    apply Units.ext
    change (↑(v.val) : ℚ_[q.val]) = _
    rw [PhaseData.natUnit_val]
    change (algebraMap ℤ_[q.val] ℚ_[q.val]) (p.val : ℤ_[q.val]) = _
    rw [map_natCast]
    simp [rationalToLocal, rationalPrime]
  have hv : localUnitPart q z = (v ^ e)⁻¹ := by
    apply Units.ext
    apply Subtype.val_injective
    rw [localUnitPart_val, hz, haway q hqp, map_pow, one_div, ← hv₀, ← map_pow, ← map_inv]
    rfl
  rw [hv, map_inv, legendreUnit_inv, map_pow, Units.val_pow_eq_pow_val,
    legendreUnit_apply, PhaseData.natUnit_val, map_natCast]
  congr 1
  simpa only [legendreSym, Int.cast_natCast, emb, Function.Embedding.coeFn_mk] using
    congrArg (fun n : ℤ => (n : O)) (jacobiSym.legendreSym.to_jacobiSym q.val (p.val : ℤ))

end ZInQ.Manuscript.RC.O7Normalizers

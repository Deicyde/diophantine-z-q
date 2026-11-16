import ZInQKernel.Contrib.OneProof.SGRDirectNV

set_option linter.style.haveILetI false

noncomputable section

open Polynomial GlueDescent.B2Q NumberField
open HDec HDec.G0ModField HDec.PropTSRed LeafQM.AV

namespace SGRDirect

/-- A nonzero rational of `p`-adic valuation `0` has numerator and denominator prime to `p`. -/
theorem not_dvd_num_den_of_padicValRat_eq_zero (p : ℕ) [hp : Fact p.Prime] {u : ℚ} (hu : u ≠ 0)
    (h : padicValRat p u = 0) : ¬ (p : ℤ) ∣ u.num ∧ ¬ p ∣ u.den := by
  have hnum : u.num ≠ 0 := Rat.num_ne_zero.mpr hu
  have hcop : u.num.natAbs.Coprime u.den := u.reduced
  rw [padicValRat_def] at h
  constructor
  · intro hn
    have h1 : p ∣ u.num.natAbs := Int.natCast_dvd.mp hn
    have hd : ¬ p ∣ u.den := fun hd =>
      (Nat.Prime.coprime_iff_not_dvd hp.out).mp (Nat.Coprime.coprime_dvd_left h1 hcop) hd
    have hv1 : padicValNat p u.den = 0 := padicValNat.eq_zero_of_not_dvd hd
    have hv2 : 1 ≤ padicValNat p u.num.natAbs :=
      one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hnum) h1
    rw [padicValInt, hv1] at h
    omega
  · intro hd
    have hn : ¬ p ∣ u.num.natAbs := fun h1 =>
      (Nat.Prime.coprime_iff_not_dvd hp.out).mp (Nat.Coprime.coprime_dvd_left h1 hcop) hd
    have hv1 : padicValNat p u.num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hn
    have hv2 : 1 ≤ padicValNat p u.den := one_le_padicValNat_of_dvd u.den_nz hd
    rw [padicValInt, hv1] at h
    omega

/-- **A square root of `q ∈ ℚ` in a number field unramified at `p` forces `v_p(q)` even.** -/
theorem even_padicValRat_of_sq_mem (L : IntermediateField ℚ Qbar) [FiniteDimensional ℚ L] (p : ℕ)
    (hp : p.Prime) (hL : UnramifiedAt L p) (q : ℚ) (hq : q ≠ 0) (β : Qbar) (hβ : β ∈ L)
    (hsq : β ^ 2 = algebraMap ℚ Qbar q) : Even (padicValRat p q) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hodd
  rw [Int.not_even_iff_odd] at hodd
  obtain ⟨k, hk⟩ := hodd
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp0' : (p : Qbar) ≠ 0 := by exact_mod_cast hp.ne_zero
  set u : ℚ := q * (p : ℚ) ^ (-(2 * k + 1)) with hu
  have hu0 : u ≠ 0 := mul_ne_zero hq (zpow_ne_zero _ hp0)
  have hvu : padicValRat p u = 0 := by
    rw [hu, padicValRat.mul hq (zpow_ne_zero _ hp0), padicValRat.zpow _ (k := -(2 * k + 1)),
      padicValRat.self hp.one_lt, hk]
    ring
  obtain ⟨hnum, hden⟩ := not_dvd_num_den_of_padicValRat_eq_zero p hu0 hvu
  set γ : Qbar := (u.den : Qbar) * β * (p : Qbar) ^ (-k) with hγdef
  have hγL : γ ∈ L :=
    L.mul_mem (L.mul_mem (L.algebraMap_mem (u.den : ℚ)) hβ) (zpow_mem (L.algebraMap_mem (p : ℚ)) _)
  have hqu : algebraMap ℚ Qbar q = algebraMap ℚ Qbar u * (p : Qbar) ^ (2 * k + 1) := by
    rw [hu, map_mul, map_zpow₀, map_natCast, mul_assoc, ← zpow_add₀ hp0']
    simp
  have hud : (u.den : Qbar) * algebraMap ℚ Qbar u = (u.num : Qbar) := by
    have h := Rat.mul_den_eq_num u
    have := congrArg (algebraMap ℚ Qbar) h
    rw [map_mul, map_natCast, map_intCast] at this
    rw [mul_comm]; exact this
  have hγsq : γ ^ 2 = ((u.den * u.num * p : ℤ) : Qbar) := by
    rw [hγdef, mul_pow, mul_pow, hsq, hqu]
    push_cast
    rw [← zpow_natCast ((p : Qbar) ^ (-k)) 2, ← zpow_mul]
    have e : (u.den : Qbar) ^ 2 * (algebraMap ℚ Qbar u * (p : Qbar) ^ (2 * k + 1)) *
        (p : Qbar) ^ (-k * ((2 : ℕ) : ℤ)) =
        ((u.den : Qbar) * algebraMap ℚ Qbar u) * u.den * ((p : Qbar) ^ (2 * k + 1) *
          (p : Qbar) ^ (-k * ((2 : ℕ) : ℤ))) := by ring
    rw [e, hud, ← zpow_add₀ hp0']
    have e2 : 2 * k + 1 + -k * ((2 : ℕ) : ℤ) = 1 := by push_cast; ring
    rw [e2, zpow_one]
    ring
  -- the integral element `γ` and a prime of `𝓞 L` over `p`
  letI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  set N : ℤ := u.den * u.num * p with hN
  have hγsqL : (⟨γ, hγL⟩ : L) ^ 2 = (N : L) := Subtype.ext (by
    rw [IntermediateField.coe_pow]
    rw [hγsq]
    rfl)
  have hintγ : IsIntegral ℤ (⟨γ, hγL⟩ : L) := by
    refine ⟨X ^ 2 - Polynomial.C N, monic_X_pow_sub_C _ (by norm_num), ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hγsqL, sub_eq_zero]
    simp
  set γL : 𝓞 L := ⟨⟨γ, hγL⟩, hintγ⟩ with hγLdef
  have hγLsq : γL ^ 2 = (N : 𝓞 L) := by
    apply RingOfIntegers.coe_injective
    push_cast
    show (⟨γ, hγL⟩ : L) ^ 2 = _
    rw [hγsqL, map_intCast]
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨P, hP, hPu⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 L)
    (Ideal.span {(p : ℤ)}) (by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have : (x : 𝓞 L) = 0 := by simpa using hx
      have hx0 : x = 0 := by exact_mod_cast this
      rw [hx0]; exact Ideal.zero_mem _)
  have hpP : ((p : ℤ) : 𝓞 L) ∈ P := by
    have h1 : (p : ℤ) ∈ P.under ℤ := by rw [hPu]; exact Ideal.mem_span_singleton_self _
    simpa using h1
  have he := hL P hP hpP
  have hγP : γL ∈ P := by
    apply hP.mem_of_pow_mem 2
    rw [hγLsq, hN]
    push_cast
    exact P.mul_mem_left _ hpP
  have hsqP : ((p : ℤ) : 𝓞 L) * ((u.den * u.num : ℤ) : 𝓞 L) ∈ P ^ 2 := by
    have h2 : γL ^ 2 ∈ P ^ 2 := Ideal.pow_mem_pow hγP 2
    rw [hγLsq, hN] at h2
    push_cast at h2 ⊢
    convert h2 using 1
    ring
  have hP0 : P ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpP
    have : ((p : ℤ) : 𝓞 L) ≠ 0 := by exact_mod_cast hp.ne_zero
    exact this hpP
  have hPmax : P.IsMaximal := hP.isMaximal hP0
  have hrad : (P ^ 2).radical = P := by rw [Ideal.radical_pow P two_ne_zero, hP.radical]
  have hprim : (P ^ 2).IsPrimary := Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; exact hPmax)
  rcases (Ideal.isPrimary_iff.mp hprim).2 hsqP with h | h
  · -- `p ∈ P²` contradicts `e(P | p) = 1`
    have hle : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≤ P ^ 2 := by
      rw [Ideal.map_span, Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]
      simpa using h
    haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPu.symm⟩
    have hsp0 : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
    have he' := Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P hsp0
    rw [he] at he'
    have h2mem : 2 ∈ {n | Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≤ P ^ n} := hle
    by_cases hbdd : BddAbove {n | Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {(p : ℤ)}) ≤ P ^ n}
    · have := le_csSup hbdd h2mem
      rw [Ideal.ramificationIdx'] at he'
      omega
    · rw [Ideal.ramificationIdx', Nat.sSup_of_not_bddAbove hbdd] at he'
      exact zero_ne_one he'
  · rw [hrad] at h
    have h1 : (u.den * u.num : ℤ) ∈ P.under ℤ := by simpa using h
    rw [hPu, Ideal.mem_span_singleton] at h1
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd h1 with h2 | h2
    · exact hden (by exact_mod_cast h2)
    · exact hnum h2

open CategoryTheory AlgebraicGeometry in
/-- **A point over `0` with unramified residue field**, on every triple (from `R1R2fp` and T5). -/
theorem exists_point_zero_unram (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π) :
    ∃ y : fieldPt Qbar ⟶ Y, π.val (K := Qbar) y.left = OnePoint.some 0 ∧
      UnramifiedAbove5 (residueImage (X := Y.left) y.left) := by
  have hM := CurveGlue.mobiusGlue_of_T5 hT
  have hCM := Pin.cm_objects_of_R1R2fp hRR
  obtain ⟨Y₁, Φ₁, π₁, h11, h21, hfib⟩ := exists_fibre_object hRR
  obtain ⟨y₁, P₁, -, hy₁⟩ := hfib (OnePoint.some 0)
  obtain ⟨g₁, hΦ₁, hπ₁⟩ := Pin.sameTripleMor_of_mobius hM hCM h11 h21 h1 h2
  set y := (Φ Qbar).symm (Φ₁ Qbar y₁) with hydef
  have hyg : y ≫ g₁ = y₁ := (Φ₁ Qbar).injective (by rw [← hΦ₁, hydef, Equiv.apply_symm_apply])
  have hπy : π.val (K := Qbar) y.left = OnePoint.some 0 := by rw [hπ₁ y, hyg, hy₁]
  obtain ⟨Y₀, Φ₀, π₀, h10, h20, hbr⟩ := residue_unramified_over_branch hRR
  obtain ⟨g₀, hΦ₀, hπ₀⟩ := Pin.sameTripleMor_of_mobius hM hCM h10 h20 h1 h2
  have h0 := hbr (y ≫ g₀) (Or.inl (by rw [← hπ₀ y]; exact hπy))
  rw [PropTSRed.residueImage_comp_eq_of_pt g₀ hΦ₀ y] at h0
  exact ⟨y, hπy, h0⟩

open CategoryTheory AlgebraicGeometry in
/-- **From any square root of `c (27X + 16)` in `E` to one with constant prime to `p`** (`p ≥ 5`): the residue
fields over `0` are unramified at `p` (`exists_point_zero_unram`) and contain `√c`, so `v_p(c)` is even. -/
theorem exists_good_sqrt (hRR : R1R2fp) (hT : ObjBridge.TorsionStructure)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π)
    (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] (hN : NormalizationModel Y π E)
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (c : ℚ) (hc : c ≠ 0) (s : E)
    (hs : s ^ 2 = algebraMap ℚ[X] E (C c * (C 27 * X + C 16))) :
    ∃ (a : ℤ) (s' : E), ¬ (p : ℤ) ∣ a ∧
      s' ^ 2 = algebraMap ℚ[X] E (C (a : ℚ) * (C 27 * X + C 16)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hπy, hun⟩ := exists_point_zero_unram hRR hT h1 h2
  obtain ⟨h, hO, himg, hval⟩ := hN
  obtain ⟨y', hy'⟩ := himg y.left (by rw [hπy]; exact OnePoint.coe_ne_infty _)
  set ψ := (Spec.preimage y').hom with hψ
  have hy'' : y' = Spec.map (CommRingCat.ofHom ψ) := by
    rw [hψ, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hψX : ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = 0 := by
    have := hval ψ
    rw [← hy'', ← hy', hπy] at this
    exact (OnePoint.coe_injective this).symm
  have hψC : ∀ r : ℚ, ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) (C r)) = algebraMap ℚ Qbar r := by
    intro r
    have hsub : ((ψ.comp (algebraMap ℚ[X] (integralClosure ℚ[X] E))).comp C : ℚ →+* Qbar) =
        algebraMap ℚ Qbar := Subsingleton.elim _ _
    exact congrArg (fun f : ℚ →+* Qbar => f r) hsub
  have hres : residueImage (X := Y.left) y.left = IntermediateField.adjoin ℚ (Set.range ψ) := by
    rw [hy', PropTSRed.residueImage_comp_openImmersion h y', hy'', PropTSRed.residueImage_specMap]
  -- `s` is integral over `ℚ[X]`
  have hintE : IsIntegral ℚ[X] s := by
    refine ⟨X ^ 2 - Polynomial.C (C c * (C 27 * X + C 16)), monic_X_pow_sub_C _ (by norm_num), ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hs, sub_self]
  set sB : integralClosure ℚ[X] E := ⟨s, hintE⟩ with hsB
  have hsBsq : sB ^ 2 = algebraMap ℚ[X] (integralClosure ℚ[X] E) (C c * (C 27 * X + C 16)) :=
    Subtype.ext (by
      show s ^ 2 = algebraMap ℚ[X] E _
      exact hs)
  have hψs : ψ sB ^ 2 = algebraMap ℚ Qbar (16 * c) := by
    rw [← map_pow, hsBsq]
    simp only [map_mul, map_add, hψX, hψC, mul_zero, zero_add]
    rw [mul_comm]
  set β : Qbar := ψ sB / 4 with hβdef
  have hβL : β ∈ IntermediateField.adjoin ℚ (Set.range ψ) :=
    IntermediateField.div_mem _ (IntermediateField.subset_adjoin ℚ _ ⟨sB, rfl⟩)
      (IntermediateField.algebraMap_mem _ (4 : ℚ))
  have hβsq : β ^ 2 = algebraMap ℚ Qbar c := by
    rw [hβdef, div_pow, hψs, map_mul]
    norm_num
  rw [hres] at hun
  obtain ⟨hfin, hdisc⟩ := hun
  letI : NumberField (IntermediateField.adjoin ℚ (Set.range ψ)) := @NumberField.mk _ _ _ hfin
  have hU := GlueB3Unram.unramifiedAt_of_not_dvd_discr _ p hp (hdisc p hp hp5)
  obtain ⟨k, hk⟩ := even_padicValRat_of_sq_mem _ p hp hU c hc β hβL hβsq
  -- `c = p^{2k} u` with `u` a `p`-adic unit
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  set u : ℚ := c * (p : ℚ) ^ (-(k + k)) with hu
  have hu0 : u ≠ 0 := mul_ne_zero hc (zpow_ne_zero _ hp0)
  have hvu : padicValRat p u = 0 := by
    rw [hu, padicValRat.mul hc (zpow_ne_zero _ hp0), padicValRat.zpow _ (k := -(k + k)),
      padicValRat.self hp.one_lt, hk]
    ring
  obtain ⟨hnum, hden⟩ := not_dvd_num_den_of_padicValRat_eq_zero p hu0 hvu
  set ι : ℚ →+* E := (algebraMap ℚ[X] E).comp C with hι
  refine ⟨u.den * u.num, ι u.den * s * ι ((p : ℚ) ^ (-k)), ?_, ?_⟩
  · intro hdvd
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_or_dvd hdvd with h2 | h2
    · exact hden (by exact_mod_cast h2)
    · exact hnum h2
  · have hq : (u.den : ℚ) ^ 2 * c * ((p : ℚ) ^ (-k)) ^ 2 = ((u.den * u.num : ℤ) : ℚ) := by
      have hud : u * u.den = u.num := Rat.mul_den_eq_num u
      have hc' : c = u * (p : ℚ) ^ (k + k) := by
        rw [hu, mul_assoc, ← zpow_add₀ hp0]; simp
      rw [hc', ← zpow_natCast ((p : ℚ) ^ (-k)) 2, ← zpow_mul]
      push_cast
      have e : (u.den : ℚ) ^ 2 * (u * (p : ℚ) ^ (k + k)) * (p : ℚ) ^ (-k * 2) =
          (u * u.den) * u.den * ((p : ℚ) ^ (k + k) * (p : ℚ) ^ (-k * 2)) := by ring
      rw [e, hud, ← zpow_add₀ hp0]
      have e2 : k + k + -k * 2 = 0 := by ring
      rw [e2, zpow_zero]
      ring
    rw [mul_pow, mul_pow, hs, map_mul, map_mul]
    have : algebraMap ℚ[X] E (C (((u.den * u.num : ℤ) : ℚ))) = ι (((u.den * u.num : ℤ) : ℚ)) := rfl
    rw [this, ← hq, map_mul, map_mul, map_pow, map_pow]
    have : algebraMap ℚ[X] E (C c) = ι c := rfl
    rw [this]
    ring

end SGRDirect

#print axioms SGRDirect.exists_good_sqrt

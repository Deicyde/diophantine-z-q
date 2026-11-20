import ZInQKernel.Contrib.OneProof.RC.CMField2.SplitPrime
import ZInQKernel.Contrib.OneProof.RC.CMField2.Membership
import ZInQKernel.Contrib.Chebotarev.Exists

/-! The arithmetic comparison at a separating Chebotarev prime. Provenance (c). -/

noncomputable section

open NumberField Ideal Polynomial Module IntermediateField TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields

namespace ZInQ.Manuscript.RC.CMField2

private theorem rational_prime_span_ne_bot {p : ℕ} (hp : p.Prime) :
    (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hp.ne_zero

private theorem absNorm_under_eq_of_pow_fixed
    {E M : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Algebra M E]
    (p : ℕ) [Fact p.Prime] (Q : Ideal (𝓞 E)) [Q.IsMaximal]
    [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (h : ∀ x : 𝓞 M, x ^ p - x ∈ Q.under (𝓞 M)) :
    (Q.under (𝓞 M)).absNorm = p := by
  classical
  let P := Q.under (𝓞 M)
  let : P.IsMaximal := isMaximal_under_of_isIntegral_of_isMaximal Q
  have hp : p.Prime := Fact.out
  have hPZ : P.under ℤ = Ideal.span {(p : ℤ)} :=
    (Ideal.under_under (𝔓 := Q)).trans (Q.over_def (Ideal.span {(p : ℤ)})).symm
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPZ.symm⟩
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (rational_prime_span_ne_bot hp) P
  let F := 𝓞 M ⧸ P
  let : Field F := Ideal.Quotient.field P
  let : Finite F := Ring.HasFiniteQuotients.finiteQuotient hP0
  let : Fintype F := Fintype.ofFinite F
  have hchar : ((p : ℕ) : F) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem,
      ← Int.cast_natCast]
    change (p : ℤ) ∈ P.under ℤ
    rw [hPZ]
    exact Ideal.subset_span (Set.mem_singleton _)
  let : CharP F p := (CharP.charP_iff_prime_eq_zero hp).mpr hchar
  have hlo : p ≤ Nat.card F := by
    simpa using Nat.card_le_card_of_injective
      (ZMod.castHom (dvd_refl p) F) (ZMod.castHom_injective (n := p) (R := F))
  let f : F[X] := X ^ p - X
  have hdeg : f.natDegree = p := by
    dsimp [f]
    rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
    simpa using hp.one_lt
  have hf : f ≠ 0 := by
    intro hz
    exact hp.ne_zero (hdeg.symm.trans (by simp [hz]))
  have hroots : Finset.univ ⊆ f.roots.toFinset := by
    intro x _
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf, Polynomial.IsRoot.def]
    have hy : Ideal.Quotient.mk P (y ^ p - y) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (h y)
    simpa only [f, eval_sub, eval_pow, eval_X, map_sub, map_pow] using hy
  have hhi : Nat.card F ≤ p := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    exact (Finset.card_le_card hroots).trans
      ((Multiset.toFinset_card_le _).trans (hdeg ▸ Polynomial.card_roots' f))
  exact le_antisymm hhi hlo

private theorem absNorm_under_eq_of_frob_fixes
    {E M : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Algebra M E]
    (p : ℕ) [Fact p.Prime] (Q : Ideal (𝓞 E)) [Q.IsMaximal]
    [Q.LiesOver (Ideal.span {(p : ℤ)})] {σ : E ≃ₐ[ℚ] E}
    (hσ : IsArithFrobAt ℤ σ Q) (hfix : ∀ x : M, σ (algebraMap M E x) = algebraMap M E x) :
    (Q.under (𝓞 M)).absNorm = p := by
  apply absNorm_under_eq_of_pow_fixed p Q
  intro x
  let a := algebraMap (𝓞 M) (𝓞 E)
  have hfix' : σ • a x = a x := RingOfIntegers.ext (hfix (x : M))
  have h := hσ (a x)
  change σ • a x - (a x) ^ Nat.card (ℤ ⧸ Q.under ℤ) ∈ Q at h
  rw [Ideal.natCard_quotient_under_of_liesOver (p := p) Q, hfix'] at h
  change a (x ^ p - x) ∈ Q
  rw [map_sub, map_pow, ← neg_sub]
  exact Q.neg_mem h

private theorem not_mem_of_norm_lt
    {E : Type} [Field E] [NumberField E] (p : ℕ)
    (Q : Ideal (𝓞 E)) [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hp : I.absNorm < p) :
    ¬ I ≤ Q := by
  intro h
  have hn : (I.absNorm : ℤ) ∈ Q.under ℤ := by
    change algebraMap ℤ (𝓞 E) (I.absNorm : ℤ) ∈ Q
    rw [map_natCast]
    exact h I.absNorm_mem
  rw [← Q.over_def (Ideal.span {(p : ℤ)}), Ideal.mem_span_singleton] at hn
  exact (not_le_of_gt hp) (Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)) (by exact_mod_cast hn))

/-- A Frobenius fixing the embedded ring class field, at a rational prime
larger than the conductor norm, yields a split degree-one prime of the base. -/
theorem splitPrime_of_frob_fixes_ringClass
    {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E]
    (O : NumberFieldOrder K) [Algebra K E] [Algebra (ringClassField O) E]
    [IsScalarTower K (ringClassField O) E]
    (p : ℕ) [Fact p.Prime] (Q : Ideal (𝓞 E)) [Q.IsMaximal]
    [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (hp : O.conductor.absNorm < p) {σ : E ≃ₐ[ℚ] E}
    (hσ : IsArithFrobAt ℤ σ Q)
    (hfix : ∀ x : ringClassField O,
      σ (algebraMap (ringClassField O) E x) = algebraMap (ringClassField O) E x) :
    ∃ J : integralIdealsPrimeTo O.conductorModulus, ∃ _ : (J : Ideal (𝓞 K)).IsMaximal,
      (J : Ideal (𝓞 K)).absNorm = p ∧
      ((J : Ideal (𝓞 K)).primesOver (𝓞 (ringClassField O))).ncard =
        finrank K (ringClassField O) := by
  let H := ringClassField O
  let P := Q.under (𝓞 K)
  let R := Q.under (𝓞 H)
  let : P.IsMaximal := isMaximal_under_of_isIntegral_of_isMaximal Q
  let : R.IsMaximal := isMaximal_under_of_isIntegral_of_isMaximal Q
  let : R.LiesOver P := ⟨(under_under (𝔓 := Q)).symm⟩
  have hPp : P.under ℤ = Ideal.span {(p : ℤ)} :=
    (under_under (𝔓 := Q)).trans (Q.over_def (Ideal.span {(p : ℤ)})).symm
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPp.symm⟩
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (rational_prime_span_ne_bot (Fact.out : p.Prime)) P
  have hcon : ¬ O.conductor ≤ P := not_mem_of_norm_lt p P O.conductor O.conductor_ne_bot hp
  have hcop : P ⊔ O.conductor = ⊤ := by
    by_contra hne
    exact hcon (sup_le_iff.mp ((Ideal.IsMaximal.eq_of_le inferInstance hne le_sup_left).ge)).2
  let J : integralIdealsPrimeTo O.conductorModulus :=
    ⟨P, O.mem_integralIdealsPrimeTo_conductorModulus_iff.mpr ⟨hP0, hcop⟩⟩
  have hdegP : P.absNorm = p := absNorm_under_eq_of_frob_fixes p Q hσ (fun x : K => by
    rw [IsScalarTower.algebraMap_apply K H E, hfix])
  have hdegR : R.absNorm = p := absNorm_under_eq_of_frob_fixes p Q hσ hfix
  have hdeg : R.inertiaDeg (𝓞 K) = 1 := by
    have hpow := Ideal.cardQuot_pow_inertiaDeg P R
    change P.absNorm ^ R.inertiaDeg (𝓞 K) = R.absNorm at hpow
    rw [hdegP, hdegR] at hpow
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le (hpow.trans (pow_one p).symm)
  refine ⟨J, inferInstance, hdegP, ?_⟩
  have horder := orderOf_picClass_eq_inertiaDeg O J R
  have hcount := ncard_primesOver_ringClassField_mul_orderOf_picClass O J
  rw [horder, hdeg, mul_one, ← finrank_ringClassField] at hcount
  exact hcount

/-- All the singular moduli lie in the same embedded ring class field. For
each value, a separating Frobenius inside a finite normal closure gives a
split prime and hence an incompatible diagonal reduction unless it fixes the value. -/
theorem singularModulusMemRingClass : SingularModulusMemRingClass := by
  classical
  intro K _ _ O hk hc κ
  let H := ringClassField O
  let : Algebra K ℂ := κ.toAlgebra
  let : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let ιK : H →ₐ[K] ℂ := IsAlgClosed.lift
  let ι := ιK.restrictScalars ℚ
  refine ⟨ι.toRingHom, RingHom.ext ιK.commutes, ?_⟩
  intro I
  let j := singularModulus O hk hc κ I
  have hj : IsIntegral ℤ j := singularModulus_isIntegral O hk hc κ I
  let J := IntermediateField.adjoin ℚ {j}
  let : FiniteDimensional ℚ J :=
    IntermediateField.adjoin.finiteDimensional (hj.tower_top : IsIntegral ℚ j)
  let : FiniteDimensional ℚ ι.fieldRange := ι.toLinearMap.finiteDimensional_range
  let F := ι.fieldRange ⊔ J
  let : FiniteDimensional ℚ F := by dsimp [F]; infer_instance
  let E := normalClosure ℚ F ℂ
  have hFE : F ≤ E := IntermediateField.le_normalClosure F
  have hHE : ι.fieldRange ≤ E := le_sup_left.trans hFE
  have hJE : J ≤ E := (show J ≤ F from le_sup_right).trans hFE
  let x : E := ⟨j, hJE (IntermediateField.mem_adjoin_simple_self ℚ j)⟩
  let : NumberField E := ⟨⟩
  let : IsNormalClosure ℚ F E := Algebra.IsAlgebraic.isNormalClosure_normalClosure
    (F := ℚ) (K := F) (L := ℂ) (fun _ => IsAlgClosed.splits _)
  let : IsGalois ℚ E := isGalois_iff.mpr ⟨inferInstance, IsNormalClosure.normal (K := F)⟩
  let e : H →ₐ[ℚ] E := ι.codRestrict E.toSubalgebra (fun z => hHE ⟨z, rfl⟩)
  let H' := e.fieldRange
  let : Algebra H E := e.toRingHom.toAlgebra
  let : Algebra K E := ((algebraMap H E).comp (algebraMap K H)).toAlgebra
  let : IsScalarTower K H E := IsScalarTower.of_algebraMap_eq' rfl
  suffices hx : x ∈ H' by
    obtain ⟨a, ha⟩ := hx
    exact ⟨a, congrArg (fun z : E => (z : ℂ)) ha⟩
  rw [← IsGalois.fixedField_fixingSubgroup H', IntermediateField.mem_fixedField_iff]
  intro σ hσ
  by_contra hne
  have hfix (z : H) : σ (algebraMap H E z) = algebraMap H E z :=
    (IntermediateField.mem_fixingSubgroup_iff H' σ).mp hσ (e z) ⟨z, rfl⟩
  let f := IsScalarTower.toAlgHom ℤ E ℂ
  have hxint : IsIntegral ℤ x := (isIntegral_algHom_iff f f.injective).mp hj
  let a : 𝓞 E := ⟨x, hxint⟩
  let b : 𝓞 E := σ • a - a
  let D : Ideal (𝓞 E) := Ideal.span {b}
  have hD : D ≠ ⊥ := by
    intro hz
    have hb0 : b = 0 := Ideal.span_singleton_eq_bot.mp hz
    exact hne (sub_eq_zero.mp (congrArg (fun y : 𝓞 E => (y : E)) hb0))
  let S := Finset.range (max O.conductor.absNorm D.absNorm + 1)
  obtain ⟨p, hp, hpS, Q, hQ, hQp, _, hFrob⟩ := ZInQ.Contrib.chebotarevExists E S σ
  let : Fact p.Prime := ⟨hp⟩
  let : Q.IsPrime := hQ
  let : Q.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hQp.symm⟩
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (rational_prime_span_ne_bot hp) Q
  let : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ0 hQ
  have hpgt : max O.conductor.absNorm D.absNorm < p := by
    simpa only [S, Finset.mem_range, not_lt, Nat.succ_le_iff] using hpS
  obtain ⟨P, hPm, hPnorm, hsplit⟩ :=
    splitPrime_of_frob_fixes_ringClass O p Q ((le_max_left _ _).trans_lt hpgt) hFrob hfix
  let : (P : Ideal (𝓞 K)).IsMaximal := hPm
  let k := 𝓞 E ⧸ Q
  let : Field k := Ideal.Quotient.field Q
  let r := Ideal.Quotient.mk Q
  have hchar : (p : k) = 0 := by
    rw [← map_natCast r, Ideal.Quotient.eq_zero_iff_mem, ← Int.cast_natCast]
    change (p : ℤ) ∈ Q.under ℤ
    rw [hQp]
    exact Ideal.subset_span (Set.mem_singleton _)
  let : CharP k p := (CharP.charP_iff_prime_eq_zero hp).mpr hchar
  let v : (𝓞 E) →+* ℂ := E.val.toRingHom.comp (algebraMap (𝓞 E) E)
  have hv := singularModulus_reduction_pow_eq_of_split O hk hc κ I p P
    hPnorm hsplit v (E.val.injective.comp RingOfIntegers.coe_injective) r a rfl
  have hqa := hFrob.mk_apply a
  change r (σ • a) = r a ^ Nat.card (ℤ ⧸ Q.under ℤ) at hqa
  rw [Ideal.natCard_quotient_under_of_liesOver (p := p) Q, hv] at hqa
  have hb : b ∈ Q := Ideal.Quotient.eq.mp hqa
  exact (not_mem_of_norm_lt p Q D hD ((le_max_right _ _).trans_lt hpgt))
    ((Ideal.span_singleton_le_iff_mem Q).mpr hb)


end ZInQ.Manuscript.RC.CMField2

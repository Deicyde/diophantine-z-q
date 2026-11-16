import ZInQKernel.Contrib.OneProof.SGRDirectNV

set_option linter.style.haveILetI false

noncomputable section

open Polynomial

namespace SGRDirect

section Ram

variable {E : Type} [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
  [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]

/-- The inclusion of the integral closure of `ℚ[X]` in an intermediate field into that in `E`. -/
def incl (K' : IntermediateField (RatFunc ℚ) E) :
    integralClosure ℚ[X] K' →+* integralClosure ℚ[X] E where
  toFun x := ⟨((x : K') : E), by
    have h := x.2
    exact h.map (IsScalarTower.toAlgHom ℚ[X] K' E)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

example (K' : IntermediateField (RatFunc ℚ) E) : IsDedekindDomain (integralClosure ℚ[X] K') :=
  integralClosure.isDedekindDomain (A := ℚ[X]) (K := RatFunc ℚ) (L := K')


theorem ramifiedSqrtInertia : RamifiedSqrtInertia := by
  intro E _ _ _ _ _ _ b c hc s hs Q hQ hQu he σ hσ hσs
  by_contra hne
  haveI := hQ
  -- the base `A = ℚ[X]`, `(integralClosure ℚ[X] E)` its integral closure in `E`, `G = Gal(E/ℚ(X))`
  haveI hinjE : Module.IsTorsionFree ℚ[X] E := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
    exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
  haveI : IsFractionRing (integralClosure ℚ[X] E) E := IsIntegralClosure.isFractionRing_of_finite_extension ℚ[X] (RatFunc ℚ) E _
  haveI : SMulCommClass Gal(E/RatFunc ℚ) ℚ[X] E := ⟨fun g a x => by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E, AlgEquiv.commutes]⟩
  haveI hG : IsGaloisGroup Gal(E/RatFunc ℚ) ℚ[X] (integralClosure ℚ[X] E) :=
    IsGaloisGroup.of_isFractionRing Gal(E/RatFunc ℚ) ℚ[X] (integralClosure ℚ[X] E) (RatFunc ℚ) E
  -- the intermediate field fixed by `σ` and its ring of integers `A'`
  set K' : IntermediateField (RatFunc ℚ) E := IntermediateField.fixedField (Subgroup.zpowers σ)
  set A' := integralClosure ℚ[X] K'
  haveI : IsDedekindDomain A' := integralClosure.isDedekindDomain (A := ℚ[X]) (K := RatFunc ℚ) (L := K')
  letI : Algebra A' (integralClosure ℚ[X] E) := (incl K').toAlgebra
  haveI : IsScalarTower ℚ[X] A' (integralClosure ℚ[X] E) := IsScalarTower.of_algebraMap_eq (fun a => by
    apply Subtype.ext
    show algebraMap ℚ[X] E a = (((algebraMap ℚ[X] A' a : A') : K') : E)
    rw [IsScalarTower.algebraMap_apply ℚ[X] K' E]
    rfl)
  have hincl_inj : Function.Injective (algebraMap A' (integralClosure ℚ[X] E)) := by
    intro x y hxy
    have h1 : (((x : K') : E)) = (((y : K') : E)) :=
      congrArg (fun z : (integralClosure ℚ[X] E) => (z : E)) hxy
    exact Subtype.ext (Subtype.ext h1)
  have hQE : Function.Injective (algebraMap ℚ[X] E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mp hinjE
  have hQB : Function.Injective (algebraMap ℚ[X] (integralClosure ℚ[X] E)) := by
    intro x y h
    apply hQE
    rw [IsScalarTower.algebraMap_apply ℚ[X] (integralClosure ℚ[X] E) E x,
      IsScalarTower.algebraMap_apply ℚ[X] (integralClosure ℚ[X] E) E y, h]
  have hQA' : Function.Injective (algebraMap ℚ[X] A') := by
    intro x y h
    apply hQB
    rw [IsScalarTower.algebraMap_apply ℚ[X] A' (integralClosure ℚ[X] E) x,
      IsScalarTower.algebraMap_apply ℚ[X] A' (integralClosure ℚ[X] E) y, h]
  haveI : FaithfulSMul ℚ[X] A' := (faithfulSMul_iff_algebraMap_injective _ _).mpr hQA'
  haveI : Module.IsTorsionFree ℚ[X] A' := by
    rw [Module.isTorsionFree_iff_faithfulSMul]; infer_instance
  haveI : FaithfulSMul A' (integralClosure ℚ[X] E) := (faithfulSMul_iff_algebraMap_injective A' (integralClosure ℚ[X] E)).mpr hincl_inj
  haveI hH : IsGaloisGroup (fixingSubgroup Gal(E/RatFunc ℚ) (Set.range (algebraMap A' (integralClosure ℚ[X] E)))) A' (integralClosure ℚ[X] E) :=
    IsGaloisGroup.of_isScalarTower Gal(E/RatFunc ℚ) ℚ[X] (integralClosure ℚ[X] E) A'
  set H' := fixingSubgroup Gal(E/RatFunc ℚ) (Set.range (algebraMap A' (integralClosure ℚ[X] E))) with hH'def
  have hσK' : ∀ x : E, x ∈ K' → σ x = x := fun x hx =>
    (IntermediateField.mem_fixedField_iff _ _).1 hx σ (Subgroup.mem_zpowers σ)
  have hσH' : σ ∈ H' := by
    rw [hH'def, mem_fixingSubgroup_iff]
    rintro _ ⟨a, rfl⟩
    apply Subtype.ext
    show σ (((a : K') : E)) = ((a : K') : E)
    exact hσK' _ (a : K').2
  -- the instances of the cardinality formula
  haveI : Module.Finite ℚ[X] (integralClosure ℚ[X] E) := IsIntegralClosure.finite ℚ[X] (RatFunc ℚ) E (integralClosure ℚ[X] E)
  haveI : Module.Finite A' (integralClosure ℚ[X] E) := Module.Finite.of_restrictScalars_finite ℚ[X] A' (integralClosure ℚ[X] E)
  haveI : Module.IsTorsionFree A' (integralClosure ℚ[X] E) := by
    rw [Module.isTorsionFree_iff_faithfulSMul]; infer_instance
  haveI : Algebra.IsIntegral A' (integralClosure ℚ[X] E) := Algebra.IsInvariant.isIntegral A' (integralClosure ℚ[X] E) H'
  set Q' : Ideal A' := Q.under A' with hQ'def
  haveI : Q'.IsPrime := Ideal.IsPrime.under A' Q
  haveI : Q.LiesOver Q' := ⟨rfl⟩
  haveI : CharZero Q'.ResidueField := by
    let f : ℚ →+* Q'.ResidueField :=
      ((algebraMap A' Q'.ResidueField).comp (algebraMap ℚ[X] A')).comp Polynomial.C
    exact charZero_of_injective_ringHom f.injective
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := H') Q' Q
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx Q' Q H'] at hcard
  -- `σ` lies in the inertia of `Q` in `H'`, and is nontrivial
  have hσI : (⟨σ, hσH'⟩ : H') ∈ Q.inertia H' := by
    intro x
    obtain ⟨c', hc', hc'Q⟩ := hσ x
    have : (⟨σ, hσH'⟩ : H') • x = c' := by
      apply Subtype.ext
      rw [hc']
      rfl
    rw [this]
    exact hc'Q
  have hIne : Q.inertia H' ≠ ⊥ := by
    intro h
    have h1 : (⟨σ, hσH'⟩ : H') ∈ (⊥ : Subgroup H') := h ▸ hσI
    rw [Subgroup.mem_bot] at h1
    exact hne (congrArg Subtype.val h1)
  have h2le : 1 < Q.ramificationIdx A' := by
    rw [← hcard]
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hIne
  -- the tower `ℚ[X] ⊆ A' ⊆ B`
  have htow := Ideal.ramificationIdx_tower (R := ℚ[X]) Q' Q
  have he0 : Q.ramificationIdx ℚ[X] ≠ 0 := by
    rintro h0
    rw [h0, zero_dvd_iff] at he
    exact two_ne_zero he
  have he2 : Q.ramificationIdx ℚ[X] ≤ 2 := Nat.le_of_dvd two_pos he
  have he1 : Q'.ramificationIdx ℚ[X] = 1 := by
    have hpos : Q'.ramificationIdx ℚ[X] ≠ 0 := by
      intro h0; rw [htow, h0, zero_mul] at he0; exact he0 rfl
    rw [htow] at he2
    have : Q'.ramificationIdx ℚ[X] * 2 ≤ 2 :=
      le_trans (Nat.mul_le_mul_left _ h2le) he2
    omega
  -- `s` lies in `A'`
  have hsK' : s ∈ K' := by
    rw [IntermediateField.mem_fixedField_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih =>
      rw [zpow_add_one, AlgEquiv.mul_apply, hσs, ih (Subgroup.zpow_mem_zpowers σ n)]
    | pred n ih =>
      have h1 : (σ ^ (-(n : ℤ) - 1)) (σ s) = (σ ^ (-(n : ℤ))) s := by
        rw [← AlgEquiv.mul_apply, ← zpow_add_one, sub_add_cancel]
      rw [hσs] at h1
      rw [h1, ih (Subgroup.zpow_mem_zpowers σ _)]
  have hintE : IsIntegral ℚ[X] s := by
    refine ⟨X ^ 2 - Polynomial.C (C c * (X - C b)), monic_X_pow_sub_C _ (by norm_num), ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, hs, sub_self]
  have hintK : IsIntegral ℚ[X] (⟨s, hsK'⟩ : K') := by
    exact isIntegral_algebraMap_iff.mp hintE
  set s' : A' := ⟨⟨s, hsK'⟩, hintK⟩ with hs'def
  have hs'B : ((algebraMap A' (integralClosure ℚ[X] E) s' : integralClosure ℚ[X] E) : E) = s := rfl
  have hs'sq : s' ^ 2 = algebraMap ℚ[X] A' (C c * (X - C b)) := by
    apply hincl_inj
    apply Subtype.ext
    rw [map_pow, ← IsScalarTower.algebraMap_apply]
    show (((algebraMap A' (integralClosure ℚ[X] E) s' : integralClosure ℚ[X] E) : E)) ^ 2 = _
    rw [hs'B, hs]
    rfl
  -- `s' ∈ Q'`
  have hpQ : C c * (X - C b) ∈ Q.under ℚ[X] := by
    rw [hQu, Ideal.mem_span_singleton]
    exact dvd_mul_left _ _
  have hs'Q : s' ∈ Q' := by
    apply (inferInstance : Q'.IsPrime).mem_of_pow_mem 2
    rw [hs'sq, ← Ideal.mem_comap, ← Ideal.under_def, hQ'def, Ideal.under_under]
    exact hpQ
  -- `p A' ⊆ Q'²`
  have hle : Ideal.map (algebraMap ℚ[X] A') (Ideal.span {X - C b}) ≤ Q' ^ 2 := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨f, hf, rfl⟩
    rw [Set.mem_singleton_iff] at hf
    subst hf
    have : algebraMap ℚ[X] A' (X - C b) = algebraMap ℚ[X] A' (C c⁻¹) * s' ^ 2 := by
      rw [hs'sq, ← map_mul, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hs'Q 2)
  -- contradiction with `e(Q' | p) = 1`
  haveI : Q'.LiesOver (Ideal.span {X - C b}) := ⟨by rw [hQ'def, Ideal.under_under, hQu]⟩
  have hp0 : (Ideal.span {X - C b} : Ideal ℚ[X]) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact X_sub_C_ne_zero b
  have he1' := Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {X - C b}) Q' hp0
  rw [he1] at he1'
  have h2mem : 2 ∈ {n | Ideal.map (algebraMap ℚ[X] A') (Ideal.span {X - C b}) ≤ Q' ^ n} := hle
  by_cases hbdd : BddAbove {n | Ideal.map (algebraMap ℚ[X] A') (Ideal.span {X - C b}) ≤ Q' ^ n}
  · have := le_csSup hbdd h2mem
    rw [Ideal.ramificationIdx'] at he1'
    omega
  · rw [Ideal.ramificationIdx', Nat.sSup_of_not_bddAbove hbdd] at he1'
    exact zero_ne_one he1'

end Ram

end SGRDirect
#print axioms SGRDirect.ramifiedSqrtInertia

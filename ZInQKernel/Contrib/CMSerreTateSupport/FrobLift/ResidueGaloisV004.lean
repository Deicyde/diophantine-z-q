import ZInQKernel.Contrib.CMSerreTateSupport.FrobLift.FrobeniusActionV001

/-!
# The residue field of `w` and the surjectivity of the residue Galois map

With `B` the integral closure of `O` in `Ω` and `Q = 𝔪_w ∩ B`, the natural map `B/Q → k_w` to the
residue field of `w` is an isomorphism (unit denominators give surjectivity). Consequently the
residue Galois map of the decomposition group, `D_w → Aut(k_w)` (the action whose kernel is
Mathlib's `inertiaSubgroup`), hits every ring automorphism of `k_w` fixing the image of `O`; and a
Frobenius lift acts on `k_w` by `t ↦ t^q`.
-/

noncomputable section

namespace FrobLift

open scoped Pointwise

attribute [local instance] primeQ_liesOver

variable {K : Type} [Field K] [NumberField K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {w : ValuationSubring Ω}

/-- `B → w`. -/
def incB (hw : w.comap (algebraMap K Ω) = O) : integralClosure O Ω →+* w :=
  (algebraMap (integralClosure O Ω) Ω).codRestrict w (intClosure_mem hw)

/-- `O → w`. -/
def incO (hw : w.comap (algebraMap K Ω) = O) : O →+* w :=
  (incB hw).comp (algebraMap O (integralClosure O Ω))

omit [NumberField K] [IsDiscreteValuationRing O] [IsAlgClosure K Ω] in
theorem incO_coe (hw : w.comap (algebraMap K Ω) = O) (a : O) :
    ((incO hw a : w) : Ω) = algebraMap K Ω a := by
  show algebraMap O Ω a = _
  rw [IsScalarTower.algebraMap_apply O K Ω]
  rfl

theorem primeQ_isMaximal (hw : w.comap (algebraMap K Ω) = O) : (primeQ hw).IsMaximal :=
  Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap O (integralClosure O Ω))
    (fun x => Algebra.IsIntegral.isIntegral x) (primeQ hw)
    (by rw [← Ideal.under_def, ← Ideal.over_def (primeQ hw) (IsLocalRing.maximalIdeal O)];
        infer_instance)

attribute [local instance] primeQ_isMaximal

/-- The map `B/Q → k_w`. -/
def resB (hw : w.comap (algebraMap K Ω) = O) :
    integralClosure O Ω ⧸ primeQ hw →+* IsLocalRing.ResidueField w :=
  Ideal.Quotient.lift (primeQ hw) ((IsLocalRing.residue w).comp (incB hw)) (fun b hb => by
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    exact hb)

omit [NumberField K] [IsDiscreteValuationRing O] [IsAlgClosure K Ω] in
theorem resB_mk (hw : w.comap (algebraMap K Ω) = O) (b : integralClosure O Ω) :
    resB hw (Ideal.Quotient.mk _ b) = IsLocalRing.residue w (incB hw b) := rfl

omit [NumberField K] [IsDiscreteValuationRing O] [IsAlgClosure K Ω] in
theorem residue_incB_ne_zero (hw : w.comap (algebraMap K Ω) = O) {s : integralClosure O Ω}
    (hs : w.valuation (s : Ω) = 1) : IsLocalRing.residue w (incB hw s) ≠ 0 := by
  rw [Ne, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  show ¬ w.valuation (s : Ω) < 1
  rw [hs]
  exact lt_irrefl 1

/-- **`B/Q ≅ k_w`.** -/
theorem resB_bijective (hw : w.comap (algebraMap K Ω) = O) : Function.Bijective (resB hw) := by
  constructor
  · refine (injective_iff_map_eq_zero (resB hw)).mpr ?_
    intro y hy
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [resB_mk, IsLocalRing.residue_eq_zero_iff] at hy
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hy
  intro r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨s, a, hs, ha⟩ := exists_unit_denom_intClosure hw x.2
  have hs0 := residue_incB_ne_zero hw hs
  have hsQ : (Ideal.Quotient.mk (primeQ hw) s) ≠ 0 := by
    intro h
    apply hs0
    rw [← resB_mk, h, map_zero]
  obtain ⟨t, ht⟩ := Ideal.Quotient.exists_inv hsQ
  refine ⟨Ideal.Quotient.mk _ a * t, ?_⟩
  have h1 : IsLocalRing.residue w (incB hw s) * resB hw t = 1 := by
    rw [← resB_mk, ← map_mul, ht, map_one]
  have h2 : IsLocalRing.residue w (incB hw s) * IsLocalRing.residue w x =
      IsLocalRing.residue w (incB hw a) := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext ha
  rw [map_mul, resB_mk]
  linear_combination (-(resB hw t)) * h2 + IsLocalRing.residue w x * h1

/-- **Surjectivity of the residue Galois map of the decomposition group**: every ring automorphism
of the residue field `k_w` fixing the image of `O` is the residue action of an element of the
decomposition group of `w`. -/
theorem decomposition_residueField_surjective (hw : w.comap (algebraMap K Ω) = O)
    (ρ : IsLocalRing.ResidueField w ≃+* IsLocalRing.ResidueField w)
    (hρ : ∀ a : O, ρ (IsLocalRing.residue w (incO hw a)) = IsLocalRing.residue w (incO hw a)) :
    ∃ g : w.decompositionSubgroup K,
      MulSemiringAction.toRingAut (w.decompositionSubgroup K) (IsLocalRing.ResidueField w) g = ρ := by
  set B := integralClosure O Ω
  set Q := primeQ hw
  set P := IsLocalRing.maximalIdeal O
  set e := RingEquiv.ofBijective (resB hw) (resB_bijective hw)
  set τ0 : (B ⧸ Q) ≃+* (B ⧸ Q) := (e.trans ρ).trans e.symm
  have hcomm : ∀ r : O ⧸ P, τ0 (algebraMap (O ⧸ P) (B ⧸ Q) r) = algebraMap (O ⧸ P) (B ⧸ Q) r := by
    intro r
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
    have h1 : algebraMap (O ⧸ P) (B ⧸ Q) (Ideal.Quotient.mk P a) =
        Ideal.Quotient.mk Q (algebraMap O B a) := rfl
    rw [h1]
    show e.symm (ρ (e (Ideal.Quotient.mk Q (algebraMap O B a)))) = _
    rw [RingEquiv.symm_apply_eq]
    show ρ (resB hw (Ideal.Quotient.mk Q _)) = resB hw (Ideal.Quotient.mk Q _)
    rw [resB_mk]
    exact hρ a
  let τ : (B ⧸ Q) ≃ₐ[O ⧸ P] (B ⧸ Q) := AlgEquiv.ofRingEquiv hcomm
  obtain ⟨σ, hσD, hσ⟩ := decomposition_residue_surjective hw τ
  refine ⟨⟨σ, hσD⟩, ?_⟩
  have hB : ∀ b : B, IsLocalRing.residue w (incB hw (σ • b)) =
      ρ (IsLocalRing.residue w (incB hw b)) := by
    intro b
    have h := congrArg e (hσ b)
    have e1 : e (Ideal.Quotient.mk Q (σ • b)) = IsLocalRing.residue w (incB hw (σ • b)) := rfl
    have e2 : e (τ (Ideal.Quotient.mk Q b)) = ρ (IsLocalRing.residue w (incB hw b)) := by
      show e (e.symm (ρ (e (Ideal.Quotient.mk Q b)))) = _
      rw [RingEquiv.apply_symm_apply]
      rfl
    rw [← e1, ← e2]
    exact h
  ext r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  show (⟨σ, hσD⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w x = ρ (IsLocalRing.residue w x)
  rw [← IsLocalRing.ResidueField.residue_smul]
  obtain ⟨s, a, hs, ha⟩ := exists_unit_denom_intClosure hw x.2
  have hw1 : incB hw s * x = incB hw a := Subtype.ext (by
    show (s : Ω) * x = a
    exact ha)
  have hcomp : ∀ b : B, (⟨σ, hσD⟩ : w.decompositionSubgroup K) • incB hw b = incB hw (σ • b) :=
    fun b => Subtype.ext rfl
  have hw2 : (⟨σ, hσD⟩ : w.decompositionSubgroup K) • incB hw s *
      ((⟨σ, hσD⟩ : w.decompositionSubgroup K) • x) =
      (⟨σ, hσD⟩ : w.decompositionSubgroup K) • incB hw a := by
    rw [← smul_mul', hw1]
  rw [hcomp, hcomp] at hw2
  have hr := congrArg (IsLocalRing.residue w) hw2
  rw [map_mul, hB, hB] at hr
  have hs0 := residue_incB_ne_zero hw hs
  have hres : IsLocalRing.residue w x =
      IsLocalRing.residue w (incB hw a) * (IsLocalRing.residue w (incB hw s))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hs0, ← map_mul, mul_comm, hw1]
  rw [hres, map_mul, map_inv₀, eq_mul_inv_iff_mul_eq₀ ((map_ne_zero ρ).mpr hs0), mul_comm]
  exact hr

omit [NumberField K] [IsDiscreteValuationRing O] [IsAlgClosure K Ω] in
/-- A Frobenius lift acts on the residue field of `w` by `t ↦ t^q`. -/
theorem residue_frobenius {σ : Ω ≃ₐ[K] Ω} (hD : σ ∈ w.decompositionSubgroup K) {q : ℕ}
    (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ q) < 1) (x : w) :
    IsLocalRing.residue w ((⟨σ, hD⟩ : w.decompositionSubgroup K) • x) =
      IsLocalRing.residue w x ^ q := by
  rw [← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ValuationSubring.valuation_lt_one_iff]
  exact hcong x x.2

end FrobLift

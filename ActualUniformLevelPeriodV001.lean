import ActualFiniteLinearActionV001

/-!
# Uniform coprime periods on an entire original finite torsion level

The period is the order of the actual division-field restriction. It
fixes every torsion point of the level at once, not only one chosen
point. No period or factoring model is an input.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry MonObj

namespace ActualUniformLevelPeriod
open ActualFiniteLevel ActualDivisionField
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

lemma galAct_pow (A : PkgI3.AbVar K) (σ : Ω ≃ₐ[K] Ω) (r : ℕ) (x : A.Pt Ω) :
    A.galAct (σ ^ r) x = (A.galAct σ)^[r] x := by
  induction r with
  | zero => rw [pow_zero, galAct_one, Function.iterate_zero_apply]
  | succ r ih => rw [pow_succ', galAct_mul, ih, Function.iterate_succ_apply']

lemma exists_uniform_period [CharZero K] [IsAlgClosure K Ω]
    (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (hu : IsUnit (ℓ : O)) (n : ℕ)
    [Finite (torsionSubgroup A Ω (ℓ ^ n))] (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ a : Ω, a ≠ 0 → w.valuation (σ a - a) < w.valuation a) :
    ∃ r : ℕ, 0 < r ∧ Nat.Coprime r (ℓ ^ n) ∧
      ∀ x : A.Pt Ω, x ^ (ℓ ^ n) = 1 → (A.galAct σ)^[r] x = x := by
  let τ := restriction (Ω := Ω) A (ℓ ^ n) σ
  refine ⟨orderOf τ, orderOf_pos τ, ?_, ?_⟩
  · exact (WildFiniteRestriction.restriction_order_coprime O w hw ℓ Fact.out hu σ hσ
      (finiteDivisionField A (ℓ ^ n))).pow_right n
  · intro x hx
    rw [← galAct_pow]
    apply (mem_action_ker A (ℓ ^ n) (σ ^ orderOf τ)).mp
    · change action A (ℓ ^ n) (σ ^ orderOf τ) = 1
      rw [← factoredAction_restriction, map_pow]
      change factoredAction A (ℓ ^ n) (τ ^ orderOf τ) = 1
      rw [pow_orderOf_eq_one, map_one]
    · exact hx

lemma uniform_tate_coordinate_period [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (σ : Ω ≃ₐ[K] Ω) (r : ℕ)
    (h : ∀ x : A.Pt Ω, x ^ (ℓ ^ n) = 1 → (A.galAct σ)^[r] x = x)
    (t : PkgI3.Tate.T ℓ (Additive (A.Pt Ω))) :
    (PkgI3.Tate.map (MonoidHom.toAdditive (A.galAct (σ ^ r))) t).1 n = t.1 n := by
  change Additive.ofMul (A.galAct (σ ^ r) (Additive.toMul (t.1 n))) = t.1 n
  rw [galAct_pow, h _ (PkgI3.Tate.pow_smul_eq_zero t.2 n)]
  rfl

end ActualUniformLevelPeriod

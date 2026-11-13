import ZInQKernel.Contrib.T31.Main
import ZInQKernel.HDecomp.Descent.WP3

/-!
# T31 wired into its consumers

`GlueDescent.B2Q.b2_of_leaves` and `GlueWP3.b3_degree_le_QM_of_T14_T15` with the hypothesis
`hUnr : LeafUnramified` discharged by `ZInQ.Contrib.T31.leafUnramified`.
-/

namespace ZInQ.Contrib.T31

open GlueDescent.B2 GlueDescent.B2Q PkgI6

/-- `GlueDescent.B2Q.b2_of_leaves` without the leaf `LeafUnramified`. -/
theorem b2_of_leaves_T31 (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε)
    (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :
    ∃ (N : ℕ) (hN : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ),
      (∀ q : ℕ, q.Prime → q ∣ N → q ∈ T) ∧
      orderOf χ ≤ 2 * ∏ p ∈ T.filter (· ≠ 2), (p - 1) ∧
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
      ∀ x y, β x * β y = ε x y * β (x * y) :=
  b2_of_leaves hHasse hTwo hSq leafUnramified L ε hε hinf T hT hram

/-- `GlueWP3.b3_degree_le_QM_of_T14_T15` without the leaf `LeafUnramified`. -/
theorem b3_degree_le_QM_of_T14_T15_T31 (hH : BrauerHasse2C)
    (hR : BrauerReciprocity2C) (hC : LocalH2CardC) (hSq : LeafSqrtCrit)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℝ)
    (hRD : (ZInQ.heightD : ℝ) ≤ R) (hRS : ∀ p ∈ S, (p : ℝ) ≤ R) (hR12 : (10 : ℝ) ^ 12 ≤ R)
    (u : ℚ)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD)
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε) (h11 : ε 1 1 = 1)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ GlueDescent.ramSet S u → UnramifiedAt L p)
    (η : GQ →* ℂˣ) (hη : ∀ x, η x ^ 2 = 1) (hηl : IsLocallyConstant η) :
    ∃ (N : ℕ) (hN : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ)
      (L' : IntermediateField ℚ (AlgebraicClosure ℚ)),
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
      (∀ x y, β x * β y = ε x y * β (x * y)) ∧
      L ≤ L' ∧ FiniteDimensional ℚ L' ∧ IsGalois ℚ L' ∧
      (∀ σ : GQ, σ ∈ GlueDescent.B3Q.GQL L' ↔ σ ∈ GlueDescent.B3Q.GQL L ∧ β σ = 1) ∧
      (Module.finrank ℚ L' : ℝ) ≤ ZInQ.heightQ R * ZInQ.contactSupport S u :=
  GlueWP3.b3_degree_le_QM_of_T14_T15 hH hR hC hSq leafUnramified S hS R hRD hRS hR12 u L hLD
    ε hε hinf h11 hram η hη hηl

end ZInQ.Contrib.T31

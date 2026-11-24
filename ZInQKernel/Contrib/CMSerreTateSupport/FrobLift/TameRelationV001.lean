import ZInQKernel.Contrib.CMSerreTateSupport.FrobLift.FrobeniusActionV001
import ZInQKernel.Contrib.CMSerreTateSupport.TameCharacterV005
import ZInQKernel.HDecomp.Objects

/-!
# The Frobenius lift and the tame relation, in the kernel's inertia vocabulary

`K` a number field, `O ⊆ K` a discrete valuation subring, `Ω` an algebraic closure of `K`, `w` a
valuation subring of `Ω` over `O`, `q = #(O / 𝔪_O)`. There is `φ` in the decomposition group of `w`
with `φ x ≡ x^q (mod 𝔪_w)` for all `x ∈ w` (`q ≥ 2`), and for every inertia element `τ`
(`PkgI2.IsInertia`) the element `(φ τ φ⁻¹)⁻¹ τ^q` satisfies the literal wild condition
`v_w(g x - x) < v_w(x)` for all `x ≠ 0`.
-/

noncomputable section

namespace FrobLift

variable {K : Type} [Field K] [NumberField K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {w : ValuationSubring Ω}

/-- **Frobenius lift with the tame relation.** -/
theorem frobenius_lift_tame (hw : w.comap (algebraMap K Ω) = O) :
    ∃ φ : Ω ≃ₐ[K] Ω, φ ∈ w.decompositionSubgroup K ∧
      2 ≤ Nat.card (IsLocalRing.ResidueField O) ∧
      (∀ x ∈ w, w.valuation (φ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1) ∧
      ∀ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ →
        ∀ x : Ω, x ≠ 0 →
          w.valuation (((φ * τ * φ⁻¹)⁻¹ * τ ^ Nat.card (IsLocalRing.ResidueField O)) x - x) <
            w.valuation x := by
  obtain ⟨φ, hD, hcong⟩ := exists_frobenius_lift hw
  refine ⟨φ, hD, two_le_card_residueField O, hcong, fun τ hτ => ?_⟩
  exact WildTameCharacter.isWild_frobenius_of_inertia _ hτ hD hcong

/-- The same, for every element of the decomposition group satisfying the Frobenius congruence
(every Frobenius lift, not only the constructed one). -/
theorem tame_relation_of_frobenius {φ : Ω ≃ₐ[K] Ω} (hD : φ ∈ w.decompositionSubgroup K) {q : ℕ}
    (hcong : ∀ x ∈ w, w.valuation (φ x - x ^ q) < 1) (τ : Ω ≃ₐ[K] Ω) (hτ : PkgI2.IsInertia w τ) :
    ∀ x : Ω, x ≠ 0 → w.valuation (((φ * τ * φ⁻¹)⁻¹ * τ ^ q) x - x) < w.valuation x :=
  WildTameCharacter.isWild_frobenius_of_inertia q hτ hD hcong

end FrobLift

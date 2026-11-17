import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionDistributionTwo
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTraceTwoZeroConvention

/-!
# Zero-extended torsion function and the full two-division distribution

The zero-extended function `reg N a b τ` is `0` when `N` divides both `a` and `b`, and the raw
torsion logarithmic derivative `Torsion.torsionLogDerivative N a b τ` otherwise; the raw
definition is unchanged. For every positive level `N` and all integers `a, b`,
`Σ_{r,s ∈ {0,1}} reg (2N) (a + N r) (b + N s) τ = 2 reg N a b τ`.

* For admissible `(a, b)` this is the raw distribution identity (all preimages admissible).
* For `N ∣ a`, `N ∣ b` every preimage is a two-torsion label at level `2N`: the inadmissible one
  is `0` by definition, and each admissible one has raw value `0` by the two-torsion vanishing.

The raw identity fails at inadmissible images (the zero label has raw value `1/2`), so the zero
extension is needed for the unrestricted statement.
-/

noncomputable section

open Complex
open scoped Real UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionDistributionTwo

open Classical in
/-- The zero-extended torsion function. -/
def reg (N : ℕ) (a b : ℤ) (τ : ℍ) : ℂ :=
  if (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b then 0 else Torsion.torsionLogDerivative N a b τ

theorem reg_of_good {N : ℕ} {a b : ℤ} (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) (τ : ℍ) :
    reg N a b τ = Torsion.torsionLogDerivative N a b τ := by
  classical
  unfold reg
  exact ite_eq_right_of_eq_false _ _ (eq_false hg)

theorem reg_of_bad {N : ℕ} {a b : ℤ} (hb : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) (τ : ℍ) :
    reg N a b τ = 0 := by
  classical
  unfold reg
  exact ite_eq_left_of_eq_true _ _ (eq_true hb)

/-- **Full two-division distribution** for the zero-extended function, for all integer labels. -/
theorem reg_distribution_two (N : ℕ) (hN : 0 < N) (τ : ℍ) (a b : ℤ) :
    ∑ r : Fin 2, ∑ s : Fin 2, reg (2 * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ =
      2 * reg N a b τ := by
  by_cases hg : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · have : NeZero N := ⟨hN.ne'⟩
    obtain ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ := hg
    rw [reg_of_bad ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩, mul_zero]
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun s _ => ?_
    by_cases hp : ((2 * N : ℕ) : ℤ) ∣ a + N * ((r : ℕ) : ℤ) ∧
        ((2 * N : ℕ) : ℤ) ∣ b + N * ((s : ℕ) : ℤ)
    · exact reg_of_bad hp τ
    · rw [reg_of_good hp]
      exact AllLevelTraceTwoZeroConvention.half_order_zero N _ _ hp
        ⟨a' + ((r : ℕ) : ℤ), by rw [ha']; ring⟩ ⟨b' + ((s : ℕ) : ℤ), by rw [hb']; ring⟩ τ
  · rw [reg_of_good hg]
    have hterm : ∀ r s : Fin 2,
        reg (2 * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ =
          Torsion.torsionLogDerivative (2 * N) (a + N * ((r : ℕ) : ℤ)) (b + N * ((s : ℕ) : ℤ)) τ :=
      fun r s => reg_of_good (good_preimage hg r s) τ
    simp_rw [hterm]
    exact distribution_two N hN τ a b hg

end ZInQ.Contrib.HeckePrimeRationality.TorsionDistributionTwo

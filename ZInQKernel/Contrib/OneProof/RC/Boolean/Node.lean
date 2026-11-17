import ZInQKernel.Contrib.CloudB3RC53.Nodes
import ZInQKernel.Contrib.OneProof.RC.Boolean.CoefficientTransfer

/-!
# Lane RC1-boolean, part 8: the blueprint's `MissingAddressNode`, proved

The shared top layer of the proof of Theorem 5.3 isolates the missing-address argument of
Proposition `ex:limits-coefficient-transfer` (`diophantine_zq.tex` 5647–5739; tex 5666–5735, the
choice (5.10) and the estimate (5.11)) as the node `ZInQ.Contrib.CloudB3RC53.MissingAddressNode`.
This file proves it (kind PROVED) from parts 1–6:

* the blueprint's sign `sgn x g = (-1)^{⟨x, g⟩}` and coefficientwise sign evaluation are this
  lane's `signChar (dotPairing b)` and `signEval (dotPairing b)` (`sgn_eq_signChar`,
  `blueprint_signEval_eq`);
* the bounded denominators in `ClearingIdentity` give `ũ_x ∈ Λ[1/2]` (`inLambdaHalf_of_norm_le`);
* `coefficient_transfer_at` (the Boolean step at the `L_T + 2` tested coefficients, then (5.11))
  gives the address.

The node takes the pole bound at the one precision `M`, which is all the argument uses (the text's
(5.9) supplies it for every `M`). It does not restate the inequality `M − 2c > B`, which follows
from `B + 2c_det < M` and `c ≤ c_det`; `missingAddressNode_gt` records it. The decay of the
group-basis coefficients of `f` in `ClearingIdentity` (membership of `f` in `𝒪[G]`) is not used.
-/

namespace ZInQ.Manuscript.RC.Boolean

/-- The blueprint's sign `(-1)^{⟨x, g⟩}` is the sign character `χ_x(g)` of the standard pairing. -/
theorem sgn_eq_signChar {b : ℕ} (x g : Address b) :
    ZInQ.Contrib.CloudB3RC53.sgn x g = signChar (dotPairing b) x g := by
  have h : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  have hs : (∑ i, x i * g i) = (dotPairing b g) x := by
    simp only [dotPairing, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  unfold ZInQ.Contrib.CloudB3RC53.sgn signChar
  rw [hs]
  rcases h ((dotPairing b g) x) with h0 | h1
  · rw [h0]; rfl
  · rw [h1]; rfl

/-- The blueprint's coefficientwise sign evaluation is this lane's `signEval (dotPairing b)`. -/
theorem blueprint_signEval_eq {b : ℕ} (F : Address b → ℤ → ℤ_[2]) (x : Address b) (i : ℤ) :
    ZInQ.Contrib.CloudB3RC53.signEval F x i = signEval (dotPairing b) (fun g => F g i) x := by
  unfold ZInQ.Contrib.CloudB3RC53.signEval signEval
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [sgn_eq_signChar]

/-- **The missing-address node** (Proposition `ex:limits-coefficient-transfer`, tex 5666–5735,
(5.10)–(5.11); kind PROVED). With `M > c_det`, `M > B + 2c_det`, `b > (L_T + 2)(2^M − 1)`, the
clearing identity (5.9), the pole bound at `M` and a regular base with `c ≤ c_det`, some nonzero
address `x` has `v₂(ũ_x(0) − ũ_0(0)) ≥ M − 2c`. -/
theorem missingAddressNode : ZInQ.Contrib.CloudB3RC53.MissingAddressNode := by
  intro b M LT B cdet c C hcM _hBM hb hc hclear hpole hbase
  obtain ⟨_hdecay, ⟨e, he⟩, hid⟩ := hclear
  obtain ⟨hΛ, hne, hval⟩ := hbase
  have identity : ∀ (x : Address b) (n : ℤ),
      HasSum (fun k : ℕ =>
          ((signEval (dotPairing b) (fun g => C.F g (n - k)) x : ℤ_[2]) : ℚ_[2]) * C.u x k)
        ((signEval (dotPairing b) (fun g => C.D g n) x : ℤ_[2]) : ℚ_[2]) := by
    intro x n
    have h := hid x n
    simp only [blueprint_signEval_eq] at h
    exact h
  have hreg : ∀ x, InLambdaHalf (C.u x) := fun x => inLambdaHalf_of_norm_le (he x)
  have hΛ' : ∀ i : ℤ, i < 0 → signEval (dotPairing b) (fun g => C.F g i) 0 = 0 := by
    intro i hi
    rw [← blueprint_signEval_eq]
    exact hΛ i hi
  have hne' : fZeroConst (dotPairing b) C.F ≠ 0 := by
    unfold fZeroConst
    rw [← blueprint_signEval_eq]
    exact hne
  have hval' : (fZeroConst (dotPairing b) C.F).valuation = c := by
    unfold fZeroConst
    rw [← blueprint_signEval_eq]
    exact hval
  have hpole' : ∀ (x : Address b) (i : ℤ), i < -(LT : ℤ) →
      (2 : ℤ_[2]) ^ M ∣ signEval (dotPairing b) (fun g => C.F g i) x := by
    intro x i hi
    rw [← blueprint_signEval_eq]
    exact hpole x i hi
  obtain ⟨x, hx0, hest⟩ := coefficient_transfer_at (dotPairing b) identity hreg hΛ' hne' hval'
    (lt_of_le_of_lt hc hcM) hpole' (degree_sum_lt_of_lt hb)
  refine ⟨x, hx0, ?_⟩
  rw [show -((M : ℤ) - 2 * (c : ℤ)) = 2 * (c : ℤ) - M by ring]
  exact hest

/-- The inequality `M − 2c > B` of the proposition, which the node leaves implicit: it follows from
`B + 2c_det < M` and `c ≤ c_det` (tex 5657, 5688–5690). -/
theorem missingAddressNode_gt {M B cdet c : ℕ} (hBM : B + 2 * cdet < M) (hc : c ≤ cdet) :
    (B : ℤ) < (M : ℤ) - 2 * (c : ℤ) := by
  omega

end ZInQ.Manuscript.RC.Boolean

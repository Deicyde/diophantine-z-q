import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.PairJ
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_cyclicQuotientJ_variableChange_eq

/-! # The actual quotient invariant of an elliptic curve with a cyclic subgroup -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric2

variable {k : Type*} [Field k] [CharZero k] [DecidableEq k] {N : ℕ} [NeZero N]

/-- The quotient invariant is computed by the iterated Vélu quotient of the actual pair.
At each step the least prime dividing the remaining order specifies the prime-order part of
the kernel. The step uses the Vélu quotient equation (with its separate order-two formula)
and transports the remaining subgroup by the quotient formulas. The final value is
`c₄ ^ 3 / Δ` of the resulting equation. -/
noncomputable def pairQuotientJ : PairClasses k N → k :=
  Quot.lift (fun A : EnhancedCurve k N => A.equation.cyclicQuotientJ A.subgroup.val N) (by
    intro A B h
    obtain ⟨v, hv, hsub⟩ := h
    obtain ⟨V, hV, D⟩ := B
    change v • A.equation = V at hv
    subst V
    let e := Affine.Point.addEquivVariableChange A.equation v
    change e.symm.mapAddSubgroup A.subgroup.val = D.val at hsub
    refine (cyclicQuotientJ_variableChange_eq v A.equation A.subgroup.val D.val
      (fun P => ?_) N (Nat.cast_ne_zero.mpr (NeZero.ne N))).symm
    have he : Affine.Point.vcFun v A.equation.toAffine P = e P := by
      cases P <;> rfl
    rw [he, ← hsub]
    constructor
    · rintro ⟨Q, hQ, h⟩
      change e.symm Q = P at h
      rw [← h, e.apply_symm_apply]
      exact hQ
    · intro hP
      exact ⟨e P, hP, e.symm_apply_apply P⟩)

@[simp] theorem pairQuotientJ_mk (A : EnhancedCurve k N) :
    pairQuotientJ (Quot.mk _ A : PairClasses k N) =
      A.equation.cyclicQuotientJ A.subgroup.val N :=
  rfl

#print axioms pairQuotientJ
#print axioms pairQuotientJ_mk

end WeierstrassCurve.ModelLevels.ModelGeneric2

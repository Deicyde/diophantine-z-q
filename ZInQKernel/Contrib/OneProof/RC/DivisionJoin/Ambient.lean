import ZInQKernel.Contrib.OneProof.RC.Eichler.Local
import ZInQKernel.Contrib.OneProof.RC.LocalDivision.Algebra

/-!
# The ambient algebra at the detecting prime

The two quaternion presentations agree coefficient by coefficient. The comparison is
on-the-spot (c), for tex 8462–8464 and 8496–8497.
-/

namespace ZInQ.Manuscript.RC.DivisionJoin

open Eichler LocalDivision QuaternionAlgebra

variable (p : ℕ) [Fact p.Prime]

/-- The completion of the rational presentation `(-1,-p)`. -/
abbrev LocalB := Bp p (-1) (-(p : ℚ))

/-- The coefficient-preserving equivalence with the local division presentation. -/
noncomputable def ambientEquiv : LocalB p ≃ₐ[ℚ_[p]] D p where
  toFun x := ⟨x.re, x.imI, x.imJ, x.imK⟩
  invFun x := ⟨x.re, x.imI, x.imJ, x.imK⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' x y := by
    ext <;> simp [re_mul, imI_mul, imJ_mul, imK_mul]
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The same comparison over the ring of (p)-adic integers. -/
noncomputable def ambientIntegralEquiv : LocalB p ≃ₐ[ℤ_[p]] D p where
  __ := (ambientEquiv p).toRingEquiv
  commutes' _ := rfl

/-- Reduced trace in the completed rational presentation. -/
noncomputable def reducedTrace (x : LocalB p) : ℚ_[p] := 2 * x.re

/-- Reduced norm in the completed rational presentation: the scalar in `x * star x`. -/
noncomputable def reducedNorm (x : LocalB p) : ℚ_[p] := (x * star x).re

theorem ambient_trace (x : LocalB p) :
    (tr : D p → ℚ_[p]) (ambientEquiv p x) = reducedTrace p x := rfl

theorem ambient_norm (x : LocalB p) :
    (nrd : D p → ℚ_[p]) (ambientEquiv p x) = reducedNorm p x := by
  have hs : ambientEquiv p (star x) = star (ambientEquiv p x) := rfl
  change (ambientEquiv p x * star (ambientEquiv p x)).re = _
  rw [← hs, ← map_mul]
  rfl

theorem reducedNorm_formula (x : LocalB p) :
    reducedNorm p x = x.re ^ 2 + x.imI ^ 2 + (p : ℚ_[p]) * (x.imJ ^ 2 + x.imK ^ 2) := by
  rw [← ambient_norm p x, nrd_formula]
  rfl

#print axioms ambientEquiv
#print axioms ambientIntegralEquiv
#print axioms reducedTrace
#print axioms reducedNorm
#print axioms ambient_trace
#print axioms ambient_norm
#print axioms reducedNorm_formula

end ZInQ.Manuscript.RC.DivisionJoin

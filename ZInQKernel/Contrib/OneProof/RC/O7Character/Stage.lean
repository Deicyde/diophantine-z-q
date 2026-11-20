import ZInQKernel.Contrib.OneProof.RC.O7Character.Basis
import ZInQKernel.Contrib.OneProof.RC.O7Actual.Family

/-! The three arithmetic fields of the actual stage's integral support. -/

noncomputable section

open NumberField

namespace ZInQ.Manuscript.RC.O7Character

open O7Actual

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m : ℤ}

/-- The arithmetic data for `IntegralSupport` on a stage, independent of
the local half-integrality of its supported vectors. -/
structure StageIntegralArithmetic (s : StageAt O N M hN m) (D : ℤ)
    (F : Type) [Field F] [NumberField F] where
  basis : QuadraticBasis F (D * -(s.weights.m : ℤ))
  disc_neg : D * -(s.weights.m : ℤ) < 0
  disc_mod_eight : (D * -(s.weights.m : ℤ)) % 8 = 1

/-- Discriminant and integral basis on the actual level order stage. -/
def stageIntegralArithmetic (s : StageAt O N M hN m) {F : Type} [Field F]
    [NumberField F] {D : ℤ} (h₂ : Module.finrank ℚ F = 2)
    (hdisc : discr F = D * -m) (hneg : D * -m < 0) (height : (D * -m) % 8 = 1) :
    StageIntegralArithmetic s D F where
  basis := by
    rw [s.m_eq]
    exact quadraticBasis h₂ hdisc hneg (by omega)
  disc_neg := by simpa only [s.m_eq] using hneg
  disc_mod_eight := by simpa only [s.m_eq] using height

end ZInQ.Manuscript.RC.O7Character

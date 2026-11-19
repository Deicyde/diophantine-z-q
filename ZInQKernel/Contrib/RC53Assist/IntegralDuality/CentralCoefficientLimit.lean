import ZInQKernel.Contrib.RC53Assist.IntegralDuality.IntegralCoefficientLimit
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.CentralCoefficients

/-!
# The central coefficient limit and its finite constant reductions

The central full torsion supplies the actual cyclotomic character limit data.
The finite trace coefficient reduction factors through the same canonical
p-adic residue projection. This concerns coefficient lines only: no compatible
family of primitive-root trivializations, roots-of-unity Tate-module
identification, or local invariant normalization is asserted.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.DerivedKummer.CentralLocalFit (centralRoots)

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The canonical all-level limit property for the actual central coefficient line. -/
theorem centralCoefficient_isTwoAdicLimit (D : GenuineKummerData K E₀ hZ) :
    ZInQ.Contrib.RC53Assist.Finiteness.IsTwoAdicLimit (integralCoefficientProj K D.S) :=
  integralCoefficient_isTwoAdicLimit K D.S

/-- The canonical levels respect the actual central-support Galois action. -/
theorem centralCoefficient_isEquivariantLevels (D : GenuineKummerData K E₀ hZ) :
    ZInQ.Contrib.RC53Assist.Finiteness.IsEquivariantLevels (GKS K D.S)
      (integralCoefficientProj K D.S) := integralCoefficient_isEquivariantLevels K D.S

/-- The finite trace coefficient reduction is exactly the constant extension of the
canonical cyclotomic residue projection, in the fixed coefficient coordinates. -/
theorem centralTraceCoefficientReduction_factor (D : GenuineKummerData K E₀ hZ)
    (i : ℕ) (t : IntegralTate1 K D.S) :
    CharMod.equiv (Acoef i) (cycA (Acoef i) (centralRoots D i))
        (centralTraceCoefficientReduction D i t) =
      algebraMap (ZMod (2 ^ i)) (Acoef i)
        (CharMod.equiv (ZMod (2 ^ i))
          (cycS (HasTwoPowerRoots.roots (K := K) (S := D.S) i))
          (integralCoefficientProj K D.S i t)) := by
  rw [centralTraceCoefficientReduction_underlying, integralCoefficientProj_apply,
    constRed_eq_toZModPow]

end ZInQ.Contrib.RC53Assist.IntegralDuality

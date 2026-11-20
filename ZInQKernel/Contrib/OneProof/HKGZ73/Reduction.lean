import ZInQKernel.Contrib.OneProof.HKRefereed.HKRefereedConsumed
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.ModularNewformPrinted
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Descent
import ZInQKernel.Contrib.RC53Assist.G0Prints.Carayol

/-! # The rational point in Gross–Zagier (7.3)(1) and the pole argument -/

namespace ZInQ.Manuscript.HKGZ73

open ZInQ.Contrib.CloudB3RC53 (IsLContinuation)
open ZInQ.Contrib.RC53Assist.G0Prints (associatedGeometricConductorExponent)
open RC.PrintsAnalytic (IsNewformOf)
open HeckeRing.GL2 (Newform)

/-- A positive integer is the geometric conductor of `E` if its prime exponents
are the Artin conductor exponents of the cohomological Tate representations.
At a place `p` the auxiliary Tate prime `q` is distinct from `p`. -/
def IsGeometricConductorLevel (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) : Prop :=
  0 < N ∧
    ∀ (q p : ℕ) [Fact q.Prime] [Fact p.Prime], p ≠ q →
      associatedGeometricConductorExponent E q p = (N.factorization p : ℚ)

/-- **Print draft**: Gross–Zagier, Invent. Math. 84 (1986), Thm (7.3)(1), p. 231 (AI-READ).
Under the standing assumption of a weight-two newform of `E/ℚ` at its conductor,
if `L(E,1) = 0` and `L'(E,1) ≠ 0`, then `E(ℚ)` has a point of infinite order.
The value and derivative are of the uncompleted continuation. -/
def GZ73Print : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (N : ℕ) [NeZero N] (f : Newform N 2),
    IsGeometricConductorLevel E N → IsNewformOf E f →
    ∀ F : ℂ → ℂ, IsLContinuation E F → F 1 = 0 → deriv F 1 ≠ 0 →
      ∃ P : E.toAffine.Point, ¬ IsOfFinAddOrder P

end ZInQ.Manuscript.HKGZ73

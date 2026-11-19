import ZInQKernel.Contrib.RC53Assist.IntegralDuality.ContinuousCharacterLine
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.DeterminantContinuity

/-!
# The integral cyclotomic coefficient line and actual Tate pairing

The coefficient line is the two-adic integers with their inherited topology
and the action of the existing two-adic cyclotomic character. The pairing is
the existing determinant form on the actual Tate module, read in that line.
No geometric or Galois objects are replaced.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.FibreDuality

variable (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The integral cyclotomic line with its two-adic topology. -/
abbrev IntegralTate1 : Type := ContinuousCharacterLine ℤ_[2] (cyc2 K S)

instance integralTate1_isContinuous :
    ContinuousCharacterLine.IsContinuous ℤ_[2] (cyc2 K S) :=
  ⟨continuous_coe_cyc2⟩

variable {K S} {W : WeierstrassCurve K} [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- The actual determinant form, valued in the integral cyclotomic line. -/
def integralBeta : TateS K S W →ₗ[ℤ_[2]] TateS K S W →ₗ[ℤ_[2]] IntegralTate1 K S :=
  (detT (K := K) (S := S) (W := W)).compr₂
    (ContinuousCharacterLine.equiv ℤ_[2] (cyc2 K S)).symm.toLinearMap

/-- Reading the pairing in the underlying two-adic integers recovers the source form. -/
theorem integralBeta_underlying (x y : TateS K S W) :
    ContinuousCharacterLine.equiv ℤ_[2] (cyc2 K S) (integralBeta x y) = detT x y := rfl

/-- The genuine Galois action is compatible with the integral cyclotomic pairing. -/
theorem integralBeta_galois (σ : GKS K S) (x y : TateS K S W) :
    integralBeta (σ • x) (σ • y) = σ • integralBeta x y := by
  change detT (σ • x) (σ • y) = (cyc2 K S σ : ℤ_[2]) * detT x y
  exact detT_smul σ x y

/-- Joint continuity uses the actual Tate topology and inherited coefficient topology. -/
theorem integralBeta_continuous :
    Continuous fun p : TateS K S W × TateS K S W => integralBeta p.1 p.2 :=
  (ContinuousCharacterLine.homeomorph ℤ_[2] (cyc2 K S)).symm.continuous.comp continuous_detT

/-- The integral coefficient pairing is alternating. -/
theorem integralBeta_self (x : TateS K S W) : integralBeta x x = 0 := by
  change detT x x = 0
  exact detT_self x

/-- The integral determinant adjoint is bijective. This is coefficient perfectness,
not a derived Selmer duality assertion. -/
theorem integralBeta_bijective :
    Function.Bijective (integralBeta (K := K) (S := S) (W := W)) :=
  detT_bijective

end ZInQ.Contrib.RC53Assist.IntegralDuality

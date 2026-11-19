import ZInQKernel.Contrib.RC53Assist.IntegralDuality.CentralCoefficients
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.F2Alternating

/-!
# Same-map level-one reduction of the actual central integral pairing

At level one both genuine finite Weil forms are nondegenerate alternating
forms on a group isomorphic to the two-dimensional vector space over the
field with two elements. Their equality under the actual twist isomorphism
is a consequence of uniqueness, not an extra hypothesis. The determinant
normalization unit is one at this level. Applying the existing central Tate
coefficient reduction and the cyclotomic trace coefficient reduction therefore
identifies the integral pairing with the existing finite Weil pairing.

Only level one is asserted. No higher-level quadratic-twist Weil naturality
or global duality statement is claimed.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open NumberField IsDedekindDomain TensorProduct
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.FibreDuality
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.DerivedKummer.CentralLocalFit (centralRoots)

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The actual twist isomorphism preserves the genuine finite Weil form at level one. -/
theorem centralWeil_level_one (D : GenuineKummerData K E₀ hZ)
    (P Q : Lev K D.S (centralCurve D) 1) :
    weilS (centralCurve D) (centralRoots D 1) P Q =
      weilS D.W (centralRoots D 1)
        (globalTwistTorsEquiv D.W D.s D.hs D.hs0 1 P)
        (globalTwistTorsEquiv D.W D.s D.hs D.hs0 1 Q) := by
  obtain ⟨f⟩ := torsS_addEquiv_prod (centralCurve D) (centralFullTorsion D 1)
  exact f2Alternating_apply_addEquiv f
    (globalTwistTorsEquiv D.W D.s D.hs D.hs0 1)
    (weilS (centralCurve D) (centralRoots D 1)) (weilS D.W (centralRoots D 1))
    (weilS_self (centralRoots D 1)) (weilS_self (centralRoots D 1))
    (weilS_injective (centralCurve D) (centralRoots D 1) (centralFullTorsion D 1))
    (weilS_injective D.W (centralRoots D 1) (D.hFull 1)) P Q

/-- The source determinant normalization equals the genuine Weil form at level one. -/
theorem centralDet_level_one (D : GenuineKummerData K E₀ hZ)
    (x y : TateS K D.S (centralCurve D)) :
    PadicInt.toZModPow 1 (detT x y) =
      weilS D.W (centralRoots D 1)
        (globalTwistTorsEquiv D.W D.s D.hs D.hs0 1 (projLev 1 x))
        (globalTwistTorsEquiv D.W D.s D.hs D.hs0 1 (projLev 1 y)) := by
  have hε : weilS (centralCurve D) (centralRoots D 1)
      (projLev 1 (tateBasis 0)) (projLev 1 (tateBasis 1)) = 1 :=
    zmod_two_eq_one_of_ne_zero _
      (isUnit_weilS_basis (W := centralCurve D) 1 (centralRoots D 1)).ne_zero
  have h := detT_mod_eq_weil (W := centralCurve D) 1 (centralRoots D 1) x y
  rw [hε, mul_one] at h
  exact h.trans (centralWeil_level_one D (projLev 1 x) (projLev 1 y))

/-- Same-map reduction into the literal finite cyclotomic line. The right factor is the
existing central coefficient map transported by the preserved self-inverse-character proof. -/
theorem centralPairing_level_one (D : GenuineKummerData K E₀ hZ)
    (x y : TateS K D.S (centralCurve D)) :
    centralTraceCoefficientReduction D 1 (centralIntegralBeta D x y) =
      weilPairingM (S := D.S) D.W (centralRoots D 1) (Acoef 1)
        (centralChar 1 D.s D.hs D.hs0) (centralCoefficientReduction D 1 x)
        (centralRightCoefficientEquiv D 1 (centralCoefficientReduction D 1 y)) := by
  apply (CharMod.equiv (Acoef 1) (cycA (Acoef 1) (centralRoots D 1))).injective
  rw [centralTraceCoefficientReduction_underlying, integralBeta_underlying,
    weilPairingM_apply, centralRightCoefficientEquiv_apply]
  change constRed 1 (detT x y) =
    weilA D.W (centralRoots D 1) (Acoef 1)
      ((1 : Acoef 1) ⊗ₜ[ℤ] globalTwistTorsEquiv D.W D.s D.hs D.hs0 1 (projLev 1 x))
      ((1 : Acoef 1) ⊗ₜ[ℤ] globalTwistTorsEquiv D.W D.s D.hs D.hs0 1 (projLev 1 y))
  rw [weilA_tmul, one_mul, one_mul, constRed_eq_toZModPow, centralDet_level_one]

/-- The identical coefficient equality in the fixed trivializations. -/
theorem centralPairing_level_one_underlying (D : GenuineKummerData K E₀ hZ)
    (x y : TateS K D.S (centralCurve D)) :
    constRed 1 (detT x y) =
      CharMod.equiv (Acoef 1) (cycA (Acoef 1) (centralRoots D 1))
        (weilPairingM (S := D.S) D.W (centralRoots D 1) (Acoef 1)
          (centralChar 1 D.s D.hs D.hs0) (centralCoefficientReduction D 1 x)
          (centralRightCoefficientEquiv D 1 (centralCoefficientReduction D 1 y))) := by
  have h := congrArg (CharMod.equiv (Acoef 1) (cycA (Acoef 1) (centralRoots D 1)))
    (centralPairing_level_one D x y)
  simpa only [centralTraceCoefficientReduction_underlying, integralBeta_underlying] using h

end ZInQ.Contrib.RC53Assist.IntegralDuality

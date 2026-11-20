import ZInQKernel.Contrib.OneProof.RC.Wiring.KummerCorankOne
import ZInQKernel.Contrib.CloudB3E2Norm.KcSelSplit
import ZInQKernel.Contrib.CloudB3RC53.Finiteness.TwoInSupportCompositum

/-!
# Rank one from the finite-level Selmer description

At the signed address, the genuine data `G` already provide finite support and full two-power
torsion. The support contains the places above two by `h2_of_hasFullTwoTorsion_proof`. The
comparison `kcKummerCoefficientComparisonSigned` uses the original coefficient quotient and
Selmer complex. Thus the calibration's rank condition (tex 4005–4021) needs neither a separate
signed comparison nor `KummerCorankOneGlue` as input. The finite-level Selmer description,
the two analytic ranks, the two Milne finiteness inputs and `Prints` remain explicit.

The finite-level Selmer description is not discharged here: see Milne, *Arithmetic Duality
Theorems*, 2nd ed., Ch. I, I.3.8 (pp. 46–47), I.6.1 (p. 73) and the proof of I.6.5 (p. 76).
The fixed-level argument and identification of the original local maps are GLUE, not a literal
reading of the primary-limit display.
-/

noncomputable section

namespace ZInQ.Manuscript.RC

open NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Manuscript.RC53Assist.CentralUniversal
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.Finiteness
open ZInQ.Contrib.CloudB3E2.KcSplit
open ZInQ.Contrib.RC53Assist.Calibration ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.InnerLimitArith

/-- The central first cohomology has rank one at an address of either sign, from the named
finite-level Selmer inputs and the forward theorems. The support, ellipticity, and coefficient
comparison refer to the same address data. Kind: PROVED from the stated inputs. -/
theorem centralRankOne_of_forward_level (Pr : Prints)
    (hloc : MilneLocalFiniteness) (hglob : MilneGlobalFiniteness)
    {k : ℤ} {ℓ : ℕ} {h : ℤ} (hk : k < 0)
    (G : GenuineKummerData (QuadraticField k) (Ecurve ℓ) h)
    (hsel : KcSelOfLocFinite k G.S (curve ((ℓ : ℚ) * h)))
    (hlift : KcLocOfSel k G.S (curve ((ℓ : ℚ) * h)))
    (h1 : AnalyticRank (Etw ℓ h) 1) (h0 : AnalyticRank (Etw ℓ (h * k)) 0) :
    Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1 := by
  letI : (curve ((ℓ : ℚ) * h)).IsElliptic := isElliptic_curve_mul_of_genuineKummerData G
  letI : HasFullTwoTorsion (QuadraticField k) G.S (centralCurve G) := ⟨centralFullTorsion G⟩
  have h2 := h2_of_hasFullTwoTorsion_proof (S := G.S) (centralCurve G)
  let hFull := arithmeticCentralFullSigned ((ℓ : ℚ) * h) k G (centralCurve_eq_curve_mul G)
  let I := kcKummerCoefficientComparisonSigned ((ℓ : ℚ) * h) k G.S hFull hk G.hSfin h2
    (kcArithSelmerLevel_of k G.S _ hsel hlift)
  exact centralRankOne_of_forward_ne_mw Pr hloc hglob hk G h2 I h1 h0

end ZInQ.Manuscript.RC

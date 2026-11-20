import ZInQKernel.Contrib.OneProof.HKGZ.HKGZAuxiliary
import ZInQKernel.Contrib.OneProof.HKGZ.HKGZFactorization
import ZInQKernel.Contrib.OneProof.HKGZ.HKGZDescent
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.ModularNewformPrinted

/-! # Conditional replacement of the consumed pole input -/

namespace ZInQ.Manuscript.HKGZ

open NumberField WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.ModularWeil (LiCarayolNewformOfModular)

open Classical in
/-- Conditional substitution for the rank-one fragment. The newform extraction
`LiCarayolNewformOfModular` and `PoleCMTraceDictionary` are separate open GLUE inputs. -/
theorem hkConsumed_of_grossZagier
    (hB : PoleS12.BCDTThmA) (hNew : LiCarayolNewformOfModular)
    (hCM : PoleCMTraceDictionary) (hBFH : BFHTwistNonvanishingDraft)
    (hGZ : GrossZagierTraceDraft) (hConj : HeegnerTraceConjugationDraft) :
    HKRefereed.HKConsumed := by
  have hM := RC.PrintsAnalytic.modularNewform_of_bcdt_liCarayol hB hNew
  intro ℓ hℓ hsf h12 _h8 hMod hA
  let E := curve (ℓ : ℚ)
  have hEq : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne'
  let : E.IsElliptic := PoleRC.curve_isElliptic hEq
  obtain ⟨hw, K, hF, hNF, hK, hodd, hcop, hVal⟩ := exists_auxiliary_of_bfh hBFH hM E hA
  let : Field K := hF
  let : NumberField K := hNF
  obtain ⟨P, hP⟩ := hCM ℓ hℓ hsf h12 hMod K hK hodd
  obtain ⟨F, hFd, hFK, hF'⟩ := exists_baseChange_simple_derivative hM E K hK hodd hcop hA hVal
  have hnt := hGZ E K P hK hodd hP F hFd hFK hF'
  let : Algebra.IsQuadraticExtension ℚ K := ⟨hK.1⟩
  have hcard := Algebra.IsQuadraticExtension.card_algEquiv_eq_two ℚ K
  obtain ⟨σ, hσ, _⟩ := (Nat.card_eq_two_iff' (1 : K ≃ₐ[ℚ] K)).mp hcard
  exact exists_rational_of_conjugate_sub_torsion E K hK.1 hσ P hnt (hConj E K P hK hodd hP hw σ hσ)

end ZInQ.Manuscript.HKGZ

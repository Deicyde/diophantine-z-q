import ZInQKernel.Contrib.OneProof.R16Thm1
import ZInQKernel.Contrib.OneProof.BShStandardGeometry
import ZInQKernel.Contrib.OneProof.BShStandardField

/-! ON THE SPOT (provenance (c)): identify the stalk evaluation with the
finite germ value, as in the predecessor's private diamond argument. -/

noncomputable section

namespace BShTraces

open scoped MatrixGroups
open AlgebraicGeometry CategoryTheory Filter UpperHalfPlane MonoidalCategory CartesianMonoidalCategory MonObj
open LeafModCurves PkgI3 PkgI3.AbVar AfTateLam ShimuraPointDict

set_option backward.isDefEq.respectTransparency false

variable {X : Over SpecQ} [IsIntegral X.left] {jX tX : X.left.functionField} {N : ℕ}
local notation "KX" => X.left.functionField

private theorem atTau_eval (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) {τ : ℍ} {x : CPt X}
    (hx : AtTau N jX tX x τ) {a : KX} {c : ℂ} (ha : HasValue (fieldGerm hN hG τ a) c) :
    ∃ r : X.left.presheaf.stalk (complexMap x (IsLocalRing.closedPoint ℂ)),
      algebraMap _ KX r = a ∧ Scheme.stalkClosedPointTo (complexMap x) r = c := by
  obtain ⟨P, Q, hQ, rfl⟩ := exists_polynomial_fraction hG.1 a
  simp only [algEval_apply] at hQ ha ⊢
  exact regAt_iff_stalk.mp (hx P Q c hQ ((hasValue_fraction_iff hN hG τ P Q hQ c).mp ha))

theorem atTau_stalk_value (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) {τ : ℍ} {x : CPt X}
    (hx : AtTau N jX tX x τ)
    (r : X.left.presheaf.stalk (complexMap x (IsLocalRing.closedPoint ℂ))) :
    HasValue (fieldGerm hN hG τ (algebraMap _ KX r))
      (Scheme.stalkClosedPointTo (complexMap x) r) := by
  have hmem : algebraMap _ KX r ∈ finiteSubring (fieldGerm hN hG τ) := by
    by_contra h
    have hv := hasValue_inv_of_not_mem (fieldGerm hN hG τ) (fieldGerm_meromorphic hN hG τ) h
    obtain ⟨s, hs, h₀⟩ := atTau_eval hN hG hx hv
    have hn : algebraMap _ KX r ≠ 0 := fun hh => h (hh ▸ (finiteSubring _).zero_mem)
    have hrs : r * s = 1 := IsFractionRing.injective _ KX (by
      rw [map_mul, map_one, hs]
      exact mul_inv_cancel₀ hn)
    have := congrArg (Scheme.stalkClosedPointTo (complexMap x)).hom hrs
    simp [h₀] at this
  obtain ⟨c, hc⟩ := hmem
  obtain ⟨s, hs, hv⟩ := atTau_eval hN hG hx hc
  have hsr : s = r := IsFractionRing.injective _ KX hs
  rw [hsr] at hv
  rw [hv]
  exact hc

#print axioms atTau_eval
#print axioms atTau_stalk_value

end BShTraces

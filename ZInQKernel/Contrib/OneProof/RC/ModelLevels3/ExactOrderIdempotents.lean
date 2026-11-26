import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.ExactOrderGrading
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # The discriminant unit and complement idempotents on the cover -/

namespace WeierstrassCurve.ModelLevels

open ModelTorsion

variable {R : Type*} [CommRing R] {n : ℕ} (hn : IsUnit ((n + 2 : ℕ) : ShortBase R))
  [Algebra R (ExactOrderAlgebra (shortFamily R) hn)]
  [IsScalarTower R (ShortBase R) (ExactOrderAlgebra (shortFamily R) hn)]

/-- The discriminant unit of the short family in the exact-order cover. -/
noncomputable def shortExactOrderDiscriminantUnit : (ExactOrderAlgebra (shortFamily R) hn)ˣ :=
  Units.map (algebraMap (ShortBase R) (ExactOrderAlgebra (shortFamily R) hn)) (shortFamily R).Δ'

/-- The discriminant unit lies in weight twelve. -/
theorem shortExactOrderDiscriminantUnit_mem :
    (shortExactOrderDiscriminantUnit hn : ExactOrderAlgebra (shortFamily R) hn) ∈
      shortExactOrderGrading hn 12 := by
  change algebraMap (ShortBase R) (ExactOrderAlgebra (shortFamily R) hn) (shortFamily R).Δ ∈ _
  exact shortExactOrderDiscriminant_mem hn

private theorem localization_idempotent_eq_one {A : Type*} [CommRing A] {e x : A}
    (hx : IsIdempotentElem x) (hdiv : x ∣ e) :
    algebraMap A (ClopenFactor e) x = 1 := by
  let f := algebraMap A (ClopenFactor e)
  have hu : IsUnit (f e) := IsLocalization.Away.algebraMap_isUnit e
  have hunit := isUnit_of_dvd_unit (map_dvd f hdiv) hu
  exact (IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp (hx.map f)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- After localizing to exact order, each proper-divisor complement
idempotent equals the identity. -/
theorem exactOrder_divisorIdempotent_eq_one {d : ℕ} (hd : d ∣ n + 2) (hlt : d < n + 2) :
    affineToExactOrder (shortFamily R) hn (divisorIdempotent (shortFamily R) hn hd) = 1 := by
  classical
  let W := shortFamily R
  let D := {m // m ∈ (n + 2).properDivisors}
  let i : D := ⟨d, Nat.mem_properDivisors.mpr ⟨hd, hlt⟩⟩
  let F : D → AffineTorsionAlgebra W (n + 2) :=
    fun j => divisorIdempotent W hn (Nat.mem_properDivisors.mp j.property).1
  have hdiv : F i ∣ ∏ j ∈ (n + 2).properDivisors.attach, F j :=
    Finset.dvd_prod_of_mem F (Finset.mem_attach (n + 2).properDivisors i)
  have hdiv' : divisorIdempotent W hn hd ∣ exactOrderIdempotent W hn := hdiv
  change algebraMap _ (ClopenFactor (exactOrderIdempotent W hn)) (divisorIdempotent W hn hd) = 1
  exact localization_idempotent_eq_one (divisorIdempotent_spec W hn hd).1 hdiv'

/-- The images of the proper-divisor idempotents on the exact-order cover
are homogeneous of degree zero. -/
theorem exactOrder_divisorIdempotent_mem {d : ℕ} (hd : d ∣ n + 2) (hlt : d < n + 2) :
    affineToExactOrder (shortFamily R) hn (divisorIdempotent (shortFamily R) hn hd) ∈
      shortExactOrderGrading hn 0 := by
  rw [exactOrder_divisorIdempotent_eq_one hn hd hlt]
  exact SetLike.one_mem_graded (presentationWeight shortCoordinateWeight (exactOrderShortPresentation hn))

#print axioms shortExactOrderDiscriminantUnit
#print axioms shortExactOrderDiscriminantUnit_mem
#print axioms localization_idempotent_eq_one
#print axioms exactOrder_divisorIdempotent_eq_one
#print axioms exactOrder_divisorIdempotent_mem

end WeierstrassCurve.ModelLevels

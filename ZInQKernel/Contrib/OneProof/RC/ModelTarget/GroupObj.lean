import ZInQKernel.Contrib.OneProof.RC.ModelTarget.GroupLaw
import ZInQKernel.Contrib.NeronC.NeronGroup

/-! The projective cubic of a unit-discriminant equation over a noetherian domain, smooth
over the base, is a group object over the base; at the detector this is the good cubic of
the fixed equation. The axioms are checked at field points, where they are the group laws
of Mathlib's affine points. On the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open WeierstrassCurve WeierstrassCurve.ModelTorsion

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ZInQ.Manuscript.RC.ModelTarget

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem isReduced_of_smooth_hom {T : Over (Spec (.of R))} (h : Smooth T.hom) : IsReduced T.left :=
  ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian.solution
    T.hom

variable (W : WeierstrassCurve R) [W.IsElliptic]

/-- The group object structure of the smooth projective cubic over the base. -/
@[instance_reducible]
def cubicGrp (hs : Smooth (projStructure W)) : GrpObj (cubic W) := by
  have hX : Smooth (cubic W).hom := hs
  have hU := ZInQ.Contrib.NeronC.smooth_tensorUnit (Spec (.of R))
  have hXX := ZInQ.Contrib.NeronC.smooth_tensor _ _ hX hX
  haveI : IsReduced (cubic W).left := isReduced_of_smooth_hom hX
  haveI : IsReduced (cubic W ⊗ cubic W).left := isReduced_of_smooth_hom hXX
  haveI : IsReduced ((cubic W ⊗ cubic W) ⊗ cubic W).left :=
    isReduced_of_smooth_hom (ZInQ.Contrib.NeronC.smooth_tensor _ _ hXX hX)
  haveI : IsReduced (𝟙_ (Over (Spec (.of R))) ⊗ cubic W).left :=
    isReduced_of_smooth_hom (ZInQ.Contrib.NeronC.smooth_tensor _ _ hU hX)
  haveI : IsReduced (cubic W ⊗ 𝟙_ (Over (Spec (.of R)))).left :=
    isReduced_of_smooth_hom (ZInQ.Contrib.NeronC.smooth_tensor _ _ hX hU)
  refine
    { one := cubicOne W
      mul := cubicMul W
      inv := cubicInv W
      one_mul := ?_
      mul_one := ?_
      mul_assoc := ?_
      left_inv := ?_
      right_inv := ?_ }
  · apply cubicHom_ext W
    intro F _ g p
    classical
    conv_lhs =>
      rw [← lift_comp_fst_snd p, lift_whiskerRight_assoc]
    rw [val_mul, leftUnitor_hom]
    rw [show p ≫ fst _ _ = toUnit _ from isTerminalTensorUnit.hom_ext _ _, val_one, zero_add]
  · apply cubicHom_ext W
    intro F _ g p
    classical
    conv_lhs =>
      rw [← lift_comp_fst_snd p, lift_whiskerLeft_assoc]
    rw [val_mul, rightUnitor_hom]
    rw [show p ≫ snd _ _ = toUnit _ from isTerminalTensorUnit.hom_ext _ _, val_one, add_zero]
  · apply cubicHom_ext W
    intro F _ g p
    classical
    let t := p ≫ fst _ _
    have hp : p = lift (lift (t ≫ fst _ _) (t ≫ snd _ _)) (p ≫ snd _ _) := by
      simp only [t, lift_comp_fst_snd]
    conv_lhs =>
      rw [hp, lift_whiskerRight_assoc, val_mul, val_mul]
    conv_rhs =>
      rw [hp, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc, val_mul, val_mul]
    exact add_assoc _ _ _
  · apply cubicHom_ext W
    intro F _ g p
    classical
    rw [comp_lift_assoc, Category.comp_id, val_mul, val_inv, neg_add_cancel, ← Category.assoc,
      comp_toUnit, val_one]
  · apply cubicHom_ext W
    intro F _ g p
    classical
    rw [comp_lift_assoc, Category.comp_id, val_mul, val_inv, add_neg_cancel, ← Category.assoc,
      comp_toUnit, val_one]

variable (ell : ℕ) [Fact ell.Prime]

/-- **The group law on the detector's good cubic.** For an integral Weierstrass equation
whose discriminant is prime to the detector `ℓ ≥ 5`, the projective cubic of its
localization at `ℓ` is a group object over the detector ring. -/
@[instance_reducible]
def weierstrassModelGrp (h₅ : 5 ≤ ell) (W₀ : WeierstrassCurve ℤ) (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ) :
    GrpObj (ModelNeron.weierstrassModel ell (W₀.map (algebraMap ℤ (LocalIntegers ell)))) :=
  haveI := ModelNeron.isElliptic_at_detector ell W₀ hΔ
  cubicGrp (W₀.map (algebraMap ℤ (LocalIntegers ell))) (weierstrassModel_smooth ell h₅ W₀ hΔ)

/-- **The Néron property of the detector's good cubic**, from its smoothness and group law
(`ModelNeron.weierstrassModel_neron`). -/
theorem weierstrassModel_isNeron (h₅ : 5 ≤ ell) (W₀ : WeierstrassCurve ℤ)
    (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ) :
    CToPrinted.IsNeronModelOver (LocalIntegers ell) ℚ
      (ModelNeron.weierstrassModel ell (W₀.map (algebraMap ℤ (LocalIntegers ell)))) := by
  letI := weierstrassModelGrp ell h₅ W₀ hΔ
  haveI := weierstrassModel_smooth ell h₅ W₀ hΔ
  exact ModelNeron.weierstrassModel_neron ell _

#print axioms isReduced_of_smooth_hom
#print axioms cubicGrp
#print axioms weierstrassModelGrp
#print axioms weierstrassModel_isNeron

end ZInQ.Manuscript.RC.ModelTarget

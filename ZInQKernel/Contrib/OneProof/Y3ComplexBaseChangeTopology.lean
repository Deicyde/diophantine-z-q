import ZInQKernel.Contrib.OneProof.Y3ComplexPointTopology
import ZInQKernel.Contrib.OneProof.SmoothCurveComplexCompact
import ZInQKernel.Contrib.CloudB3W17Hodge.Bridge

/-! The period topology on the rational scheme agrees with the native
analytification topology after change of base to the complex numbers. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open LeafQM.AV
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Y3P1j

variable (X : Over (Spec (CommRingCat.of ℚ)))

abbrev complexBaseChange : Over (Spec (CommRingCat.of ℂ)) :=
  Over.mk (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))

/-- The literal base-change point correspondence at the complex field. -/
def complexPointBaseChangeEquiv : ComplexPoint (complexBaseChange X) ≃ (fieldPt ℂ ⟶ X) where
  toFun x := Over.homMk (x.left ≫ pullback.fst _ _) (by
    change (x.left ≫ pullback.fst X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))) ≫
      X.hom = Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))
    have hx : x.left ≫ pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) =
        𝟙 (Spec (CommRingCat.of ℂ)) := x.w
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx]
    exact Category.id_comp _)
  invFun y := Over.homMk (pullback.lift y.left (𝟙 _) (y.w.trans (Category.id_comp _).symm))
    (pullback.lift_snd _ _ _)
  left_inv x := Over.OverMorphism.ext (pullback.hom_ext
    (pullback.lift_fst _ _ _) ((pullback.lift_snd _ _ _).trans x.w.symm))
  right_inv y := Over.OverMorphism.ext (pullback.lift_fst _ _ _)

private theorem regVal_comp {A B : Scheme.{0}} (y : Spec (CommRingCat.of ℂ) ⟶ A)
    (f : A ⟶ B) (U : B.Opens) (s : Γ(B, U)) :
    ShimuraSplit.regVal U s (y ≫ f) = ShimuraSplit.regVal (f ⁻¹ᵁ U) (f.app U s) y := by
  by_cases h : ShimuraSplit.ptC (y ≫ f) ∈ U
  · have h' : ShimuraSplit.ptC y ∈ f ⁻¹ᵁ U := h
    rw [ShimuraSplit.regVal, dite_eq_left h, ShimuraSplit.regVal, dite_eq_left h']
    exact LeafQM.AV.Pin.ImagePlane.ev_comp _ _ h _
  · have h' : ShimuraSplit.ptC y ∉ f ⁻¹ᵁ U := h
    rw [ShimuraSplit.regVal, dite_eq_right h, ShimuraSplit.regVal, dite_eq_right h']

/-- Projecting from the complex base change is continuous for the regular
function topology on the rational complex-point set. -/
theorem continuous_complexPointBaseChangeEquiv :
    Continuous[Point.analyticTopology, complexPointTopology X] (complexPointBaseChangeEquiv X) := by
  apply continuous_generateFrom_iff.mpr
  rintro _ ⟨U, s, V, hV, rfl⟩
  let f : (complexBaseChange X).left ⟶ X.left := pullback.fst _ _
  let W := f ⁻¹ᵁ U
  let s' := f.app U s
  convert Point.isOpen_overOpen_inter_preimage W s' V hV using 1
  ext y
  have hpoint : ShimuraSplit.ptC (complexPointBaseChangeEquiv X y).left =
      f y.underlying := rfl
  change (ShimuraSplit.ptC (complexPointBaseChangeEquiv X y).left ∈ U ∧
    ShimuraSplit.regVal U s (complexPointBaseChangeEquiv X y).left ∈ V) ↔
      y.underlying ∈ W ∧ Point.evaluate W s' y ∈ V
  rw [hpoint]
  change f y.underlying ∈ U ∧ _ ↔ f y.underlying ∈ U ∧ _
  apply and_congr_right
  intro hy
  have hy' : y.underlying ∈ W := hy
  have hreg : ShimuraSplit.regVal U s (complexPointBaseChangeEquiv X y).left =
      ShimuraSplit.regVal W s' y.left := regVal_comp y.left f U s
  have he : ShimuraSplit.regVal W s' y.left = Point.evaluate W s' y := by
    have hy'' : ShimuraSplit.ptC y.left ∈ W := hy'
    rw [CloudB3W17Hodge.evaluate_eq (complexBaseChange X) y W s' hy',
      ShimuraSplit.regVal, dite_eq_left hy'']
    exact congrArg (fun ψ : Γ((complexBaseChange X).left, W) →+* ℂ => ψ s')
      (X6Glue.ev_eq_psi W y.left hy')
  rw [hreg, he]

/-- On a proper smooth rational curve, the regular-function and native
complex-point topologies agree. -/
def complexPointBaseChangeHomeomorph [IsProper X.hom] [SmoothOfRelativeDimension 1 X.hom]
    :
    @Homeomorph (ComplexPoint (complexBaseChange X)) (fieldPt ℂ ⟶ X)
      Point.analyticTopology (complexPointTopology X) := by
  let _ := complexPointTopology X
  have : T2Space (fieldPt ℂ ⟶ X) := t2Space_complexPoints_of_proper_smooth X
  have : IsProper (complexBaseChange X).hom := inferInstanceAs
    (IsProper (pullback.snd X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))))
  have : SmoothOfRelativeDimension 1 (complexBaseChange X).hom := inferInstanceAs
    (SmoothOfRelativeDimension 1 (pullback.snd X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))))
  have := compactSpace_complexPoint_of_proper_smooth (complexBaseChange X)
  exact Continuous.homeoOfEquivCompactToT2 (f := complexPointBaseChangeEquiv X)
    (continuous_complexPointBaseChangeEquiv X)

end Y3P1j

#print axioms Y3P1j.complexPointBaseChangeHomeomorph

import ZInQKernel.Contrib.CloudR2Poincare.L1.CechBaseChangeSectionSquares
import ZInQKernel.Contrib.CloudR2Poincare.L1.CechCoefficientMaps
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechBaseChange

/-!
# Actual scalar-extension naturality of native Čech face maps

The comparison uses the literal commuting face/base-change square and ACTUAL
native pullbackComp maps. Every scalar is allowed, including nonflat residue
fields. No dimension-selected map or flatness premise is introduced.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- The ACTUAL basechanged face on sections, followed by its native coefficient
comparison and canonical preimage-open transport. It is Γ(T)-linear. -/
def faceScalarBaseChangeSectionsLinearMap
    {X Y XB YB T : Scheme.{u}} (qB : XB ⟶ T)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (square : jB ≫ a = b ≫ j) (M : X.Modules) (U : X.Opens) :
    Scheme.Modules.sectionsModule qB ((Scheme.Modules.pullback a).obj M) (a ⁻¹ᵁ U) →ₗ[Γ(T, ⊤)]
      Scheme.Modules.sectionsModule (jB ≫ qB)
        ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M)) (b ⁻¹ᵁ j ⁻¹ᵁ U) :=
  (faceOpenEqLinearEquiv (jB ≫ qB)
    ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
    (congrArg (fun c : YB ⟶ X ↦ c ⁻¹ᵁ U) square)).toLinearMap ∘ₗ
    coefficientSectionsLinearMap (jB ≫ qB) (nativeFaceBaseChangeCoefficientIso j a b jB square M).hom
      ((jB ≫ a) ⁻¹ᵁ U) ∘ₗ faceSectionsLinearMap qB jB ((Scheme.Modules.pullback a).obj M) (a ⁻¹ᵁ U)

/-- Actual sections scalar-extension/face square, with NO scalar flatness
hypothesis. Both vertical arrows are the EXISTING native base-change maps. -/
theorem faceScalarBaseChangeSectionsLinearMap_square
    {X Y XB YB S T : Scheme.{u}} (q : X ⟶ S) (qB : XB ⟶ T) (g : T ⟶ S)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (HC : IsPullback a qB q g) (HD : IsPullback b (jB ≫ qB) (j ≫ q) g)
    (square : jB ≫ a = b ≫ j) (M : X.Modules) (U : X.Opens)
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom) :
    faceScalarBaseChangeSectionsLinearMap qB j a b jB square M U ∘ₗ
        Scheme.Modules.sectionsModuleBaseChange HC M hg U =
      Scheme.Modules.sectionsModuleBaseChange HD ((Scheme.Modules.pullback j).obj M) hg (j ⁻¹ᵁ U) ∘ₗ
        (faceSectionsLinearMap q j M U).baseChange Γ(T, ⊤) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [LinearMap.comp_apply, map_zero]
  | add x y hx hy => simp only [LinearMap.comp_apply, map_add] at hx hy ⊢; rw [hx, hy]
  | tmul c s =>
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
      Scheme.Modules.sectionsModuleBaseChange_tmul]
    rw [LinearMap.map_smul]
    let NBR := (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M)
    let W := b ⁻¹ᵁ j ⁻¹ᵁ U
    change c • (show Scheme.Modules.sectionsModule (jB ≫ qB) NBR W from
        faceOpenEqLinearEquiv (jB ≫ qB) NBR
          (congrArg (fun f : YB ⟶ X ↦ f ⁻¹ᵁ U) square)
          ((nativeFaceBaseChangeCoefficientIso j a b jB square M).hom.app ((jB ≫ a) ⁻¹ᵁ U)
            (Scheme.Modules.pullbackSection jB (Scheme.Modules.pullbackSection a s)))) =
      c • (show Scheme.Modules.sectionsModule (jB ≫ qB) NBR W from
        Scheme.Modules.pullbackSection b (Scheme.Modules.pullbackSection j s))
    exact congrArg (fun z : Scheme.Modules.sectionsModule (jB ≫ qB) NBR W ↦ c • z)
      (nativeFaceBaseChange_section_square (jB ≫ qB) j a b jB square M U s)

/-- Canonical equal-open transports compose without selecting a map. -/
theorem faceOpenEqLinearEquiv_trans
    {Z T : Scheme.{u}} (p : Z ⟶ T) (M : Z.Modules) {U V W : Z.Opens}
    (h : U = V) (k : V = W) (s : Scheme.Modules.sectionsModule p M U) :
    faceOpenEqLinearEquiv p M k (faceOpenEqLinearEquiv p M h s) =
      faceOpenEqLinearEquiv p M (h.trans k) s := by
  subst V
  subst W
  rfl

/-- Equal-open transport commutes with ACTUAL section pullback, independent
of the chosen scalar structures on source and target. -/
theorem pullbackSection_faceOpenEqLinearEquiv
    {X Y S T : Scheme.{u}} (p : X ⟶ S) (p' : Y ⟶ T) (j : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} (h : U = V) (s : Scheme.Modules.sectionsModule p M U) :
    Scheme.Modules.pullbackSection j (faceOpenEqLinearEquiv p M h s) =
      faceOpenEqLinearEquiv p' ((Scheme.Modules.pullback j).obj M)
        (congrArg (fun W : X.Opens ↦ j ⁻¹ᵁ W) h) (Scheme.Modules.pullbackSection j s) := by
  subst V
  rfl

end ZInQ.Contrib.CloudR2Poincare.L1

import ZInQKernel.Contrib.CloudR2Poincare.L1.CechFaceBaseChange
import ZInQKernel.Contrib.CloudR2Poincare.L1.CechCoverTransport

/-!
# Actual all-scalar native Čech face chain square

Canonical finite-intersection transports identify the actual basechanged
face coefficient and cover. The section square proves the original native
cochain maps commute, with no scalar-flatness or rank-map premise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Literal equality of the ACTUAL two pulled-back covers. -/
theorem nativeFaceBaseChange_cover_eq
    {X Y XB YB : Scheme.{u}} (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (square : jB ≫ a = b ≫ j) {ι : Type u} (U : ι → X.Opens) :
    (fun i ↦ jB ⁻¹ᵁ a ⁻¹ᵁ U i) = (fun i ↦ b ⁻¹ᵁ j ⁻¹ᵁ U i) := by
  funext i
  exact congrArg (fun c : YB ⟶ X ↦ c ⁻¹ᵁ U i) square

/-- ACTUAL basechanged-face target identification: coefficient comparison,
then canonical equality of the original pulled-back cover. -/
def nativeFaceBaseChangeCechTargetIsoNat
    {X Y XB YB T : Scheme.{u}} (qB : XB ⟶ T)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (square : jB ≫ a = b ≫ j) (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    Scheme.Modules.cechModuleComplexNat (jB ≫ qB)
        ((Scheme.Modules.pullback jB).obj ((Scheme.Modules.pullback a).obj M))
        (fun i ↦ jB ⁻¹ᵁ a ⁻¹ᵁ U i) ≅
      Scheme.Modules.cechModuleComplexNat (jB ≫ qB)
        ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
        (fun i ↦ b ⁻¹ᵁ j ⁻¹ᵁ U i) :=
  cechModuleCoefficientIsoNat (jB ≫ qB) (nativeFaceBaseChangeCoefficientIso j a b jB square M)
      (fun i ↦ jB ⁻¹ᵁ a ⁻¹ᵁ U i) ≪≫
    cechModuleCoverEqIsoNat (jB ≫ qB)
      ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
      (nativeFaceBaseChange_cover_eq j a b jB square U)

/-- Canonical scalar-compatible normalized open transports preserve the
ACTUAL two-step section pullback square. -/
theorem nativeFaceBaseChange_normalized_sections_square
    {X Y XB YB S T : Scheme.{u}} (q : X ⟶ S) (qB : XB ⟶ T)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (square : jB ≫ a = b ≫ j) (M : X.Modules)
    (W : X.Opens) (WA : XB.Opens) (WJ : Y.Opens) (WL WR : YB.Opens)
    (ha : a ⁻¹ᵁ W = WA) (hj : j ⁻¹ᵁ W = WJ)
    (hl : jB ⁻¹ᵁ WA = WL) (hr : b ⁻¹ᵁ WJ = WR) (hc : WL = WR)
    (s : Γ(M, W)) :
    faceOpenEqLinearEquiv (jB ≫ qB)
        ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M)) hc
        ((nativeFaceBaseChangeCoefficientIso j a b jB square M).hom.app WL
          (faceOpenEqLinearEquiv (jB ≫ qB)
            ((Scheme.Modules.pullback jB).obj ((Scheme.Modules.pullback a).obj M)) hl
            (Scheme.Modules.pullbackSection jB
              (faceOpenEqLinearEquiv qB ((Scheme.Modules.pullback a).obj M) ha
                (Scheme.Modules.pullbackSection a s))))) =
      faceOpenEqLinearEquiv (jB ≫ qB)
        ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M)) hr
        (Scheme.Modules.pullbackSection b
          (faceOpenEqLinearEquiv (j ≫ q) ((Scheme.Modules.pullback j).obj M) hj
            (Scheme.Modules.pullbackSection j s))) := by
  let NL := (Scheme.Modules.pullback jB).obj ((Scheme.Modules.pullback a).obj M)
  let NR := (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M)
  let δ := nativeFaceBaseChangeCoefficientIso j a b jB square M
  let hL : (jB ≫ a) ⁻¹ᵁ W = WL := (congrArg (fun V : XB.Opens ↦ jB ⁻¹ᵁ V) ha).trans hl
  let hR : (b ≫ j) ⁻¹ᵁ W = WR := (congrArg (fun V : Y.Opens ↦ b ⁻¹ᵁ V) hj).trans hr
  let hS : (jB ≫ a) ⁻¹ᵁ W = (b ≫ j) ⁻¹ᵁ W := congrArg (fun c : YB ⟶ X ↦ c ⁻¹ᵁ W) square
  have leftNorm : faceOpenEqLinearEquiv (jB ≫ qB) NL hl
      (Scheme.Modules.pullbackSection jB
        (faceOpenEqLinearEquiv qB ((Scheme.Modules.pullback a).obj M) ha (Scheme.Modules.pullbackSection a s))) =
      faceOpenEqLinearEquiv (jB ≫ qB) NL hL
        (Scheme.Modules.pullbackSection jB (Scheme.Modules.pullbackSection a s)) := by
    rw [pullbackSection_faceOpenEqLinearEquiv qB (jB ≫ qB), faceOpenEqLinearEquiv_trans]
    rfl
  have rightNorm : faceOpenEqLinearEquiv (jB ≫ qB) NR hr
      (Scheme.Modules.pullbackSection b
        (faceOpenEqLinearEquiv (j ≫ q) ((Scheme.Modules.pullback j).obj M) hj (Scheme.Modules.pullbackSection j s))) =
      faceOpenEqLinearEquiv (jB ≫ qB) NR hR
        (Scheme.Modules.pullbackSection b (Scheme.Modules.pullbackSection j s)) := by
    rw [pullbackSection_faceOpenEqLinearEquiv (j ≫ q) (jB ≫ qB), faceOpenEqLinearEquiv_trans]
    rfl
  have coeffNat := coefficient_openEq_naturality (jB ≫ qB) δ.hom hL
    (Scheme.Modules.pullbackSection jB (Scheme.Modules.pullbackSection a s))
  have sectionSquare := nativeFaceBaseChange_section_square (jB ≫ qB) j a b jB square M W s
  have sameProof : hL.trans hc = hS.trans hR := Subsingleton.elim _ _
  calc
    _ = faceOpenEqLinearEquiv (jB ≫ qB) NR hc
        (δ.hom.app WL (faceOpenEqLinearEquiv (jB ≫ qB) NL hL
          (Scheme.Modules.pullbackSection jB (Scheme.Modules.pullbackSection a s)))) := by rw [leftNorm]
    _ = faceOpenEqLinearEquiv (jB ≫ qB) NR (hL.trans hc)
        (δ.hom.app ((jB ≫ a) ⁻¹ᵁ W)
          (Scheme.Modules.pullbackSection jB (Scheme.Modules.pullbackSection a s))) := by
      have hcN := congrArg (faceOpenEqLinearEquiv (jB ≫ qB) NR hc) coeffNat
      exact hcN.trans (faceOpenEqLinearEquiv_trans (jB ≫ qB) NR hL hc _)
    _ = faceOpenEqLinearEquiv (jB ≫ qB) NR hR
        (faceOpenEqLinearEquiv (jB ≫ qB) NR hS
          (δ.hom.app ((jB ≫ a) ⁻¹ᵁ W)
            (Scheme.Modules.pullbackSection jB (Scheme.Modules.pullbackSection a s)))) := by
      rw [sameProof, faceOpenEqLinearEquiv_trans]
    _ = faceOpenEqLinearEquiv (jB ≫ qB) NR hR
        (Scheme.Modules.pullbackSection b (Scheme.Modules.pullbackSection j s)) := by rw [sectionSquare]
    _ = _ := rightNorm.symm

end ZInQ.Contrib.CloudR2Poincare.L1

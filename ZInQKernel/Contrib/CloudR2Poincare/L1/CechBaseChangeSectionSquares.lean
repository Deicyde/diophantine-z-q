import ZInQKernel.Contrib.CloudR2Poincare.L1.CechFaceMaps
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.HomSection

/-!
# Actual face/base-change section squares

Every coefficient isomorphism is the ACTUAL native pullbackComp isomorphism
with the literal commuting scheme triangle and canonical open transports.
No flatness or dimension-selected map is introduced.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Canonical equal-open transports respect ACTUAL coefficient maps. -/
theorem coefficient_openEq_naturality
    {Z T : Scheme.{u}} (p : Z ⟶ T) {M N : Z.Modules} (φ : M ⟶ N)
    {U V : Z.Opens} (h : U = V) (s : Scheme.Modules.sectionsModule p M U) :
    coefficientSectionsLinearMap p φ V (faceOpenEqLinearEquiv p M h s) =
      faceOpenEqLinearEquiv p N h (coefficientSectionsLinearMap p φ U s) := by
  subst V
  rfl

/-- The actual native coefficient inverse cancels on sections. -/
theorem coefficientIso_inv_hom_sections
    {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N) (U : Z.Opens) (s : Γ(N, U)) :
    e.hom.app U (e.inv.app U s) = s := by
  have h := congrArg (fun φ : N ⟶ N ↦ φ.app U s) e.inv_hom_id
  have h' : e.hom.app U (e.inv.app U s) = (𝟙 Γ(N, U)) s := by
    simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
      ConcreteCategory.comp_apply] using h
  exact h'.trans rfl

/-- Native nested section pullback becomes the ACTUAL composite section when
transported by pullbackComp.hom (not its inverse). -/
theorem pullbackComp_hom_pullbackSection
    {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U)
        (Scheme.Modules.pullbackSection f (Scheme.Modules.pullbackSection g s)) =
      Scheme.Modules.pullbackSection (f ≫ g) s := by
  rw [Scheme.Modules.pullbackSection_pullbackSection]
  exact coefficientIso_inv_hom_sections ((Scheme.Modules.pullbackComp f g).app M) _ _

/-- Equality of the ACTUAL composite morphisms transports the actual section,
including its open, by canonical equality isomorphisms. -/
theorem pullbackSection_eq_transport
    {X Z T : Scheme.{u}} (p : Z ⟶ T) {f g : Z ⟶ X} (h : f = g)
    (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    faceOpenEqLinearEquiv p ((Scheme.Modules.pullback g).obj M)
        (congrArg (fun a : Z ⟶ X ↦ a ⁻¹ᵁ U) h)
        ((eqToIso (congrArg (fun a : Z ⟶ X ↦ (Scheme.Modules.pullback a).obj M) h)).hom.app
          (f ⁻¹ᵁ U) (Scheme.Modules.pullbackSection f s)) =
      Scheme.Modules.pullbackSection g s := by
  subst g
  rfl

/-- ACTUAL coefficient comparison in a face/base-change square. Its order is
nested left → composite left → equal composite right → nested right. -/
def nativeFaceBaseChangeCoefficientIso
    {X Y XB YB : Scheme.{u}} (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (square : jB ≫ a = b ≫ j) (M : X.Modules) :
    (Scheme.Modules.pullback jB).obj ((Scheme.Modules.pullback a).obj M) ≅
      (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M) :=
  (Scheme.Modules.pullbackComp jB a).app M ≪≫
    eqToIso (congrArg (fun p : YB ⟶ X ↦ (Scheme.Modules.pullback p).obj M) square) ≪≫
      ((Scheme.Modules.pullbackComp b j).app M).symm

/-- The ACTUAL face/pullback section square, with its actual scalar-compatible
coefficient comparison and canonical open transport. -/
theorem nativeFaceBaseChange_section_square
    {X Y XB YB T : Scheme.{u}} (p : YB ⟶ T)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (square : jB ≫ a = b ≫ j) (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    faceOpenEqLinearEquiv p ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
        (congrArg (fun c : YB ⟶ X ↦ c ⁻¹ᵁ U) square)
        ((nativeFaceBaseChangeCoefficientIso j a b jB square M).hom.app ((jB ≫ a) ⁻¹ᵁ U)
          (Scheme.Modules.pullbackSection jB (Scheme.Modules.pullbackSection a s))) =
      Scheme.Modules.pullbackSection b (Scheme.Modules.pullbackSection j s) := by
  let f := jB ≫ a
  let g := b ≫ j
  let ho : f ⁻¹ᵁ U = g ⁻¹ᵁ U := congrArg (fun c : YB ⟶ X ↦ c ⁻¹ᵁ U) square
  let e1 := (Scheme.Modules.pullbackComp jB a).app M
  let e2 := (Scheme.Modules.pullbackComp b j).app M
  let e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback g).obj M :=
    eqToIso (congrArg (fun c : YB ⟶ X ↦ (Scheme.Modules.pullback c).obj M) square)
  calc
    _ = faceOpenEqLinearEquiv p ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M)) ho
        (e2.inv.app (f ⁻¹ᵁ U) (e.hom.app (f ⁻¹ᵁ U)
          (e1.hom.app (f ⁻¹ᵁ U)
            (Scheme.Modules.pullbackSection jB (Scheme.Modules.pullbackSection a s))))) := by
      simp only [nativeFaceBaseChangeCoefficientIso, Iso.trans_hom, Iso.symm_hom,
        Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
      rfl
    _ = faceOpenEqLinearEquiv p ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M)) ho
        (e2.inv.app (f ⁻¹ᵁ U) (e.hom.app (f ⁻¹ᵁ U) (Scheme.Modules.pullbackSection f s))) := by
      have hl : e1.hom.app (f ⁻¹ᵁ U)
          (Scheme.Modules.pullbackSection jB (Scheme.Modules.pullbackSection a s)) =
          Scheme.Modules.pullbackSection f s :=
        pullbackComp_hom_pullbackSection jB a M U s
      exact congrArg (fun x : Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) ↦
        faceOpenEqLinearEquiv p ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M)) ho
          (e2.inv.app (f ⁻¹ᵁ U) (e.hom.app (f ⁻¹ᵁ U) x))) hl
    _ = e2.inv.app (g ⁻¹ᵁ U)
        (faceOpenEqLinearEquiv p ((Scheme.Modules.pullback g).obj M) ho
          (e.hom.app (f ⁻¹ᵁ U) (Scheme.Modules.pullbackSection f s))) :=
      (coefficient_openEq_naturality p e2.inv ho _).symm
    _ = e2.inv.app (g ⁻¹ᵁ U) (Scheme.Modules.pullbackSection g s) := by
      exact congrArg (fun x : Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ U) ↦
        e2.inv.app (g ⁻¹ᵁ U) x) (pullbackSection_eq_transport p square M U s)
    _ = Scheme.Modules.pullbackSection b (Scheme.Modules.pullbackSection j s) :=
      (Scheme.Modules.pullbackSection_pullbackSection b j s).symm

end ZInQ.Contrib.CloudR2Poincare.L1

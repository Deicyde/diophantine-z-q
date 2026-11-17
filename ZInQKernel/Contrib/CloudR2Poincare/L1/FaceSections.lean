import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechComplex
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.HomSection

/-!
# Actual face maps on native coefficient sections

No Cartesian or flatness hypothesis is imposed on the face morphism. The
structure map of its source is the literal composite j ≫ q. Every section
map is the actual pullback-pushforward adjunction unit, with the actual
base-global-functions action. Unit comparisons use pullbackObjUnitIso in
its native orientation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits Opposite AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- The original base functions act through the actual face structure triangle. -/
theorem face_baseScalar_app_compatibility
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (U : X.Opens) (a : Γ(S, ⊤)) :
    j.app U (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (q.appTop a)) =
      Y.presheaf.map (homOfLE (le_top : j ⁻¹ᵁ U ≤ ⊤)).op ((j ≫ q).appTop a) := by
  have h := j.naturality (homOfLE (le_top : U ≤ ⊤)).op
  change X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ j.app U =
    j.appTop ≫ Y.presheaf.map (homOfLE (le_top : j ⁻¹ᵁ U ≤ ⊤)).op at h
  change (q.appTop ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ j.app U) a =
    ((j ≫ q).appTop ≫ Y.presheaf.map (homOfLE (le_top : j ⁻¹ᵁ U ≤ ⊤)).op) a
  rw [h, Scheme.Hom.comp_appTop, Category.assoc]

/-- Actual native section pullback along the face, linear over the ORIGINAL base. -/
def faceSectionsLinearMap
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    Scheme.Modules.sectionsModule q M U →ₗ[Γ(S, ⊤)]
      Scheme.Modules.sectionsModule (j ≫ q) ((Scheme.Modules.pullback j).obj M) (j ⁻¹ᵁ U) where
  toFun := Scheme.Modules.pullbackSection j
  map_add' := fun x y ↦ Scheme.Modules.pullbackSection_add j x y
  map_smul' a x := by
    letI : Module Γ(X, U) (Scheme.Modules.sectionsModule q M U) :=
      inferInstanceAs (Module Γ(X, U) Γ(M, U))
    letI : Module Γ(Y, j ⁻¹ᵁ U)
        (Scheme.Modules.sectionsModule (j ≫ q) ((Scheme.Modules.pullback j).obj M) (j ⁻¹ᵁ U)) :=
      inferInstanceAs (Module Γ(Y, j ⁻¹ᵁ U) Γ((Scheme.Modules.pullback j).obj M, j ⁻¹ᵁ U))
    change Scheme.Modules.pullbackSection j
        (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (q.appTop a) • x) =
      Y.presheaf.map (homOfLE (le_top : j ⁻¹ᵁ U ≤ ⊤)).op ((j ≫ q).appTop a) •
        Scheme.Modules.pullbackSection j x
    rw [Scheme.Modules.pullbackSection_smul, face_baseScalar_app_compatibility]

@[simp]
theorem faceSectionsLinearMap_apply
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (s : Scheme.Modules.sectionsModule q M U) :
    faceSectionsLinearMap q j M U s = Scheme.Modules.pullbackSection j s := rfl

/-- The actual face section map commutes with every actual open restriction. -/
theorem faceSectionsLinearMap_restrict
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (M : X.Modules)
    {V U : X.Opens} (h : V ≤ U) (s : Scheme.Modules.sectionsModule q M U) :
    faceSectionsLinearMap q j M V (Scheme.Modules.sectionsModuleRestrict q M h s) =
      Scheme.Modules.sectionsModuleRestrict (j ≫ q) ((Scheme.Modules.pullback j).obj M)
        (j.preimage_mono h) (faceSectionsLinearMap q j M U s) :=
  Scheme.Modules.pullbackSection_map j h s

/-- The section maps use the ACTUAL adjunction coefficient naturality. -/
theorem faceSectionsLinearMap_coefficient_naturality
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) {M N : X.Modules}
    (φ : M ⟶ N) (U : X.Opens) (s : Scheme.Modules.sectionsModule q M U) :
    ((Scheme.Modules.pullback j).map φ).app (j ⁻¹ᵁ U) (faceSectionsLinearMap q j M U s) =
      faceSectionsLinearMap q j N U (φ.app U s) :=
  Scheme.Modules.pullbackUnit_naturality_apply j φ U s

/-- Native coefficient maps on sections, with the actual base scalar action. -/
def coefficientSectionsLinearMap
    {X S : Scheme.{u}} (q : X ⟶ S) {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) :
    Scheme.Modules.sectionsModule q M U →ₗ[Γ(S, ⊤)] Scheme.Modules.sectionsModule q N U where
  toFun := φ.app U
  map_add' := fun x y ↦ (φ.app U).hom.map_add x y
  map_smul' a s := by
    letI : Module Γ(X, U) (Scheme.Modules.sectionsModule q M U) :=
      inferInstanceAs (Module Γ(X, U) Γ(M, U))
    letI : Module Γ(X, U) (Scheme.Modules.sectionsModule q N U) :=
      inferInstanceAs (Module Γ(X, U) Γ(N, U))
    change φ.app U (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (q.appTop a) • s) =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (q.appTop a) • φ.app U s
    exact Scheme.Modules.Hom.app_smul _ _ _

/-- Pushforward sections are the ACTUAL sections on the preimage open, including
compatibility with the ORIGINAL base's action, not merely an AddEquiv. -/
def pushforwardSectionsLinearEquiv
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (N : Y.Modules) (U : X.Opens) :
    Scheme.Modules.sectionsModule q ((Scheme.Modules.pushforward j).obj N) U ≃ₗ[Γ(S, ⊤)]
      Scheme.Modules.sectionsModule (j ≫ q) N (j ⁻¹ᵁ U) where
  toFun := fun s ↦ s
  invFun := fun s ↦ s
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  map_add' := fun _ _ ↦ rfl
  map_smul' a s := by
    letI : Module Γ(Y, j ⁻¹ᵁ U)
        (Scheme.Modules.sectionsModule q ((Scheme.Modules.pushforward j).obj N) U) :=
      inferInstanceAs (Module Γ(Y, j ⁻¹ᵁ U) Γ(N, j ⁻¹ᵁ U))
    letI : Module Γ(Y, j ⁻¹ᵁ U) (Scheme.Modules.sectionsModule (j ≫ q) N (j ⁻¹ᵁ U)) :=
      inferInstanceAs (Module Γ(Y, j ⁻¹ᵁ U) Γ(N, j ⁻¹ᵁ U))
    change j.app U (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (q.appTop a)) • s =
      Y.presheaf.map (homOfLE (le_top : j ⁻¹ᵁ U ≤ ⊤)).op ((j ≫ q).appTop a) • s
    rw [face_baseScalar_app_compatibility]

/-- The pullback of the native unit section is transported by the INVERSE unit
comparison (O_Y → j*O_X), exactly as in the native adjunction definition. -/
theorem faceSectionsLinearMap_nativeUnit_top
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) :
    faceSectionsLinearMap q j (Scheme.Modules.unit X) ⊤ (1 : Γ(X, ⊤)) =
      (Scheme.Modules.pullbackObjUnitIso j).inv.app (j ⁻¹ᵁ ⊤) (1 : Γ(Y, ⊤)) :=
  Scheme.Modules.pullbackSection_one_eq j

end ZInQ.Contrib.CloudR2Poincare.L1

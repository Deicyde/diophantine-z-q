import Mathlib
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace T
/-- Precomposing a field point with `Spec L → Spec K` keeps the point and composes the
residue-field embedding with `f`. -/
theorem specToEquivOfField_comp {K L : Type} [Field K] [Field L] {X : Scheme.{0}} (f : K →+* L)
    (y : Spec (CommRingCat.of K) ⟶ X) :
    Scheme.SpecToEquivOfField L X (Spec.map (CommRingCat.ofHom f) ≫ y) =
      ⟨(Scheme.SpecToEquivOfField K X y).1,
        (Scheme.SpecToEquivOfField K X y).2 ≫ CommRingCat.ofHom f⟩ := by
  obtain ⟨p, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
  rw [Equiv.apply_symm_apply]
  have : Spec.map (CommRingCat.ofHom f) ≫ (Scheme.SpecToEquivOfField K X).symm p =
      (Scheme.SpecToEquivOfField L X).symm ⟨p.1, p.2 ≫ CommRingCat.ofHom f⟩ := by
    simp only [Scheme.SpecToEquivOfField_symm_apply, Spec.map_comp, Category.assoc]
  rw [this, Equiv.apply_symm_apply]

def fieldPt (K : Type) [Field K] [Algebra ℚ K] : Over (Spec (CommRingCat.of ℚ)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K)))

/-- `Spec L → Spec K` over `ℚ`, for `f : K →ₐ[ℚ] L`. -/
def fieldMap {K L : Type} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L) :
    fieldPt L ⟶ fieldPt K :=
  Over.homMk (Spec.map (CommRingCat.ofHom (f : K →+* L))) (by
    simp only [fieldPt, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact f.comp_algebraMap)

/-- (test copy) -/
def IsNaturalRelabel (Y : Over (Spec (CommRingCat.of ℚ)))
    (τ : ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) ≃ (fieldPt K ⟶ Y)) : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y), τ L (fieldMap f ≫ y) = fieldMap f ≫ τ K y


section RvG0Exotic

/-- Any two morphisms `Spec K ⟶ Spec ℚ` agree (`ℚ` is initial among fields of char. 0). -/
theorem spec_to_specQ_eq {K : Type} [Field K]
    (g h : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ)) : g = h := by
  rw [← Spec.map_preimage g, ← Spec.map_preimage h]
  congr 1
  apply CommRingCat.hom_ext
  exact Subsingleton.elim _ _

variable {X : Scheme.{0}} (s : X ≃ X) (φ : ∀ x, X.residueField (s x) ≅ X.residueField x)

/-- The relabeled field point: `(x, ι) ↦ (s x, φ x ≫ ι)`. -/
noncomputable def relabelPt (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ X) :
    Spec (CommRingCat.of K) ⟶ X :=
  (Scheme.SpecToEquivOfField K X).symm
    ⟨s (Scheme.SpecToEquivOfField K X y).1, (φ _).hom ≫ (Scheme.SpecToEquivOfField K X y).2⟩

theorem relabelPt_symm (K : Type) [Field K] (p : Σ x, X.residueField x ⟶ CommRingCat.of K) :
    relabelPt s φ K ((Scheme.SpecToEquivOfField K X).symm p) =
      (Scheme.SpecToEquivOfField K X).symm ⟨s p.1, (φ p.1).hom ≫ p.2⟩ := by
  unfold relabelPt
  rw [Equiv.apply_symm_apply]

theorem relabelPt_bijective (K : Type) [Field K] : Function.Bijective (relabelPt s φ K) := by
  constructor
  · intro y₁ y₂ h
    obtain ⟨⟨x₁, ι₁⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y₁
    obtain ⟨⟨x₂, ι₂⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y₂
    rw [relabelPt_symm, relabelPt_symm] at h
    have h' := (Scheme.SpecToEquivOfField K X).symm.injective h
    simp only [Sigma.mk.inj_iff] at h'
    obtain ⟨hx, hι⟩ := h'
    have hx' : x₁ = x₂ := s.injective hx
    subst hx'
    have hι' := eq_of_heq hι
    have : ι₁ = ι₂ := (cancel_epi (φ x₁).hom).mp hι'
    rw [this]
  · intro y
    obtain ⟨⟨x', ι'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
    obtain ⟨x, rfl⟩ := s.surjective x'
    refine ⟨(Scheme.SpecToEquivOfField K X).symm ⟨x, (φ x).inv ≫ ι'⟩, ?_⟩
    rw [relabelPt_symm]
    simp

/-- Naturality: `τ(y ∘ Spec f) = τ(y) ∘ Spec f`. -/
theorem relabelPt_comp {K L : Type} [Field K] [Field L] (f : K →+* L)
    (y : Spec (CommRingCat.of K) ⟶ X) :
    relabelPt s φ L (Spec.map (CommRingCat.ofHom f) ≫ y) =
      Spec.map (CommRingCat.ofHom f) ≫ relabelPt s φ K y := by
  apply (Scheme.SpecToEquivOfField L X).injective
  have h1 : Scheme.SpecToEquivOfField K X (relabelPt s φ K y) =
      ⟨s (Scheme.SpecToEquivOfField K X y).1,
        (φ _).hom ≫ (Scheme.SpecToEquivOfField K X y).2⟩ := by
    unfold relabelPt; rw [Equiv.apply_symm_apply]
  rw [specToEquivOfField_comp f (relabelPt s φ K y), h1]
  unfold relabelPt
  rw [Equiv.apply_symm_apply, specToEquivOfField_comp f y]
  simp only [Category.assoc]

/-- The point of `τ(y)` is `s` of the point of `y`: the relabeling moves points as `s` does. -/
theorem relabelPt_point (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ X) :
    (Scheme.SpecToEquivOfField K X (relabelPt s φ K y)).1 =
      s (Scheme.SpecToEquivOfField K X y).1 := by
  unfold relabelPt; rw [Equiv.apply_symm_apply]

/-- The relabeling on field points of `Y` over `ℚ`. -/
noncomputable def relabelOver (Y : Over (Spec (CommRingCat.of ℚ))) (s : Y.left ≃ Y.left)
    (φ : ∀ x, Y.left.residueField (s x) ≅ Y.left.residueField x)
    (K : Type) [Field K] [Algebra ℚ K] : (fieldPt K ⟶ Y) ≃ (fieldPt K ⟶ Y) :=
  Equiv.ofBijective
    (fun y => Over.homMk (relabelPt s φ K y.left) (spec_to_specQ_eq _ _))
    (by
      constructor
      · intro y₁ y₂ h
        have h' := congrArg (fun g : fieldPt K ⟶ Y => g.left) h
        exact Over.OverMorphism.ext ((relabelPt_bijective s φ K).1 h')
      · intro y
        obtain ⟨z, hz⟩ := (relabelPt_bijective s φ K).2 y.left
        exact ⟨Over.homMk z (spec_to_specQ_eq _ _), Over.OverMorphism.ext hz⟩)

theorem relabelOver_natural (Y : Over (Spec (CommRingCat.of ℚ))) (s : Y.left ≃ Y.left)
    (φ : ∀ x, Y.left.residueField (s x) ≅ Y.left.residueField x) :
    IsNaturalRelabel Y (relabelOver Y s φ) := by
  intro K L _ _ _ _ f y
  apply Over.OverMorphism.ext
  exact relabelPt_comp s φ (f : K →+* L) y.left

end RvG0Exotic
end T
#print axioms T.relabelOver_natural
#print axioms T.relabelPt_point

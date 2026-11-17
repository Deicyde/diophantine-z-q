import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Adjunction.CompositionIso

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace WeilProof.Mates

variable {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
  [MonoidalCategory C₀] [MonoidalCategory C₁] [MonoidalCategory C₂]
  {F₁ : C₀ ⥤ C₁} {G₁ : C₁ ⥤ C₀} {F₂ : C₁ ⥤ C₂} {G₂ : C₂ ⥤ C₁} {F₃ : C₀ ⥤ C₂} {G₃ : C₂ ⥤ C₀}
  (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂) (adj₃ : F₃ ⊣ G₃)
  [G₁.LaxMonoidal] [G₂.LaxMonoidal] [G₃.LaxMonoidal]

set_option backward.defeqAttrib.useBackward true in
/-- **The left adjoint comparison of a monoidal right adjoint comparison is oplax monoidal.** -/
theorem leftAdjointCompIso_δ (e : G₂ ⋙ G₁ ≅ G₃)
    (he : ∀ X Y : C₂, μ G₁ (G₂.obj X) (G₂.obj Y) ≫ G₁.map (μ G₂ X Y) ≫ e.hom.app (X ⊗ Y) =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ G₃ X Y) (X Y : C₀) :
    letI := adj₁.leftAdjointOplaxMonoidal
    letI := adj₂.leftAdjointOplaxMonoidal
    letI := adj₃.leftAdjointOplaxMonoidal
    δ F₃ X Y ≫ ((Adjunction.leftAdjointCompIso adj₁ adj₂ adj₃ e).inv.app X ⊗ₘ
        (Adjunction.leftAdjointCompIso adj₁ adj₂ adj₃ e).inv.app Y) =
      (Adjunction.leftAdjointCompIso adj₁ adj₂ adj₃ e).inv.app (X ⊗ Y) ≫
        F₂.map (δ F₁ X Y) ≫ δ F₂ (F₁.obj X) (F₁.obj Y) := by
  let _ := adj₁.leftAdjointOplaxMonoidal
  let _ := adj₂.leftAdjointOplaxMonoidal
  let _ := adj₃.leftAdjointOplaxMonoidal
  set ψ := Adjunction.leftAdjointCompIso adj₁ adj₂ adj₃ e
  have hu : ∀ Z : C₀, adj₃.unit.app Z ≫ G₃.map (ψ.inv.app Z) =
      (adj₁.comp adj₂).unit.app Z ≫ e.hom.app ((F₁ ⋙ F₂).obj Z) := by
    intro Z
    rw [← unit_conjugateEquiv (adj₁.comp adj₂) adj₃ ψ.inv Z,
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
  have hC := Adjunction.unit_app_tensor_comp_map_δ (adj₁.comp adj₂) X Y
  simp only [Functor.comp_map, Functor.OplaxMonoidal.comp_δ] at hC
  apply (adj₃.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    Adjunction.unit_app_tensor_comp_map_δ_assoc, ← μ_natural, tensorHom_comp_tensorHom_assoc, hu, hu,
    ← tensorHom_comp_tensorHom_assoc, ← he, Functor.map_comp, reassoc_of% (hu (X ⊗ Y))]
  have hn := e.hom.naturality (F₂.map (δ F₁ X Y) ≫ δ F₂ (F₁.obj X) (F₁.obj Y))
  simp only [Functor.comp_map] at hn
  rw [← hn, reassoc_of% hC]
  simp [Functor.LaxMonoidal.comp_μ]

end WeilProof.Mates

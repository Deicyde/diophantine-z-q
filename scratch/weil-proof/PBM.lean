import ZInQKernel.Contrib.OneProof.WeilFormula

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory Limits

section MatesSec
open Functor.LaxMonoidal Functor.OplaxMonoidal
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

end MatesSec

namespace WeilProof.PBM
open Scheme.Modules

universe u
variable {X Y Z : Scheme.{u}}

attribute [local instance] Scheme.Modules.presheafPullbackCompSheafificationMonoidal

abbrev PP (f : X ⟶ Y) :=
  PresheafOfModules.pullbackOfCommRingCat (F := TopologicalSpace.Opens.map f.base)
    (R := X.sheaf.obj) (S := Y.sheaf.obj) f.toRingCatPresheafHom

abbrev GG (f : X ⟶ Y) := PP f ⋙ sheafification X

abbrev ee (f : X ⟶ Y) : Scheme.Modules.sheafification Y ⋙ Scheme.Modules.pullback f ≅
    PP f ⋙ Scheme.Modules.sheafification X :=
  SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom

example (f : X ⟶ Y) : (PP f).Monoidal := inferInstance
example (f : X ⟶ Y) : (GG f).Monoidal := inferInstance
example : (sheafification X).Monoidal := inferInstance

lemma mu_sheafified (f : X ⟶ Y) (A B : Y.PresheafOfModules) :
    Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) ((sheafification Y).obj A)
        ((sheafification Y).obj B) =
      ((ee f).hom.app A ⊗ₘ (ee f).hom.app B) ≫
        Functor.LaxMonoidal.μ (sheafification X) ((PP f).obj A) ((PP f).obj B) ≫
        (sheafification X).map (Functor.LaxMonoidal.μ (PP f) A B) ≫
        (ee f).inv.app (A ⊗ B) ≫
        (Scheme.Modules.pullback f).map (Functor.OplaxMonoidal.δ (sheafification Y) A B) := by
  let _ : (GG f).Monoidal := presheafPullbackCompSheafificationMonoidal f
  let _ := Scheme.Modules.pullbackLocalizationLifting f
  exact Localization.Monoidal.functorMonoidalOfComp_μ (sheafification Y) _ (Scheme.Modules.pullback f)
    (GG f) A B

abbrev PF (f : X ⟶ Y) := PresheafOfModules.pushforwardOfCommRingCat
  (F := TopologicalSpace.Opens.map f.base) (R := X.sheaf.obj) (S := Y.sheaf.obj) f.toRingCatPresheafHom

abbrev AD (f : X ⟶ Y) : PP f ⊣ PF f := PresheafOfModules.adjunctionOfCommRingCat
  (F := TopologicalSpace.Opens.map f.base) (R := X.sheaf.obj) (S := Y.sheaf.obj) f.toRingCatPresheafHom

abbrev PFQ (f : X ⟶ Y) := PresheafOfModules.pushforward f.toRingCatSheafHom.hom

def eQ (f : X ⟶ Y) (g : Y ⟶ Z) : PFQ f ⋙ PFQ g ≅ PFQ (f ≫ g) := PresheafOfModules.pushforwardComp _ _

def eF (f : X ⟶ Y) (g : Y ⟶ Z) : PF f ⋙ PF g ≅ PF (f ≫ g) := eQ f g

def pcP (f : X ⟶ Y) (g : Y ⟶ Z) : PP g ⋙ PP f ≅ PP (f ≫ g) :=
  Adjunction.leftAdjointCompIso (AD g) (AD f) (AD (f ≫ g)) (eF f g)

local notation "L" => Scheme.Modules.sheafification

abbrev shA (X : Scheme.{u}) := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)

abbrev adjS (f : X ⟶ Y) := Scheme.Modules.pullbackPushforwardAdjunction f

abbrev RS (X : Scheme.{u}) := SheafOfModules.forget X.ringCatSheaf ⋙
  PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)

lemma push_RS (g : Y ⟶ Z) {M N : Y.Modules} (h : M ⟶ N) :
    (PresheafOfModules.restrictScalars (𝟙 Z.ringCatSheaf.obj)).map
        ((SheafOfModules.forget Z.ringCatSheaf).map ((pushforward g).map h)) =
      (PF g).map ((PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map
        ((SheafOfModules.forget Y.ringCatSheaf).map h)) := rfl

lemma push_push (f : X ⟶ Y) (g : Y ⟶ Z) {M N : X.Modules} (h : M ⟶ N) :
    (pushforward g).map ((pushforward f).map h) = (pushforward (f ≫ g)).map h := rfl

lemma PF_PF (f : X ⟶ Y) (g : Y ⟶ Z) {M N : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)}
    (h : M ⟶ N) : (PF g).map ((PF f).map h) = (PF (f ≫ g)).map h := rfl

/-- (U1) -/
lemma unit_ee (f : X ⟶ Y) (P : Y.PresheafOfModules) :
    (shA Y).unit.app P ≫ (RS Y).map ((adjS f).unit.app ((L Y).obj P)) ≫
        (RS Y).map ((pushforward f).map ((ee f).hom.app P)) =
      (AD f).unit.app P ≫ (PF f).map ((shA X).unit.app ((PP f).obj P)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app ((shA Y).comp (adjS f)) ((AD f).comp (shA X)) P
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Category.assoc] at h
  exact h

/-- (U3) -/
lemma unit_pcP (f : X ⟶ Y) (g : Y ⟶ Z) (A : Z.PresheafOfModules) :
    (AD g).unit.app A ≫ (PF g).map ((AD f).unit.app ((PP g).obj A)) ≫
        (PF g).map ((PF f).map ((pcP f g).hom.app A)) = (AD (f ≫ g)).unit.app A := by
  have h := unit_conjugateEquiv_symm (AD (f ≫ g)) ((AD g).comp (AD f)) (eF f g).inv A
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Category.assoc] at h
  rw [← Functor.map_comp]
  exact h.symm

/-- (U2) -/
lemma unit_pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    (adjS g).unit.app M ≫ (pushforward g).map ((adjS f).unit.app ((Scheme.Modules.pullback g).obj M)) ≫
        (pushforward g).map ((pushforward f).map ((pullbackComp f g).hom.app M)) =
      (adjS (f ≫ g)).unit.app M := by
  have h := unit_conjugateEquiv_symm (adjS (f ≫ g)) ((adjS g).comp (adjS f))
    (Scheme.Modules.pushforwardComp f g).inv M
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Category.assoc] at h
  rw [← Functor.map_comp]
  exact h.symm

set_option maxHeartbeats 1000000 in
/-- (E) -/
lemma ee_comp (f : X ⟶ Y) (g : Y ⟶ Z) (A : Z.PresheafOfModules) :
    (Scheme.Modules.pullback f).map ((ee g).hom.app A) ≫ (ee f).hom.app ((PP g).obj A) ≫
        (L X).map ((pcP f g).hom.app A) =
      (pullbackComp f g).hom.app ((L Z).obj A) ≫ (ee (f ≫ g)).hom.app A := by
  apply (((shA Z).comp ((adjS g).comp (adjS f))).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc, Functor.comp_map, Functor.comp_obj]
  -- right side
  have u2 := congrArg (fun φ => (RS Z).map φ) (unit_pullbackComp f g ((L Z).obj A))
  simp only [Functor.map_comp, Functor.comp_map] at u2
  dsimp only [Scheme.Modules.sheafification] at u2 ⊢
  rw [reassoc_of% u2, push_push f g ((ee (f ≫ g)).hom.app A)]
  have u1fg := unit_ee (f ≫ g) A
  simp only [Functor.comp_map] at u1fg
  dsimp only [Scheme.Modules.sheafification] at u1fg
  rw [u1fg]
  -- left side
  have nat := (adjS f).unit.naturality ((ee g).hom.app A)
  have n2 : (PresheafOfModules.restrictScalars (𝟙 Z.ringCatSheaf.obj)).map
        ((SheafOfModules.forget Z.ringCatSheaf).map ((pushforward g).map
          ((adjS f).unit.app ((Scheme.Modules.pullback g).obj
            ((PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).obj A))))) ≫
      (PresheafOfModules.restrictScalars (𝟙 Z.ringCatSheaf.obj)).map
        ((SheafOfModules.forget Z.ringCatSheaf).map ((pushforward g).map ((pushforward f).map
          ((Scheme.Modules.pullback f).map ((ee g).hom.app A))))) =
      (PresheafOfModules.restrictScalars (𝟙 Z.ringCatSheaf.obj)).map
        ((SheafOfModules.forget Z.ringCatSheaf).map ((pushforward g).map ((ee g).hom.app A))) ≫
      (PresheafOfModules.restrictScalars (𝟙 Z.ringCatSheaf.obj)).map
        ((SheafOfModules.forget Z.ringCatSheaf).map ((pushforward g).map
          ((adjS f).unit.app ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj
            ((PP g).obj A))))) := by
    simp only [← Functor.map_comp]
    congr 3
    exact nat.symm
  rw [reassoc_of% n2]
  have u1g := unit_ee g A
  simp only [Functor.comp_map] at u1g
  dsimp only [Scheme.Modules.sheafification] at u1g
  rw [reassoc_of% u1g]
  rw [push_RS g, push_RS g, push_RS g]
  have u1f := unit_ee f ((PP g).obj A)
  simp only [Functor.comp_map] at u1f
  dsimp only [Scheme.Modules.sheafification] at u1f
  have natX := (shA X).unit.naturality ((pcP f g).hom.app A)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at natX
  have key : (shA Y).unit.app ((PP g).obj A) ≫
      (PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map ((SheafOfModules.forget Y.ringCatSheaf).map
        ((adjS f).unit.app ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).obj ((PP g).obj A)))) ≫
      (PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map ((SheafOfModules.forget Y.ringCatSheaf).map
        ((pushforward f).map ((ee f).hom.app ((PP g).obj A)))) ≫
      (PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map ((SheafOfModules.forget Y.ringCatSheaf).map
        ((pushforward f).map ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
          ((pcP f g).hom.app A)))) =
      (AD f).unit.app ((PP g).obj A) ≫ (PF f).map ((pcP f g).hom.app A) ≫
        (PF f).map ((shA X).unit.app ((PP (f ≫ g)).obj A)) := by
    rw [reassoc_of% u1f, push_RS f, ← Functor.map_comp, ← natX, Functor.map_comp]
  rw [← Functor.map_comp (PF g), ← Functor.map_comp (PF g), ← Functor.map_comp (PF g), key,
    Functor.map_comp, Functor.map_comp, reassoc_of% (unit_pcP f g A), PF_PF f g]

lemma mu_tmul (f : X ⟶ Y) (M N : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
    (U : (TopologicalSpace.Opens Y)ᵒᵖ) (m : M.obj ((TopologicalSpace.Opens.map f.base).op.obj U))
    (n : N.obj ((TopologicalSpace.Opens.map f.base).op.obj U)) :
    ModuleCat.Hom.hom ((Functor.LaxMonoidal.μ (PF f) M N).app U) (m ⊗ₜ n) = m ⊗ₜ n :=
  PresheafOfModules.pushforward_μ_app_tmul _ M N U m n

/-- presheaf pushforward composition is monoidal -/
lemma eF_monoidal (f : X ⟶ Y) (g : Y ⟶ Z) (M N : PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) :
    Functor.LaxMonoidal.μ (PF g) ((PF f).obj M) ((PF f).obj N) ≫ (PF g).map (Functor.LaxMonoidal.μ (PF f) M N) ≫
        (eF f g).hom.app (M ⊗ N) =
      ((eF f g).hom.app M ⊗ₘ (eF f g).hom.app N) ≫ Functor.LaxMonoidal.μ (PF (f ≫ g)) M N := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  simp only [PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  have h1 := mu_tmul g ((PF f).obj M) ((PF f).obj N) U m n
  erw [h1]
  change ModuleCat.Hom.hom ((Functor.LaxMonoidal.μ (PF f) M N).app _) (m ⊗ₜ n) =
    ModuleCat.Hom.hom ((Functor.LaxMonoidal.μ (PF (f ≫ g)) M N).app U) (m ⊗ₜ n)
  rw [mu_tmul, mu_tmul]
  rfl

/-- (P), δ-form -/
lemma pcP_delta (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Z.PresheafOfModules) :
    Functor.OplaxMonoidal.δ (PP (f ≫ g)) A B ≫ ((pcP f g).inv.app A ⊗ₘ (pcP f g).inv.app B) =
      (pcP f g).inv.app (A ⊗ B) ≫ (PP f).map (Functor.OplaxMonoidal.δ (PP g) A B) ≫
        Functor.OplaxMonoidal.δ (PP f) ((PP g).obj A) ((PP g).obj B) := by
  exact Mates.leftAdjointCompIso_δ (AD g) (AD f) (AD (f ≫ g)) (eF f g) (eF_monoidal f g) A B

/-- (P) -/
lemma pcP_monoidal (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Z.PresheafOfModules) :
    Functor.LaxMonoidal.μ (PP f) ((PP g).obj A) ((PP g).obj B) ≫
        (PP f).map (Functor.LaxMonoidal.μ (PP g) A B) ≫ (pcP f g).hom.app (A ⊗ B) =
      ((pcP f g).hom.app A ⊗ₘ (pcP f g).hom.app B) ≫ Functor.LaxMonoidal.μ (PP (f ≫ g)) A B := by
  rw [← cancel_mono (Functor.OplaxMonoidal.δ (PP (f ≫ g)) A B ≫
    ((pcP f g).inv.app A ⊗ₘ (pcP f g).inv.app B))]
  conv_lhs => rw [pcP_delta]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.Monoidal.μ_δ_assoc,
    tensorHom_comp_tensorHom, Iso.hom_inv_id_app]
  rw [← Functor.map_comp_assoc, Functor.Monoidal.μ_δ, CategoryTheory.Functor.map_id, Category.id_comp,
    Functor.Monoidal.μ_δ]
  simp

/-- The main identity on sheafified objects. -/
theorem main_sheafified (f : X ⟶ Y) (g : Y ⟶ Z) (A B : Z.PresheafOfModules) :
    Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) ((Scheme.Modules.pullback g).obj ((L Z).obj A))
        ((Scheme.Modules.pullback g).obj ((L Z).obj B)) ≫
      (Scheme.Modules.pullback f).map
        (Functor.LaxMonoidal.μ (Scheme.Modules.pullback g) ((L Z).obj A) ((L Z).obj B)) ≫
        (pullbackComp f g).hom.app ((L Z).obj A ⊗ (L Z).obj B) =
      ((pullbackComp f g).hom.app ((L Z).obj A) ⊗ₘ (pullbackComp f g).hom.app ((L Z).obj B)) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.pullback (f ≫ g)) ((L Z).obj A) ((L Z).obj B) := by
  -- precompose with the iso `f^*(e_g⁻¹) ⊗ f^*(e_g⁻¹)`
  rw [← cancel_epi ((Scheme.Modules.pullback f).map ((ee g).inv.app A) ⊗ₘ
    (Scheme.Modules.pullback f).map ((ee g).inv.app B))]
  -- LHS: naturality of `μ_f`
  have n1 := Functor.LaxMonoidal.μ_natural (Scheme.Modules.pullback f) ((ee g).inv.app A) ((ee g).inv.app B)
  simp only [Functor.comp_obj] at n1
  rw [reassoc_of% n1]
  rw [mu_sheafified f, mu_sheafified g, mu_sheafified (f ≫ g)]
  simp only [Functor.map_comp, Category.assoc]
  have c1 : (Scheme.Modules.pullback f).map ((ee g).inv.app A ⊗ₘ (ee g).inv.app B) ≫
      (Scheme.Modules.pullback f).map ((ee g).hom.app A ⊗ₘ (ee g).hom.app B) = 𝟙 _ := by
    rw [← Functor.map_comp, tensorHom_comp_tensorHom, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    simp
  have c2 : (Scheme.Modules.pullback f).map (Functor.OplaxMonoidal.δ (L Y) ((PP g).obj A) ((PP g).obj B)) ≫
      (Scheme.Modules.pullback f).map (Functor.LaxMonoidal.μ (L Y) ((PP g).obj A) ((PP g).obj B)) = 𝟙 _ := by
    rw [← Functor.map_comp, Functor.Monoidal.δ_μ, CategoryTheory.Functor.map_id]
  have c3 : (ee f).inv.app ((PP g).obj A ⊗ (PP g).obj B) ≫
      (Scheme.Modules.pullback f).map ((L Y).map (Functor.LaxMonoidal.μ (PP g) A B)) =
      (L X).map ((PP f).map (Functor.LaxMonoidal.μ (PP g) A B)) ≫ (ee f).inv.app ((PP g).obj (A ⊗ B)) :=
    ((ee f).inv.naturality (Functor.LaxMonoidal.μ (PP g) A B)).symm
  have c4 : (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map (Functor.OplaxMonoidal.δ (L Z) A B)) ≫
      (pullbackComp f g).hom.app ((L Z).obj A ⊗ (L Z).obj B) =
      (pullbackComp f g).hom.app ((L Z).obj (A ⊗ B)) ≫
        (Scheme.Modules.pullback (f ≫ g)).map (Functor.OplaxMonoidal.δ (L Z) A B) :=
    (pullbackComp f g).hom.naturality (Functor.OplaxMonoidal.δ (L Z) A B)
  have hE : ∀ C : Z.PresheafOfModules, (pullbackComp f g).hom.app ((L Z).obj C) =
      (Scheme.Modules.pullback f).map ((ee g).hom.app C) ≫ (ee f).hom.app ((PP g).obj C) ≫
        (L X).map ((pcP f g).hom.app C) ≫ (ee (f ≫ g)).inv.app C := by
    intro C
    rw [reassoc_of% (ee_comp f g C), Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have c5 : (ee f).inv.app ((PP g).obj (A ⊗ B)) ≫ (Scheme.Modules.pullback f).map ((ee g).inv.app (A ⊗ B)) ≫
      (pullbackComp f g).hom.app ((L Z).obj (A ⊗ B)) =
      (L X).map ((pcP f g).hom.app (A ⊗ B)) ≫ (ee (f ≫ g)).inv.app (A ⊗ B) := by
    rw [hE]
    simp [← Functor.map_comp_assoc]
  have c6 : ∀ C : Z.PresheafOfModules, (Scheme.Modules.pullback f).map ((ee g).inv.app C) ≫
      (pullbackComp f g).hom.app ((L Z).obj C) ≫ (ee (f ≫ g)).hom.app C =
      (ee f).hom.app ((PP g).obj C) ≫ (L X).map ((pcP f g).hom.app C) := by
    intro C
    rw [hE]
    simp [← Functor.map_comp_assoc]
  rw [reassoc_of% c1]
  try simp only [Category.id_comp]
  rw [reassoc_of% c2]
  try simp only [Category.id_comp]
  rw [reassoc_of% c3, c4, reassoc_of% c5]
  rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]
  rw [c6, c6, ← tensorHom_comp_tensorHom_assoc, Functor.LaxMonoidal.μ_natural_assoc]
  have hP := congrArg (fun φ => (L X).map φ) (pcP_monoidal f g A B)
  simp only [Functor.map_comp] at hP
  rw [reassoc_of% hP]

/-- The counit `L(M.val) ≅ M`. -/
abbrev epsM (M : Z.Modules) : (L Z).obj M.val ≅ M :=
  (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.obj)).counit).app M

/-- **`pullbackComp` is monoidal**, from (E) and (P). -/
theorem pullbackComp_monoidal (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules) :
    Functor.LaxMonoidal.μ (Scheme.Modules.pullback f) ((Scheme.Modules.pullback g).obj M)
        ((Scheme.Modules.pullback g).obj N) ≫
      (Scheme.Modules.pullback f).map (Functor.LaxMonoidal.μ (Scheme.Modules.pullback g) M N) ≫
        (pullbackComp f g).hom.app (M ⊗ N) =
      ((pullbackComp f g).hom.app M ⊗ₘ (pullbackComp f g).hom.app N) ≫
        Functor.LaxMonoidal.μ (Scheme.Modules.pullback (f ≫ g)) M N := by
  rw [← cancel_epi ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map (epsM M).hom) ⊗ₘ
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map (epsM N).hom))]
  rw [Functor.LaxMonoidal.μ_natural_assoc, ← Functor.map_comp_assoc, Functor.LaxMonoidal.μ_natural,
    Functor.map_comp_assoc]
  have nc := (pullbackComp f g).hom.naturality ((epsM M).hom ⊗ₘ (epsM N).hom)
  simp only [Functor.comp_map] at nc
  rw [nc, tensorHom_comp_tensorHom_assoc]
  have nM := (pullbackComp f g).hom.naturality (epsM M).hom
  have nN := (pullbackComp f g).hom.naturality (epsM N).hom
  simp only [Functor.comp_map] at nM nN
  rw [nM, nN, ← tensorHom_comp_tensorHom_assoc, Functor.LaxMonoidal.μ_natural]
  rw [reassoc_of% (main_sheafified f g M.val N.val)]

end WeilProof.PBM

theorem WeilProof.pullbackCompMonoidal_proof : WeilProof.PullbackCompMonoidal :=
  fun f g M N => WeilProof.PBM.pullbackComp_monoidal f g M N

#print axioms WeilProof.pullbackCompMonoidal_proof

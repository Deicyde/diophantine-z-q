import ZInQKernel.Contrib.OneProof.WeilFormula
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.DescentIsomorphism
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.DescentEffective
import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# Descent of a translation-invariant trivialization along `m` (phisurj)

`PhiSurj.Desc.nonempty_iso_of_invariant`: for `m : X ⟶ X` an fpqc covering, endomorphisms `tᵢ` with `tᵢ ≫ m = m`
whose sections `x ↦ (x, tᵢ x)` cover `X ×_{m,X,m} X` by open immersions, a quasi-coherent `M` and `ψ : 𝒪 ≅ m^*M`
that is `tᵢ`-invariant (Mumford's formula `t^*ψ ∘ ψ⁻¹` is `1`), `M ≅ 𝒪`. The descent step is the vendored
`nonempty_iso_of_toDescentData_iso` (fpqc descent of quasi-coherent modules is fully faithful); the compatibility over
the chosen pullback is checked after pulling back along the sections (Mathlib's `DescentData'`).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite
open Pseudofunctor LocallyDiscreteOpToCat

namespace PhiSurj.Desc

open Scheme.Modules PicDict.Transport

variable {X : Scheme.{0}} (m : X ⟶ X)

/-- The chosen pullback `X ×_{m,X,m} X`. -/
abbrev cpb : ChosenPullback m m where
  pullback := pullback m m
  p₁ := pullback.fst m m
  p₂ := pullback.snd m m
  condition := pullback.condition
  isLimit := pullbackIsPullback m m

lemma cpb3_w : (pullback.fst (cpb m).p₂ (cpb m).p₁ ≫ (cpb m).p₁) ≫ m =
    (pullback.snd (cpb m).p₂ (cpb m).p₁ ≫ (cpb m).p₂) ≫ m := by
  rw [Category.assoc, Category.assoc, (cpb m).condition, pullback.condition_assoc, (cpb m).condition]

/-- A chosen triple pullback. -/
def cpb3 : ChosenPullback₃ (cpb m) (cpb m) (cpb m) where
  chosenPullback :=
    { pullback := pullback (cpb m).p₂ (cpb m).p₁
      p₁ := pullback.fst _ _
      p₂ := pullback.snd _ _
      condition := pullback.condition
      isLimit := pullbackIsPullback _ _ }
  p := pullback.fst _ _ ≫ (cpb m).p
  p₁ := pullback.fst _ _ ≫ (cpb m).p₁
  p₃ := pullback.snd _ _ ≫ (cpb m).p₂
  l :=
    { f := pullback.lift (pullback.fst (cpb m).p₂ (cpb m).p₁ ≫ (cpb m).p₁)
        (pullback.snd (cpb m).p₂ (cpb m).p₁ ≫ (cpb m).p₂) (cpb3_w m)
      f_p₁ := by simp
      f_p₂ := by simp
      f_p := by simp }
  hp₁ := rfl
  hp₃ := rfl

section Generic

lemma toLoc_comp_eq {C : Type*} [Category* C] {a b c : C} (f : b ⟶ c) (g : a ⟶ b) {f' : a ⟶ c}
    (h : g ≫ f = f') : f.op.toLoc ≫ g.op.toLoc = f'.op.toLoc := by
  subst h; rfl

variable {C : Type*} [Category* C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {ι : Type*} {S : C} {X' : ι → C} {f : ∀ i, X' i ⟶ S}

/-- Pulling back a descent datum's comparison map along `g`. -/
lemma map_descentData_hom (D : F.DescentData f) {Y Y' : C} (q : Y ⟶ S) {i₁ i₂ : ι}
    (f₁ : Y ⟶ X' i₁) (f₂ : Y ⟶ X' i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) (g : Y' ⟶ Y)
    (q' : Y' ⟶ S) (hq : g ≫ q = q')
    (gf₁ : Y' ⟶ X' i₁) (gf₂ : Y' ⟶ X' i₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (F.map g.op.toLoc).toFunctor.map (D.hom q f₁ f₂ hf₁ hf₂) =
      (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by rw [← hgf₁]; rfl)).inv.toNatTrans.app _ ≫
        D.hom q' gf₁ gf₂ (by rw [← hq, ← hgf₁, Category.assoc, hf₁])
          (by rw [← hq, ← hgf₂, Category.assoc, hf₂]) ≫
        (F.mapComp' f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by rw [← hgf₂]; rfl)).hom.toNatTrans.app _ := by
  rw [map_eq_pullHom _ g gf₁ gf₂ hgf₁ hgf₂, D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]

/-- Pulling back a pulled-back morphism along `g`. -/
lemma map_map_eq {Y Y' Z : C} (f₁ : Y ⟶ Z) (g : Y' ⟶ Y) (gf₁ : Y' ⟶ Z) (hgf₁ : g ≫ f₁ = gf₁)
    {A B : F.obj (.mk (op Z))} (a : A ⟶ B) :
    (F.map g.op.toLoc).toFunctor.map ((F.map f₁.op.toLoc).toFunctor.map a) =
      (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by rw [← hgf₁]; rfl)).inv.toNatTrans.app _ ≫
        (F.map gf₁.op.toLoc).toFunctor.map a ≫
        (F.mapComp' f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by rw [← hgf₁]; rfl)).hom.toNatTrans.app _ :=
  (mapComp'_naturality_1 F _ _ _ _ a).symm

set_option backward.isDefEq.respectTransparency false in
/-- **The descent condition over the universal pair from the sections.** For the single arrow `m`, if morphisms on
`X₀ ×_S X₀` are determined by their pull-backs along sections `s k` (`s k ≫ p₁ = 𝟙`, `s k ≫ p₂ = g k`), the
compatibility of `E` over `(p₁, p₂)` follows from the compatibilities over `(𝟙, g k)`. -/
lemma comm_universal_of_sections {S X₀ : C} (m : X₀ ⟶ S) (P : ChosenPullback m m)
    (A B : F.obj (.mk (op S)))
    (E : (F.map m.op.toLoc).toFunctor.obj A ⟶ (F.map m.op.toLoc).toFunctor.obj B)
    {κ : Type*} (s : κ → (X₀ ⟶ P.pullback)) (g : κ → (X₀ ⟶ X₀)) (hs1 : ∀ k, s k ≫ P.p₁ = 𝟙 X₀)
    (hs2 : ∀ k, s k ≫ P.p₂ = g k) (hg : ∀ k, g k ≫ m = m)
    (hinj : ∀ α β : (F.map P.p₁.op.toLoc).toFunctor.obj ((F.map m.op.toLoc).toFunctor.obj A) ⟶
        (F.map P.p₂.op.toLoc).toFunctor.obj ((F.map m.op.toLoc).toFunctor.obj B),
      (∀ k, (F.map (s k).op.toLoc).toFunctor.map α = (F.map (s k).op.toLoc).toFunctor.map β) → α = β)
    (H : ∀ k, (F.map (𝟙 X₀).op.toLoc).toFunctor.map E ≫
        (DescentData.ofObj (f := fun _ : PUnit.{1} => m) B).hom m (i₁ := ⟨⟩) (i₂ := ⟨⟩) (𝟙 X₀) (g k)
          (Category.id_comp m) (hg k) =
      (DescentData.ofObj (f := fun _ : PUnit.{1} => m) A).hom m (i₁ := ⟨⟩) (i₂ := ⟨⟩) (𝟙 X₀) (g k)
          (Category.id_comp m) (hg k) ≫
        (F.map (g k).op.toLoc).toFunctor.map E) :
    (F.map P.p₁.op.toLoc).toFunctor.map E ≫
        (DescentData.ofObj (f := fun _ : PUnit.{1} => m) B).hom P.p (i₁ := ⟨⟩) (i₂ := ⟨⟩) P.p₁ P.p₂ P.hp₁ P.hp₂ =
      (DescentData.ofObj (f := fun _ : PUnit.{1} => m) A).hom P.p (i₁ := ⟨⟩) (i₂ := ⟨⟩) P.p₁ P.p₂ P.hp₁ P.hp₂ ≫
        (F.map P.p₂.op.toLoc).toFunctor.map E := by
  apply hinj
  intro k
  rw [Functor.map_comp, Functor.map_comp, map_map_eq F P.p₁ (s k) (𝟙 X₀) (hs1 k),
    map_map_eq F P.p₂ (s k) (g k) (hs2 k)]
  have hq : s k ≫ P.p = m := by rw [← P.hp₁, ← Category.assoc, hs1 k, Category.id_comp]
  erw [map_descentData_hom F (DescentData.ofObj (f := fun _ : PUnit.{1} => m) B) P.p P.p₁ P.p₂ P.hp₁ P.hp₂
      (s k) m hq (𝟙 X₀) (g k) (hs1 k) (hs2 k),
    map_descentData_hom F (DescentData.ofObj (f := fun _ : PUnit.{1} => m) A) P.p P.p₁ P.p₂ P.hp₁ P.hp₂
      (s k) m hq (𝟙 X₀) (g k) (hs1 k) (hs2 k)]
  simp only [Category.assoc]
  erw [Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  erw [reassoc_of% (H k), Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The compatibility over `(𝟙, g)` for pulled-back data reduces to a commutation with `mapComp' m g m`. -/
lemma comm_id_of {S X₀ : C} (m : X₀ ⟶ S) (A B : F.obj (.mk (op S)))
    (E : (F.map m.op.toLoc).toFunctor.obj A ⟶ (F.map m.op.toLoc).toFunctor.obj B) (g : X₀ ⟶ X₀)
    (hg : g ≫ m = m)
    (h : E ≫ (F.mapComp' m.op.toLoc g.op.toLoc m.op.toLoc (toLoc_comp_eq m g hg)).hom.toNatTrans.app B =
      (F.mapComp' m.op.toLoc g.op.toLoc m.op.toLoc (toLoc_comp_eq m g hg)).hom.toNatTrans.app A ≫
        (F.map g.op.toLoc).toFunctor.map E) :
    (F.map (𝟙 X₀).op.toLoc).toFunctor.map E ≫
        (DescentData.ofObj (f := fun _ : PUnit.{1} => m) B).hom m (i₁ := ⟨⟩) (i₂ := ⟨⟩) (𝟙 X₀) g
          (Category.id_comp m) hg =
      (DescentData.ofObj (f := fun _ : PUnit.{1} => m) A).hom m (i₁ := ⟨⟩) (i₂ := ⟨⟩) (𝟙 X₀) g
          (Category.id_comp m) hg ≫ (F.map g.op.toLoc).toFunctor.map E := by
  simp only [DescentData.ofObj_hom]
  have e1 : ∀ N : F.obj (.mk (op S)),
      (F.mapComp' m.op.toLoc (𝟙 X₀).op.toLoc m.op.toLoc (by simp)).inv.toNatTrans.app N =
        (F.mapId _).hom.toNatTrans.app ((F.map m.op.toLoc).toFunctor.obj N) := by
    intro N
    have := Pseudofunctor.mapComp'_comp_id_inv_app F m.op.toLoc N
    simpa using this
  rw [e1, e1, Category.assoc]
  have nat := (F.mapId (LocallyDiscrete.mk (op X₀))).hom.toNatTrans.naturality E
  erw [reassoc_of% nat]
  erw [h]

end Generic

/-- The module identity behind the compatibility over `(𝟙, t)`: invariance of `ψ` under `t` (Mumford's formula
is `1`) gives `θ_t ∘ (pOU m ≫ ψ) = t^*(pOU m ≫ ψ) ∘ θ_t`. -/
lemma theta_identity (t : X ⟶ X) (h : t ≫ m = m) (M : X.Modules)
    (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M)
    (hinv : (pOU t).inv ≫ (Scheme.Modules.pullback t).map ψ.hom ≫ (pullbackComp t m).hom.app M ≫
      (pullbackCongr h).hom.app M ≫ ψ.inv = 𝟙 _) :
    (pullbackCompOfEq t m m h (unit X)).hom ≫ (pOU m ≪≫ ψ).hom =
      (Scheme.Modules.pullback t).map (pOU m ≪≫ ψ).hom ≫ (pullbackCompOfEq t m m h M).hom := by
  have h1 : (Scheme.Modules.pullback t).map ψ.hom ≫ (pullbackComp t m).hom.app M ≫
      (pullbackCongr h).hom.app M = (pOU t).hom ≫ ψ.hom := by
    have e := congrArg (fun φ => (pOU t).hom ≫ φ ≫ ψ.hom) hinv
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id,
      Category.id_comp] at e
    exact e
  have h2 : (pOU t).inv ≫ (Scheme.Modules.pullback t).map (pOU m).inv ≫ (pullbackComp t m).hom.app (unit X) ≫
      (pullbackCongr h).hom.app (unit X) = (pOU m).inv := by
    conv_rhs => rw [← pOU_inv_congr h, pOU_inv_comp]
    simp only [Category.assoc]
  have h3 : (pullbackComp t m).hom.app (unit X) ≫ (pullbackCongr h).hom.app (unit X) ≫ (pOU m).hom =
      (Scheme.Modules.pullback t).map (pOU m).hom ≫ (pOU t).hom := by
    rw [← cancel_epi ((Scheme.Modules.pullback t).map (pOU m).inv), ← cancel_epi (pOU t).inv,
      reassoc_of% h2]
    simp
  simp only [pullbackCompOfEq, Iso.trans_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [h1, reassoc_of% h3]

/-- The section `x ↦ (x, t x)` of `X ×_{m,X,m} X`, for `t ≫ m = m`. -/
abbrev sec {t : X ⟶ X} (ht : t ≫ m = m) : X ⟶ (cpb m).pullback :=
  pullback.lift (𝟙 X) t (by rw [ht, Category.id_comp])

set_option maxHeartbeats 1000000 in
/-- **Descent of a trivialization along `m`.** If the sections `x ↦ (x, tᵢ x)` cover `X ×_{m,X,m} X` by open
immersions, `m` is an fpqc covering, and `ψ : 𝒪 ≅ m^*M` is invariant under every `tᵢ` (Mumford's formula is `1`),
then `M ≅ 𝒪`. -/
theorem nonempty_iso_of_invariant
    (hcov : Sieve.ofArrows (fun _ : PUnit.{1} => X) (fun _ => m) ∈ Scheme.fpqcTopology X)
    {ι : Type} (t : ι → (X ⟶ X)) (ht : ∀ i, t i ≫ m = m)
    [hopen : ∀ i, IsOpenImmersion (sec m (ht i))]
    (hsurj : ⨆ i, (sec m (ht i)).opensRange = ⊤)
    (M : X.Modules) [hM : M.IsQuasicoherent] (ψ : unit X ≅ (Scheme.Modules.pullback m).obj M)
    (hinv : ∀ i, (pOU (t i)).inv ≫ (Scheme.Modules.pullback (t i)).map ψ.hom ≫ (pullbackComp (t i) m).hom.app M ≫
      (pullbackCongr (ht i)).hom.app M ≫ ψ.inv = 𝟙 _) :
    Nonempty (unit X ≅ M) := by
  let f : PUnit.{1} → (X ⟶ X) := fun _ => m
  let sq : ∀ i j : PUnit.{1}, ChosenPullback (f i) (f j) := fun _ _ => cpb m
  let sq₃ : ∀ i j k : PUnit.{1}, ChosenPullback₃ (sq i j) (sq j k) (sq i k) := fun _ _ _ => cpb3 m
  have hO : (unit X).IsQuasicoherent := inferInstance
  refine nonempty_iso_of_toDescentData_iso f hcov (M := unit X) (N := M) hO hM ?_
  refine (DescentData'.descentDataEquivalence modulesPseudofunctor sq sq₃).fullyFaithfulInverse.preimageIso ?_
  refine DescentData'.isoMk (fun _ => pOU m ≪≫ ψ) ?_
  intro i j
  have hs1 : ∀ k, sec m (ht k) ≫ (cpb m).p₁ = 𝟙 X := fun k => pullback.lift_fst _ _ _
  have hs2 : ∀ k, sec m (ht k) ≫ (cpb m).p₂ = t k := fun k => pullback.lift_snd _ _ _
  have hs : Sieve.ofArrows (fun _ => X) (fun k => sec m (ht k)) ∈ Scheme.fpqcTopology (cpb m).pullback :=
    ofArrows_mem_fpqcTopology_of_isOpenImmersion _ hsurj
  refine comm_universal_of_sections modulesPseudofunctor m (cpb m) (unit X) M (pOU m ≪≫ ψ).hom
    (fun k => sec m (ht k)) t hs1 hs2 ht ?_ ?_
  · intro α β h
    have h0 : SheafOfModules.IsQuasicoherent ((modulesPseudofunctor.map m.op.toLoc).toFunctor.obj (unit X)) :=
      isQuasicoherent_pullback m (unit X)
    have h0' : SheafOfModules.IsQuasicoherent ((modulesPseudofunctor.map m.op.toLoc).toFunctor.obj M) :=
      isQuasicoherent_pullback m M
    have hA : SheafOfModules.IsQuasicoherent ((modulesPseudofunctor.map (cpb m).p₁.op.toLoc).toFunctor.obj
        ((modulesPseudofunctor.map m.op.toLoc).toFunctor.obj (unit X))) :=
      isQuasicoherent_pullback _ _
    have hB : SheafOfModules.IsQuasicoherent ((modulesPseudofunctor.map (cpb m).p₂.op.toLoc).toFunctor.obj
        ((modulesPseudofunctor.map m.op.toLoc).toFunctor.obj M)) :=
      isQuasicoherent_pullback _ _
    apply (bijective_toDescentData_map_of_mem_fpqcTopology _ hs _ _ hA hB).1
    ext k
    exact h k
  · intro k
    refine comm_id_of modulesPseudofunctor m (unit X) M (pOU m ≪≫ ψ).hom (t k) (ht k) ?_
    have hθ := theta_identity m (t k) (ht k) M ψ (hinv k)
    erw [modulesPseudofunctor_mapComp'_hom_app_eq m (t k) m (ht k) M,
      modulesPseudofunctor_mapComp'_hom_app_eq m (t k) m (ht k) (unit X)]
    have hθ' : (pOU m ≪≫ ψ).hom ≫ (pullbackCompOfEq (t k) m m (ht k) M).inv =
        (pullbackCompOfEq (t k) m m (ht k) (unit X)).inv ≫
          (Scheme.Modules.pullback (t k)).map (pOU m ≪≫ ψ).hom := by
      rw [Iso.eq_inv_comp, ← Category.assoc, hθ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact hθ'

end PhiSurj.Desc

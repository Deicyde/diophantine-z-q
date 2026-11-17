import ZInQKernel.Contrib.OneProof.NeronGoodModelIso

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace DedekindFree

open ZInQ.Contrib LeafQM.AV.R1UnivRigid PkgI3

/-- `Spec E → Spec K` for a field extension. -/
abbrev κm (K E : Type) [Field K] [Field E] [Algebra K E] :
    Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K E))

lemma one_left_eq {K : Type} [Field K] (A : AbVar K) : (1 : A.Pt K).left = η[A.X].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
  simp [AbVar.ptObj]

instance grpObj_pullback {K E : Type} [Field K] [Field E] [Algebra K E] (A : AbVar K) :
    GrpObj ((Over.pullback (κm K E)).obj A.X) := Functor.grpObjObj

/-- `A_E`, as `PkgI3.AbVar.baseChange` but reducible. -/
abbrev AE {K : Type} [Field K] (A : AbVar K) (E : Type) [Field E] [Algebra K E] : AbVar E where
  X := (Over.pullback (κm K E)).obj A.X
  grp := grpObj_pullback A
  proper := by dsimp; infer_instance
  smooth := by dsimp; infer_instance
  geomInt := by dsimp; infer_instance

lemma baseChange_eta_left_fst {K E : Type} [Field K] [Field E] [Algebra K E] (A : AbVar K) :
    η[(AE A E).X].left ≫ pullback.fst A.X.hom (κm K E) = κm K E ≫ η[A.X].left := by
  change (Functor.LaxMonoidal.ε (Over.pullback (κm K E)) ≫ (Over.pullback (κm K E)).map η[A.X]).left ≫ _ = _
  have hs : inv (pullback.snd (𝟙 _) (κm K E)) ≫ pullback.fst (𝟙 _) (κm K E) = κm K E := by
    rw [IsIso.inv_comp_eq, ← pullback.condition, Category.comp_id]
  simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst,
    Over.ε_pullback_left]
  rw [← Category.assoc]
  erw [hs]

lemma one_left_hom {E : Type} [Field E] (B : AbVar E) : (1 : B.Pt E).left ≫ B.X.hom = 𝟙 _ := by
  rw [Over.w (1 : B.Pt E)]
  exact ZInQ.Contrib.GroupLawNeron.spec_algebraMap_self E

lemma eta_left_g {K : Type} [Field K] {S : Scheme.{0}} {F : Over S} {e : S ⟶ F.left}
    {ηS : Spec (CommRingCat.of K) ⟶ S} {A : AbVar K} {g : A.X.left ⟶ F.left}
    (hA : IsAbVarFibre F e ηS A g) : η[A.X].left ≫ g = ηS ≫ e := by
  have h2 := hA.2
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left] at h2
  simp only [AbVar.ptObj, Over.mk_hom, ZInQ.Contrib.GroupLawNeron.spec_algebraMap_self] at h2
  rw [← h2, Category.assoc]; exact (Category.id_comp _).symm

lemma baseChange_one_left_fst {K E : Type} [Field K] [Field E] [Algebra K E] (A : AbVar K) :
    (1 : (AE A E).Pt E).left ≫ pullback.fst A.X.hom (κm K E) = κm K E ≫ η[A.X].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left, Category.assoc, baseChange_eta_left_fst]
  simp only [AbVar.ptObj, Over.mk_hom, ZInQ.Contrib.GroupLawNeron.spec_algebraMap_self]
  exact Category.id_comp _


open scoped CategoryTheory.Obj in
/-- **Inverse on a fibre** (rigidity, as `R1UnivRigid.isGrpFibre_of_rigidity`): the identification of an abelian
variety with a fibre of a proper smooth group object commutes with the inverses. -/
theorem inv_fibre {S : Scheme.{0}} (F : Over S) [GrpObj F] [IsProper F.hom]
    [Smooth F.hom] {K : Type} [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (A : AbVar K)
    (g : A.X.left ⟶ F.left) (h : IsAbVarFibre F η[F].left s A g) : ι[A.X].left ≫ g = g ≫ ι[F].left := by
  obtain ⟨hpb, h1⟩ := h
  let Fs : Over (Spec (CommRingCat.of K)) := (Over.pullback s).obj F
  have : IsProper Fs.hom := by dsimp [Fs]; infer_instance
  have : Smooth Fs.hom := by dsimp [Fs]; infer_instance
  let eA : A.X ≅ Fs := Over.isoMk hpb.isoPullback (by simp [Fs])
  have : GeometricallyIntegral Fs.hom := by
    have e : eA.inv.left ≫ A.X.hom = Fs.hom := Over.w eA.inv
    have : MorphismProperty.RespectsIso (C := Scheme) @GeometricallyIntegral := by
      rw [GeometricallyIntegral.eq_geometrically]; infer_instance
    rw [← e]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral eA.inv.left
      A.X.hom).2 inferInstance
  let AF : AbVar K := ⟨Fs⟩
  have hg : eA.hom.left ≫ pullback.fst F.hom s = g := hpb.isoPullback_hom_fst
  have h1' : η[A.X].left ≫ g = s ≫ η[F].left := by
    rw [← h1]
    change _ = ((toUnit (AbVar.ptObj (K := K) K)) ≫ η[A.X]).left ≫ g
    rw [Over.comp_left, Over.toUnit_left]
    simp [AbVar.ptObj, Algebra.algebraMap_self]
  have hη : η[A.X] ≫ eA.hom = η[AF.X] := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [Over.comp_left, Category.assoc, hg, h1']
      change s ≫ η[F].left = (Functor.LaxMonoidal.ε (Over.pullback s) ≫
        (Over.pullback s).map η[F]).left ≫ pullback.fst F.hom s
      have hs : inv (pullback.snd (𝟙 S) s) ≫ pullback.fst (𝟙 S) s = s := by
        rw [IsIso.inv_comp_eq, ← pullback.condition, Category.comp_id]
      simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst,
        Over.ε_pullback_left]
      rw [← Category.assoc]
      erw [hs]
    · exact (Over.w (η[A.X] ≫ eA.hom)).trans (Over.w η[AF.X]).symm
  have hmon : IsMonHom eA.hom := G0FibreSimple.rigidityHom K A AF eA.hom hη
  have hi : ι[A.X] ≫ eA.hom = eA.hom ≫ ι[AF.X] := by
    have := GrpObj.inv_comp (𝟙 A.X) eA.hom
    rw [Hom.inv_def, Hom.inv_def, Category.id_comp, Category.id_comp] at this
    exact this
  rw [← hg, ← Category.assoc, ← Over.comp_left, hi]
  change (eA.hom ≫ (Over.pullback s).map ι[F]).left ≫ pullback.fst F.hom s = _
  simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst]

section Fibre

variable {S S' : Scheme.{0}} (p : S' ⟶ S) (F : Over S) (e : S ⟶ F.left) (he : e ≫ F.hom = 𝟙 S)
  {K E : Type} [Field K] [Field E] [Algebra K E]
  (ηS : Spec (CommRingCat.of K) ⟶ S) (η₁ : Spec (CommRingCat.of E) ⟶ S')
  (hsq : η₁ ≫ p = κm K E ≫ ηS)
  (A : AbVar K) (g : A.X.left ⟶ F.left) (hA : IsAbVarFibre F e ηS A g)

/-- The base-changed section `e₁ = (p ≫ e, id)`. -/
def e₁ : S' ⟶ ((Over.pullback p).obj F).left :=
  pullback.lift (p ≫ e) (𝟙 S') (by rw [Category.assoc, he]; simp)

include hA hsq in
/-- The fibre map of `F₁ = F ×_S S'` at `η₁`, from that of `F` at `ηS`. -/
def g₁ : pullback A.X.hom (κm K E) ⟶ ((Over.pullback p).obj F).left :=
  pullback.lift (pullback.fst A.X.hom (κm K E) ≫ g) (pullback.snd A.X.hom (κm K E) ≫ η₁) (by
    rw [Category.assoc, hA.1.w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, hsq])

lemma g₁_fst : g₁ p F e ηS η₁ hsq A g hA ≫ pullback.fst F.hom p = pullback.fst A.X.hom (κm K E) ≫ g :=
  pullback.lift_fst _ _ _

lemma g₁_snd : g₁ p F e ηS η₁ hsq A g hA ≫ pullback.snd F.hom p = pullback.snd A.X.hom (κm K E) ≫ η₁ :=
  pullback.lift_snd _ _ _

theorem isAbVarFibre₁ :
    IsAbVarFibre ((Over.pullback p).obj F) (e₁ p F e he) η₁ (AE A E) (g₁ p F e ηS η₁ hsq A g hA) := by
  constructor
  · have hcomp : IsPullback (pullback.fst A.X.hom (κm K E) ≫ g) (pullback.snd A.X.hom (κm K E)) F.hom
        (κm K E ≫ ηS) := (IsPullback.of_hasPullback A.X.hom (κm K E)).paste_horiz hA.1
    refine IsPullback.of_right (h₁₂ := pullback.fst F.hom p) (h₂₂ := p) ?_ (g₁_snd ..)
      (IsPullback.of_hasPullback F.hom p)
    rw [g₁_fst, hsq]
    exact hcomp
  · have key : ∀ x : Spec (CommRingCat.of E) ⟶ pullback A.X.hom (κm K E),
        x ≫ pullback.fst A.X.hom (κm K E) = κm K E ≫ η[A.X].left →
        x ≫ pullback.snd A.X.hom (κm K E) = 𝟙 _ → x ≫ g₁ p F e ηS η₁ hsq A g hA = η₁ ≫ e₁ p F e he := by
      intro x h1 h2
      apply pullback.hom_ext
      · rw [Category.assoc, g₁_fst, ← Category.assoc, h1, Category.assoc, eta_left_g hA]
        simp only [e₁, Category.assoc, pullback.lift_fst]
        rw [← Category.assoc, ← Category.assoc, hsq]
      · rw [Category.assoc, g₁_snd, ← Category.assoc, h2, Category.id_comp]
        simp [e₁]
    exact key _ (baseChange_one_left_fst A) (one_left_hom (AE A E))

end Fibre

lemma AE_inv_left_fst {K E : Type} [Field K] [Field E] [Algebra K E] (A : AbVar K) :
    ι[(AE A E).X].left ≫ pullback.fst A.X.hom (κm K E) = pullback.fst A.X.hom (κm K E) ≫ ι[A.X].left := by
  change ((Over.pullback (κm K E)).map ι[A.X]).left ≫ _ = _
  simp

section Generic

variable {S S' : Scheme.{0}} (p : S' ⟶ S) (F : Over S) (e : S ⟶ F.left) (he : e ≫ F.hom = 𝟙 S)
  {K E : Type} [Field K] [Field E] [Algebra K E]
  (ηS : Spec (CommRingCat.of K) ⟶ S) (η₁ : Spec (CommRingCat.of E) ⟶ S')
  (hsq : η₁ ≫ p = κm K E ≫ ηS)
  (A : AbVar K) (g : A.X.left ⟶ F.left) (hA : IsAbVarFibre F e ηS A g)
  [IsProper F.hom] [Smooth F.hom] [GrpObj ((Over.pullback p).obj F)]
  (hη₁ : η[(Over.pullback p).obj F].left = e₁ p F e he)

include hη₁ hsq hA in
/-- **The inverse of `F₁` at a point over the generic point `η₁`** is computed by the inverse of `A` over `K`. -/
theorem gen_inv {T : Scheme.{0}} (a : T ⟶ ((Over.pullback p).obj F).left) (τ : T ⟶ Spec (CommRingCat.of E))
    (ha : a ≫ ((Over.pullback p).obj F).hom = τ ≫ η₁) :
    ∃ w : T ⟶ A.X.left, w ≫ g = a ≫ pullback.fst F.hom p ∧ w ≫ A.X.hom = τ ≫ κm K E ∧
      a ≫ ι[(Over.pullback p).obj F].left ≫ pullback.fst F.hom p = w ≫ ι[A.X].left ≫ g := by
  have hF := isAbVarFibre₁ p F e he ηS η₁ hsq A g hA
  rw [← hη₁] at hF
  have : IsProper ((Over.pullback p).obj F).hom := by dsimp; infer_instance
  have : Smooth ((Over.pullback p).obj F).hom := by dsimp; infer_instance
  have hinv := inv_fibre _ η₁ (AE A E) _ hF
  have hpbE := hF.1
  obtain ⟨v, hv1, hv2⟩ : ∃ v : T ⟶ pullback A.X.hom (κm K E),
      v ≫ g₁ p F e ηS η₁ hsq A g hA = a ∧ v ≫ pullback.snd A.X.hom (κm K E) = τ :=
    ⟨hpbE.lift a τ ha, hpbE.lift_fst _ _ _, hpbE.lift_snd _ _ _⟩
  refine ⟨v ≫ pullback.fst A.X.hom (κm K E), ?_, ?_, ?_⟩
  · rw [Category.assoc, ← g₁_fst p F e ηS η₁ hsq A g hA, ← Category.assoc, hv1]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hv2]
  · rw [← hv1, Category.assoc]
    erw [← reassoc_of% hinv]
    rw [g₁_fst, ← Category.assoc (ι[(AE A E).X].left), AE_inv_left_fst]
    simp only [Category.assoc]

end Generic

end DedekindFree

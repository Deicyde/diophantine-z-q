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

end DedekindFree

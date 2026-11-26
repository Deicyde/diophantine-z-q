import ZInQKernel.Contrib.OneProof.RC.ModelTarget.FormulaGluing

/-! Gluing local morphisms into the relative cubic that compute a given rule on field
points. The rule assigns to every field point of the source, with its ring map from the
base, an affine point of the base-changed curve. On the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve

set_option autoImplicit false

namespace ZInQ.Manuscript.RC.ModelTarget

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (T : Scheme.{0}) (s : T ⟶ Spec (.of R))

/-- A rule on field points of a scheme over the base. -/
abbrev PointRule := ∀ (F : Type) [Field F] (g : R →+* F) (p : Spec (.of F) ⟶ T),
  p ≫ s = Spec.map (CommRingCat.ofHom g) → (W.map g).toAffine.Point

variable {W T s}

theorem PointRule.congr (rule : PointRule W T s) {F : Type} [Field F] (g : R →+* F)
    {p p' : Spec (.of F) ⟶ T} (e : p = p') (hp : p ≫ s = Spec.map (CommRingCat.ofHom g))
    (hp' : p' ≫ s = Spec.map (CommRingCat.ofHom g)) : rule F g p hp = rule F g p' hp' := by
  subst e
  rfl

private theorem fieldPoint_lifts' {X Y : Scheme.{0}} {F : Type} [Field F]
    (f : Y ⟶ X) [IsOpenImmersion f] (p : Spec (.of F) ⟶ X)
    (h : p default ∈ Set.range f) :
    ∃ q : Spec (.of F) ⟶ Y, q ≫ f = p := by
  have hh : Set.range p ⊆ Set.range f := by
    rintro _ ⟨z, rfl⟩
    simpa only [Subsingleton.elim z (default : Spec (.of F))] using h
  exact ⟨IsOpenImmersion.lift f p hh, IsOpenImmersion.lift_fac _ _ _⟩

variable (W T s)

/-- Local morphisms computing one rule glue on a reduced source. -/
theorem morphism_of_rule [W.IsElliptic] [IsReduced T] (rule : PointRule W T s)
    (h : ∀ x : T, ∃ (A : CommRingCat.{0}) (inc : Spec A ⟶ T)
        (m : Spec A ⟶ Proj W.toProjective.grading) (hm : m ≫ projStructure W = inc ≫ s),
      IsOpenImmersion inc ∧ x ∈ Set.range inc ∧
      ∀ (F : Type) [Field F] (g : R →+* F) (q : Spec (.of F) ⟶ Spec A)
        (hq : q ≫ inc ≫ s = Spec.map (CommRingCat.ofHom g)),
        fieldValue W g (q ≫ m) (comp_structure W hm hq) =
          rule F g (q ≫ inc) (by rwa [Category.assoc])) :
    ∃ (m : T ⟶ Proj W.toProjective.grading) (hm : m ≫ projStructure W = s),
      ∀ (F : Type) [Field F] (g : R →+* F) (p : Spec (.of F) ⟶ T)
        (hp : p ≫ s = Spec.map (CommRingCat.ofHom g)),
        fieldValue W g (p ≫ m) (comp_structure W hm hp) = rule F g p hp := by
  classical
  choose A inc m hm hc hmem hval using h
  let cover : T.OpenCover :=
    { I₀ := T
      X x := Spec (A x)
      f := inc
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun p => ⟨p, hmem p⟩, hc⟩ }
  have agree (i j : cover.I₀) :
      pullback.fst (cover.f i) (cover.f j) ≫ m i =
        pullback.snd (cover.f i) (cover.f j) ≫ m j := by
    haveI : IsReduced (pullback (cover.f i) (cover.f j)) :=
      isReduced_of_isOpenImmersion (pullback.fst (cover.f i) (cover.f j) ≫ cover.f i)
    have h1 : (pullback.fst (cover.f i) (cover.f j) ≫ m i) ≫ projStructure W =
        pullback.fst (cover.f i) (cover.f j) ≫ inc i ≫ s := by
      rw [Category.assoc, hm]
    have h2 : (pullback.snd (cover.f i) (cover.f j) ≫ m j) ≫ projStructure W =
        pullback.fst (cover.f i) (cover.f j) ≫ inc i ≫ s := by
      rw [Category.assoc, hm, ← Category.assoc, ← Category.assoc]
      congr 1
      exact pullback.condition.symm
    apply eq_of_fieldValues W _ _ _ h1 h2
    intro F _ g q hq
    have hq1 : (q ≫ pullback.fst (cover.f i) (cover.f j)) ≫ inc i ≫ s =
        Spec.map (CommRingCat.ofHom g) := by rw [Category.assoc]; exact hq
    have hq2 : (q ≫ pullback.snd (cover.f i) (cover.f j)) ≫ inc j ≫ s =
        Spec.map (CommRingCat.ofHom g) := by
      rw [← hq, Category.assoc, ← Category.assoc (pullback.snd _ _), ← pullback.condition]
      rfl
    have hpt : (q ≫ pullback.fst (cover.f i) (cover.f j)) ≫ inc i =
        (q ≫ pullback.snd (cover.f i) (cover.f j)) ≫ inc j := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (q ≫ ·) pullback.condition
    calc _ = fieldValue W g ((q ≫ pullback.fst (cover.f i) (cover.f j)) ≫ m i)
          (comp_structure W (hm i) hq1) :=
          fieldValue_congr W g (Category.assoc _ _ _).symm _ _
      _ = _ := hval i F g _ hq1
      _ = _ := rule.congr g hpt _ (by rwa [Category.assoc])
      _ = fieldValue W g ((q ≫ pullback.snd (cover.f i) (cover.f j)) ≫ m j)
          (comp_structure W (hm j) hq2) := (hval j F g _ hq2).symm
      _ = _ := fieldValue_congr W g (Category.assoc _ _ _) _ _
  refine ⟨cover.glueMorphisms m agree, ?_, ?_⟩
  · apply cover.hom_ext
    intro i
    rw [← Category.assoc, cover.ι_glueMorphisms, hm]
  · intro F _ g p hp
    let i := p default
    obtain ⟨q, hq⟩ := fieldPoint_lifts' (cover.f i) p (hmem i)
    have hq' : q ≫ inc i ≫ s = Spec.map (CommRingCat.ofHom g) := by
      rw [← Category.assoc]
      change (q ≫ cover.f i) ≫ s = _
      rw [hq]
      exact hp
    calc _ = fieldValue W g (q ≫ m i) (comp_structure W (hm i) hq') :=
          fieldValue_congr W g (by rw [← hq, Category.assoc, cover.ι_glueMorphisms]) _ _
      _ = _ := hval i F g q hq'
      _ = _ := rule.congr g hq _ _

#print axioms morphism_of_rule

end ZInQ.Manuscript.RC.ModelTarget

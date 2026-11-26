import ZInQKernel.Contrib.OneProof.RC.ModelTarget.FieldValue
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! Morphisms into the relative projective cubic built from polynomial formulas on
charts of a reduced source over the base. If one of the formulas is nonzero at every
point with values in a field, and every nonzero value computes a fixed operation on
affine points, the local chart morphisms glue. Agreement on overlaps is checked at
field points (the source is reduced and the cubic is separated). This generalizes the
rational construction of `J0Cusps.projectiveMorphism_of_formulas` to any base. On the
spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve HomogeneousLocalization

set_option autoImplicit false

namespace ZInQ.Manuscript.RC.ModelTarget

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

theorem fieldValue_congr {F : Type} [Field F] (g : R →+* F)
    {p p' : Spec (.of F) ⟶ Proj W.toProjective.grading} (e : p = p')
    (hp : p ≫ projStructure W = Spec.map (CommRingCat.ofHom g))
    (hp' : p' ≫ projStructure W = Spec.map (CommRingCat.ofHom g)) :
    fieldValue W g p hp = fieldValue W g p' hp' := by
  subst e
  rfl

/-- The ring map to a field induced by a field point of a scheme over the base. -/
def pointRing {T : Scheme.{0}} (s : T ⟶ Spec (.of R)) {F : Type} [Field F]
    (p : Spec (.of F) ⟶ T) : R →+* F :=
  (Spec.preimage (p ≫ s)).hom

theorem pointRing_spec {T : Scheme.{0}} (s : T ⟶ Spec (.of R)) {F : Type} [Field F]
    (p : Spec (.of F) ⟶ T) : p ≫ s = Spec.map (CommRingCat.ofHom (pointRing s p)) := by
  rw [pointRing, CommRingCat.ofHom_hom, Spec.map_preimage]

instance projStructure_isSeparated : IsSeparated (projStructure W) := by
  unfold projStructure
  infer_instance

theorem comp_structure {T : Scheme.{0}} {s : T ⟶ Spec (.of R)} {F : Type} [Field F]
    {g : R →+* F} {f : T ⟶ Proj W.toProjective.grading} (hf : f ≫ projStructure W = s)
    {p : Spec (.of F) ⟶ T} (hp : p ≫ s = Spec.map (CommRingCat.ofHom g)) :
    (p ≫ f) ≫ projStructure W = Spec.map (CommRingCat.ofHom g) := by
  rw [Category.assoc, hf, hp]

/-- Two morphisms from a reduced scheme with the same field-point values agree. -/
theorem eq_of_fieldValues [W.IsElliptic] {T : Scheme.{0}} [IsReduced T] (s : T ⟶ Spec (.of R))
    (f f' : T ⟶ Proj W.toProjective.grading) (hf : f ≫ projStructure W = s)
    (hf' : f' ≫ projStructure W = s)
    (h : ∀ (F : Type) [Field F] (g : R →+* F) (p : Spec (.of F) ⟶ T)
      (hp : p ≫ s = Spec.map (CommRingCat.ofHom g)),
      fieldValue W g (p ≫ f) (comp_structure W hf hp) = fieldValue W g (p ≫ f') (comp_structure W hf' hp)) :
    f = f' := by
  apply ext_of_fromSpecResidueField_eq f f' (projStructure W) Set.univ dense_univ
  · intro x _
    exact fieldValue_injective W (pointRing s (T.fromSpecResidueField x)) _ _ _ _
      (h _ _ _ (pointRing_spec s _))
  · rw [hf, hf']

private theorem fieldPoint_lifts {X Y : Scheme.{0}} {F : Type} [Field F]
    (f : Y ⟶ X) [IsOpenImmersion f] (p : Spec (.of F) ⟶ X)
    (h : p default ∈ Set.range f) :
    ∃ q : Spec (.of F) ⟶ Y, q ≫ f = p := by
  have hh : Set.range p ⊆ Set.range f := by
    rintro _ ⟨z, rfl⟩
    simpa only [Subsingleton.elim z (default : Spec (.of F))] using h
  exact ⟨IsOpenImmersion.lift f p hh, IsOpenImmersion.lift_fac _ _ _⟩

variable {n : ℕ} (T : Scheme.{0}) (s : T ⟶ Spec (.of R)) (f : Fin n → (T ⟶ Proj W.toProjective.grading))
  (hf : ∀ a, f a ≫ projStructure W = s)
  (op : ∀ (F : Type) [Field F] (g : R →+* F),
    (Fin n → (W.map g).toAffine.Point) → (W.map g).toAffine.Point)

/-- The defining property of a morphism computing `op` at every field point. -/
def Computes {Y : Scheme.{0}} (inc : Y ⟶ T) (m : Y ⟶ Proj W.toProjective.grading)
    (hm : m ≫ projStructure W = inc ≫ s) : Prop :=
  ∀ (F : Type) [Field F] (g : R →+* F) (q : Spec (.of F) ⟶ Y)
    (hq : q ≫ inc ≫ s = Spec.map (CommRingCat.ofHom g)),
    fieldValue W g (q ≫ m) (comp_structure W hm hq) =
      op F g (fun a => fieldValue W g ((q ≫ inc) ≫ f a)
        (comp_structure W (hf a) (by rwa [Category.assoc])))

/-- Local morphisms computing one operation glue on a reduced source. -/
theorem morphism_of_local [W.IsElliptic] [IsReduced T]
    (h : ∀ x : T, ∃ (A : CommRingCat.{0}) (inc : Spec A ⟶ T)
        (m : Spec A ⟶ Proj W.toProjective.grading) (hm : m ≫ projStructure W = inc ≫ s),
      IsOpenImmersion inc ∧ x ∈ Set.range inc ∧ Computes W T s f hf op inc m hm) :
    ∃ (m : T ⟶ Proj W.toProjective.grading) (hm : m ≫ projStructure W = s),
      Computes W T s f hf op (𝟙 T) m (by rw [hm, Category.id_comp]) := by
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
    have e1 := hval i F g _ hq1
    have e2 := hval j F g _ hq2
    have hpt : (q ≫ pullback.fst (cover.f i) (cover.f j)) ≫ inc i =
        (q ≫ pullback.snd (cover.f i) (cover.f j)) ≫ inc j := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (q ≫ ·) pullback.condition
    calc _ = fieldValue W g ((q ≫ pullback.fst (cover.f i) (cover.f j)) ≫ m i)
          (comp_structure W (hm i) hq1) :=
          fieldValue_congr W g (Category.assoc _ _ _).symm _ _
      _ = _ := e1
      _ = op F g (fun a => fieldValue W g (((q ≫ pullback.snd (cover.f i) (cover.f j)) ≫ inc j) ≫ f a)
          (comp_structure W (hf a) (by rwa [Category.assoc]))) := by
          congr 1
          funext a
          exact fieldValue_congr W g (by rw [hpt]) _ _
      _ = fieldValue W g ((q ≫ pullback.snd (cover.f i) (cover.f j)) ≫ m j)
          (comp_structure W (hm j) hq2) := e2.symm
      _ = _ := fieldValue_congr W g (Category.assoc _ _ _) _ _
  refine ⟨cover.glueMorphisms m agree, ?_, ?_⟩
  · apply cover.hom_ext
    intro i
    rw [← Category.assoc, cover.ι_glueMorphisms, hm]
  · intro F _ g p hp
    let i := p default
    obtain ⟨q, hq⟩ := fieldPoint_lifts (cover.f i) p (hmem i)
    have hq' : q ≫ inc i ≫ s = Spec.map (CommRingCat.ofHom g) := by
      rw [← Category.assoc]
      change (q ≫ cover.f i) ≫ s = _
      rw [hq]
      simpa using hp
    calc _ = fieldValue W g (q ≫ m i) (comp_structure W (hm i) hq') :=
          fieldValue_congr W g (by rw [← hq, Category.assoc, cover.ι_glueMorphisms]) _ _
      _ = _ := hval i F g q hq'
      _ = _ := by
          congr 1
          funext a
          exact fieldValue_congr W g (by rw [Category.comp_id]; exact congrArg (· ≫ f a) hq) _ _

#print axioms eq_of_fieldValues
#print axioms morphism_of_local

end ZInQ.Manuscript.RC.ModelTarget

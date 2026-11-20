import ZInQKernel.Contrib.OneProof.T10Proetale.ExtensionFibres

/-!
# The sheaf of lifts attached to a degree-one class

The local fibres of an extension form a sheaf of sets. A choice of lift
trivializes it on the slice over the object admitting that lift.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace ZInQ.Manuscript.T10Proetale

noncomputable section

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} {T : C} (hT : IsTerminal T)
  (s : S.X₃.obj.obj (op T))

/-- The restrictions of one section at the terminal object. -/
abbrev sectionAt (U : C) : S.X₃.obj.obj (op U) :=
  S.X₃.obj.map (hT.from U).op s

private theorem sectionAt_restrict {U V : C} (f : V ⟶ U) :
    S.X₃.obj.map f.op (sectionAt hT s U) = sectionAt hT s V := by
  rw [← Functor.map_comp_apply, ← op_comp, hT.hom_ext (f ≫ hT.from U) (hT.from V)]

/-- The presheaf of local lifts of a section. -/
def liftPresheaf : Cᵒᵖ ⥤ Type w where
  obj U := sectionLifts (S := S) (sectionAt hT s U.unop)
  map {U V} f := ↾fun t => ⟨S.X₂.obj.map f t.val, by
    rw [NatTrans.naturality_apply S.g.hom f, t.2]
    exact sectionAt_restrict hT s f.unop⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    simp

variable [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- Compatible local lifts glue in the middle sheaf, and the glued section is a lift
because the quotient sheaf is separated. -/
theorem liftPresheaf_isSheaf : Presieve.IsSheaf J (liftPresheaf hT s) := by
  intro U R hR
  let E := S.X₂.obj ⋙ forget AddCommGrpCat.{w}
  let Q := S.X₃.obj ⋙ forget AddCommGrpCat.{w}
  let F := liftPresheaf hT s
  have hE : Presieve.IsSheafFor E R.arrows :=
    ((isSheaf_iff_isSheaf_of_type J E).mp ((sheafCompose J (forget AddCommGrpCat.{w})).obj S.X₂).property)
      R hR
  have hQ : Presieve.IsSeparatedFor Q R.arrows :=
    ((isSheaf_iff_isSheaf_of_type J Q).mp ((sheafCompose J (forget AddCommGrpCat.{w})).obj S.X₃).property)
      |>.isSeparated R hR
  intro t ht
  let a : Presieve.FamilyOfElements E R.arrows := fun _ f hf => (t f hf).val
  have ha : a.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h
    exact congrArg Subtype.val (ht g₁ g₂ hf₁ hf₂ h)
  obtain ⟨x, hx, hxUnique⟩ := hE a ha
  have hxs : S.g.hom.app (op U) x = sectionAt hT s U := by
    apply hQ.ext
    intro V f hf
    change S.X₃.obj.map f.op (S.g.hom.app (op U) x) =
      S.X₃.obj.map f.op (sectionAt hT s U)
    have hxf : S.X₂.obj.map f.op x = (t f hf).val := hx f hf
    rw [← NatTrans.naturality_apply S.g.hom f.op, hxf, (t f hf).2, sectionAt_restrict]
  refine ⟨(⟨x, hxs⟩ : F.obj (op U)), fun V f hf => Subtype.ext (hx f hf), ?_⟩
  intro y hy
  apply Subtype.ext
  apply hxUnique
  intro V f hf
  exact congrArg Subtype.val (hy f hf)

/-- The actual sheaf of lifts. -/
def liftSheaf : Sheaf J (Type w) :=
  ⟨liftPresheaf hT s, (isSheaf_iff_isSheaf_of_type J _).mpr (liftPresheaf_isSheaf hT s)⟩

variable [HasSheafify J AddCommGrpCat.{w}] (hS : S.ShortExact)

/-- A chosen lift gives a trivialization by translation of the kernel sheaf. -/
def liftTrivialization {U : C} (x : (liftSheaf hT s).obj.obj (op U)) :
    S.X₁.obj.obj (op U) ≃ (liftSheaf hT s).obj.obj (op U) := by
  refine Equiv.ofBijective (fun a => ⟨S.f.hom.app (op U) a + x.val, ?_⟩) ?_
  · have hz : S.g.hom.app (op U) (S.f.hom.app (op U) a) = 0 := by
      have H := congrArg (fun q : S.X₁ ⟶ S.X₃ => q.hom.app (op U) a) S.zero
      exact H
    rw [map_add, hz, zero_add, x.2]
  · refine ⟨?_, ?_⟩
    · intro a b hab
      apply (exact_and_injective_on_sections hS U).2
      exact add_right_cancel (congrArg Subtype.val hab)
    · intro y
      obtain ⟨a, ha, _⟩ := sectionLifts_existsUnique_translate hS x y
      exact ⟨a, Subtype.ext ha⟩

set_option linter.unusedSectionVars false in
/-- The trivializations from a chosen lift commute with every restriction of that lift. -/
theorem liftTrivialization_restrict {U V : C} (f : V ⟶ U)
    (x : (liftSheaf hT s).obj.obj (op U)) (a : S.X₁.obj.obj (op U)) :
    (liftSheaf hT s).obj.map f.op (liftTrivialization hT s hS x a) =
      liftTrivialization hT s hS ((liftSheaf hT s).obj.map f.op x) (S.X₁.obj.map f.op a) :=
  Subtype.ext (translate_restrict f a x.val)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

include hS in
/-- Over every site object the lift sheaf has a section after passing to a
covering sieve. -/
theorem liftSheaf_locallyNonempty (U : C) :
    (Presheaf.imageSieve S.g.hom (sectionAt hT s U)) ∈ J U :=
  local_sectionLifts hS (sectionAt hT s U)

end
end ZInQ.Manuscript.T10Proetale

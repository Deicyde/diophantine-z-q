import ZInQKernel.Contrib.HeightBC.H5GlueOpen

/-! # Compare two actual open subgroups of the same fiber

The identification is over the original ambient group. It applies to the special fiber
of the global identity-component open and the subgroup in the printed semistability clause.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.IsogenyDegree

universe u v

private theorem monHom_of_comp_monic {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {U V W : C} [MonObj U] [MonObj V] [MonObj W] (f : U ⟶ V) (j : V ⟶ W)
    [Mono j] [IsMonHom j] [IsMonHom (f ≫ j)] : IsMonHom f := by
  constructor
  · apply (cancel_mono j).mp
    calc
      (η[U] ≫ f) ≫ j = η[U] ≫ (f ≫ j) := Category.assoc _ _ _
      _ = η[W] := IsMonHom.one_hom (f ≫ j)
      _ = η[V] ≫ j := (IsMonHom.one_hom j).symm
  · apply (cancel_mono j).mp
    calc
      (μ[U] ≫ f) ≫ j = μ[U] ≫ (f ≫ j) := Category.assoc _ _ _
      _ = ((f ≫ j) ⊗ₘ (f ≫ j)) ≫ μ[W] := IsMonHom.mul_hom (f ≫ j)
      _ = ((f ⊗ₘ f) ≫ μ[V]) ≫ j := by
        rw [← tensorHom_comp_tensorHom, Category.assoc, ← IsMonHom.mul_hom j, Category.assoc]

/-- The image of the actual pullback map is the preimage under the first projection.
This is useful for identifying the same special-fiber open subgroup. -/
theorem range_over_pullback_map {S T : Scheme.{u}} (s : T ⟶ S) {U V : Over S} (i : U ⟶ V) :
    Set.range ((Over.pullback s).map i).left = pullback.fst V.hom s ⁻¹' Set.range i.left := by
  have hm : ((Over.pullback s).map i).left =
      pullback.map U.hom s V.hom s i.left (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [Over.pullback_map_left]
  rw [hm, Scheme.Pullback.range_map]
  have h : Set.range ((𝟙 T : T ⟶ T) : T → T) = Set.univ :=
    Set.range_eq_univ.mpr fun x => ⟨x, rfl⟩
  rw [h, Set.preimage_univ, Set.inter_univ]

/-- Two open group insertions into the same ambient group with the same image are
identified by a group isomorphism over that very ambient group. -/
theorem exists_open_group_iso_of_range_eq {S : Scheme.{u}} {U V W : Over S}
    [MonObj U] [MonObj V] [MonObj W] (i : U ⟶ W) (j : V ⟶ W)
    [IsOpenImmersion i.left] [IsOpenImmersion j.left] [IsMonHom i] [IsMonHom j]
    (h : Set.range i.left = Set.range j.left) :
    ∃ e : U ≅ V, IsMonHom e.hom ∧ e.hom ≫ j = i := by
  let a := IsOpenImmersion.isoOfRangeEq i.left j.left h
  have ha : a.hom ≫ j.left = i.left := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let e : U ≅ V := Over.isoMk a (by rw [← Over.w j, ← Category.assoc, ha, Over.w])
  have he : e.hom ≫ j = i := Over.OverMorphism.ext ha
  have : Mono j := (Over.forget S).mono_of_mono_map (inferInstance : Mono j.left)
  have : IsMonHom (e.hom ≫ j) := by rw [he]; infer_instance
  exact ⟨e, monHom_of_comp_monic e.hom j, he⟩

#print axioms range_over_pullback_map
#print axioms exists_open_group_iso_of_range_eq

end ZInQ.Contrib.IsogenyDegree

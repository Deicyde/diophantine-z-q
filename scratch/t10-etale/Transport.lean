import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

open CategoryTheory Limits AlgebraicGeometry Opposite Scheme

universe u

namespace T10Transport

set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}}

/-- `π_X : X.ProEt ⥤ Scheme`, `(U → X) ↦ U`. -/
abbrev piX (X : Scheme.{u}) : X.ProEt ⥤ Scheme.{u} := Scheme.ProEt.forget X ⋙ Over.forget X

/-- **Lemma A.** A sieve on `U` in the small pro-étale site of `X` covers iff its image in
`Scheme` is a pro-étale covering sieve of `U.left`. -/
lemma mem_topology_iff {U : X.ProEt} (S : Sieve U) :
    S ∈ Scheme.ProEt.topology X U ↔ S.functorPushforward (piX X) ∈ proetaleTopology U.left := by
  have h2 : Scheme.ProEt.topology X =
      (Scheme.ProEt.forget X).restrictedTopology (proetaleTopology.over X) :=
    MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology (P := @WeaklyEtale) (S := X)
      _ proetalePrecoverage_le_precoverage_weaklyEtale
  rw [h2, Functor.mem_restrictedTopology_iff, GrothendieckTopology.mem_over_iff,
    Sieve.functorPushforward_comp]
  rfl


/-- `WeaklyEtale` holds for isomorphisms. -/
lemma weaklyEtale_hom (e : X ≅ Y) : (@WeaklyEtale : MorphismProperty Scheme.{u}) e.hom :=
  (inferInstance : WeaklyEtale e.hom)

/-- The functor `X.ProEt ⥤ Y.ProEt`, `(U → X) ↦ (U → X → Y)`, for a scheme isomorphism `e`. -/
noncomputable def proEtMap (e : X ≅ Y) : X.ProEt ⥤ Y.ProEt :=
  MorphismProperty.Over.map ⊤ (weaklyEtale_hom e)

/-- The equivalence of small pro-étale sites induced by a scheme isomorphism. -/
noncomputable def proEtEquiv (e : X ≅ Y) : X.ProEt ≌ Y.ProEt :=
  CategoryTheory.Equivalence.mk (proEtMap e) (proEtMap e.symm)
    ((MorphismProperty.Over.mapId ⊤ X).symm ≪≫
      MorphismProperty.Over.mapComp ⊤ (weaklyEtale_hom e) (weaklyEtale_hom e.symm) (𝟙 X) (by simp))
    ((MorphismProperty.Over.mapComp ⊤ (weaklyEtale_hom e.symm) (weaklyEtale_hom e) (𝟙 Y)
      (by simp)).symm ≪≫ MorphismProperty.Over.mapId ⊤ Y)

instance (e : X ≅ Y) : (proEtEquiv e).inverse.IsDenseSubsite (Scheme.ProEt.topology Y)
    (Scheme.ProEt.topology X) where
  functorPushforward_mem_iff {U S} := by
    rw [mem_topology_iff, mem_topology_iff, ← Sieve.functorPushforward_comp]
    rfl

/-- The equivalence of categories of abelian sheaves on the pro-étale sites. -/
noncomputable def sheafEquiv (e : X ≅ Y) :
    Sheaf (Scheme.ProEt.topology X) Ab.{u+1} ≌ Sheaf (Scheme.ProEt.topology Y) Ab.{u+1} :=
  (proEtEquiv e).sheafCongr _ _ _

instance (e : X ≅ Y) : (sheafEquiv e).functor.Additive where
  map_add := by intros; apply Sheaf.hom_ext; rfl

end T10Transport

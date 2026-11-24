/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

New construction (2026-11-14), after the ten-file checked checkpoint:
shrink an actual rational-pointed etale neighbourhood so that its WHOLE
closed fibre is the specified residue scheme. The section and all field
embeddings are retained as actual scheme morphisms. This is NOT a
henselization constructor, a model-properness theorem or effective descent.

The open-section argument uses Mathlib's open diagonal and morphism-property
API (Christian Merten, Andrew Yang and the respective Mathlib authors).
No existing Lane5 checkpoint file, source provider or cache is changed.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Gluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.PointedRefinement

/-- A section of an unramified morphism locally of finite type is an open
    immersion. This constructs the needed property from the open diagonal,
    rather than assuming that a rational point is a scheme-theoretic fibre. -/
theorem section_isOpenImmersion {X B : Scheme.{u}} (q : X ⟶ B)
    [FormallyUnramified q] [LocallyOfFiniteType q]
    (s : B ⟶ X) (hs : s ≫ q = 𝟙 B) : IsOpenImmersion s := by
  haveI : MorphismProperty.HasOfPostcompProperty
      (@IsOpenImmersion : MorphismProperty Scheme.{u})
      ((@LocallyOfFiniteType : MorphismProperty Scheme.{u}) ⊓
        (@FormallyUnramified : MorphismProperty Scheme.{u})) := by
    rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
    intro X Y f ⟨hft, hfu⟩
    exact inferInstanceAs (IsOpenImmersion (pullback.diagonal f))
  haveI : IsOpenImmersion (s ≫ q) := by rw [hs]; infer_instance
  exact MorphismProperty.of_postcomp @IsOpenImmersion
    (W' := @LocallyOfFiniteType ⊓ @FormallyUnramified) s q
    ⟨inferInstance, inferInstance⟩ inferInstance

/-- The actual comparison of the refined closed fibre with the old one. -/
def fibreComparison {U S B : Scheme.{u}} (p : U ⟶ S) (i : B ⟶ S)
    (V : U.Opens) : pullback (V.ι ≫ p) i ⟶ pullback p i :=
  pullback.lift (pullback.fst (V.ι ≫ p) i ≫ V.ι)
    (pullback.snd (V.ι ≫ p) i) (by rw [Category.assoc]; exact pullback.condition)

@[reassoc (attr := simp)]
theorem fibreComparison_fst {U S B : Scheme.{u}} (p : U ⟶ S) (i : B ⟶ S)
    (V : U.Opens) : fibreComparison p i V ≫ pullback.fst p i =
      pullback.fst (V.ι ≫ p) i ≫ V.ι := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fibreComparison_snd {U S B : Scheme.{u}} (p : U ⟶ S) (i : B ⟶ S)
    (V : U.Opens) : fibreComparison p i V ≫ pullback.snd p i =
      pullback.snd (V.ι ≫ p) i := pullback.lift_snd _ _ _

theorem isPullback_fibreComparison {U S B : Scheme.{u}}
    (p : U ⟶ S) (i : B ⟶ S) (V : U.Opens) :
    IsPullback (fibreComparison p i V) (pullback.fst (V.ι ≫ p) i)
      (pullback.fst p i) V.ι := by
  have h : IsPullback (fibreComparison p i V ≫ pullback.snd p i)
      (pullback.fst (V.ι ≫ p) i) i (V.ι ≫ p) := by
    rw [fibreComparison_snd]
    exact (IsPullback.of_hasPullback (V.ι ≫ p) i).flip
  exact h.of_right (fibreComparison_fst p i V) (IsPullback.of_hasPullback p i).flip

instance fibreComparison_isOpenImmersion {U S B : Scheme.{u}}
    (p : U ⟶ S) (i : B ⟶ S) (V : U.Opens) : IsOpenImmersion (fibreComparison p i V) :=
  MorphismProperty.of_isPullback (isPullback_fibreComparison p i V).flip inferInstance

/-- From an actual section of the closed fibre, construct an affine-open
    refinement whose ENTIRE closed fibre is isomorphic to the original
    specified residue scheme B. The hypotheses allow any one-point residue
    scheme, so no perfectness, characteristic or universe restriction enters.

    The new section maps back to the original section under fibreComparison;
    the inverse of its isomorphism is the ACTUAL fibre projection. -/
theorem exists_affine_refinement_of_closed_fibre_section
    {U S B : Scheme.{u}} [Subsingleton B] [Nonempty B]
    (p : U ⟶ S) [Etale p] (i : B ⟶ S) [IsClosedImmersion i]
    (s : B ⟶ pullback p i) (hs : s ≫ pullback.snd p i = 𝟙 B) :
    ∃ V : U.Opens, IsAffineOpen V ∧
      ∃ e : B ≅ pullback (V.ι ≫ p) i,
        e.inv = pullback.snd (V.ι ≫ p) i ∧
        e.hom ≫ fibreComparison p i V = s := by
  let F : Scheme.{u} := pullback p i
  let a : F ⟶ U := pullback.fst p i
  let q : F ⟶ B := pullback.snd p i
  haveI : IsOpenImmersion s := section_isOpenImmersion q s hs
  let bad : Set F := (Set.range s)ᶜ
  have hbad : IsClosed bad := s.isOpenEmbedding.isOpen_range.isClosed_compl
  have hbadImage : IsClosed (a '' bad) := a.isClosedMap bad hbad
  let W : U.Opens := ⟨(a '' bad)ᶜ, hbadImage.isOpen_compl⟩
  let b₀ : B := Classical.choice inferInstance
  let u₀ : U := a (s b₀)
  have hu₀ : u₀ ∈ W := by
    rintro ⟨z, hz, he⟩
    have hz' : z = s b₀ := a.isEmbedding.injective he
    exact hz ⟨b₀, hz'.symm⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, huV, hVW⟩ :=
    U.isBasis_affineOpens.exists_subset_of_mem_open hu₀ W.isOpen
  change U.Opens at V
  change IsAffineOpen V at hV
  have hrange : Set.range (s ≫ a) ⊆ Set.range V.ι := by
    rintro _ ⟨b, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hb : b = b₀ := Subsingleton.elim _ _
    simpa only [Scheme.Hom.comp_apply, hb] using huV
  let t : B ⟶ V.toScheme := IsOpenImmersion.lift V.ι (s ≫ a) hrange
  have ht : t ≫ V.ι = s ≫ a := IsOpenImmersion.lift_fac _ _ _
  have ht_over : t ≫ (V.ι ≫ p) = (𝟙 B) ≫ i := by
    rw [← Category.assoc, ht, Category.assoc, pullback.condition,
      ← Category.assoc, hs]
  let s' : B ⟶ pullback (V.ι ≫ p) i := pullback.lift t (𝟙 B) ht_over
  have hs' : s' ≫ pullback.snd (V.ι ≫ p) i = 𝟙 B := pullback.lift_snd _ _ _
  have hs_comp : s' ≫ fibreComparison p i V = s := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, fibreComparison_fst, s', pullback.lift_fst_assoc] using ht
    · simp only [Category.assoc, fibreComparison_snd, s', pullback.lift_snd, hs]
  haveI : IsOpenImmersion s' := section_isOpenImmersion (pullback.snd (V.ι ≫ p) i) s' hs'
  have hsurj : Function.Surjective s' := by
    intro z
    let z' : F := fibreComparison p i V z
    have hz' : z' ∈ Set.range s := by
      by_contra hz
      have hbad' : a z' ∈ a '' bad := ⟨z', hz, rfl⟩
      have hmemV : a z' ∈ V := by
        have he := congrArg (fun r : pullback (V.ι ≫ p) i ⟶ U => r z)
          (fibreComparison_fst p i V)
        change a z' = V.ι (pullback.fst (V.ι ≫ p) i z) at he
        rw [he]
        exact (pullback.fst (V.ι ≫ p) i z).2
      exact (hVW hmemV) hbad'
    obtain ⟨b, hb⟩ := hz'
    refine ⟨b, (fibreComparison p i V).isOpenEmbedding.injective ?_⟩
    have he := congrArg (fun r : B ⟶ F => r b) hs_comp
    simpa only [Scheme.Hom.comp_apply] using he.trans hb
  haveI : Surjective s' := ⟨hsurj⟩
  haveI : IsIso s' := (isIso_iff_isOpenImmersion_and_surjective s').mpr ⟨inferInstance, inferInstance⟩
  have hright : pullback.snd (V.ι ≫ p) i ≫ s' = 𝟙 _ := by
    apply (cancel_epi s').mp
    rw [← Category.assoc, hs', Category.id_comp, Category.comp_id]
  exact ⟨V, hV, ⟨s', pullback.snd (V.ι ≫ p) i, hs', hright⟩, rfl, hs_comp⟩

#print axioms section_isOpenImmersion
#print axioms exists_affine_refinement_of_closed_fibre_section

end ZInQ.Contrib.CloudR2NOS.GoodDescent.PointedRefinement

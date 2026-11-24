import ZInQKernel.Contrib.CloudB3W17bGraphScout.GroupProjection
import ZInQKernel.Contrib.CloudB3W17bGraphScout.WitnessExtraction

/-!
The algebraic graph tail, with its genuinely missing input exposed as a concrete
closed group subscheme and an exact image statement on the original points.
This is not an analytic-Chow theorem or a closing GAGAMorphism contribution.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 (AbVar)
open ZInQ.LeafPush2 (CPts cptObj)

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bGraphScout

/-- A concrete algebraic graph subgroup realizes the actual original point homomorphism.
The source need not be supplied as an abelian variety: properness and finite type
are derived, and Cartier supplies the smooth/reduced algebraic self-pullback. -/
theorem exists_scheme_realization_of_concrete_algebraic_graph (A B : AbVar ℂ)
    (F : CPts A (RingHom.id ℂ) →* CPts B (RingHom.id ℂ))
    (G : Over (Spec (.of ℂ))) [GrpObj G] (j : G ⟶ A.X ⊗ B.X)
    [IsMonHom j] [IsClosedImmersion j.left]
    (hgraph : ∀ (P : CPts A (RingHom.id ℂ)) (Q : CPts B (RingHom.id ℂ)),
      F P = Q ↔ ∃ t : cptObj (RingHom.id ℂ) ⟶ G,
        t ≫ (j ≫ fst A.X B.X) = P ∧ t ≫ (j ≫ snd A.X B.X) = Q) :
    ∃ f : A.X ⟶ B.X, ∀ P : CPts A (RingHom.id ℂ), F P = P ≫ f := by
  let p : G ⟶ A.X := j ≫ fst A.X B.X
  let q : G ⟶ B.X := j ≫ snd A.X B.X
  haveI : Mono j := Over.mono_of_mono_left j
  haveI : IsMonHom p := inferInstanceAs (IsMonHom (j ≫ fst A.X B.X))
  haveI : IsProper (fst A.X B.X).left := by
    dsimp
    infer_instance
  haveI : IsProper p.left := by
    change IsProper (j.left ≫ (fst A.X B.X).left)
    infer_instance
  haveI : IsProper G.hom := by
    rw [← p.w]
    infer_instance
  have hmatch : ∀ t : cptObj (RingHom.id ℂ) ⟶ G, F (t ≫ p) = t ≫ q := by
    intro t
    exact (hgraph (t ≫ p) (t ≫ q)).mpr ⟨t, rfl, rfl⟩
  have hp : Function.Bijective
      (fun t : cptObj (RingHom.id ℂ) ⟶ G => t ≫ p) := by
    constructor
    · intro t u htu
      apply (cancel_mono j).1
      apply CartesianMonoidalCategory.hom_ext
      · simpa only [Category.assoc, p] using htu
      · have hqu : t ≫ q = u ≫ q :=
          (hmatch t).symm.trans ((congrArg F htu).trans (hmatch u))
        simpa only [Category.assoc, q] using hqu
    · intro P
      obtain ⟨t, ht, -⟩ := (hgraph P (F P)).mp rfl
      exact ⟨t, ht⟩
  haveI : IsIso p := isIso_of_proper_complex_groupHom_bijective_original_points p hp
  exact exists_scheme_realization_of_concrete_graphIso A B G p q F hmatch

end ZInQ.Contrib.CloudB3W17bGraphScout

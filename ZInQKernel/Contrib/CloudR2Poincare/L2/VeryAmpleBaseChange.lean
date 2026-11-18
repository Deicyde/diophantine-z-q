import ZInQKernel.Contrib.CloudR2Poincare.L2.VeryAmple

/-!
# Actual base change of conventional very-ampleness

This pulls back an EXISTING closed projective embedding and its actual O(1)
comparison. It does not construct an embedding of an abelian variety (C4 owns
that theorem) and does not assume ampleness preservation as a desired Fact.
Native relative projective space and its twist commute with base change.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits
open Scheme.Modules ProjectiveSpace

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- Conventional very-ampleness is preserved by an ACTUAL cartesian base
change, using the original embedding and native O(1) pullback comparison. -/
theorem VeryAmple.baseChange {X S X' S' : Scheme.{u}}
    {π : X ⟶ S} {π' : X' ⟶ S'} {p : X' ⟶ X} {q : S' ⟶ S} {M : X.Modules}
    (hM : VeryAmple π M) (h : IsPullback p π' π q) :
    VeryAmple π' ((Scheme.Modules.pullback p).obj M) := by
  obtain ⟨coordinates, hfinite, e, he, heπ, ⟨comparison⟩⟩ := hM
  letI : Finite coordinates := hfinite
  letI : IsClosedImmersion e := he
  have hc : π' ≫ q = (p ≫ e) ≫ ℙ(coordinates; S) ↘ S := by
    rw [Category.assoc, heπ]
    exact h.w.symm
  let e' := ProjectiveSpace.liftBaseChange π' (p ≫ e) hc
  have hpull : IsPullback p e' e (ProjectiveSpace.map coordinates q) := by
    apply ProjectiveSpace.isPullback_liftBaseChange
    simpa only [heπ] using h
  have he' : IsClosedImmersion e' := MorphismProperty.of_isPullback hpull he
  refine ⟨coordinates, hfinite, e', he', ProjectiveSpace.liftBaseChange_over _ _ _, ?_⟩
  refine ⟨(Scheme.Modules.pullback p).mapIso comparison ≪≫
    (Scheme.Modules.pullbackComp p e).app (twist coordinates S 1) ≪≫
    (Scheme.Modules.pullbackCongr hpull.w).app (twist coordinates S 1) ≪≫
    ((Scheme.Modules.pullbackComp e' (ProjectiveSpace.map coordinates q)).app
      (twist coordinates S 1)).symm ≪≫
    (Scheme.Modules.pullback e').mapIso (ProjectiveSpace.pullbackMapTwistIso coordinates q 1)⟩

/-- In particular the original bundle on an actual A remains very ample on
the ACTUAL PkgI3 field base change A_Ω, not on a replacement variety. -/
theorem veryAmple_abVar_baseChange {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (A : PkgI3.AbVar k) (M : A.X.left.Modules) (hM : VeryAmple A.X.hom M) :
    VeryAmple (A.baseChange Ω).X.hom
      ((Scheme.Modules.pullback (pullback.fst A.X.hom
        (Spec.map (CommRingCat.ofHom (algebraMap k Ω))))).obj M) := by
  exact hM.baseChange (IsPullback.of_hasPullback _ _)

end ZInQ.Contrib.CloudR2Poincare.L2

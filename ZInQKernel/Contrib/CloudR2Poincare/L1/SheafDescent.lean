import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over

/-!
# Descent of sheaf sections along a quotient map

H-72 round 2, L1. This is the noncircular descent step: a Picard SHEAF exists
before any Picard SCHEME. A compatible section over an fppf quotient descends
uniquely to a section of that sheaf. In the next module, normalization at a
rational point turns the descended section into an actual line-bundle class.
No general dual or Picard representability assumption is used.
-/

noncomputable section

universe u v w

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- A compatible section descends uniquely along a singleton covering map. -/
theorem sheaf_section_descent_of_cover
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F : Sheaf J (Type w)) {T D : C} (q : T ⟶ D)
    (hq : Sieve.generate (Presieve.singleton q) ∈ J D)
    (x : F.obj.obj (.op T))
    (hx : ∀ {Z : C} (a b : Z ⟶ T), a ≫ q = b ≫ q →
      F.obj.map a.op x = F.obj.map b.op x) :
    ∃! y : F.obj.obj (.op D), F.obj.map q.op y = x := by
  have hF := (isSheaf_iff_isSheaf_of_type J F.obj).mp F.property
  exact (Presieve.isSheafFor_singleton.mp (hF.isSheafFor (Presieve.singleton q) hq)) x hx

/-- Equality on a quotient's actual kernel-pair relation is the full descent condition. -/
theorem sheaf_section_descent_of_kernelPair
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F : Sheaf J (Type w)) {R T D : C} (q : T ⟶ D) (t s : R ⟶ T)
    (hp : IsPullback t s q q)
    (hq : Sieve.generate (Presieve.singleton q) ∈ J D)
    (x : F.obj.obj (.op T)) (hx : F.obj.map t.op x = F.obj.map s.op x) :
    ∃! y : F.obj.obj (.op D), F.obj.map q.op y = x := by
  apply sheaf_section_descent_of_cover J F q hq x
  intro Z a b hab
  let z : Z ⟶ R := hp.lift a b hab
  calc
    F.obj.map a.op x = F.obj.map z.op (F.obj.map t.op x) := by
      rw [← Functor.map_comp_apply, ← op_comp, hp.lift_fst]
    _ = F.obj.map z.op (F.obj.map s.op x) := congrArg (F.obj.map z.op) hx
    _ = F.obj.map b.op x := by
      rw [← Functor.map_comp_apply, ← op_comp, hp.lift_snd]

/-- A surjective flat locally finitely presented map over S is a singleton fppf cover. -/
theorem singleton_fppf_cover {S : Scheme.{u}} {T D : Over S} (q : T ⟶ D)
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    Sieve.generate (Presieve.singleton q) ∈ Scheme.fppfTopology.over S D := by
  rw [GrothendieckTopology.mem_over_iff]
  change Sieve.functorPushforward (Over.forget S)
      (Sieve.generate (Presieve.singleton q)) ∈ Scheme.fppfTopology D.left
  rw [← Sieve.generate_map_eq_functorPushforward, Presieve.map_singleton]
  exact Precoverage.generate_mem_toGrothendieck q.left.singleton_mem_fppfPrecoverage

/-- Scheme-theoretic quotient descent for ANY fppf sheaf, not only represented ones. -/
theorem fppf_section_descent_of_kernelPair {S : Scheme.{u}}
    (F : Sheaf (Scheme.fppfTopology.over S) (Type w))
    {R T D : Over S} (q : T ⟶ D) (t s : R ⟶ T)
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    (hp : IsPullback t s q q)
    (x : F.obj.obj (.op T)) (hx : F.obj.map t.op x = F.obj.map s.op x) :
    ∃! y : F.obj.obj (.op D), F.obj.map q.op y = x :=
  sheaf_section_descent_of_kernelPair _ F q t s hp (singleton_fppf_cover q) x hx

end ZInQ.Contrib.CloudR2Poincare.L1

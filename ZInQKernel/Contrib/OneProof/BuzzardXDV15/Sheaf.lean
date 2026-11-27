import ZInQKernel.Contrib.OneProof.BuzzardXDV15.Defs

/-!
# The `V₁(5)`-points of a false elliptic curve form an étale sheaf

For a false elliptic curve `A/S`, the subfunctor `V15Sub A` of the points of `A` (sections that
are `5`-torsion, killed by `ι(e5)`, and nonzero at every geometric point) is a sheaf for the
étale topology on `S`-schemes, and its value at `S` itself is the record `V15 A`.

* The points of `A` form an étale sheaf (the étale topology is subcanonical), so the two
  equational conditions are local: two points agreeing on a covering sieve are equal.
* "Nonzero at every geometric point" is local because a geometric point of `T` lifts through
  some member of every étale-covering sieve of `T`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj

namespace Y3Buzzard.XDV15

attribute [local instance] FEC.grp

/-- The `V₁(5)`-points of `A` form a sheaf for the étale topology on `S`-schemes (lifted to
`Type 1`, where the sheafification of level structures lives). -/
theorem v15_isSheaf {S : Scheme.{0}} (A : FEC S) :
    Presheaf.IsSheaf (etaleOver S) ((V15Sub A).toFunctor ⋙ uliftFunctor.{1, 0}) := by
  rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
    Subfunctor.isSheaf_iff _ (points_isSheaf A)]
  intro T x hR
  have hsep : Presieve.IsSeparatedFor (yoneda.obj A.F)
      (((V15Sub A).sieveOfSection x : Sieve T.unop) : Presieve T.unop) :=
    (points_isSheaf A _ hR).isSeparatedFor
  refine ⟨?_, ?_, ?_⟩
  · apply hsep.ext
    intro Y f hf
    obtain ⟨h1, -, -⟩ := hf
    show f ≫ pt x ^ 5 = f ≫ 1
    rw [MonObj.comp_pow, MonObj.comp_one]
    exact h1
  · apply hsep.ext
    intro Y f hf
    obtain ⟨-, h2, -⟩ := hf
    show f ≫ (pt x ≫ iotaO A e5) = f ≫ 1
    rw [← Category.assoc, MonObj.comp_one]
    exact h2
  · intro k _ _ s heq
    obtain ⟨U, f, hf, l, hl⟩ := geomPt_lift _ hR s
    obtain ⟨-, -, h3⟩ := hf
    apply h3 k l
    show l ≫ (f ≫ x).left = l ≫ U.hom ≫ torsZeroL A
    rw [Over.comp_left, ← Over.w f]
    simpa only [← Category.assoc, hl] using heq

/-- `V15Sub` at the terminal object is the record `V15` of the project. -/
def v15SubEquiv {S : Scheme.{0}} (A : FEC S) :
    (V15Sub A).toFunctor.obj (Opposite.op (Over.mk (𝟙 S))) ≃ V15 A where
  toFun x :=
    { Q := x.1.left
      Q_sec := Over.w x.1
      order := x.2.1
      inKer := x.2.2.1
      nonzero := by
        intro k _ _ s h
        apply x.2.2.2 k s
        have h' := congrArg (fun f : Over.mk s ⟶ A.F => f.left) h
        simp only [Over.homMk_left] at h'
        show s ≫ x.1.left = s ≫ (Over.mk (𝟙 S)).hom ≫ torsZeroL A
        rw [h', one_left_eq]
        simp only [Over.mk_hom, Category.id_comp] }
  invFun α := ⟨Over.homMk (U := Over.mk (𝟙 S)) α.Q α.Q_sec, α.order, α.inKer, by
      intro k _ _ s h
      apply α.nonzero k s
      apply Over.OverMorphism.ext
      rw [one_left_eq]
      exact h.trans (congrArg (fun t => s ≫ t) (Category.id_comp (torsZeroL A)))⟩
  left_inv x := Subtype.ext (Over.OverMorphism.ext rfl)
  right_inv α := rfl

end Y3Buzzard.XDV15

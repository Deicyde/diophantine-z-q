import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FibreTransfer
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV
open scoped CategoryTheory.Obj
namespace Y3Buzzard

/-!
# Descent of generators of full level structures along finite surjective epimorphisms

Let `f : T' ⟶ T` be finite, surjective and an epimorphism of schemes, and `P : T ⟶ A`.
If `f ≫ P` generates a full level-`M` structure, so does `P`.

* Clause 1 (`M`-torsion) descends because precomposition with the epimorphism
  `Over.homMk f` is injective on hom-monoids and commutes with powers.
* Clause 2 (generation at geometric points) descends because every geometric point of `T`
  lifts through `f`: the fibre of `f` over `Spec k ⟶ T` is a nonempty finite `k`-scheme, so it
  has a closed point, and a closed point of a scheme locally of finite type over an
  algebraically closed field is a `k`-rational point.
-/

attribute [local instance] FEC.grp

/-- The descent statement in its finite form. -/
def IsGenDescentFinite : Prop :=
  ∀ (M : ℕ) (S : Scheme.{0}) (A : FEC S) (T T' : Scheme.{0}) (f : T' ⟶ T) (P : T ⟶ A.F.left),
    AlgebraicGeometry.IsFinite f → AlgebraicGeometry.Surjective f → Epi f →
      IsGen M A (f ≫ P) → IsGen M A P

/-- Geometric points lift along finite surjective morphisms: for `f : T' ⟶ T` finite and
surjective, an algebraically closed field `k` and `s : Spec k ⟶ T`, there is
`s' : Spec k ⟶ T'` with `s' ≫ f = s`.

Mathematically: the fibre `T' ×_T Spec k` is finite over `Spec k`, hence affine and
quasi-compact, and nonempty by surjectivity; so it has a closed point. By the Nullstellensatz
(Stacks, Theorem 10.34.1, tag 00FV, part 1) the residue field at a closed point of a scheme
locally of finite type over `k` is finite over `k`, hence equal to `k` as `k` is algebraically
closed; this gives a section of the fibre over `Spec k`. -/
def FiniteSurjLiftsGeomPoints : Prop :=
  ∀ (T T' : Scheme.{0}) (f : T' ⟶ T), AlgebraicGeometry.IsFinite f →
    AlgebraicGeometry.Surjective f →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ T),
        ∃ s' : Spec (CommRingCat.of k) ⟶ T', s' ≫ f = s

/-! ## 1. Clause 1: torsion descends along an epimorphism -/

/-- `Over.homMk g` is an epimorphism when `g` is. -/
theorem epi_over_homMk {X : Scheme.{0}} {U V : Over X} (g : U.left ⟶ V.left)
    (w : g ≫ V.hom = U.hom) (hg : Epi g) : Epi (Over.homMk g w : U ⟶ V) := by
  constructor
  intro Z a b hab
  apply Over.OverMorphism.ext
  have h' : g ≫ a.left = g ≫ b.left := congrArg (fun z => z.left) hab
  exact (cancel_epi g).1 h'

/-- In a hom-monoid, `x ^ n = 1` follows from `(y ≫ x) ^ n = 1` for an epimorphism `y`. -/
theorem pow_eq_one_of_epi_comp {X : Scheme.{0}} {G U V : Over X} [MonObj G] (y : U ⟶ V)
    [Epi y] (x : V ⟶ G) (n : ℕ) (h : (y ≫ x) ^ n = 1) : x ^ n = 1 :=
  (cancel_epi y).1 ((MonObj.comp_pow x n y).trans (h.trans (MonObj.comp_one y).symm))

/-- Clause 1 of `IsGen` descends along an epimorphism `f`. -/
theorem isGen_pow_descent {M : ℕ} {S : Scheme.{0}} {A : FEC S} {T T' : Scheme.{0}}
    (f : T' ⟶ T) (hf : Epi f) (P : T ⟶ A.F.left)
    (h1 : (Over.homMk (U := Over.mk ((f ≫ P) ≫ A.F.hom)) (f ≫ P) rfl :
      Over.mk ((f ≫ P) ≫ A.F.hom) ⟶ A.F) ^ M = 1) :
    (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) ^ M = 1 := by
  have h1' := (homMk_pow_eq_one_congr A (Category.assoc f P A.F.hom) (f ≫ P) rfl
    (Category.assoc f P A.F.hom) M).1 h1
  haveI hy_epi : Epi (Over.homMk (U := Over.mk (f ≫ P ≫ A.F.hom)) (V := Over.mk (P ≫ A.F.hom))
      f rfl) :=
    epi_over_homMk (U := Over.mk (f ≫ P ≫ A.F.hom)) (V := Over.mk (P ≫ A.F.hom)) f rfl hf
  have hy : (Over.homMk (U := Over.mk (f ≫ P ≫ A.F.hom)) (V := Over.mk (P ≫ A.F.hom)) f rfl) ≫
        (Over.homMk (U := Over.mk (P ≫ A.F.hom)) P rfl : Over.mk (P ≫ A.F.hom) ⟶ A.F) =
      (Over.homMk (U := Over.mk (f ≫ P ≫ A.F.hom)) (f ≫ P) (Category.assoc f P A.F.hom) :
        Over.mk (f ≫ P ≫ A.F.hom) ⟶ A.F) :=
    Over.OverMorphism.ext rfl
  exact pow_eq_one_of_epi_comp _ _ M ((congrArg (fun z => z ^ M) hy).trans h1')

/-! ## 2. Descent from the lifting property -/

/-- `IsGen` descends along finite surjective epimorphisms, given that geometric points lift
along finite surjective morphisms. -/
theorem isGenDescentFinite_of_lifts (hlift : FiniteSurjLiftsGeomPoints) : IsGenDescentFinite := by
  intro M S A T T' f P hf hsurj hepi hgen
  dsimp only [IsGen] at hgen ⊢
  obtain ⟨h1, h2⟩ := hgen
  refine ⟨isGen_pow_descent f hepi P h1, ?_⟩
  intro k _ _ s
  obtain ⟨s', hs⟩ := hlift T T' f hf hsurj k s
  have e : s' ≫ (f ≫ P) ≫ A.F.hom = s ≫ P ≫ A.F.hom :=
    (congrArg (fun z => s' ≫ z) (Category.assoc f P A.F.hom)).trans
      ((Category.assoc s' f (P ≫ A.F.hom)).symm.trans
        (congrArg (fun z => z ≫ P ≫ A.F.hom) hs))
  have h₂ : (s' ≫ f ≫ P) ≫ A.F.hom = s ≫ P ≫ A.F.hom :=
    (Category.assoc s' (f ≫ P) A.F.hom).trans e
  refine IsGenAt.of_eq ?_
    ((isGenAt_congr A e (s' ≫ f ≫ P) (Category.assoc _ _ _) h₂).1 (h2 k s'))
  exact Over.OverMorphism.ext
    ((Category.assoc s' f P).symm.trans (congrArg (fun z => z ≫ P) hs))

/-! ## 3. Lifting geometric points along finite surjective morphisms -/

/-- Geometric points lift along finite surjective morphisms. -/
theorem finiteSurjLiftsGeomPoints : FiniteSurjLiftsGeomPoints := by
  intro T T' f hf hsurj k _ _ s
  haveI hfin : AlgebraicGeometry.IsFinite (pullback.snd f s) :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsFinite)
      (IsPullback.of_hasPullback f s) hf
  haveI hsur : AlgebraicGeometry.Surjective (pullback.snd f s) :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective)
      (IsPullback.of_hasPullback f s) hsurj
  haveI : IsAffine (pullback f s) := isAffine_of_isAffineHom (pullback.snd f s)
  haveI : CompactSpace ↥(pullback f s : Scheme.{0}) := by
    first
      | exact inferInstance
      | exact Scheme.compactSpace_of_isAffine _
  obtain ⟨z, -⟩ := AlgebraicGeometry.Surjective.surj (f := pullback.snd f s)
    (IsLocalRing.closedPoint k)
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton
    (isClosed_univ : IsClosed (Set.univ : Set ↥(pullback f s : Scheme.{0}))) ⟨z, Set.mem_univ z⟩
  refine ⟨pointOfClosedPoint (pullback.snd f s) x hx ≫ pullback.fst f s, ?_⟩
  rw [Category.assoc, pullback.condition]
  exact pointOfClosedPoint_comp_assoc (pullback.snd f s) x hx s

/-! ## 4. The descent leaf -/

/-- `IsGen` descends along finite surjective epimorphisms of schemes. -/
theorem isGenDescentFinite : IsGenDescentFinite :=
  isGenDescentFinite_of_lifts finiteSurjLiftsGeomPoints

end Y3Buzzard

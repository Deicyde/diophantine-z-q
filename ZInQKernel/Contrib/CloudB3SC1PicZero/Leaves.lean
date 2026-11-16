import ZInQKernel.OneProof.H.TailZ24
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Kleiman's printed statements about the Picard scheme over a field

Three statements from S. L. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry:
Grothendieck's FGA Explained*, Math. Surveys Monogr. 123, Amer. Math. Soc., 2005, Chapter 9
(arXiv:math/0504020v1, where the same statements are numbered without the chapter prefix 9).
Each is stated over `S = Spec K` for a field `K` (a field is Noetherian), over genuine definitions:
the fppf Picard sheaf `picardFunctor` (the fppf sheaf associated to `T ↦ Pic(X ×_K T)`, which by
Kleiman §9.2, text after Def. 9.2.2 (arXiv p. 17), is `Pic_(X/S)(fppf)`), its representing objects, the group law
`picardFunctorCommGrpObj` and the identity component `T09Pic.identityComponent`. Each statement is
the print or a consequence of it (hypotheses added, conclusion clauses dropped), never stronger.
Representing objects of a functor are unique up to unique isomorphism, so quantifying over every
representing object `P` is the print's `Pic_{X/S}`.

"Projective" is stated as a closed immersion into `ℙ^N_K` over `K` for a finite index type `N`;
over a field this is projective in every usual sense (Hartshorne II §4, EGA II 5.5.2). -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open scoped CategoryTheory.MonObj

namespace CloudB3SC1PicZero

open T09Pic

/-- **Kleiman, *The Picard scheme* (FGA Explained, 2005), Thm 9.4.8 (Main), part (1)** (arXiv:math/0504020v1
Thm 4.8, p. 27, AI-read): "Assume `f : X → S` is projective Zariski locally over `S`, and is flat with integral
geometric fibers. Then `Pic_{X/S}` exists, is separated and locally of finite type over `S`, and represents
`Pic_(X/S)(ét)`." At `S = Spec K`; only the clause "locally of finite type" is kept. (By the text after
Def. 9.4.1 (arXiv p. 26), a scheme representing `Pic_(X/S)(ét)` also represents `Pic_(X/S)(fppf)`.) Book page UNVERIFIED; no human reading recorded. -/
def KleimanThm948Field : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))),
    (∃ (N : Type) (_ : Finite N) (i : X.left ⟶ ℙ(N; Spec (CommRingCat.of K))),
      IsClosedImmersion i ∧ i ≫ ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) = X.hom) →
    Flat X.hom → GeometricallyIntegral X.hom →
    ∀ (P : Over (Spec (CommRingCat.of K))), (picardFunctor X.hom).obj.RepresentableBy P →
      LocallyOfFiniteType P.hom

/-- **Kleiman, *The Picard scheme* (FGA Explained, 2005), Lemma 9.5.1 (3)** (arXiv:math/0504020v1 Lemma 5.1,
pp. 36-37, AI-read): "Let `k` be a field, and `G` a group scheme locally of finite type. Let `G⁰` denote the connected
component of the identity element `e`. ... (3) Then `G⁰` is an open and closed group subscheme of finite type;
it is geometrically irreducible; and forming it commutes with extending `k`." Kept: `G⁰` is open, closed under
the group law and the inverse, and geometrically irreducible. Also SGA 3, Exp. VI_A, 2.4 (not read here).
Book page UNVERIFIED; no human reading recorded. -/
def KleimanLem951 : Prop :=
  ∀ (K : Type) [Field K] (G : Over (Spec (CommRingCat.of K))) [GrpObj G], LocallyOfFiniteType G.hom →
    ∃ V : G.left.Opens, (V : Set G.left) = identityComponent G ∧
      (∀ z : (G ⊗ G).left, (CartesianMonoidalCategory.fst G G).left z ∈ V →
        (CartesianMonoidalCategory.snd G G).left z ∈ V → μ[G].left z ∈ V) ∧
      (∀ g : G.left, g ∈ V → ((𝟙 G)⁻¹ : G ⟶ G).left g ∈ V) ∧
      GeometricallyIrreducible (V.ι ≫ G.hom)

/-- **Kleiman, *The Picard scheme* (FGA Explained, 2005), Remark 9.5.24** (arXiv:math/0504020v1 Remark 5.24,
pp. 50-51, AI-read): "Assume `X` is an Abelian `S`-scheme of relative dimension `g`; that is, `X` is a smooth and
proper `S`-group scheme with geometrically connected fibers of dimension `g`. ... Assume `X/S` is projective, and
`S` is Noetherian. Then `Pic⁰_{X/S}` exists, and is also a projective Abelian `S`-scheme of relative dimension
`g`." At `S = Spec K` the only fibre is `X`, so "fibers of dimension `g`" is `dim X = g` for a natural number `g`
(Krull dimension of the underlying space). The group law is assumed commutative (an added hypothesis; it
holds for every abelian variety by Mathlib's `isCommMonObj_of_isProper_of_geometricallyIntegral`); `Pic⁰_{X/K}` is the
open subscheme on the connected component of the identity of `Pic_{X/K}` (Lemma 9.5.1, Prop. 9.5.3, Prop.
9.5.20). Kept from the conclusion: `Pic⁰_{X/K}` is smooth and proper over `K`. Book page UNVERIFIED; no human reading recorded. -/
def KleimanRmk9524Field : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))) [GrpObj X] [IsCommMonObj X],
    Smooth X.hom → IsProper X.hom → GeometricallyConnected X.hom →
    ∀ g : ℕ, topologicalKrullDim X.left = (g : WithBot ℕ∞) →
    (∃ (N : Type) (_ : Finite N) (i : X.left ⟶ ℙ(N; Spec (CommRingCat.of K))),
      IsClosedImmersion i ∧ i ≫ ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) = X.hom) →
    ∀ (P : Over (Spec (CommRingCat.of K))) (rep : (picardFunctor X.hom).obj.RepresentableBy P)
      (V : P.left.Opens),
      letI := picardFunctorCommGrpObj X.hom rep
      (V : Set P.left) = identityComponent P → Smooth (V.ι ≫ P.hom) ∧ IsProper (V.ι ≫ P.hom)

end CloudB3SC1PicZero

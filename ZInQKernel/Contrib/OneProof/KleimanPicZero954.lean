import ZInQKernel.Contrib.OneProof.PicZeroAbVarCharZero
import ZInQKernel.Contrib.OneProof.PicLocFinType
import ZInQKernel.Contrib.OneProof.IdentityComponentLFT
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.RepresentableGroup
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Group.QuasiProjective

/-!
# Kleiman 9.5.4 as printed (kleiman-section2)

`PicFix.KleimanPicZeroProper` (`Contrib/OneProof/PicZeroAbVar.lean`) asks `Pic⁰_{X/K}` to be proper for every `X`
proper and geometrically normal over a field `K`. Kleiman, *The Picard scheme* (FGA Explained, Ch. 9;
arXiv math/0504020), Thm 9.5.4, assumes `X/K` **projective** and geometrically integral (geometrically normal for
the clause "`Pic⁰` is projective"); the proper case is only the sketch Remark 9.5.6. Kleiman's representability
statements are also over **locally Noetherian** test schemes, while the tree's `RepresentableBy` quantifies over all
`K`-schemes. This file restates the leaf as 9.5.4 and discharges the abelian-variety consumer:

* `LocNoeth S`, `picardFunctorLN f`: the tree's `picardFunctor f` (fppf sheafification of `T ↦ Pic(X ×_S T)`, which
  Kleiman, right after Def. 9.2.2, calls `Pic_{(X/S)(fppf)}`) restricted to locally Noetherian `S`-schemes;
* `KleimanPicZeroProper954` (**LEAF**): for `X` with a closed immersion into `ℙ^N_K` over `K`, geometrically integral,
  geometrically normal and with a `K`-point, every `P` locally of finite type over `K` representing
  `picardFunctorLN X.hom`, and every open `V` on the connected component of the point classifying `𝒪`,
  `V → Spec K` is proper;
* `repLN`, `identityComponentLN_repLN` (step (a)): a representation over all `K`-schemes restricts to one over
  locally Noetherian ones (when `P` is locally Noetherian), with the same identity component;
* `isClosedImmersion_of_proper`: an immersion of a proper `K`-scheme into `ℙ^N_K` over `K` is a closed immersion;
* `picZeroProperAt_of_954`, `picZeroAbVar0_of_954`: the consumer. An abelian variety is projective (vendored
  `GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral`), geometrically integral (its
  field), geometrically normal (smooth, `PicFix.geometricallyNormal_of_smooth`), has the identity point; its Picard
  scheme is locally of finite type (`PicLFT.picLocFinType_proof`, proved).

Step (b), EGA IV_2 6.7.7 (normal after `K̄` iff after every field), is not needed: the leaf's hypothesis
`geometrically IsNormalScheme` (normal after every field extension) is the stronger one, and the consumer proves it.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

namespace KleimanSection2

open Scheme T09Pic PkgI3 PkgI3.AbVar PicDict PicFix

/-- **Locally Noetherian `S`-schemes**: the test category of Kleiman's representability statements
(*The Picard scheme*, §9.2–9.4: the Picard functors are considered on locally Noetherian `S`-schemes). -/
def LocNoeth (S : Scheme.{u}) : ObjectProperty (Over S) := fun T => IsLocallyNoetherian T.left

/-- **Kleiman's `Pic_{(X/S)(fppf)}` on locally Noetherian test schemes**: the tree's `picardFunctor f` (the fppf
sheafification of `T ↦ Pic(X ×_S T)`; Kleiman, remark after Def. 9.2.2, and BLR §8.1, p. 199: this is
`Pic_{(X/S)(fppf)}`) restricted to locally Noetherian `S`-schemes. -/
def picardFunctorLN {X S : Scheme.{u}} (f : X ⟶ S) : (LocNoeth S).FullSubcategoryᵒᵖ ⥤ Type (u + 1) :=
  (LocNoeth S).ι.op ⋙ (picardFunctor f).obj

/-- An `S`-scheme locally of finite type over a locally Noetherian `S` is locally Noetherian (Mathlib). -/
lemma locNoeth_of_lft {S : Scheme.{u}} [IsLocallyNoetherian S] {P : Over S} (hP : LocallyOfFiniteType P.hom) :
    LocNoeth S P :=
  LocallyOfFiniteType.isLocallyNoetherian P.hom

/-- The final object `Spec K` as a locally Noetherian test scheme. -/
def unitLN (K : Type) [Field K] : (LocNoeth (Spec (CommRingCat.of K))).FullSubcategory :=
  ⟨𝟙_ (Over (Spec (CommRingCat.of K))),
    (inferInstance : IsLocallyNoetherian (Spec (CommRingCat.of K)))⟩

/-- **The identity point** of a scheme `P` representing the restricted Picard functor: the `K`-point classifying
the trivial class (the class of `𝒪_X`, the unit of `Pic`). -/
def unitPt {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))} {P : Over (Spec (CommRingCat.of K))}
    {hP : LocNoeth _ P} (rep : (picardFunctorLN X.hom).RepresentableBy ⟨P, hP⟩) :
    𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P :=
  (rep.homEquiv (X := unitLN K)).symm
    ((toSheafify (fppfTopology.over _) (picardPresheaf X.hom)).app (op (𝟙_ _))
      (1 : (pullback X.hom (𝟙_ (Over (Spec (CommRingCat.of K)))).hom).Pic)) |>.hom

/-- **The identity component** `Pic⁰` of a scheme representing the restricted Picard functor: the connected
component of its identity point (Kleiman 9.5.1 for a group scheme locally of finite type over a field). -/
def identityComponentLN {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))}
    {P : Over (Spec (CommRingCat.of K))} {hP : LocNoeth _ P}
    (rep : (picardFunctorLN X.hom).RepresentableBy ⟨P, hP⟩) : Set P.left :=
  {x | ∃ s : (𝟙_ (Over (Spec (CommRingCat.of K)))).left, x ∈ connectedComponent ((unitPt rep).left s)}

/-- **LEAF (printed form).** Kleiman, *The Picard scheme* (FGA Explained, Ch. 9; arXiv math/0504020), Thm 9.5.4:
for `X` projective and geometrically integral over a field `K` (and geometrically normal, needed there only for
"`Pic⁰_{X/K}` is projective"), the identity component `Pic⁰_{X/K}` of the Picard scheme is proper. Stated with:
projective = a closed immersion `X → ℙ^N_K` over `K`; geometrically integral and geometrically normal after every
field extension (at least as strong as after `K̄`); a `K`-point (an extra hypothesis, so that by Kleiman 9.2.5 the
étale and fppf Picard sheaves agree); the Picard scheme = any `P` locally of finite type over `K` representing
`Pic_{(X/K)(fppf)}` on locally Noetherian `K`-schemes (Kleiman's test category; `P` is unique up to unique
isomorphism there, and Kleiman's `Pic_{X/K}` is one by Thm 9.4.8); `Pic⁰` = any open `V` whose underlying set is the
connected component of the point classifying `𝒪_X`. Numbering and hypotheses as reported from a reading of the
arXiv text (functor remark on p. 37); no copy on the build host, so UNVERIFIED there. -/
def KleimanPicZeroProper954 : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))),
    (∃ (N : Type) (_ : Finite N) (i : X.left ⟶ ℙ(N; Spec (CommRingCat.of K))),
      IsClosedImmersion i ∧ i ≫ ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K) = X.hom) →
    GeometricallyIntegral X.hom → geometrically IsNormalScheme X.hom →
    (∃ σ : Spec (CommRingCat.of K) ⟶ X.left, σ ≫ X.hom = 𝟙 _) →
    ∀ (P : Over (Spec (CommRingCat.of K))) (hP : LocallyOfFiniteType P.hom)
      (rep : (picardFunctorLN X.hom).RepresentableBy ⟨P, locNoeth_of_lft hP⟩) (V : P.left.Opens),
      (V : Set P.left) = identityComponentLN rep → IsProper (V.ι ≫ P.hom)

/-! ## Step (a): from all test schemes to locally Noetherian ones -/

/-- **Restriction of a representation** of the tree's `picardFunctor` (over all `S`-schemes) to locally Noetherian
test schemes, for `P` itself locally Noetherian. -/
def repLN {X S : Scheme.{u}} {f : X ⟶ S} {P : Over S} (rep : (picardFunctor f).obj.RepresentableBy P)
    (hP : LocNoeth S P) : (picardFunctorLN f).RepresentableBy ⟨P, hP⟩ where
  homEquiv {T} := (InducedCategory.homEquiv).trans (rep.homEquiv (X := T.obj))
  homEquiv_comp g φ := rep.homEquiv_comp g.hom φ.hom

/-- The identity component for the restricted representation is the tree's `identityComponent` for the group law
`picardFunctorCommGrpObj` (the identity points are the same point, by definition). -/
lemma identityComponentLN_repLN {K : Type} [Field K] {X : Over (Spec (CommRingCat.of K))}
    {P : Over (Spec (CommRingCat.of K))} (rep : (picardFunctor X.hom).obj.RepresentableBy P)
    (hP : LocNoeth _ P) :
    identityComponentLN (repLN rep hP) =
      (letI := picardFunctorCommGrpObj X.hom rep; identityComponent P) := by
  rfl

/-! ## Projectivity of abelian varieties in the closed-immersion form -/

/-- An immersion `i : X → ℙ^N_K` over `K` with `X` proper over `K` is a closed immersion (`i` is proper since
`ℙ^N_K` is separated over `K`, so its range is closed). -/
lemma isClosedImmersion_of_proper {K : Type} [Field K] {X : Scheme.{0}} {N : Type} [Finite N]
    (i : X ⟶ ℙ(N; Spec (CommRingCat.of K))) [IsImmersion i]
    [IsProper (i ≫ ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))] : IsClosedImmersion i := by
  have : IsProper i := IsProper.of_comp i (ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K))
  refine .of_isPreimmersion _ ?_
  rw [← Set.image_univ]
  exact i.isClosedMap _ isClosed_univ

/-! ## The consumer -/

/-- **`PicZeroChar0.PicZeroProperAt K`** (properness of `Pic⁰` of an abelian variety) from Kleiman 9.5.4: an abelian
variety is projective (vendored `GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral`,
closed by `isClosedImmersion_of_proper`), geometrically integral, smooth hence geometrically normal, and has the
identity point; a scheme representing its Picard functor is locally of finite type (`PicLFT.picLocFinType_proof`),
hence locally Noetherian, so the representation restricts (`repLN`). -/
theorem picZeroProperAt_of_954 (h : KleimanPicZeroProper954) (K : Type) [Field K] :
    PicZeroChar0.PicZeroProperAt K := by
  intro A P rep V hV
  obtain ⟨N, hN, i, hi, hover⟩ :=
    GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral A.X
  have : IsProper (i ≫ ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := by
    rw [hover]; infer_instance
  have hP := PicLFT.picLocFinType_proof K A P rep
  exact h K A.X ⟨N, hN, i, isClosedImmersion_of_proper i, hover⟩ inferInstance
    (geometricallyNormal_of_smooth A.X.hom) ⟨η[A.X].left, Over.w η[A.X]⟩ P hP (repLN rep _) V
    (by rw [identityComponentLN_repLN]; exact hV)

/-- **The hand fold's consumer**: `PicZeroChar0.PicZeroAbVar0` from Kleiman 9.5.4 alone, with `PicLocFinType`,
`IdentityComponentLFT` and Cartier's theorem proved (the argument of `PicZeroChar0.picZeroAbVar0_of_leaves`). -/
theorem picZeroAbVar0_of_954 (h : KleimanPicZeroProper954) : PicZeroChar0.PicZeroAbVar0 := fun K _ _ =>
  PicZeroChar0.picZeroAbVarAt_of PicLFT.picLocFinType_proof IdCompLFT.identityComponentLFT_proof K
    (PicZeroChar0.picZeroSmoothAt_charZero ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof
      PicLFT.picLocFinType_proof K)
    (picZeroProperAt_of_954 h K)

end KleimanSection2

end

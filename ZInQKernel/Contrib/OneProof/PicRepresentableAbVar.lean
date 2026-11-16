import ZInQKernel.OneProof.H.TailZ24

/-! # pic-repr: `picRepresentableAbVar` from the printed Murre–Oort statement (representable, locally of finite type)

The field `picRepresentableAbVar : T09Pic.PicRepresentableAbVar` (TailZ24.lean L289) asks only for a
representing object of the relative Picard fppf sheaf of an abelian variety. No library in the tree constructs
one in dimension `≥ 2` (docs/research/pic-repr.md §2; the vendored Jacobian-Challenge proof covers smooth proper
curves over separably closed fields, and its open-chart criterion needs a chart that is equivalent to the
conclusion, `scratch/pic-repr/Chart.lean`). The field is therefore discharged here by the printed theorem
itself, in the form in which it is printed: `Pic_{A/K}` is representable **and the representing scheme is
locally of finite type** (`PicRepresentableLFTAbVar`). The same leaf also gives pic-dict's leaf
`PicDict.PicLocFinType` (every representing object is locally of finite type), copied verbatim below as
`PicRepr.PicLocFinType`, because representing objects are unique up to isomorphism. So, once pic-dict's
reduction of `picZeroAbVar` is folded, the one printed leaf replaces two leaves (`picRepresentableAbVar`
and `PicLocFinType`): −1. On main alone it is a LEAF-for-LEAF exchange (0) that makes the leaf literally the
printed statement (with "locally of finite type").

The group structure of the printed statement ("a group scheme") is not part of the leaf: it is the vendored
`AlgebraicGeometry.picardFunctorCommGrpObj`, constructed from any representation. -/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace PicRepr

/-- **LEAF (printed form): the Picard scheme of an abelian variety exists and is locally of finite type.**
For an abelian variety `A` over a field `K`, the relative Picard fppf sheaf `Pic_{A/K}` is represented by a
`K`-scheme `P` locally of finite type over `K`.
Published: Murre, *On contravariant functors from the category of pre-schemes over a field into the category of
abelian groups*, Publ. Math. IHÉS 23 (1964), main theorem (for `X` proper over a field: `Pic_{X/k}` is represented by a
group scheme locally of finite type); Oort, *Sur le schéma de Picard*, Bull. SMF 90 (1962); Grothendieck,
FGA Exp. 232, Thm 3.1 (for `X → S` projective and flat with geometrically integral fibres); Kleiman, *The Picard
scheme* (FGA Explained, 2005), Thm 9.4.8 (exists, separated, locally of finite presentation over `S`) with
Thm 9.2.5 (`f_* 𝒪_X = 𝒪_S` universally and a section exists, so the Zariski, étale and fppf sheaves agree with
`T ↦ Pic(X_T)/Pic(T)`);
Bosch–Lütkebohmert–Raynaud, *Néron models*, §8.2, Thm 3. All locators UNVERIFIED (no source read in this task).
Abelian varieties are projective (Mumford, *Abelian varieties*, §6, Application 1), so the projective versions
apply as well as the proper ones. A consequence of each print (the `S = Spec K` case, the group structure dropped),
never stronger. -/
def PicRepresentableLFTAbVar : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K),
    ∃ (P : Over (Spec (CommRingCat.of K))) (_ : (picardFunctor A.X.hom).obj.RepresentableBy P),
      LocallyOfFiniteType P.hom

/-- **The field, discharged.** `T09Pic.PicRepresentableAbVar` from the printed leaf (drop "locally of finite
type"). -/
theorem picRepresentableAbVar_of_lft (h : PicRepresentableLFTAbVar) : T09Pic.PicRepresentableAbVar :=
  fun K _ A => by
    obtain ⟨P, rep, -⟩ := h K A
    exact ⟨P, ⟨rep⟩⟩

/-- Verbatim copy of pic-dict's leaf `PicDict.PicLocFinType` (wip/pic-dict 4e95795b,
`ZInQKernel/Contrib/OneProof/PicDictionary.lean` L2201; not on main at base 0caafe66, so copied here; the
integrator checks it against the original by `rfl` when both are in the tree). **LEAF (Z1, the Picard scheme
is locally of finite type).** For an abelian variety `A` over a field `K`, a scheme representing `Pic_{A/K}` is
locally of finite type over `K`. -/
def PicLocFinType : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (_ : (picardFunctor A.X.hom).obj.RepresentableBy P), LocallyOfFiniteType P.hom

/-- Local finite type is independent of the representing object (they are isomorphic over `K`). -/
theorem locallyOfFiniteType_of_representableBy {K : Type} [Field K] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of K)} {P Q : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor f).obj.RepresentableBy P) (rep' : (picardFunctor f).obj.RepresentableBy Q)
    (hQ : LocallyOfFiniteType Q.hom) : LocallyOfFiniteType P.hom := by
  let e : P ≅ Q := rep.uniqueUpToIso rep'
  have hw : e.hom.left ≫ Q.hom = P.hom := Over.w e.hom
  rw [← hw]
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  infer_instance

/-- **pic-dict's leaf `PicLocFinType`, discharged by the same printed leaf.** -/
theorem picLocFinType_of_lft (h : PicRepresentableLFTAbVar) : PicLocFinType := by
  intro K _ A P rep
  obtain ⟨Q, rep', hQ⟩ := h K A
  exact locallyOfFiniteType_of_representableBy rep rep' hQ

/-- Both at once (the form the integrator folds when pic-dict's leaves are in the bundle). -/
theorem picRepresentableAbVar_and_picLocFinType_of_lft (h : PicRepresentableLFTAbVar) :
    T09Pic.PicRepresentableAbVar ∧ PicLocFinType :=
  ⟨picRepresentableAbVar_of_lft h, picLocFinType_of_lft h⟩

/-- Conversely the printed leaf follows from the two statements it replaces: it is exactly their conjunction,
so the exchange loses nothing. -/
theorem lft_of_picRepresentableAbVar_of_picLocFinType (h1 : T09Pic.PicRepresentableAbVar)
    (h2 : PicLocFinType) : PicRepresentableLFTAbVar := fun K _ A => by
  obtain ⟨P, ⟨rep⟩⟩ := h1 K A
  exact ⟨P, rep, h2 K A P rep⟩

end PicRepr

import ZInQKernel.Contrib.OneProof.PhiSurjCharZero
import ZInQKernel.Contrib.OneProof.PicZeroAbVarCharZero

/-!
# kleiman-proper: the field `kleimanPicZeroProper` and what the chain reads of it

* §1. `KleimanPicZeroProper` (PicZeroAbVar.lean:25) copied verbatim, with `IsNormalScheme`; checked equal to the
  original by `rfl`.
* §2. The narrowed form the chain reads (abelian varieties, characteristic `0`): `KleimanPicZeroProperAbVar0`, a
  consequence of the field, and `PicZeroAbVar0` from it (the only reader, `TailZ53`'s
  `openAddedLeaves22PZ_of_OpenAddedLeaves23`, goes through `PicZeroChar0.picZeroAbVar0_of_leaves`).
* §3. The isolated core, `PicZeroDimLeAbVar0` (`dim Pic⁰_{A/K} ≤ dim A` in characteristic `0`), derived from the
  narrowed field with the chain's leaves (phisurj's `dim_le_of_open0`). The converse (core ⇒ narrowed field) is the
  argument of the brief; it is not compiled here (docs/research/kleiman-proper.md §3).
-/

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory TopologicalSpace
open scoped CategoryTheory.MonObj

set_option linter.style.haveILetI false

namespace KleimanProper

open T09Pic PkgI3 PkgI3.AbVar PicDict

/-! ## §1. Verbatim copy -/

/-- **Normal scheme** (Stacks, Tag 033H): every local ring `𝒪_{X,x}` is a normal domain (an integrally closed
domain). -/
def IsNormalScheme : ObjectProperty Scheme.{0} :=
  fun X => ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

/-- **LEAF (printed form).** Kleiman, *The Picard scheme* (FGA Explained, Ch. 9), Thm 9.5.4: for `X` proper and
geometrically normal over a field `K` (`X_{K'}` normal for every field `K'` over `K`, Mathlib's `geometrically`),
the identity component `Pic⁰_{X/K}` of the Picard scheme is proper. Stated for every scheme `P` representing the
fppf Picard sheaf `Pic_{X/K}` (unique up to unique isomorphism) and every open `V` whose underlying set is the
identity component. UNVERIFIED numbering. -/
def KleimanPicZeroProper : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))), IsProper X.hom →
    geometrically IsNormalScheme X.hom →
    ∀ (P : Over (Spec (CommRingCat.of K))) (rep : (picardFunctor X.hom).obj.RepresentableBy P)
      (V : P.left.Opens),
      letI := picardFunctorCommGrpObj X.hom rep
      (V : Set P.left) = identityComponent P → IsProper (V.ι ≫ P.hom)

theorem kleimanPicZeroProper_eq : KleimanPicZeroProper = PicFix.KleimanPicZeroProper := rfl

/-! ## §2. The narrowed form the chain reads -/

/-- **`Pic⁰` of an abelian variety in characteristic `0` is proper** (`PicFix.KleimanPicZeroProper` for `X` an
abelian variety over a field of characteristic `0`; Kleiman 9.5.4 restricted, a consequence of it). -/
def KleimanPicZeroProperAbVar0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K], PicZeroChar0.PicZeroProperAt K

theorem kleimanPicZeroProperAbVar0_of (h : KleimanPicZeroProper) : KleimanPicZeroProperAbVar0 :=
  fun K _ _ => PicZeroChar0.picZeroProperAt_of_kleiman h K

/-- The chain's only use of the field, from the narrowed form (the proof of
`PicZeroChar0.picZeroAbVar0_of_leaves` with `h3` narrowed). -/
theorem picZeroAbVar0_of_narrowed (h1 : PicLocFinType) (h2 : IdentityComponentLFT)
    (h3 : KleimanPicZeroProperAbVar0) : PicZeroChar0.PicZeroAbVar0 := fun K _ _ =>
  PicZeroChar0.picZeroAbVarAt_of h1 h2 K
    (PicZeroChar0.picZeroSmoothAt_charZero ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof h1 K) (h3 K)

/-- Sanity: the narrowed route agrees with the folded one on the chain's input. -/
theorem picZeroAbVar0_of_leaves' (h1 : PicLocFinType) (h2 : IdentityComponentLFT)
    (h3 : PicFix.KleimanPicZeroProper) : PicZeroChar0.PicZeroAbVar0 :=
  picZeroAbVar0_of_narrowed h1 h2 (kleimanPicZeroProperAbVar0_of h3)

/-! ## §3. The isolated core: `dim Pic⁰ ≤ dim A` -/

/-- **`dim Pic⁰_{A/K} ≤ dim A` in characteristic `0`.** For an abelian variety `A` over a field `K` of
characteristic `0`, every scheme `P` representing `Pic_{A/K}` and every open `V` of `P` whose underlying set is the
identity component, `dim V ≤ dim A`. A consequence of Mumford, *Abelian varieties*, §13 (`Pic⁰_{A/k} = Â` is an
abelian variety of dimension `g`, `T_0 Â ≅ H¹(A, 𝒪_A)`; numbering UNVERIFIED) and of Kleiman 9.5.4 with the chain's
leaves (`picZeroDimLeAbVar0_of_narrowed`); not a printed statement. -/
def PicZeroDimLeAbVar0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (V : P.left.Opens),
    letI := picardFunctorCommGrpObj A.X.hom rep
    (V : Set P.left) = identityComponent P → topologicalKrullDim V ≤ topologicalKrullDim A.X.left

/-- The underlying space of `B` is homeomorphic to the identity component, through `j`. -/
theorem dim_eq_of_isPicZero {K : Type} [Field K] {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} {j : B.X ⟶ P}
    (hj : IsPicZero rep B j) (V : P.left.Opens)
    (hV : letI := picardFunctorCommGrpObj A.X.hom rep; (V : Set P.left) = identityComponent P) :
    topologicalKrullDim V = topologicalKrullDim B.X.left := by
  letI := picardFunctorCommGrpObj A.X.hom rep
  obtain ⟨hopen, hrange, -⟩ := hj
  haveI : IsOpenImmersion j.left := hopen
  have hmem : ∀ z : B.X.left, j.left z ∈ V := fun z => by
    rw [← SetLike.mem_coe, hV, ← hrange]; exact ⟨z, rfl⟩
  let g : B.X.left → V := fun z => ⟨j.left z, hmem z⟩
  have hg : IsHomeomorph g := by
    rw [isHomeomorph_iff_isEmbedding_surjective]
    refine ⟨(j.left.isOpenEmbedding.isEmbedding).codRestrict _ hmem, ?_⟩
    rintro ⟨p, hp⟩
    have : p ∈ Set.range j.left := by rw [hrange, ← hV]; exact hp
    obtain ⟨z, rfl⟩ := this
    exact ⟨z, rfl⟩
  exact (IsHomeomorph.topologicalKrullDim_eq g hg).symm

/-- **The core from the narrowed field** and the chain's leaves (L1 `picRepresentableAbVar` is not needed beyond
what `dim_le_of_open0` takes; the torsion leaf `mumfordTorsionAlgClosed`): `PicZeroAbVar0` gives `B` with
`IsPicZero`, and phisurj's `dim_le_of_open0` bounds `dim B`. -/
theorem picZeroDimLeAbVar0_of_narrowed (h1 : PicRepresentableAbVar) (hL : PicLocFinType)
    (hI : IdentityComponentLFT) (hT : AvSplit.MumfordTorsionAlgClosed) (h3 : KleimanPicZeroProperAbVar0) :
    PicZeroDimLeAbVar0 := by
  intro K _ _ A P rep V hV
  have h2 := picZeroAbVar0_of_narrowed hL hI h3
  obtain ⟨B, j, hj⟩ := h2 K A P rep
  obtain ⟨a, ha⟩ := PkgI3.AbVar.dim_finite A
  obtain ⟨b, hb⟩ := PkgI3.AbVar.dim_finite B
  have hba := PhiSurj.dim_le_of_open0 h1 h2 hT rep hj a b ha hb
  rw [dim_eq_of_isPicZero rep hj V hV]
  change B.dim ≤ A.dim
  rw [ha, hb]
  exact_mod_cast hba

end KleimanProper

#print axioms KleimanProper.picZeroAbVar0_of_narrowed
#print axioms KleimanProper.picZeroDimLeAbVar0_of_narrowed

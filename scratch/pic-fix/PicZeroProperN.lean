import ZInQKernel.Contrib.OneProof.PicDictionary
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime

/-!
# pic-fix (2): `Pic⁰` proper, printed form (Kleiman 9.5.4 over geometrically normal `X`)
-/

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

namespace PicFix

open T09Pic PkgI3 PkgI3.AbVar PicDict

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

/-- A scheme smooth over a field is normal (vendored FLT-project lemma: localizations of a smooth algebra over a
UFD at primes are integrally closed domains). -/
theorem isNormalScheme_of_smooth_field {Z : Scheme.{0}} {L : Type} [Field L]
    (f : Z ⟶ Spec (CommRingCat.of L)) [Smooth f] : IsNormalScheme Z := by
  intro z
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (x := z) (U := ⊤) trivial
  have hs := f.smooth_appLE (isAffineOpen_top (Spec (CommRingCat.of L))) hU le_top
  let φ : L →+* Γ(Z, U) :=
    (f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom
  have hφ : φ.Smooth := by
    refine RingHom.Smooth.comp ?_ hs
    exact RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  letI := φ.toAlgebra
  haveI : Algebra.Smooth L Γ(Z, U) := hφ
  letI : Algebra Γ(Z, U) (Z.presheaf.stalk (⟨z, hzU⟩ : U)) :=
    TopCat.Presheaf.algebra_section_stalk Z.presheaf ⟨z, hzU⟩
  haveI := hU.isLocalization_stalk ⟨z, hzU⟩
  exact ZInQ.Contrib.CloudW03NeronSurj.FLT.Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
    L Γ(Z, U) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal (Z.presheaf.stalk (⟨z, hzU⟩ : U))

/-- Smooth morphisms are geometrically normal. -/
theorem geometricallyNormal_of_smooth {X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f] :
    geometrically IsNormalScheme f := by
  intro K _ y Z fst snd h
  haveI : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h inferInstance
  exact isNormalScheme_of_smooth_field snd

/-- **`PicZeroProper` (the abelian-variety instance) from Kleiman 9.5.4**: an abelian variety is proper and
smooth, hence geometrically normal. -/
theorem picZeroProper_of_kleiman (h : KleimanPicZeroProper) : PicZeroProper := by
  intro K _ A P rep V hV
  exact h K A.X inferInstance (geometricallyNormal_of_smooth A.X.hom) P rep V hV

/-- **Main result (`PicZeroAbVar`)** from Kleiman 9.4.8 (`PicLocFinType`), SGA 3 VI_A 2.4
(`IdentityComponentLFT`), Kleiman 9.5.4 in its printed form, and `PicZeroSmooth` (pending reading). -/
theorem picZeroAbVar_of_printed (h1 : PicLocFinType) (h2 : IdentityComponentLFT) (h3a : PicZeroSmooth)
    (h3b : KleimanPicZeroProper) : PicZeroAbVar :=
  picZeroAbVar_of_leaves h1 h2 h3a (picZeroProper_of_kleiman h3b)

end PicFix

#print axioms PicFix.picZeroAbVar_of_printed

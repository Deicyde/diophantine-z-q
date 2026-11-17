/-
H5 lane3 Step 2, B2 `FiniteSquarePresentation`: ASSEMBLY PROVED from B2.a–B2.d, B1, the
all-field square I5a, C2's paired sections, and two small TRUE obligations. 2026-11-17. New file.
SOURCE-ONLY, UNCOMPILED. Universe u.

Ingredients, all by exact name:
* (B2.a) and (B2.b): C4. (B2.c): `trivialLineSectionDichotomy`, PROVED. (B2.d): mine. B1: mine.
* I5a: `Step1.TheoremOfSquare` (C2's AllFieldNativeSquare).
* C2: `pairedSectionFromActualSquare`, `pairedSection_zeroLocus` (zero ideal
  `= D.comap t_x * D.comap t_{x⁻¹}`), `pulledSectionHom`, `pulledSectionHom_zeroLocus`.

Small obligations (TRUE):
* `InfinitePointsOfNotFinite`: a proper scheme over an algebraically closed field that is not
  finite has infinitely many rational points. Finitely many rational points means finitely many
  closed points (Mathlib `pointEquivClosedPoint`), hence finitely many points (Jacobson), hence
  quasi-finite, hence finite (proper; Mathlib `IsFinite.of_isProper_of_locallyQuasiFinite`).
* `SectionDichotomySupport`: for `s : O_C ⟶ i^*M` with zero ideal `I.comap i`:
  - `s = 0` forces `range i ⊆ supp I`, since the zero locus of `0` is `⊥`, whose support is
    everything (W07 `zeroLocus_eq_bot_iff`, Mathlib `support_comap`);
  - `IsIso s` forces `range i ∩ supp I = ∅`, since an isomorphism has the unit zero ideal.
  The support of `D.comap t_x * D.comap t_{x⁻¹}` is the union of the two preimages (Mathlib
  `support_mul`/`support_comap`).
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B2.SectionDichotomy
import NativeTranslatedPairSection
import NativeZeroLocusProducts

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step2B2

local notation "tr" => H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation

/-- (TRUE) A closed subscheme of `A` that is proper but not finite over an algebraically closed
field contains infinitely many rational points of `A`. -/
def InfinitePointsOfNotFinite : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (A : Grp (Over (Spec (CommRingCat.of K))))
    {C : Scheme.{u}} (i : C ⟶ A.X.left) [IsClosedImmersion i],
    IsProper (i ≫ A.X.hom) → ¬ IsFinite (i ≫ A.X.hom) →
      {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X |
        x.left (IsLocalRing.closedPoint K) ∈ Set.range i}.Infinite

/-- (TRUE) The support dichotomy for a pulled section with a comap zero ideal. -/
def SectionDichotomySupport : Prop :=
  ∀ {X C : Scheme.{u}} (i : C ⟶ X) (M : X.Modules) [M.IsInvertible]
    (s : Scheme.Modules.unit X ⟶ M),
    (H5OriginalDVR.Lane2.NativeDivisorKernel.pulledSectionHom i M s = 0 →
      Set.range i ⊆ (s.zeroLocus.support : Set X)) ∧
    (IsIso (H5OriginalDVR.Lane2.NativeDivisorKernel.pulledSectionHom i M s) →
      Set.range i ∩ (s.zeroLocus.support : Set X) = ∅)

/-- (TRUE; Mathlib `support_mul` and `support_comap`) The support of the paired zero ideal. -/
def PairedSupportUnion : Prop :=
  ∀ {X : Scheme.{u}} (D : X.IdealSheafData) (f g : X ⟶ X),
    ((D.comap f * D.comap g).support : Set X) =
      f ⁻¹' (D.support : Set X) ∪ g ⁻¹' (D.support : Set X)

/-- B2, PROVED from its decomposition. -/
theorem finiteSquarePresentation (hA : NonFiniteContractsSubvariety.{u})
    (hB : ContractedPresentationTrivial.{u}) (hD : MumfordContractedCombinatorics.{u})
    (hB1 : H5OriginalDVR.Lane2.Step2DelegatedInterfaces.FiniteSupportStabilizer.{u})
    (hSq : ZInQ.Contrib.CloudR2NOS.Step1.TheoremOfSquare.{u})
    (hPts : InfinitePointsOfNotFinite.{u}) (hDS : SectionDichotomySupport.{u})
    (hPU : PairedSupportUnion.{u}) :
    H5OriginalDVR.Lane2.Step2DelegatedInterfaces.FiniteSquarePresentation.{u} := by
  intro K _ _ A _ N _ θ hθ D hDinv hZero hN hH d 𝔓
  by_contra hfin
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  -- (B2.a): a contracted integral, non-finite closed subvariety
  obtain ⟨C, i, hi, hCint, p, hcontr, hCnf⟩ :=
    hA A.X.hom (ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.π K d)
      𝔓.toProj 𝔓.toProj_π hfin
  haveI := hi
  haveI := hCint
  haveI : IsProper (i ≫ A.X.hom) := inferInstance
  -- (B2.b): `N^2|_C` is trivial
  have hCtriv := hB A.X.hom (Scheme.Modules.tensorPow N 2) d 𝔓 i p hcontr
  -- (B2.c) applied to each paired section, read as a support dichotomy
  have hdich : ∀ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X,
      Set.range i ⊆ (tr A x) ⁻¹' (D.support : Set A.X.left) ∪
          (tr A x⁻¹) ⁻¹' (D.support : Set A.X.left) ∨
        Set.range i ∩ ((tr A x) ⁻¹' (D.support : Set A.X.left) ∪
          (tr A x⁻¹) ⁻¹' (D.support : Set A.X.left)) = ∅ := by
    intro x
    obtain ⟨eSq⟩ := hSq A N x x⁻¹
    let s := H5OriginalDVR.Lane2.NativeTranslatedPairSection.pairedSectionFromActualSquare
      A N θ x eSq
    have hzl : (s.zeroLocus.support : Set A.X.left) =
        (tr A x) ⁻¹' (D.support : Set A.X.left) ∪ (tr A x⁻¹) ⁻¹' (D.support : Set A.X.left) := by
      rw [H5OriginalDVR.Lane2.NativeZeroLocusProducts.pairedSection_zeroLocus A N θ D hZero x eSq]
      exact hPU D _ _
    rw [← hzl]
    rcases trivialLineSectionDichotomy (i ≫ A.X.hom) _ hCtriv
        (H5OriginalDVR.Lane2.NativeDivisorKernel.pulledSectionHom i _ s) with h0 | hiso
    · exact Or.inl ((hDS i _ s).1 h0)
    · exact Or.inr ((hDS i _ s).2 hiso)
  -- the image of `C` is closed and irreducible with infinitely many rational points
  have hclosed : IsClosed (Set.range i) := i.isClosedEmbedding.isClosed_range
  have hirr : IsIrreducible (Set.range i) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ C).image i i.continuous.continuousOn
  have hinfpts : {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X |
      x.left (IsLocalRing.closedPoint K) ∈ Set.range i}.Infinite :=
    hPts A i inferInstance hCnf
  -- (B2.d): the support stabilizer is infinite, contradicting B1
  exact hD A D hDinv (Set.range i) hclosed hirr hinfpts hdich (hB1 A D hDinv hH)

end ZInQ.Contrib.CloudR2NOS.Step2B2

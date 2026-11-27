import Mathlib
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.QuotientInputs
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.ProjFiniteSets
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.BuzzardLeaves2
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.Quotients
/-!
# Finite sets in affines from local projectivity

1. Projective `N`-space `PNR R N = Proj R[x_0, ..., x_N]` over a commutative ring `R`, with
   its structure map to `Spec R`. Every finite set of its points lies in an affine open.
2. A closed subscheme of a scheme in which every finite set of points lies in an affine open
   has the same property, since closed immersions are affine.
3. A finite set of points inside an open subscheme with this property lies in an affine open
   of the ambient scheme, since open immersions carry affine opens to affine opens.
4. The glue lemma. Let `f : A ⟶ X`, where every finite set of points of `X` lies in an affine
   open, and suppose that for every affine open `U` of `X` whose ring of sections satisfies a
   ring property `P` (and every affine open does), the preimage `f⁻¹ U` is a closed subscheme
   of some projective space over `Γ(X, U)`. Then every finite set of points of `A` lies in an
   affine open. No compatibility of the closed immersion with the map to `U` is needed.
5. The glue lemma for the total space of the universal false elliptic curve of the leaves: the
   statement `fsa_A1` with the projectivity input replaced by local projectivity.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Y3Buzzard.ProjGlue

open Y3QuotientDescent (FiniteSetsInAffines)

universe u

/-! ## 1. Projective space over a commutative ring -/

/-- The homogeneous coordinate ring `R[x_0, ..., x_N]` of projective `N`-space over `R`. -/
abbrev PNRingR (R : Type) [CommRing R] (N : ℕ) : Type := MvPolynomial (Fin (N + 1)) R

/-- The grading of `PNRingR R N` by total degree. -/
abbrev PNGradingR (R : Type) [CommRing R] (N : ℕ) : ℕ → Submodule R (PNRingR R N) :=
  MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R

/-- The polynomial ring is a graded algebra for the total-degree grading. Over `ℤ` the
grading of `PNZ` is found first; the two agree definitionally (`PNR_int_eq`). -/
instance (priority := low) instGradedAlgebraPNR (R : Type) [CommRing R] (N : ℕ) :
    GradedAlgebra (PNGradingR R N) :=
  MvPolynomial.gradedAlgebra

/-- Projective `N`-space over `R`: `Proj R[x_0, ..., x_N]`. -/
abbrev PNR (R : Type) [CommRing R] (N : ℕ) : Scheme.{0} := Proj (PNGradingR R N)

/-- The structure map of `PNR R N` to `Spec R`: the map to the spectrum of the degree-zero part,
followed by the map induced by the inclusion of `R` as the constants. -/
def PNR.toSpec (R : Type) [CommRing R] (N : ℕ) : PNR R N ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (PNGradingR R N) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (PNGradingR R N 0)))

/-- Every finite set of points of `PNR R N` lies in an affine open, namely a basic open
`D₊(g)` with `g` homogeneous of positive degree. -/
theorem finiteSetsInAffines_PNR (R : Type) [CommRing R] (N : ℕ) :
    FiniteSetsInAffines (PNR R N) :=
  fun F hF => Y3ProjFiniteSets.exists_isAffineOpen_superset_of_finite (PNGradingR R N) F hF

/-- Over `ℤ`, `PNR` is the projective space `PNZ` of the leaves. -/
theorem PNR_int_eq (N : ℕ) : PNR ℤ N = PNZ N := rfl

/-! ## 2. Closed subschemes -/

/-- A closed subscheme of a scheme in which every finite set of points lies in an affine open
has the same property: closed immersions are affine morphisms. -/
theorem finiteSetsInAffines_of_isClosedImmersion {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (hY : FiniteSetsInAffines Y) : FiniteSetsInAffines Z :=
  Y3QuotientDescent.finiteSetsInAffines_of_isAffineHom i hY

/-- A closed subscheme of `PNR R N` has finite sets in affines. -/
theorem finiteSetsInAffines_of_closedImmersion_PNR {Z : Scheme.{0}} {R : Type} [CommRing R]
    {N : ℕ} (i : Z ⟶ PNR R N) [IsClosedImmersion i] : FiniteSetsInAffines Z :=
  finiteSetsInAffines_of_isClosedImmersion i (finiteSetsInAffines_PNR R N)

/-! ## 3. Open subschemes -/

/-- A finite set of points contained in an open `V` lies in an affine open of the ambient
scheme, provided every finite set of points of the open subscheme `V` lies in an affine open
of `V`. -/
theorem exists_isAffineOpen_superset_of_subset {X : Scheme.{u}} (V : X.Opens)
    (hV : FiniteSetsInAffines V.toScheme) {F : Set X} (hF : F.Finite) (hFV : F ⊆ V) :
    ∃ W : X.Opens, IsAffineOpen W ∧ F ⊆ W := by
  obtain ⟨W, hW, hsub⟩ := hV (V.ι ⁻¹' F) (hF.preimage V.ι.isOpenEmbedding.injective.injOn)
  refine ⟨V.ι ''ᵁ W, hW.image_of_isOpenImmersion V.ι, ?_⟩
  intro x hx
  obtain ⟨y, rfl⟩ : x ∈ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact hFV hx
  exact ⟨y, hsub hx, rfl⟩

/-! ## 4. The glue lemma -/

/-- Let `f : A ⟶ X` and suppose every finite set of points of `X` lies in an affine open. If
for every affine open `U` of `X` (whose ring of sections satisfies `P`, as every one does) the
preimage `f⁻¹ U` has a closed immersion into some projective space `PNR Γ(X, U) N`, then
every finite set of points of `A` lies in an affine open.

Proof: a finite `F ⊆ A` has finite image, which lies in an affine open `U` of `X`; then
`F ⊆ f⁻¹ U`, the open subscheme `f⁻¹ U` is closed in `PNR Γ(X, U) N`, hence has finite sets in
affines, and an affine open of `f⁻¹ U` containing `F` is an affine open of `A`. -/
theorem finiteSetsInAffines_of_locallyProjective {A X : AlgebraicGeometry.Scheme} (f : A ⟶ X)
    (P : ∀ (R : Type), [CommRing R] → Prop)
    (hX : Y3QuotientDescent.FiniteSetsInAffines X)
    (hP : ∀ U : X.Opens, AlgebraicGeometry.IsAffineOpen U → P Γ(X, U))
    (hproj : ∀ U : X.Opens, AlgebraicGeometry.IsAffineOpen U → P Γ(X, U) →
      ∃ (N : ℕ) (i : (f ⁻¹ᵁ U).toScheme ⟶ PNR Γ(X, U) N), AlgebraicGeometry.IsClosedImmersion i) :
    Y3QuotientDescent.FiniteSetsInAffines A := by
  intro F hF
  obtain ⟨U, hU, hFU⟩ := hX ((fun x => f x) '' F) (hF.image fun x => f x)
  obtain ⟨N, i, hi⟩ := hproj U hU (hP U hU)
  exact exists_isAffineOpen_superset_of_subset (f ⁻¹ᵁ U)
    (finiteSetsInAffines_of_isClosedImmersion i (finiteSetsInAffines_PNR Γ(X, U) N)) hF
    (fun x hx => hFU ⟨x, hx, rfl⟩)

/-! ## 5. The total space of the universal false elliptic curve -/

/-- `FiniteSetsInAffines` for the total space of the universal false elliptic curve over the
moduli scheme of the leaves, from local projectivity over the affine opens of the base. This is
`fsa_A1` with its projectivity input replaced by the hypotheses of the glue lemma. -/
theorem fsa_A1_of_locallyProjective (hB1 : BuzzardThm21Cor23V15')
    (P : ∀ (R : Type), [CommRing R] → Prop)
    (hP : ∀ U : (leafD hB1).X.left.Opens, IsAffineOpen U → P Γ((leafD hB1).X.left, U))
    (hproj : ∀ U : (leafD hB1).X.left.Opens, IsAffineOpen U → P Γ((leafD hB1).X.left, U) →
      ∃ (N : ℕ) (i : ((leafD hB1).A.F.hom ⁻¹ᵁ U).toScheme ⟶ PNR Γ((leafD hB1).X.left, U) N),
        IsClosedImmersion i) :
    FiniteSetsInAffines (leafD hB1).A.F.left :=
  finiteSetsInAffines_of_locallyProjective (leafD hB1).A.F.hom P (fsa_X1 hB1) hP hproj

end Y3Buzzard.ProjGlue

/-
H5 lane3 Step 2, B2 `FiniteSquarePresentation` (Step2DelegatedInterfaces 4d5c8dce):
DECOMPOSITION into exact native sub-obligations, with truth sketches (lead 04:27Z, risk first).
2026-11-17. New file. SOURCE-ONLY, UNCOMPILED; it states Props only, with no proofs yet.
Universe u, any characteristic.

Assembly plan for B2, the contrapositive. Suppose `toProj` is not finite.
(B2.a) There is an integral closed `C ⊆ A`, not finite over `K`, contracted to a point `p`.
(B2.b) The frame field of the presentation trivializes `N^2|_C`.
Sections: for each `x`, C2's `pairedSectionFromActualSquare` gives a section `s_x` of `N^2`
(`= t_x^*θ ⊗ t_{x⁻¹}^*θ` through the all-field square I5a). Its zero locus is
`D.comap t_x * D.comap t_{x⁻¹}` (C2 `pairedSection_zeroLocus`), and `C2 pulledSectionHom_zeroLocus`
gives its restriction to `C`.
(B2.c) Every section of a trivial line on proper integral `C` is `0` or an isomorphism. So for each
`x`: either `C ⊆ supp(t_x^*D) ∪ supp(t_{x⁻¹}^*D)` or `C` misses that union.
(B2.d) Mumford's combinatorics then make the SUPPORT stabilizer infinite.
B1 (`FiniteSupportStabilizer`, also lane3) contradicts this, given `H(D)` finite.

Commutativity of `A` is Mathlib `isCommMonObj_of_isProper_of_geometricallyIntegral`
(Group/Abelian.lean). The irreducibility of `C ×_K C` and `C ×_K D_k` comes from C5's
`GeomIrreducibleOverAlgClosed` plus Mathlib.

TRUTH SKETCHES:
* (B2.a) TRUE. Proper with finite fibres implies finite (Stacks 02OG; Mathlib ZMT and
  quasi-finite locus). A non-finite proper `φ` has a closed point with infinite fibre (fibre
  dimension is upper semicontinuous; Jacobson). An irreducible component of that fibre with the
  reduced structure is integral, proper, positive-dimensional and contracted.
* (B2.b) TRUE. If `p ∈ D₊(X_j)` then `C ⊆ toProj⁻¹ D₊(X_j)`. The frame field makes `σ_j`
  a free generator there, and pullback of a free generator is a free generator (C4 FramePullback).
* (B2.c) TRUE. `Γ(C, O_C) = K` (PMGF, using a rational point of `C`), so a section of `O_C` is a
  constant: either `0`, or a unit and hence an isomorphism.
* (B2.d) TRUE (Mumford §6 App. 1). Put `D' = supp D`, with irreducible components `D'_k`
  (finitely many, Noetherian). For each `k`, `U_k := C·D'_k⁻¹` is irreducible and lies in
  `U₊ ∪ U₋`, where `U_± := {x | C ⊆ t_{x^{±1}}⁻¹ D'}` are closed. So `U_k` lies in one of them.
  - Case `U₊`: `D'_k·(C·C⁻¹) ⊆ D'`.
  - Case `U₋`: `D'_k⁻¹·C·C ⊆ D'`.
  In both cases the irreducible translates are components of `D'`. By irreducibility of `C×C`,
  the translate map to the finite component set is constant, so every `D'_k` is fixed by `C·C⁻¹`.
  Hence `C·C⁻¹` lies in the support stabilizer. `C` has infinitely many rational points, so that
  stabilizer is infinite.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.I1StatusV2
import Step2DelegatedInterfaces

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step2B2

/-- (B2.a) A non-finite proper map contracts an integral positive-dimensional subvariety. -/
def NonFiniteContractsSubvariety : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] {X P : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (fP : P ⟶ Spec (CommRingCat.of K)) [IsProper fX] [IsSeparated fP] (φ : X ⟶ P),
    φ ≫ fP = fX → ¬ IsFinite φ →
      ∃ (C : Scheme.{u}) (i : C ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral C)
        (p : Spec (CommRingCat.of K) ⟶ P),
        i ≫ φ = (i ≫ fX) ≫ p ∧ ¬ IsFinite (i ≫ fX)

/-- (B2.b) A presentation's line is trivial on every subscheme its section map contracts. -/
def ContractedPresentationTrivial : Prop :=
  ∀ {K : Type u} [Field K] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (L : X.Modules) [L.IsInvertible] (d : ℕ)
    (𝔓 : ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ProjPresentation
      L fX d)
    {C : Scheme.{u}} (i : C ⟶ X)
    (p : Spec (CommRingCat.of K) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K)),
    i ≫ 𝔓.toProj = (i ≫ fX) ≫ p →
      Nonempty ((Scheme.Modules.pullback i).obj L ≅ 𝟙_ C.Modules)

/-- (B2.c) On a proper integral scheme over an algebraically closed field, a section of a
trivial line is zero or an isomorphism. -/
def TrivialLineSectionDichotomy : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (fC : C ⟶ Spec (CommRingCat.of K))
    [IsProper fC] [IsIntegral C] (L : C.Modules) [L.IsInvertible],
    Nonempty (L ≅ 𝟙_ C.Modules) → ∀ s : Scheme.Modules.unit C ⟶ L, s = 0 ∨ IsIso s

/-- (B2.d) Mumford's contracted-curve combinatorics, on rational points and closed sets. -/
def MumfordContractedCombinatorics : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (D : A.X.left.IdealSheafData) (_ : D.IsInvertible) (C : Set A.X.left),
    IsClosed C → IsIrreducible C →
    {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X |
      x.left (IsLocalRing.closedPoint K) ∈ C}.Infinite →
    (∀ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X,
      let W := (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x) ⁻¹'
          (D.support : Set A.X.left) ∪
        (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x⁻¹) ⁻¹'
          (D.support : Set A.X.left)
      C ⊆ W ∨ C ∩ W = ∅) →
    {x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X |
      (D.comap (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x)).support =
        D.support}.Infinite

end ZInQ.Contrib.CloudR2NOS.Step2B2

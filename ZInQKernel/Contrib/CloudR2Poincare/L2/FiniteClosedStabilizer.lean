import ZInQKernel.Contrib.CloudR2Poincare.L2.GeneralInvariant
import ZInQKernel.Contrib.CloudR2Poincare.L2.ReducedComponents
import ZInQKernel.Contrib.CloudR2Poincare.L2.KernelFibres
import ZInQKernel.Contrib.CloudR2Poincare.L1.PicardKernel

/-!
# A genuine closed normalized stabilizer is finite

The single normalized-family vanishing statement on K pulls back to every
reduced irreducible component. Ambient inversion and very-ampleness make each
integral component zero-dimensional. Native Noetherian finiteness and ZMT then
make the ORIGINAL K→Spec k finite, not a replacement group scheme.
No identity component, Cartier theorem, dual, or all-T representability Fact is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- **Finite closed normalized stabilizer bridge.** The closed scheme K need
only satisfy literal family vanishing on the parameter K. A reduced-base
seesaw proof on a closed fibre-triviality locus is enough to supply this input. -/
theorem finite_space_of_normalizedInvariant_closedSubscheme
    {k : Type u} [Field k] (A : PkgI3.AbVar k)
    (K : Over (Spec (.of k))) (j : K ⟶ A.X) [IsClosedImmersion j.left]
    (M : A.X.left.Modules) (hM : VeryAmple A.X.hom M)
    (hfamily : letI : M.IsInvertible := hM.isInvertible
      L1.normalizedPolarizationFamily A.X (Scheme.Pic.mk M) j = 1) : Finite K.left := by
  letI : M.IsInvertible := hM.isInvertible
  have : IsProper K.hom := by
    rw [← j.w]
    infer_instance
  letI : IsLocallyNoetherian K.left := LocallyOfFiniteType.isLocallyNoetherian K.hom
  letI : CompactSpace K.left := QuasiCompact.compactSpace_of_compactSpace K.hom
  letI : IsNoetherian K.left := { }
  refine finite_scheme_of_reducedComponents_dimZero K.left ?_
  intro Z hZ
  let T : Over (Spec (.of k)) := Over.mk (reducedComponentι K.left Z hZ ≫ K.hom)
  let f : T ⟶ K := Over.homMk (reducedComponentι K.left Z hZ)
  let t : T ⟶ A.X := f ≫ j
  letI : IsIntegral T.left := inferInstanceAs (IsIntegral (reducedComponent K.left Z hZ))
  letI : IsClosedImmersion t.left := by
    change IsClosedImmersion (reducedComponentι K.left Z hZ ≫ j.left)
    infer_instance
  have hT : L1.normalizedPolarizationFamily A.X (Scheme.Pic.mk M) t = 1 := by
    have h := L1.normalizedPolarizationFamily_parameter A.X (Scheme.Pic.mk M) j f
    rw [hfamily, Scheme.Pic.map_one] at h
    exact h.symm
  exact dimension_le_zero_of_normalizedInvariant_integral_closedSubscheme A t M hM hT

/-- The original structural morphism of that actual closed scheme is finite. -/
theorem isFinite_of_normalizedInvariant_closedSubscheme
    {k : Type u} [Field k] (A : PkgI3.AbVar k)
    (K : Over (Spec (.of k))) (j : K ⟶ A.X) [IsClosedImmersion j.left]
    (M : A.X.left.Modules) (hM : VeryAmple A.X.hom M)
    (hfamily : letI : M.IsInvertible := hM.isInvertible
      L1.normalizedPolarizationFamily A.X (Scheme.Pic.mk M) j = 1) : IsFinite K.hom := by
  have : IsProper K.hom := by rw [← j.w]; infer_instance
  letI : Finite K.left := finite_space_of_normalizedInvariant_closedSubscheme A K j M hM hfamily
  exact isFinite_of_finite_fibres K.hom fun _ => Set.toFinite _

/-- Over an algebraically closed field, finite underlying scheme space and
finite-type structure make the ACTUAL categorical field-point type finite. -/
theorem finite_rationalPoints_of_finite_space
    {k : Type u} [Field k] [IsAlgClosed k] (K : Over (Spec (.of k)))
    [LocallyOfFiniteType K.hom] [Finite K.left] :
    Finite (𝟙_ (Over (Spec (.of k))) ⟶ K) := by
  let pt : Spec (.of k) := IsLocalRing.closedPoint k
  let eval : (𝟙_ (Over (Spec (.of k))) ⟶ K) → K.left := fun a => a.left pt
  refine Finite.of_injective eval ?_
  intro a b h
  apply Over.OverMorphism.ext
  exact ext_of_apply_closedPoint_eq K.hom (Over.w a) (Over.w b) h

/-- The point-level composition: a genuine normalized closed cover of the
translation stabilizer makes its actual Ω-point set finite. Both still-needed
geometric inputs are explicit; this is not asserted as the forward theorem. -/
theorem finite_translationStabilizer_of_normalized_closedCover
    {k : Type u} [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k)
    (K : Over (Spec (.of k))) (j : K ⟶ A.X) [IsClosedImmersion j.left]
    (M : A.X.left.Modules) (hM : VeryAmple A.X.hom M)
    (hfamily : letI : M.IsInvertible := hM.isInvertible
      L1.normalizedPolarizationFamily A.X (Scheme.Pic.mk M) j = 1)
    (hcover : letI : M.IsInvertible := hM.isInvertible
      ∀ a ∈ L1.translationStabilizer A.X (Scheme.Pic.mk M),
        ∃ z : 𝟙_ (Over (Spec (.of k))) ⟶ K, z ≫ j = a) :
    letI : M.IsInvertible := hM.isInvertible
    (L1.translationStabilizer A.X (Scheme.Pic.mk M)).Finite := by
  letI : M.IsInvertible := hM.isInvertible
  have : IsProper K.hom := by rw [← j.w]; infer_instance
  letI : Finite K.left := finite_space_of_normalizedInvariant_closedSubscheme A K j M hM hfamily
  letI : Finite (𝟙_ (Over (Spec (.of k))) ⟶ K) := finite_rationalPoints_of_finite_space K
  exact (Set.finite_range (fun z : 𝟙_ (Over (Spec (.of k))) ⟶ K => z ≫ j)).subset
    fun a ha => hcover a ha

end ZInQ.Contrib.CloudR2Poincare.L2

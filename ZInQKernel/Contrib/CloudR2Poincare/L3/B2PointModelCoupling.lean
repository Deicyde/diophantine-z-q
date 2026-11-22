import ZInQKernel.Contrib.CloudR2Poincare.L3.B2FieldModel
import ZInQKernel.Contrib.CloudR2Poincare.L3.B2SlicePullback
import ZInQKernel.Contrib.CloudR2Poincare.L3.B2SliceVanishing
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeModel

/-! Literal coupling of actual rational fibre cohomology to the UNIVERSAL native
finite-free model. The comparison parameter is exactly data produced by the
unconditional W07 FiniteFreeModel theorem, not an assumed vanishing bridge. -/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L3
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u

/-- The unchanged comparator telescope from the native universal finite-free model. -/
def UniversalModelComparison {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (U : Y.Opens) (P : CochainComplex U.toScheme.Modules ℤ) : Prop :=
  ∀ {T X' : Scheme.{u}} (g : T ⟶ U.toScheme) (px : X' ⟶ X) (pf : X' ⟶ T)
    [HasInjectiveResolutions X'.Modules], IsPullback px pf f (g ≫ U.ι) →
    ∀ q : ℕ, Nonempty
      ((((Scheme.Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
        (Scheme.Modules.higherDirectImage pf q).obj ((Scheme.Modules.pullback px).obj F))

/-- Vanishing of native cohomology on an actual field-valued Cartesian fibre
forces zero homology of the actual pulled universal model. -/
theorem model_rational_fibre_homology_zero
    {k : Type u} [Field k] (B : PkgI3.AbVar k)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) [F.IsInvertible]
    (U : Y.Opens) (P : CochainComplex U.toScheme.Modules ℤ)
    (comparison : UniversalModelComparison f F U P)
    (g : Spec (.of k) ⟶ U.toScheme) (px : B.X.left ⟶ X)
    (square : IsPullback px B.X.hom f (g ≫ U.ι)) (q : ℕ)
    (hH : Subsingleton (((Scheme.Modules.pullback px).obj F).H q)) :
    IsZero ((((Scheme.Modules.pullback g).mapHomologicalComplex _).obj P).homology q) := by
  letI : B.X.left.Over (Spec (.of k)) := ⟨B.X.hom⟩
  haveI : QuasiCompact (B.X.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact B.X.hom)
  haveI : IsSeparated (B.X.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated B.X.hom)
  have hR := isZero_higherDirectImage_overField_of_native_H_zero (k := k)
    ((Scheme.Modules.pullback px).obj F) q hH
  obtain ⟨e⟩ := comparison g px B.X.hom square q
  exact hR.of_iso e

/-- The zero model conclusion for the FIRST projection's actual b×B fibre. -/
theorem firstSlice_model_homology_zero
    (hB1 : NativePicZeroVanishing.{u}) (hSquare : L2.NativeTheoremOfTheSquare.{u})
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (B : PkgI3.AbVar k) (M N : B.X.left.Modules) [M.IsInvertible] [N.IsInvertible]
    (hN : TranslationInvariant B (Scheme.Pic.mk N))
    (hnot : ¬ ∃ b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X,
      Scheme.Pic.mk N = L1.translationClass B.X (Scheme.Pic.mk M) b)
    (U : B.X.left.Opens) (P : CochainComplex U.toScheme.Modules ℤ)
    (comparison : UniversalModelComparison (fst B.X B.X).left (mumfordKernelBundle B M N) U P)
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X) (g : Spec (.of k) ⟶ U.toScheme)
    (hg : g ≫ U.ι = b.left) (q : ℕ) :
    IsZero ((((Scheme.Modules.pullback g).mapHomologicalComplex _).obj P).homology q) := by
  apply model_rational_fibre_homology_zero B (fst B.X B.X).left
    (mumfordKernelBundle B M N) U P comparison g (firstSlice B b).left
    (by rw [hg]; exact isPullback_firstSlice B b) q
  exact firstSlice_cohomology_vanish_of_not_in_image B M N hB1 hSquare hN hnot b q

/-- The zero model conclusion for the SECOND projection away from K(M). -/
theorem secondSlice_model_homology_zero_off_stabilizer
    (hB1 : NativePicZeroVanishing.{u}) (hSquare : L2.NativeTheoremOfTheSquare.{u})
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (B : PkgI3.AbVar k) (M N : B.X.left.Modules) [M.IsInvertible] [N.IsInvertible]
    (U : B.X.left.Opens) (P : CochainComplex U.toScheme.Modules ℤ)
    (comparison : UniversalModelComparison (snd B.X B.X).left (mumfordKernelBundle B M N) U P)
    (b : 𝟙_ (Over (Spec (.of k))) ⟶ B.X)
    (hb : b ∉ L1.translationStabilizer B.X (Scheme.Pic.mk M))
    (g : Spec (.of k) ⟶ U.toScheme) (hg : g ≫ U.ι = b.left) (q : ℕ) :
    IsZero ((((Scheme.Modules.pullback g).mapHomologicalComplex _).obj P).homology q) := by
  apply model_rational_fibre_homology_zero B (snd B.X B.X).left
    (mumfordKernelBundle B M N) U P comparison g (secondSlice B b).left
    (by rw [hg]; exact isPullback_secondSlice B b) q
  exact secondSlice_cohomology_vanish_off_stabilizer B M N hB1 hSquare b hb q

end ZInQ.Contrib.CloudR2Poincare.L3

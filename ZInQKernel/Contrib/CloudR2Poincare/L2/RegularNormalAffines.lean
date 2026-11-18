import ZInQKernel.Contrib.CloudR2Poincare.L2.GenericStalkNormal
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Regular
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Genuine all-dimensional normality of smooth scheme affine rings

Use the ALREADY-PUBLISHED W07 regular-scheme supplier, not its unrelated
regular-local-ring normality theorem with dimension≤1. A smooth scheme over
a field is regular, all localizations of a stalk are again scheme stalks,
and W07's actual Auslander–Buchsbaum/UFD proof applies to those stalks at
ALL dimensions. Mathlib gives integrally closedness and its genuine local
criterion transfers this to each nonempty affine open's actual section ring.
No normality, UFD, S2, or finite-birational endpoint Fact is introduced.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- Smoothness over the actual field implies all-dimensional normal stalks,
using the published regular-scheme UFD theorem and Mathlib's integral closure. -/
theorem isIntegrallyClosed_stalk_of_smooth
    {k : Type u} [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [Smooth π] (x : X) : IsIntegrallyClosed (X.presheaf.stalk x) := by
  letI : IsRegular X := IsRegular.of_smooth π
  letI : UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    IsRegular.uniqueFactorizationMonoid_stalk x
  infer_instance

/-- Normality of all ACTUAL scheme stalks implies integral closedness of the
ACTUAL section ring of any nonempty affine open of an integral scheme. -/
theorem isIntegrallyClosed_affineOpen_of_stalks
    {X : Scheme.{u}} [IsIntegral X]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.affineOpens) [Nonempty U.1] : IsIntegrallyClosed Γ(X, U.1) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro P _ hP
  let y : PrimeSpectrum Γ(X, U.1) := ⟨P, hP.isPrime⟩
  have hy : U.2.fromSpec y ∈ U.1 := by
    rw [← SetLike.mem_coe, ← U.2.range_fromSpec]
    exact Set.mem_range_self y
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk (U.2.fromSpec y)) :=
    X.presheaf.algebra_section_stalk ⟨_, hy⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk (U.2.fromSpec y)) P :=
    U.2.isLocalization_stalk' y hy
  letI : IsIntegrallyClosed (X.presheaf.stalk (U.2.fromSpec y)) := hX _
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv P.primeCompl (X.presheaf.stalk (U.2.fromSpec y))
      (Localization.AtPrime P)).toRingEquiv

/-- Every nonempty original affine open of an abelian variety has a genuinely
integrally closed section ring. No characteristic or dimension bound is added. -/
theorem isIntegrallyClosed_affineOpen_abVar
    {k : Type u} [Field k] (J : PkgI3.AbVar k) (U : J.X.left.affineOpens)
    [Nonempty U.1] : IsIntegrallyClosed Γ(J.X.left, U.1) := by
  letI : IsIntegral J.X.left := GeometricallyIntegral.isIntegral_of_subsingleton J.X.hom
  exact isIntegrallyClosed_affineOpen_of_stalks
    (fun x => isIntegrallyClosed_stalk_of_smooth J.X.hom x) U

end ZInQ.Contrib.CloudR2Poincare.L2

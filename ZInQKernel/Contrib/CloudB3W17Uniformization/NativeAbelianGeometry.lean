import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudB3W17Hodge.RelativeDimension
import ZInQKernel.Contrib.CloudB3W17Hodge.Port.Other.AlgebraicGeometry.ComplexPoint.SmoothConnected

/-!
# Native geometric hypotheses for the actual H103 abelian variety

Specializes the genuine Mathlib abelian-variety hypotheses and the immutable
W17 Hodge relative-dimension and smooth-connectedness donor theorems.
No dictionary leaf is assumed. Native points are still the donor's `ComplexPoint`;
conversion to BP's actual `A.Pt ℂ` remains the separate point/evaluation bridge.
-/

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace CloudB3W17Uniformization

set_option autoImplicit false

open PkgI3 (AbVar)

/-- Geometric integrality in the existing AbVar record implies actual scheme integrality. -/
theorem isIntegral_abVar (A : AbVar ℂ) : IsIntegral A.X.left :=
  GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom

/-- The actual product abelian scheme is smooth over the complex base. -/
theorem smooth_abVarProduct (A : AbVar ℂ) : Smooth (A.X ⊗ A.X).hom := by
  rw [Over.tensorObj_hom]
  infer_instance

/-- Native complex points of the actual abelian variety are connected, without a printed leaf. -/
theorem native_connectedSpace_abVar (A : AbVar ℂ) : ConnectedSpace (ComplexPoint A.X) := by
  have : IsIntegral A.X.left := isIntegral_abVar A
  have : QuasiSeparatedSpace A.X.left := quasiSeparatedSpace_of_quasiSeparated A.X.hom
  exact AlgebraicGeometry.ComplexPoint.connectedSpace A.X

/-- The factor and independently charted product have genuine constant relative dimensions. -/
theorem exists_nativeRelativeDimensions (A : AbVar ℂ) :
    ∃ g n : ℕ, SmoothOfRelativeDimension g A.X.hom ∧
      SmoothOfRelativeDimension n (A.X ⊗ A.X).hom := by
  have : IsIntegral A.X.left := isIntegral_abVar A
  have : Smooth (A.X ⊗ A.X).hom := smooth_abVarProduct A
  have : IsLocallyNoetherian A.X.left := LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  have : IsIntegral (A.X ⊗ A.X).left := by
    rw [Over.tensorObj_left]
    infer_instance
  obtain ⟨g, hg⟩ := CloudB3W17Hodge.exists_smoothOfRelativeDimension A.X.hom
  obtain ⟨n, hn⟩ := CloudB3W17Hodge.exists_smoothOfRelativeDimension (A.X ⊗ A.X).hom
  exact ⟨g, n, hg, hn⟩

end CloudB3W17Uniformization

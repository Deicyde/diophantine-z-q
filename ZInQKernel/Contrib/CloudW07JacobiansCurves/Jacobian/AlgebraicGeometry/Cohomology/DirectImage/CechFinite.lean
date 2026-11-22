-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechFinite), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechCohomology
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Proper
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.RingTheory.Finiteness.Semilinear

/-!
# Finite homology of proper Čech complexes

For a coherent module on a scheme proper over a Noetherian ring, the explicit
Čech complex of an affine cover has finite homology over the global functions
of the affine base. Its bounded truncation has the same finite homology.
These are homology finiteness results, not finiteness of the Čech terms.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {baseRing : Type u} [CommRing baseRing] [IsNoetherianRing baseRing]
  {sourceScheme : Scheme.{u}} (baseMap : sourceScheme ⟶ Spec (.of baseRing))
  [IsProper baseMap] (moduleSheaf : sourceScheme.Modules) [moduleSheaf.IsFinitePresentation]
  {coverIndex : Type u} (cover : coverIndex → sourceScheme.Opens)
  (affine : ∀ index, IsAffineOpen (cover index)) (coversTop : iSup cover = ⊤)

include affine coversTop

/-- The actual Čech complex of a coherent sheaf proper over a Noetherian ring
has finite homology over the functions of the base in every integer degree. -/
theorem finite_homology_cechModuleComplex_of_isProper (degree : ℤ) :
    Module.Finite Γ(Spec (.of baseRing), ⊤)
      ((cechModuleComplex baseMap moduleSheaf cover).homology degree) := by
  by_cases negativeDegree : degree < 0
  · have exactAt := (cechModuleComplex baseMap moduleSheaf cover).exactAt_of_isGE
      0 degree negativeDegree
    rw [HomologicalComplex.exactAt_iff_isZero_homology] at exactAt
    letI := ModuleCat.subsingleton_of_isZero exactAt
    infer_instance
  · obtain ⟨naturalDegree, rfl⟩ : ∃ naturalDegree : ℕ, (naturalDegree : ℤ) = degree :=
      ⟨degree.toNat, by omega⟩
    obtain ⟨comparison, scalarCompatible⟩ := exists_homology_cechModuleComplex_equiv_H
      baseMap moduleSheaf cover affine coversTop naturalDegree
    let linearComparison :
        (cechModuleComplex baseMap moduleSheaf cover).homology naturalDegree →ₛₗ[baseMap.appTop.hom]
          moduleSheaf.H naturalDegree :=
      { toFun := comparison
        map_add' := comparison.map_add
        map_smul' := scalarCompatible }
    exact Module.Finite.of_bijective_semilinear linearComparison comparison.bijective
      (Scheme.ΓSpecIso (.of baseRing)).inv.hom
      (hasFiniteH_of_isProper baseMap moduleSheaf naturalDegree)

/-- The bounded Čech model retains finite homology in every degree. -/
theorem finite_homology_cechModuleComplexTrunc_of_isProper [Fintype coverIndex]
    [Nonempty coverIndex] (degree : ℤ) :
    Module.Finite Γ(Spec (.of baseRing), ⊤)
      ((cechModuleComplexTrunc baseMap moduleSheaf cover).homology degree) := by
  let comparison := (cechModuleComplex baseMap moduleSheaf cover).ιTruncLE
    ((Fintype.card coverIndex : ℤ) - 1)
  letI : QuasiIso comparison :=
    quasiIso_ιTruncLE_cechModuleComplex baseMap moduleSheaf cover affine coversTop
  letI := finite_homology_cechModuleComplex_of_isProper baseMap moduleSheaf cover
    affine coversTop degree
  exact Module.Finite.equiv
    (asIso (HomologicalComplex.homologyMap comparison degree)).toLinearEquiv.symm

end AlgebraicGeometry.Scheme.Modules

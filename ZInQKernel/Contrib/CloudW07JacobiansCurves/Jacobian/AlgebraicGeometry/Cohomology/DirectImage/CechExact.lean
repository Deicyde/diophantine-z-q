-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechExact), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Affine.Leray
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-!
# Čech exactness from vanishing higher direct images

Over an affine base, a quasi-coherent sheaf on a quasi-compact separated scheme
has an exact affine-cover Čech complex in every degree where its higher direct
image vanishes.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

section
universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {sourceScheme baseScheme : Scheme.{schemeUniverse}} (projection : sourceScheme ⟶ baseScheme)

/-- **Vanishing higher direct images make Čech complexes exact.** Let `projection : sourceScheme ⟶ baseScheme` be quasi-compact
and separated with `baseScheme` affine, `cover` a cover of `sourceScheme` by affine opens and `moduleSheaf` quasi-coherent. If
`R^degree f_* moduleSheaf = 0`, then the Čech complex of `moduleSheaf` for `cover` is exact in degree `degree`: by Leray's theorem
its cohomology is `H^degree(sourceScheme, moduleSheaf) = Γ(baseScheme, R^degree f_* moduleSheaf)`. -/
theorem exactAt_cechComplex_of_isZero_higherDirectImage [IsAffine baseScheme] [QuasiCompact projection]
    [IsSeparated projection] [HasInjectiveResolutions sourceScheme.Modules] {coverIndex : Type schemeUniverse} (cover : coverIndex → sourceScheme.Opens)
    (hU : ∀ index, IsAffineOpen (cover index)) (hU' : iSup cover = ⊤) (moduleSheaf : sourceScheme.Modules)
    [SheafOfModules.IsQuasicoherent (R := sourceScheme.ringCatSheaf) moduleSheaf] (degree : ℕ)
    (vanishing : IsZero ((higherDirectImage projection degree).obj moduleSheaf)) :
    ((TopCat.Presheaf.cechComplex cover).obj moduleSheaf.presheaf).ExactAt degree := by
  have h₁ : Subsingleton Γ((higherDirectImage projection degree).obj moduleSheaf, ⊤) := ⟨fun firstSection secondSection ↦ by
    have h0 := vanishing.eq_of_src (𝟙 _) 0
    have hx : firstSection = 0 := congr($(congrArg (fun morphism ↦ Hom.app morphism ⊤) h0) firstSection)
    have hy : secondSection = 0 := congr($(congrArg (fun morphism ↦ Hom.app morphism ⊤) h0) secondSection)
    rw [hx, hy]⟩
  obtain ⟨comparison, _⟩ := exists_addEquiv_sections_higherDirectImage_H projection degree
  have h₂ : Subsingleton (moduleSheaf.H degree) := (comparison moduleSheaf).symm.subsingleton
  obtain ⟨e₂⟩ := nonempty_cechComplex_linearEquiv_H_of_isSeparated projection cover hU hU' moduleSheaf degree
  have h₃ : Subsingleton (((cechComplexFunctor cover).obj moduleSheaf.presheafModuleCat).homology degree) :=
    e₂.toEquiv.subsingleton
  have h₄ : Subsingleton (((TopCat.Presheaf.cechComplex cover).obj moduleSheaf.presheaf).homology degree) :=
    (cechComplexHomologyAddEquiv cover moduleSheaf degree).symm.subsingleton
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact AddCommGrpCat.isZero_of_subsingleton _

end AlgebraicGeometry.Scheme.Modules

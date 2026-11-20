import ZInQKernel.Contrib.OneProof.RC.KappaRational2.Periods
import ZInQKernel.Contrib.OneProof.RC.KappaRational.FixedScale
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ModelJacobian
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveAbelian
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.SourceLimit
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.WeierstrassPeriods
import ZInQKernel.Contrib.OneProof.RC.X0Branch.Model

/-! Use the independent Jacobian map of tex 1785–1787 at its own scale,
with no identification of that map with the fixed scale of tex 1825–1828. -/

noncomputable section

open AlgebraicGeometry CategoryTheory PkgI3 UpperHalfPlane WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53.CST
open scoped MatrixGroups

namespace ZInQ.Manuscript.RC.KappaRational2

open J0Cusps PreparedParam

/-- The based composite of an independently supplied Jacobian morphism
provides a rational reference scale if its interior restriction has the
analytic form given by integration of the normalized differential.
The parameter `b` is the scale of that map and is allowed to be complex. -/
theorem reference_scale_of_jacobian_values (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf E Lat)
    (φ : (J0 N).X ⟶ projectiveTarget E) {b : ℂ} (hb : b ≠ 0)
    (hval : ∀ τ : ℍ,
      projectiveValue (E := E) (F := ℂ) (J0Cusps.interior N τ ≫ aj0 N ≫ φ).left = phiAn E f Lat b τ) :
    ∃ r : ℚ, (r : ℂ) = b ∧ IsParamScale N f Lat (r : ℂ) := by
  let X := X0Branch.model N
  let π : source N ⟶ projectiveTarget E := aj0 N ≫ φ
  have hQ : π.left ≫ projectiveOverQ E = X.overQ := Over.w π
  have hm (τ : ℍ) : projectiveValue ((X.complexPoint τ).comp π.left hQ).val =
      phiAn E f Lat b τ := by
    change projectiveValue (E := E) (F := ℂ) (J0Cusps.interior N τ ≫ aj0 N ≫ φ).left = _
    exact hval τ
  obtain ⟨r, hr⟩ := KappaRational.rational_of_projective_values_on_tail
    E X f hf hLat hb π.left hQ 0 (fun τ _ => hm τ)
  refine ⟨r, hr, ?_⟩
  rw [hr]
  refine ⟨hb, fun γ hγ τ => ?_⟩
  have hγτ : J0Cusps.interior N (γ • τ) = J0Cusps.interior N τ :=
    Over.OverMorphism.ext (X0Model2.complexPoint_smul N γ hγ τ)
  have he : phiAn E f Lat b (γ • τ) = phiAn E f Lat b τ := by
    rw [← hval (γ • τ), ← hval τ, hγτ]
  let p := QuotientAddGroup.mk' Lat.lattice.toAddSubgroup
  have hp : p (b * eichlerPotential f (γ • τ)) = p (b * eichlerPotential f τ) := by
    apply (weierstrassPeriodEquiv E Lat hLat).injective
    simpa only [p, weierstrassPeriodEquiv_mk, phiAn] using he
  have hp0 : p (b * (eichlerPotential f (γ • τ) - eichlerPotential f τ)) = 0 := by
    rw [mul_sub, map_sub, hp, sub_self]
  exact (QuotientAddGroup.eq_zero_iff _).mp hp0

/-- Rationality of the original scale from the independent based composite
and its analytic comparison at any nonzero (b). -/
theorem rational_of_jacobian_values (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf E Lat) (hNC : IsNonCMLattice Lat)
    {κ : ℂ} (hκ : IsParamScale N f Lat κ)
    (φ : (J0 N).X ⟶ projectiveTarget E) {b : ℂ} (hb : b ≠ 0)
    (hval : ∀ τ : ℍ,
      projectiveValue (E := E) (F := ℂ) (J0Cusps.interior N τ ≫ aj0 N ≫ φ).left = phiAn E f Lat b τ) :
    ∃ c : ℚ, (c : ℂ) = κ := by
  obtain ⟨r, _, hr⟩ := reference_scale_of_jacobian_values E f hf hLat φ hb hval
  exact rational_of_matching_coeffs E f hf hNC hκ ⟨r, hr⟩

end ZInQ.Manuscript.RC.KappaRational2

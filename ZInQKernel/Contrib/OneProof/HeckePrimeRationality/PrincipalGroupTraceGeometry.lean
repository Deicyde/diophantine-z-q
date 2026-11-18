import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ActualPrincipalMultiplication
import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
import Mathlib.NumberTheory.ModularForms.Cusps

/-!
# Numerical geometry of actual principal groups

The determinant strengthens the entry congruences to trace congruence modulo
N squared. For N at least three this excludes elliptic traces and trace minus
two. These are actual matrix/group prerequisites, not a construction of a
compact modular curve or its Hodge line bundle.
-/

noncomputable section
set_option autoImplicit false
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.PrincipalGroupGeometry
open PrincipalMultiplication

/-- The determinant forces trace minus two to be divisible by the square of the level. -/
theorem trace_sq_level_dvd (N : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma N) :
    (N : ℤ)^2 ∣ Matrix.trace γ.1 - 2 := by
  obtain ⟨h00,h01,h10,h11⟩ := CongruenceSubgroup.Gamma_mem.mp hγ
  have hd00 : (N : ℤ) ∣ γ 0 0 - 1 := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    simpa using h00.symm
  have hd11 : (N : ℤ) ∣ γ 1 1 - 1 := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    simpa using h11.symm
  obtain ⟨a,ha⟩ := hd00
  obtain ⟨d,hd⟩ := hd11
  obtain ⟨b,hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h01
  obtain ⟨c,hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  have haa : γ 0 0 = 1 + (N : ℤ)*a := by omega
  have hdd : γ 1 1 = 1 + (N : ℤ)*d := by omega
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.property
  rw [haa,hdd,hb,hc] at hdet
  refine ⟨b*c-a*d, ?_⟩
  simp only [Matrix.trace_fin_two]
  rw [haa,hdd]
  linear_combination hdet

/-- The only trace in [-2,2] at principal level at least three is two. -/
theorem small_trace_eq_two (N : ℕ) (hN : 3 ≤ N) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) (ht : |Matrix.trace γ.1| ≤ 2) :
    Matrix.trace γ.1 = 2 := by
  obtain ⟨m,hm⟩ := trace_sq_level_dvd N γ hγ
  have hn : (3 : ℤ) ≤ N := by exact_mod_cast hN
  have hn9 : (9 : ℤ) ≤ (N : ℤ)^2 := by nlinarith
  obtain ⟨htlo,hthi⟩ := abs_le.mp ht
  have hm0 : m = 0 := by
    by_contra h
    have hc : m ≤ -1 ∨ 1 ≤ m := by omega
    rcases hc with hc | hc
    · have hprod := mul_le_mul_of_nonneg_left hc (sq_nonneg (N : ℤ))
      nlinarith
    · have hprod := mul_le_mul_of_nonneg_left hc (sq_nonneg (N : ℤ))
      nlinarith
  rw [hm0,mul_zero] at hm
  omega

theorem trace_ne_neg_two (N : ℕ) (hN : 3 ≤ N) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) : Matrix.trace γ.1 ≠ -2 := by
  intro he
  have ht := small_trace_eq_two N hN γ hγ (by rw [he]; norm_num)
  omega

@[simp] theorem mapped_trace (γ : SL(2, ℤ)) :
    Matrix.trace (mapGL ℝ γ).val = ((Matrix.trace γ.1 : ℤ) : ℝ) := by
  simp [Matrix.trace_fin_two, mapGL_coe_matrix, map_apply_coe]

@[simp] theorem mapped_det (γ : SL(2, ℤ)) : (mapGL ℝ γ).val.det = 1 := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using γ.property
  rw [Matrix.det_fin_two, mapGL_coe_matrix]
  change ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) -
    ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) = 1
  exact_mod_cast hdet

/-- No mapped principal matrix at level at least three is elliptic. -/
theorem not_isElliptic (N : ℕ) (hN : 3 ≤ N) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) : ¬ (mapGL ℝ γ).IsElliptic := by
  intro hell
  change (mapGL ℝ γ).val.discr < 0 at hell
  rw [Matrix.discr_fin_two, mapped_trace, mapped_det] at hell
  have ht : |Matrix.trace γ.1| ≤ 2 := by
    have hreal : |((Matrix.trace γ.1 : ℤ) : ℝ)| ≤ 2 := by
      apply abs_le.mpr
      constructor
      · nlinarith [sq_nonneg (((Matrix.trace γ.1 : ℤ) : ℝ) + 2)]
      · nlinarith [sq_nonneg (((Matrix.trace γ.1 : ℤ) : ℝ) - 2)]
    exact_mod_cast hreal
  have he := small_trace_eq_two N hN γ hγ ht
  rw [he] at hell
  norm_num at hell

/-- The actual mapped subgroup has no element of trace minus two. -/
theorem principal_trace_ne_neg_two (N : ℕ) (hN : 3 ≤ N)
    (g : GL (Fin 2) ℝ) (hg : g ∈ principalGroup N) : Matrix.trace g.val ≠ -2 := by
  obtain ⟨γ,hγ,rfl⟩ := hg
  rw [mapped_trace]
  exact_mod_cast trace_ne_neg_two N hN γ hγ

/-- A scalar mapped principal element at level at least three is the identity. -/
theorem mapped_center_eq_one (N : ℕ) (hN : 3 ≤ N) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) (hc : mapGL ℝ γ ∈ Subgroup.center _) :
    mapGL ℝ γ = 1 := by
  obtain ⟨r,hr⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hc
  have hdet := mapped_det γ
  rw [← hr] at hdet
  have hr2 : r^2 = 1 := by simpa [Matrix.det_fin_two, Matrix.scalar_apply, pow_two] using hdet
  rcases sq_eq_one_iff.mp hr2 with hr1 | hr1
  · apply Units.ext
    rw [← hr,hr1]
    simp
  · have htrace : Matrix.trace (mapGL ℝ γ).val = -2 := by
      rw [← hr,hr1]
      simp [Matrix.trace_fin_two, Matrix.scalar_apply]
    exact False.elim (principal_trace_ne_neg_two N hN _ ⟨γ,hγ,rfl⟩ htrace)

/-- The actual principal group acts without nonidentity fixed points in the upper half-plane. -/
theorem principal_fixed_point_eq_one (N : ℕ) (hN : 3 ≤ N)
    (g : GL (Fin 2) ℝ) (hg : g ∈ principalGroup N) (τ : ℍ) (hfix : g • τ = τ) : g = 1 := by
  obtain ⟨γ,hγ,rfl⟩ := hg
  apply mapped_center_eq_one N hN γ hγ
  by_contra hc
  have hp : 0 < (mapGL ℝ γ).val.det := by rw [mapped_det]; norm_num
  have hell := UpperHalfPlane.isElliptic_of_exists_smul_eq_self hp hc ⟨τ,hfix⟩
  exact not_isElliptic N hN γ hγ hell

/-- Excluding trace minus two gives equality of actual strict periods and periods. -/
theorem regularAtInfty_of_no_negative_trace (G : Subgroup (GL (Fin 2) ℝ))
    (hG : ∀ g ∈ G, Matrix.trace g.val ≠ -2) : G.IsRegularAtInfty := by
  change G.strictPeriods = G.periods
  apply le_antisymm G.strictPeriods_le_periods
  intro x hx
  rw [Subgroup.periods, Subgroup.mem_strictPeriods_iff, Subgroup.mem_adjoinNegOne_iff] at hx
  rw [Subgroup.mem_strictPeriods_iff]
  rcases hx with hx | hx
  · exact hx
  · exact False.elim (hG _ hx (by norm_num [Matrix.trace_fin_two, GeneralLinearGroup.upperRightHom]))

/-- Regularity at infinity is proved for the genuine mapped principal group. -/
theorem principal_regular_at_infty (N : ℕ) (hN : 3 ≤ N) :
    (principalGroup N).IsRegularAtInfty :=
  regularAtInfty_of_no_negative_trace _ (principal_trace_ne_neg_two N hN)

/-- Every real conjugate has equal strict periods and periods, the regular-cusp prerequisite. -/
theorem principal_conjugate_regular_at_infty (N : ℕ) (hN : 3 ≤ N) (δ : GL (Fin 2) ℝ) :
    (ConjAct.toConjAct δ • principalGroup N).IsRegularAtInfty := by
  apply regularAtInfty_of_no_negative_trace
  intro g hg
  obtain ⟨h,hh,rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists g (ConjAct.toConjAct δ)
    (principalGroup N)).mp hg
  have ht : Matrix.trace (ConjAct.toConjAct δ • h).val = Matrix.trace h.val := by
    change Matrix.trace (δ.val * h.val * (δ⁻¹).val) = Matrix.trace h.val
    exact Matrix.trace_units_conj δ h.val
  rw [ht]
  exact principal_trace_ne_neg_two N hN h hh

end ZInQ.Contrib.HeckePrimeRationality.PrincipalGroupGeometry

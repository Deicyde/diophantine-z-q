import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Actual primitive Eisenstein constant-term limits

A genuine positive vertical ray is dominated by the established summable
inverse-power vector majorant. Tannery derives the limit of the unchanged
gcd-one series from its individual vector limits. The modular-form
q-expansion limit identifies that limit with its actual constant coefficient.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open Complex Filter Set UpperHalfPlane EisensteinSeries Matrix.SpecialLinearGroup
open scoped Topology MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinConstants

/-- A genuine upper-half-plane vertical ray, defined at every real parameter. -/
def ray (y : ℝ) : ℍ := ⟨⟨0,max y 2⟩,lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right _ _)⟩

lemma ray_tendsto : Tendsto ray atTop UpperHalfPlane.atImInfty := by
  rw [UpperHalfPlane.atImInfty,tendsto_comap_iff]
  exact tendsto_atTop_mono (fun y : ℝ => le_max_left y 2) tendsto_id

lemma ray_mem_verticalStrip (y : ℝ) : ray y ∈ UpperHalfPlane.verticalStrip 1 2 := by
  exact ⟨by norm_num [ray],le_max_right _ _⟩

/-- The actual primitive-series summand, extended by zero only outside its gamma set. -/
def rowSummand (N : ℕ) (a : Fin 2 → ZMod N) (k : ℕ) (y : ℝ) (v : Fin 2 → ℤ) : ℂ :=
  if v ∈ EisensteinSeries.gammaSet N 1 a then EisensteinSeries.eisSummand (k : ℤ) v (ray y) else 0

/-- The actual pointwise vertical limit, before the gcd-one finite reduction. -/
def rowLimit (N : ℕ) (a : Fin 2 → ZMod N) (k : ℕ) (v : Fin 2 → ℤ) : ℂ :=
  if v ∈ EisensteinSeries.gammaSet N 1 a then
    if v 0 = 0 then (v 1 : ℂ)^(-(k : ℤ)) else 0 else 0

lemma nonzero_first_coordinate_limit (k : ℕ) (hk : 3 ≤ k) (v : Fin 2 → ℤ) (hv : v 0 ≠ 0) :
    Tendsto (fun y : ℝ => EisensteinSeries.eisSummand (k : ℤ) v (ray y)) atTop (𝓝 0) := by
  have hc : (1 : ℝ) ≤ |(v 0 : ℝ)| := by exact_mod_cast Int.one_le_abs hv
  have hbound (y : ℝ) : y ≤ ‖(v 0 : ℂ)*(ray y : ℂ)+(v 1 : ℂ)‖ := by
    have him : ((v 0 : ℂ)*(ray y : ℂ)+(v 1 : ℂ)).im = (v 0 : ℝ)*max y 2 := by simp [ray]
    have hy : 0 ≤ max y (2 : ℝ) := le_trans (by norm_num) (le_max_right _ _)
    calc y ≤ max y 2 := le_max_left _ _
      _ ≤ |(v 0 : ℝ)| * max y 2 := le_mul_of_one_le_left hy hc
      _ = |((v 0 : ℂ)*(ray y : ℂ)+(v 1 : ℂ)).im| := by rw [him,abs_mul,abs_of_nonneg hy]
      _ ≤ _ := Complex.abs_im_le_norm _
  have hn : Tendsto (fun y : ℝ => ‖(v 0 : ℂ)*(ray y : ℂ)+(v 1 : ℂ)‖) atTop atTop :=
    tendsto_atTop_mono hbound tendsto_id
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [EisensteinSeries.eisSummand,norm_zpow]
  exact (tendsto_pow_neg_atTop (by omega : k ≠ 0)).comp hn

lemma rowSummand_tendsto (N : ℕ) (a : Fin 2 → ZMod N) (k : ℕ) (hk : 3 ≤ k) (v : Fin 2 → ℤ) :
    Tendsto (fun y => rowSummand N a k y v) atTop (𝓝 (rowLimit N a k v)) := by
  classical
  by_cases hγ : v ∈ EisensteinSeries.gammaSet N 1 a
  · by_cases hv : v 0 = 0
    · simp only [rowSummand,rowLimit,ite_eq_left hγ,ite_eq_left hv,EisensteinSeries.eisSummand,
        hv,Int.cast_zero,zero_mul,zero_add]
      exact tendsto_const_nhds
    · simp only [rowSummand,rowLimit,ite_eq_left hγ,ite_eq_right hv]
      exact nonzero_first_coordinate_limit k hk v hv
  · simp only [rowSummand,rowLimit,ite_eq_right hγ]
    exact tendsto_const_nhds

/-- An actual summable majorant independent of the vertical parameter and residue row. -/
def vectorMajorant (k : ℕ) (v : Fin 2 → ℤ) : ℝ :=
  EisensteinSeries.r ⟨⟨1,2⟩,by norm_num⟩ ^ (-(k : ℝ)) * ‖v‖ ^ (-(k : ℝ))

lemma vectorMajorant_summable (k : ℕ) (hk : 3 ≤ k) : Summable (vectorMajorant k) := by
  exact (EisensteinSeries.summable_one_div_norm_rpow (by exact_mod_cast (by omega : 2 < k))).mul_left _

lemma rowSummand_bound (N : ℕ) (a : Fin 2 → ZMod N) (k : ℕ) (hk : 3 ≤ k) (y : ℝ) (v : Fin 2 → ℤ) :
    ‖rowSummand N a k y v‖ ≤ vectorMajorant k v := by
  classical
  by_cases hγ : v ∈ EisensteinSeries.gammaSet N 1 a
  · simp only [rowSummand,ite_eq_left hγ,EisensteinSeries.eisSummand,norm_zpow,vectorMajorant]
    simpa only [← Real.rpow_intCast,Int.cast_neg,Int.cast_natCast] using
      EisensteinSeries.summand_bound_of_mem_verticalStrip (by positivity : (0 : ℝ) ≤ k)
        v (by norm_num : (0 : ℝ) < 2) (ray_mem_verticalStrip y)
  · simp only [rowSummand,ite_eq_right hγ,norm_zero,vectorMajorant]
    exact mul_nonneg (Real.rpow_nonneg (EisensteinSeries.r_pos _).le _) (Real.rpow_nonneg (norm_nonneg _) _)

/-- The actual gamma-set series is precisely the extended summand sum. -/
lemma series_eq_extended (N : ℕ) (a : Fin 2 → ZMod N) (k : ℕ) (y : ℝ) :
    eisensteinSeries a (k : ℤ) (ray y) = ∑' v : Fin 2 → ℤ, rowSummand N a k y v := by
  classical
  rw [eisensteinSeries]
  exact tsum_subtype (EisensteinSeries.gammaSet N 1 a)
    (fun v : Fin 2 → ℤ => EisensteinSeries.eisSummand (k : ℤ) v (ray y))

/-- Tannery's hypotheses are derived from actual summands and the actual
summable vector majorant, not supplied as wanted input. -/
theorem actual_series_vertical_limit (N : ℕ) (a : Fin 2 → ZMod N) (k : ℕ) (hk : 3 ≤ k) :
    Tendsto (fun y => eisensteinSeries a (k : ℤ) (ray y)) atTop
      (𝓝 (∑' v : Fin 2 → ℤ, rowLimit N a k v)) := by
  have he := tendsto_tsum_of_dominated_convergence (vectorMajorant_summable k hk)
    (rowSummand_tendsto N a k hk) (Filter.Eventually.of_forall (rowSummand_bound N a k hk))
  simpa only [← series_eq_extended] using he

lemma level_period (N : ℕ) :
    (N : ℝ) ∈ ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)).strictPeriods := by
  simp only [CongruenceSubgroup.strictPeriods_Gamma]
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨1,by simp⟩

/-- The actual primitive modular-form coefficient is the independently proved
vertical limit sum. -/
theorem primitive_coefficient_zero_eq_limit_sum (N : ℕ) [NeZero N]
    (k : ℕ) (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    (UpperHalfPlane.qExpansion (N : ℝ)
      (ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) a)).coeff 0 =
      ∑' v : Fin 2 → ℤ, rowLimit N a k v := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hc := (ModularFormClass.tendsto_atImInfty
    (ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) a) hN (level_period N)).comp ray_tendsto
  exact tendsto_nhds_unique hc (actual_series_vertical_limit N a k hk)

end ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinConstants

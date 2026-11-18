import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitivePeterssonSeedBounds

/-!
# An absolutely integrable zero cuspidal strip seed

Integrability of the genuine unfolding seed over the whole positive strip is
proved from actual cusp bounds. Fubini is then applied with that integrability
proof, so the vanishing does not use the default value of a nonintegrable
Bochner integral.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set UpperHalfPlane Complex
open scoped Topology MatrixGroups ModularForm ComplexConjugate

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson

lemma vertical_majorant_integrable (h : ℝ) {S : Set ℝ} {g : ℝ → ℝ} (hg : IntegrableOn g S) :
    IntegrableOn (fun p : ℝ × ℝ => g p.2) (Icc 0 h ×ˢ S) := by
  have hx : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc 0 h) := continuous_const.integrableOn_Icc
  have hp := hx.mul_prod hg
  simpa only [one_mul,Measure.prod_restrict,← Measure.volume_eq_prod,IntegrableOn] using hp

/-- The genuine cuspidal unfolding seed is absolutely integrable over the full
positive strip, for every k≥3 and actual arithmetic-level cusp form. -/
theorem planeSeed_integrable_strip {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (k : ℕ) (hk : 3 ≤ k) (f : CuspForm Γ (k : ℤ))
    (h : ℝ) (hh : 0 < h) (hp : h ∈ Γ.strictPeriods) :
    IntegrableOn (planeSeed k f) (Icc 0 h ×ˢ Ioi 0) := by
  obtain ⟨C,hC,hbound⟩ := seed_global_bound k hk f
  obtain ⟨D,Y,hD,hY,hexp⟩ := cusp_uniform_exp_bound f h hh hp
  have hMeas (S : Set ℝ) (hS : MeasurableSet S) (hpos : S ⊆ Ioi 0) :
      AEStronglyMeasurable (planeSeed k f) (volume.restrict (Icc 0 h ×ˢ S)) :=
    ((planeSeed_continuousOn k f).mono (by intro p hp; exact hpos hp.2)).aestronglyMeasurable
      (measurableSet_Icc.prod hS)
  have hpow : IntegrableOn (fun y : ℝ => C*y^((k : ℝ)/2-2)) (Ioc 0 Y) := by
    have hi : IntegrableOn (fun y : ℝ => y^((k : ℝ)/2-2)) (Ioo 0 Y) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hY).mpr (seed_exponent_gt_neg_one k hk)
    have hh : IntegrableOn (fun y : ℝ => y^((k : ℝ)/2-2)) (Ioc 0 Y) :=
      (integrableOn_Ioc_iff_integrableOn_Ioo).mpr hi
    exact hh.const_mul C
  have hLow : IntegrableOn (planeSeed k f) (Icc 0 h ×ˢ Ioc 0 Y) := by
    apply (vertical_majorant_integrable h hpow).mono' (hMeas (Ioc 0 Y) measurableSet_Ioc Ioc_subset_Ioi_self)
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Ioc)] with p hp
    exact hbound p.1 p.2 hp.2.1
  have ha : 0 < 2*Real.pi/h := div_pos (mul_pos (by norm_num) Real.pi_pos) hh
  have htail := seed_tail_majorant_integrable k (2*Real.pi/h) Y D ha
  have hHigh : IntegrableOn (planeSeed k f) (Icc 0 h ×ˢ Ioi Y) := by
    apply (vertical_majorant_integrable h htail).mono'
      (hMeas (Ioi Y) measurableSet_Ioi (Ioi_subset_Ioi hY.le))
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Ioi)] with p hp
    have hy : 0 < p.2 := hY.trans hp.2
    let τ : ℍ := ⟨(p.1 : ℂ)+p.2*Complex.I,by simpa using hy⟩
    have hb := hexp τ (by simpa [τ] using hp.2.le)
    have he : τ.im = p.2 := by simp [τ]
    rw [he] at hb
    change ‖horizontal f p.2 hy p.1‖ ≤ D*Real.exp (-(2*Real.pi/h)*p.2) at hb
    rw [seed_at_positive k f p.1 p.2 hy,norm_mul,norm_conj,norm_pow,Complex.norm_of_nonneg hy.le]
    exact mul_le_mul_of_nonneg_right hb (by positivity)
  have hu : Icc 0 h ×ˢ Ioi (0 : ℝ) = (Icc 0 h ×ˢ Ioc 0 Y) ∪ (Icc 0 h ×ˢ Ioi Y) := by
    ext p
    simp only [mem_prod,mem_Ioi,mem_Ioc,mem_union]
    constructor
    · rintro ⟨hx,hy⟩
      rcases le_or_gt p.2 Y with hp | hp
      · exact Or.inl ⟨hx,hy,hp⟩
      · exact Or.inr ⟨hx,hp⟩
    · rintro (⟨hx,hy,_⟩ | ⟨hx,hy⟩)
      · exact ⟨hx,hy⟩
      · exact ⟨hx,hY.trans hy⟩
  rw [hu]
  exact hLow.union hHigh

/-- The actual whole-strip seed integral is zero by proved integrability and
actual cuspidal horizontal constant-term vanishing. -/
theorem planeSeed_strip_integral_zero {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (k : ℕ) (hk : 3 ≤ k) (f : CuspForm Γ (k : ℤ))
    (h : ℝ) (hh : 0 < h) (hp : h ∈ Γ.strictPeriods) :
    ∫ p in Icc 0 h ×ˢ Ioi (0 : ℝ), planeSeed k f p = 0 := by
  have hi := planeSeed_integrable_strip k hk f h hh hp
  have hprod : Integrable (planeSeed k f) ((volume.restrict (Icc 0 h)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    simpa only [Measure.prod_restrict,← Measure.volume_eq_prod,IntegrableOn] using hi
  rw [Measure.volume_eq_prod,← Measure.prod_restrict,integral_prod_symm _ hprod]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro y hy
  change 0 < y at hy
  have hline : (fun x : ℝ => planeSeed k f (x,y)) =
      (fun x => conj (horizontal f y hy x)*(y : ℂ)^(k-2)) := funext fun x => seed_at_positive k f x y hy
  rw [hline,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hh.le]
  have he : ((k-2 : ℕ) : ℤ) = (k : ℤ)-2 := by omega
  rw [← _root_.zpow_natCast]
  rw [he]
  exact horizontal_weighted_mean_zero f h hh hp y hy

end ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson

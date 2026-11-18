import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitivePeterssonHorizontal
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Absolute integrability of the actual cuspidal unfolding seed

The seed in Lebesgue strip coordinates is conjugate(f(x+iy)) y^(k-2).
At y→0 the genuine global cusp bound gives y^(k/2-2), integrable for k>2;
at y→∞ the actual cusp q-expansion gives exponential decay. These bounds are
derived from actual cusp forms, not taken as unfolding or orthogonality inputs.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter Asymptotics UpperHalfPlane Complex
open scoped Topology MatrixGroups ModularForm ComplexConjugate

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson

/-- The actual cuspidal strip seed after absorbing dx dy / y². -/
def planeSeed {Γ : Subgroup (GL (Fin 2) ℝ)} (k : ℕ) (f : CuspForm Γ (k : ℤ))
    (p : ℝ × ℝ) : ℂ :=
  conj (f (UpperHalfPlane.ofComplex ((p.1 : ℂ) + p.2 * Complex.I))) * (p.2 : ℂ) ^ (k-2)

lemma seed_at_positive {Γ : Subgroup (GL (Fin 2) ℝ)} (k : ℕ) (f : CuspForm Γ (k : ℤ))
    (x y : ℝ) (hy : 0 < y) :
    planeSeed k f (x,y) = conj (horizontal f y hy x) * (y : ℂ)^(k-2) := by
  rw [planeSeed,UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]
  rfl

/-- Genuine continuity on the positive-height coordinate domain. -/
theorem planeSeed_continuousOn {Γ : Subgroup (GL (Fin 2) ℝ)} (k : ℕ) (f : CuspForm Γ (k : ℤ)) :
    ContinuousOn (planeSeed k f) {p : ℝ × ℝ | 0 < p.2} := by
  intro p hp
  have hz : 0 < ((p.1 : ℂ)+p.2*Complex.I).im := by simpa using hp
  have hc : ContinuousAt (fun q : ℝ × ℝ => (q.1 : ℂ)+q.2*Complex.I) p := by fun_prop
  have hu : ContinuousAt (fun q : ℝ × ℝ => UpperHalfPlane.ofComplex ((q.1 : ℂ)+q.2*Complex.I)) p :=
    ContinuousAt.comp' (g := UpperHalfPlane.ofComplex)
      (f := fun q : ℝ × ℝ => (q.1 : ℂ)+q.2*Complex.I)
      (UpperHalfPlane.contMDiffAt_ofComplex (n := 1) hz).continuousAt hc
  have hf : ContinuousAt (fun q : ℝ × ℝ => f (UpperHalfPlane.ofComplex ((q.1 : ℂ)+q.2*Complex.I))) p :=
    ContinuousAt.comp' (g := fun τ : ℍ => f τ)
      (f := fun q : ℝ × ℝ => UpperHalfPlane.ofComplex ((q.1 : ℂ)+q.2*Complex.I))
      (ModularFormClass.continuous f).continuousAt hu
  have hs : ContinuousAt (fun q : ℝ × ℝ => conj (f (UpperHalfPlane.ofComplex ((q.1 : ℂ)+q.2*Complex.I)))) p :=
    Complex.continuous_conj.continuousAt.comp' hf
  have hw : ContinuousAt (fun q : ℝ × ℝ => (q.2 : ℂ)^(k-2)) p := by fun_prop
  exact (hs.mul hw).continuousWithinAt

/-- The real exponent at zero is strictly greater than minus one. -/
theorem seed_exponent_gt_neg_one (k : ℕ) (hk : 3 ≤ k) : -1 < (k : ℝ)/2-2 := by
  have hr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- Actual global cusp bound supplies an absolute low-height majorant. -/
theorem seed_global_bound {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (k : ℕ) (hk : 3 ≤ k) (f : CuspForm Γ (k : ℤ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, 0 < y → ‖planeSeed k f (x,y)‖ ≤ C * y^((k : ℝ)/2-2) := by
  obtain ⟨C,hC⟩ := CuspFormClass.exists_bound f
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro x y hy
  let τ : ℍ := ⟨(x : ℂ)+y*Complex.I,by simpa using hy⟩
  have he : τ.im = y := by simp [τ]
  have hb := hC τ
  rw [he] at hb
  rw [seed_at_positive k f x y hy,norm_mul,norm_conj,norm_pow,Complex.norm_of_nonneg hy.le]
  have hc : ‖horizontal f y hy x‖ ≤ max C 0 / y^((k : ℤ)/2 : ℝ) :=
    hb.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  have hpow : (max C 0 / y^((k : ℤ)/2 : ℝ)) * y^(k-2) =
      max C 0 * y^((k : ℝ)/2-2) := by
    rw [← Real.rpow_natCast,div_eq_mul_inv,← Real.rpow_neg hy.le,mul_assoc,← Real.rpow_add hy]
    congr 1
    have he : ((k-2 : ℕ) : ℝ) = (k : ℝ)-2 := by
      have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.sub_add_cancel (by omega : 2 ≤ k))
      push_cast at h
      linarith
    push_cast
    rw [he]
    ring
  calc ‖horizontal f y hy x‖ * y^(k-2) ≤ (max C 0 / y^((k : ℤ)/2 : ℝ)) * y^(k-2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := hpow

/-- The actual q-expansion cusp decay gives a height-uniform exponential bound. -/
theorem cusp_uniform_exp_bound {Γ : Subgroup (GL (Fin 2) ℝ)} {w : ℤ}
    (f : CuspForm Γ w) (h : ℝ) (hh : 0 < h) (hp : h ∈ Γ.strictPeriods) :
    ∃ C Y : ℝ, 0 < C ∧ 0 < Y ∧ ∀ τ : ℍ, Y ≤ τ.im →
      ‖f τ‖ ≤ C * Real.exp (-(2*Real.pi/h)*τ.im) := by
  obtain ⟨C,hC,hb⟩ := (CuspFormClass.exp_decay_atImInfty f hh hp).exists_pos
  rw [IsBigOWith,UpperHalfPlane.atImInfty,eventually_comap,eventually_atTop] at hb
  obtain ⟨Y,hY⟩ := hb
  refine ⟨C,max 1 Y,hC,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro τ hτ
  have hb := hY τ.im ((le_max_right _ _).trans hτ) τ rfl
  have he : -2*Real.pi*τ.im/h = -(2*Real.pi/h)*τ.im := by ring
  simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),he] using hb

/-- Exponential decay times the genuine polynomial seed weight is integrable at infinity. -/
theorem seed_tail_majorant_integrable (k : ℕ) (a Y C : ℝ) (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => C*Real.exp (-a*y)*y^(k-2)) (Ioi Y) := by
  have hO : (fun y : ℝ => Real.exp (-a*y)*y^((k-2 : ℕ) : ℝ)) =O[atTop]
      (fun y : ℝ => Real.exp (-(a/2)*y)) := by
    exact (isLittleO_exp_mul_rpow_of_lt (k-2 : ℕ) (by linarith : -a < -(a/2))).isBigO
  have hi := integrable_of_isBigO_exp_neg (by linarith : 0 < a/2)
    (by fun_prop : ContinuousOn (fun y : ℝ => Real.exp (-a*y)*y^(k-2)) (Ici Y))
    (by simpa only [Real.rpow_natCast] using hO)
  change Integrable (fun y : ℝ => C*Real.exp (-a*y)*y^(k-2)) (volume.restrict (Ioi Y))
  simpa only [mul_assoc] using hi.const_mul C

end ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson

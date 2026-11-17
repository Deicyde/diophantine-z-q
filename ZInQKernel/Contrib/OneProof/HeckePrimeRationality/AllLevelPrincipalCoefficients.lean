import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCoefficients
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Principal-level coefficients of the full torsion family

For normalized first coordinates, the two paired theta branches have
nonnegative exponents in the period-N parameter. Their contributions are
added even when the two exponent images overlap. Local analytic division
then identifies the coefficients of the original torsion function.
-/

noncomputable section

open Complex UpperHalfPlane Filter
open scoped Topology

namespace ZInQ.Contrib.HeckePrimeRationality.AllLevelPrincipalCoefficients

open ZInQ.Contrib.HeckePrimeRationality.Torsion
open ZInQ.Contrib.HeckePrimeRationality.ThetaFiveTorsionCoefficients
  (tri two_mul_tri le_tri triangularCoeff)

/-- Positive theta branch after multiplying by the cusp parameter to the first coordinate. -/
def ep (N a j : ℕ) : ℕ := N * tri j + a * (j + 1)

/-- Negative theta branch after the same multiplication. -/
def em (N a j : ℕ) : ℕ := N * tri j - a * j

lemma em_sub_bound {N a : ℕ} (ha : a < N) (j : ℕ) : a * j ≤ N * tri j := by
  nlinarith [le_tri j]

lemma tri_succ (j : ℕ) : tri (j + 1) = tri j + j + 1 := by
  have h := two_mul_tri j
  have h' := two_mul_tri (j + 1)
  nlinarith

lemma ep_strict {N a : ℕ} (hN : 0 < N) : StrictMono (ep N a) := by
  apply strictMono_nat_of_lt_succ
  intro j
  dsimp [ep]
  rw [tri_succ]
  nlinarith

lemma em_strict {N a : ℕ} (ha : a < N) : StrictMono (em N a) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have hb := em_sub_bound ha j
  have hb' := em_sub_bound ha (j + 1)
  have hsub : em N a j + a * j = N * tri j := by dsimp [em]; omega
  have hsub' : em N a (j + 1) + a * (j + 1) = N * tri (j + 1) := by dsimp [em]; omega
  have hstep : N * tri (j + 1) = N * tri j + N * (j + 1) := by rw [tri_succ]; ring
  nlinarith

lemma le_ep {N a : ℕ} (hN : 0 < N) (j : ℕ) : j ≤ ep N a j := by
  dsimp [ep]
  nlinarith [le_tri j]

lemma le_em {N a : ℕ} (ha : a < N) (j : ℕ) : j ≤ em N a j := by
  have hle := Nat.mul_le_mul_left N (le_tri j)
  have hb := em_sub_bound ha j
  have hsub : em N a j + a * j = N * tri j := by dsimp [em]; omega
  nlinarith

section Sparse
variable {K : Type*} [Field K]

/-- Sparse coefficients along one exponent branch, extended by zero. -/
def sparse (e : ℕ → ℕ) (c : ℕ → K) (m : ℕ) : K := by
  classical
  exact if h : ∃ j, e j = m then c h.choose else 0

lemma sparse_at (e : ℕ → ℕ) (he : Function.Injective e) (c : ℕ → K) (j : ℕ) :
    sparse e c (e j) = c j := by
  rw [sparse, dite_eq_left ⟨j, rfl⟩]
  congr 1
  exact he (Exists.choose_spec (⟨j, rfl⟩ : ∃ i, e i = e j))

lemma sparse_off (e : ℕ → ℕ) (c : ℕ → K) (m : ℕ) (h : m ∉ Set.range e) :
    sparse e c m = 0 := by
  have h' : ¬ ∃ j, e j = m := h
  rw [sparse, dite_eq_right h']

def cp (v : K) (j : ℕ) : K := (-1) ^ j * v ^ j

def cm (v : K) (j : ℕ) : K := -(-1) ^ j * (v ^ (j + 1))⁻¹

def dp (v : K) (j : ℕ) : K := (j : K) * cp v j

def dm (v : K) (j : ℕ) : K := (j + 1 : K) * (-1) ^ j * (v ^ (j + 1))⁻¹

/-- The denominator coefficients add the two branches, including overlaps. -/
def P (N a : ℕ) (v : K) : PowerSeries K :=
  PowerSeries.mk (sparse (ep N a) (cp v)) + PowerSeries.mk (sparse (em N a) (cm v))

/-- The scaled derivative is formed by the analogous honest branch sum. -/
def M (N a : ℕ) (v : K) : PowerSeries K :=
  PowerSeries.mk (sparse (ep N a) (dp v)) + PowerSeries.mk (sparse (em N a) (dm v))

def completion (N a : ℕ) : K := (a : K) / (N : K) + 1 / 2

def R (N a : ℕ) (v : K) : PowerSeries K :=
  PowerSeries.C (completion N a) + M N a v * (P N a v)⁻¹

lemma sparse_zero (e : ℕ → ℕ) (he : Function.Injective e) (he0 : e 0 = 0) (c : ℕ → K) :
    sparse e c 0 = c 0 := by
  simpa only [he0] using sparse_at e he c 0

lemma P_zero {N a : ℕ} (hN : 0 < N) (ha : a < N) (v : K) :
    (P N a v).coeff 0 = if a = 0 then 1 - v⁻¹ else -v⁻¹ := by
  have hem0 : em N a 0 = 0 := by simp [em, tri]
  rw [P, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    sparse_zero _ (em_strict ha).injective hem0]
  dsimp [cm]
  simp only [pow_zero, pow_one, neg_one_mul]
  split_ifs with hz
  · subst a
    have hep0 : ep N 0 0 = 0 := by simp [ep, tri]
    rw [sparse_zero _ (ep_strict hN).injective hep0]
    simp [cp, sub_eq_add_neg]
  · have hnot : 0 ∉ Set.range (ep N a) := by
      rintro ⟨j, hj⟩
      have h := le_ep (a := a) hN j
      dsimp [ep] at hj
      have ha0 : 0 < a := Nat.pos_of_ne_zero hz
      nlinarith
    rw [sparse_off _ _ _ hnot]
    simp

lemma map_sparse {L : Type*} [Field L] (φ : K →+* L) (e : ℕ → ℕ) (c : ℕ → K) (m : ℕ) :
    φ (sparse e c m) = sparse e (φ ∘ c) m := by
  classical
  dsimp [sparse]
  split_ifs <;> simp

lemma map_P {L : Type*} [Field L] (φ : K →+* L) (N a : ℕ) (v : K) :
    PowerSeries.map φ (P N a v) = P N a (φ v) := by
  have hcp : φ ∘ cp v = cp (φ v) := by ext j; simp [cp]
  have hcm : φ ∘ cm v = cm (φ v) := by ext j; simp [cm]
  ext m
  simp only [P, PowerSeries.coeff_map, map_add, PowerSeries.coeff_mk, map_sparse, hcp, hcm]

lemma map_M {L : Type*} [Field L] (φ : K →+* L) (N a : ℕ) (v : K) :
    PowerSeries.map φ (M N a v) = M N a (φ v) := by
  have hdp : φ ∘ dp v = dp (φ v) := by ext j; simp [dp, cp]
  have hdm : φ ∘ dm v = dm (φ v) := by ext j; simp [dm]
  ext m
  simp only [M, PowerSeries.coeff_map, map_add, PowerSeries.coeff_mk, map_sparse, hdp, hdm]

end Sparse

variable (N : ℕ) [NeZero N] (a : ℕ) (ha : a < N)

/-- The principal-level local parameter. -/
def Q (τ : ℍ) : ℂ := Function.Periodic.qParam (N : ℝ) τ

lemma Q_ne_zero (τ : ℍ) : Q N τ ≠ 0 := Function.Periodic.qParam_ne_zero _

lemma theta_positive (b : ℤ) (τ : ℍ) (j : ℕ) :
    Q N τ ^ a * jacobiTheta₂_term j (shiftedPoint N a b τ) τ =
      cp (w N b) j * Q N τ ^ ep N a j := by
  have htri : (2 : ℂ) * (tri j : ℂ) = (j : ℂ) * ((j : ℂ) + 1) := by
    exact_mod_cast two_mul_tri j
  rw [Q, Function.Periodic.qParam, ← Complex.exp_nat_mul, jacobiTheta₂_term,
    ← Complex.exp_add]
  have he : (a : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * τ / (N : ℂ)) +
      (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * shiftedPoint N a b τ +
        (Real.pi : ℂ) * Complex.I * (j : ℂ) ^ 2 * (τ : ℂ)) =
      (j : ℂ) * ((Real.pi : ℂ) * Complex.I) +
      (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * b / (N : ℂ)) +
      (ep N a j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * τ / (N : ℂ)) := by
    dsimp [shiftedPoint, ep]
    push_cast
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    field_simp [hN0]
    linear_combination -(τ : ℂ) * (N : ℂ) * htri
  push_cast
  rw [he, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_nat_mul,
    Complex.exp_nat_mul, Complex.exp_pi_mul_I,
    ← ZInQ.Contrib.HeckePrimeRationality.AllLevelTorsionCoefficients.w_eq_exp]
  simp [cp, Q, Function.Periodic.qParam]

lemma theta_negative (ha : a < N) (b : ℤ) (τ : ℍ) (j : ℕ) :
    Q N τ ^ a * jacobiTheta₂_term (-((j : ℤ) + 1)) (shiftedPoint N a b τ) τ =
      cm (w N b) j * Q N τ ^ em N a j := by
  have htri : (2 : ℂ) * (tri j : ℂ) = (j : ℂ) * ((j : ℂ) + 1) := by
    exact_mod_cast two_mul_tri j
  have hem : (em N a j : ℂ) = (N : ℂ) * (tri j : ℂ) - (a : ℂ) * j := by
    rw [em, Nat.cast_sub (em_sub_bound ha j)]
    push_cast
    rfl
  rw [Q, Function.Periodic.qParam, ← Complex.exp_nat_mul, jacobiTheta₂_term,
    ← Complex.exp_add]
  have he : (a : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * τ / (N : ℂ)) +
      (2 * (Real.pi : ℂ) * Complex.I * ((-((j : ℤ) + 1) : ℤ) : ℂ) * shiftedPoint N a b τ +
        (Real.pi : ℂ) * Complex.I * (((-((j : ℤ) + 1) : ℤ) : ℂ)) ^ 2 * (τ : ℂ)) =
      -((j + 1 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I) +
      -((j + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * b / (N : ℂ)) +
      (em N a j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * τ / (N : ℂ)) := by
    rw [hem]
    dsimp [shiftedPoint]
    push_cast
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    field_simp [hN0]
    linear_combination -(τ : ℂ) * (N : ℂ) * htri
  push_cast at he ⊢
  rw [he, Complex.exp_add, Complex.exp_add, neg_mul, neg_mul,
    Complex.exp_neg, Complex.exp_neg]
  rw [show (j : ℂ) + 1 = ((j + 1 : ℕ) : ℂ) by push_cast; rfl]
  rw [Complex.exp_nat_mul, Complex.exp_nat_mul, Complex.exp_nat_mul,
    Complex.exp_pi_mul_I,
    ← ZInQ.Contrib.HeckePrimeRationality.AllLevelTorsionCoefficients.w_eq_exp]
  simp [cm, Q, Function.Periodic.qParam, pow_succ]
  rw [← inv_pow]
  norm_num

lemma sparse_hasSum (e : ℕ → ℕ) (he : Function.Injective e) (c : ℕ → ℂ)
    (z : ℂ) {s : ℂ} (hc : HasSum (fun j => c j * z ^ e j) s) :
    HasSum (fun m => sparse e c m * z ^ m) s := by
  apply (he.hasSum_iff (f := fun m => sparse e c m * z ^ m) ?_).mp
  · change HasSum (fun j => sparse e c (e j) * z ^ e j) s
    simpa only [sparse_at e he] using hc
  · intro m hm
    rw [sparse_off e c m hm, zero_mul]

/-- Pair an actual integer sum into two independent sparse branches. -/
lemma paired_sparse_hasSum (e f : ℕ → ℕ) (he : Function.Injective e) (hf : Function.Injective f)
    (c d : ℕ → ℂ) (z : ℂ) (g : ℤ → ℂ) {s : ℂ} (hg : HasSum g s)
    (hp : ∀ j : ℕ, g j = c j * z ^ e j)
    (hm : ∀ j : ℕ, g (-((j : ℤ) + 1)) = d j * z ^ f j) :
    HasSum (fun m => (sparse e c m + sparse f d m) * z ^ m) s := by
  have hn : Summable (fun j : ℕ => c j * z ^ e j) := by
    have hnat := hg.summable.comp_injective Nat.cast_injective
    change Summable (fun j : ℕ => g j) at hnat
    simpa only [hp] using hnat
  have hneg : Summable (fun j : ℕ => d j * z ^ f j) := by
    have hnat := hg.summable.comp_injective (show Function.Injective Int.negSucc from @Int.negSucc.inj)
    change Summable (fun j : ℕ => g (-((j : ℤ) + 1))) at hnat
    simpa only [hm] using hnat
  have hsum : (∑' j : ℕ, c j * z ^ e j) + (∑' j : ℕ, d j * z ^ f j) = s := by
    rw [← hn.tsum_add hneg]
    simpa only [hp, hm] using hg.nat_add_neg_add_one.tsum_eq
  rw [← hsum]
  simpa only [add_mul] using (sparse_hasSum e he c z hn.hasSum).add
    (sparse_hasSum f hf d z hneg.hasSum)

lemma P_hasSum (ha : a < N) (b : ℤ) (τ : ℍ) :
    HasSum (fun m => (P N a (w N b)).coeff m * Q N τ ^ m)
      (Q N τ ^ a * jacobiTheta₂ (shiftedPoint N a b τ) τ) := by
  have hg := (hasSum_jacobiTheta₂_term (shiftedPoint N a b τ) τ.im_pos).mul_left (Q N τ ^ a)
  simpa only [P, map_add, PowerSeries.coeff_mk] using
    paired_sparse_hasSum (ep N a) (em N a) (ep_strict (NeZero.pos N)).injective
      (em_strict ha).injective (cp (w N b)) (cm (w N b)) (Q N τ)
      (fun n => Q N τ ^ a * jacobiTheta₂_term n (shiftedPoint N a b τ) τ) hg
      (theta_positive N a b τ) (theta_negative N a ha b τ)

lemma M_hasSum (ha : a < N) (b : ℤ) (τ : ℍ) :
    HasSum (fun m => (M N a (w N b)).coeff m * Q N τ ^ m)
      (Q N τ ^ a * (jacobiTheta₂' (shiftedPoint N a b τ) τ /
        (2 * (Real.pi : ℂ) * Complex.I))) := by
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hg : HasSum (fun n : ℤ => Q N τ ^ a * ((n : ℂ) *
      jacobiTheta₂_term n (shiftedPoint N a b τ) τ))
      (Q N τ ^ a * (jacobiTheta₂' (shiftedPoint N a b τ) τ /
        (2 * (Real.pi : ℂ) * Complex.I))) := by
    convert ((hasSum_jacobiTheta₂'_term (shiftedPoint N a b τ) τ.im_pos).div_const
      (2 * (Real.pi : ℂ) * Complex.I)).mul_left (Q N τ ^ a) using 1
    ext n
    dsimp [jacobiTheta₂'_term]
    field_simp
  have hp : ∀ j : ℕ, Q N τ ^ a * ((j : ℂ) *
      jacobiTheta₂_term j (shiftedPoint N a b τ) τ) = dp (w N b) j * Q N τ ^ ep N a j := by
    intro j
    rw [mul_left_comm, theta_positive N a b τ]
    dsimp [dp]
    ring
  have hm : ∀ j : ℕ, Q N τ ^ a * (((-((j : ℤ) + 1) : ℤ) : ℂ) *
      jacobiTheta₂_term (-((j : ℤ) + 1)) (shiftedPoint N a b τ) τ) =
      dm (w N b) j * Q N τ ^ em N a j := by
    intro j
    rw [mul_left_comm, theta_negative N a ha b τ]
    dsimp [dm, cm]
    push_cast
    ring
  simpa only [M, map_add, PowerSeries.coeff_mk] using
    paired_sparse_hasSum (ep N a) (em N a) (ep_strict (NeZero.pos N)).injective
      (em_strict ha).injective (dp (w N b)) (dm (w N b)) (Q N τ)
      (fun n => Q N τ ^ a * ((n : ℂ) * jacobiTheta₂_term n (shiftedPoint N a b τ) τ)) hg
      (by intro j; simpa only [Int.cast_natCast] using hp j) hm

lemma norm_cp (b : ℤ) (j : ℕ) : ‖cp (w N b) j‖ = 1 := by
  simp [cp, norm_mul, norm_pow, ZInQ.Contrib.HeckePrimeRationality.AllLevelTorsionCoefficients.norm_w]

lemma norm_cm (b : ℤ) (j : ℕ) : ‖cm (w N b) j‖ = 1 := by
  simp [cm, norm_mul, norm_pow, norm_inv,
    ZInQ.Contrib.HeckePrimeRationality.AllLevelTorsionCoefficients.norm_w]

lemma norm_dp (b : ℤ) (j : ℕ) : ‖dp (w N b) j‖ = j := by
  simp [dp, norm_mul, norm_cp]

lemma norm_dm (b : ℤ) (j : ℕ) : ‖dm (w N b) j‖ = j + 1 := by
  have he : dm (w N b) j = -((j + 1 : ℕ) : ℂ) * cm (w N b) j := by
    dsimp [dm, cm]
    push_cast
    ring
  rw [he, norm_mul, norm_neg, Complex.norm_natCast, norm_cm, mul_one]
  norm_cast

lemma sparse_norm_bound (e : ℕ → ℕ) (c : ℕ → ℂ) (B : ℕ → ℝ)
    (h : ∀ j, ‖c j‖ ≤ B (e j)) (hB : ∀ m, 0 ≤ B m) (m : ℕ) :
    ‖sparse e c m‖ ≤ B m := by
  classical
  rw [sparse]
  split_ifs with hj
  · have h' := h hj.choose
    rwa [hj.choose_spec] at h'
  · simpa only [norm_zero] using hB m

lemma P_norm_bound (ha : a < N) (b : ℤ) (m : ℕ) : ‖(P N a (w N b)).coeff m‖ ≤ 2 := by
  have hp := sparse_norm_bound (ep N a) (cp (w N b)) (fun _ => 1)
    (fun j => (norm_cp N b j).le) (by intro m; norm_num) m
  have hm := sparse_norm_bound (em N a) (cm (w N b)) (fun _ => 1)
    (fun j => (norm_cm N b j).le) (by intro m; norm_num) m
  rw [P, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  exact (norm_add_le _ _).trans (by linarith)

lemma M_norm_bound (ha : a < N) (b : ℤ) (m : ℕ) : ‖(M N a (w N b)).coeff m‖ ≤ 2 * m + 1 := by
  have hp := sparse_norm_bound (ep N a) (dp (w N b)) (fun m => (m : ℝ))
    (fun j => by rw [norm_dp]; exact_mod_cast le_ep (a := a) (NeZero.pos N) j)
    (by intro m; positivity) m
  have hm := sparse_norm_bound (em N a) (dm (w N b)) (fun m => (m : ℝ) + 1)
    (fun j => by rw [norm_dm]; exact_mod_cast Nat.add_le_add_right (le_em ha j) 1)
    (by intro m; positivity) m
  rw [M, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  exact (norm_add_le _ _).trans (by linarith)

lemma P_radius (ha : a < N) (b : ℤ) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ (fun m => (P N a (w N b)).coeff m)).radius := by
  apply FormalMultilinearSeries.le_radius_of_bound _ 2 (r := 1)
  intro m
  simpa only [FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one, one_pow, mul_one]
    using P_norm_bound N a ha b m

lemma M_radius (ha : a < N) (b : ℤ) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ (fun m => (M N a (w N b)).coeff m)).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  have hr' : (r : ℝ) < 1 := by exact_mod_cast hr
  have hs0 := summable_geometric_of_lt_one r.2 hr'
  have hs1 : Summable (fun m : ℕ => (m : ℝ) * (r : ℝ) ^ m) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (r := (r : ℝ)) (by
        change ‖(r : ℝ)‖ < 1
        rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ (r : ℝ) by positivity)]
        exact hr')
  have hs : Summable (fun m : ℕ => (2 * (m : ℝ) + 1) * (r : ℝ) ^ m) := by
    simpa [add_mul, mul_assoc] using (hs1.mul_left 2).add hs0
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  simp only [FormalMultilinearSeries.ofScalars_norm]
  exact Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun m => mul_le_mul_of_nonneg_right (M_norm_bound N a ha b m) (by positivity)) hs

def pSum (b : ℤ) : ℂ → ℂ :=
  FormalMultilinearSeries.ofScalarsSum (fun m => (P N a (w N b)).coeff m)

def mSum (b : ℤ) : ℂ → ℂ :=
  FormalMultilinearSeries.ofScalarsSum (fun m => (M N a (w N b)).coeff m)

lemma pSum_analytic (ha : a < N) (b : ℤ) : AnalyticAt ℂ (pSum N a b) 0 :=
  (FormalMultilinearSeries.hasFPowerSeriesOnBall _
    (zero_lt_one.trans_le (P_radius N a ha b))).analyticAt

lemma mSum_analytic (ha : a < N) (b : ℤ) : AnalyticAt ℂ (mSum N a b) 0 :=
  (FormalMultilinearSeries.hasFPowerSeriesOnBall _
    (zero_lt_one.trans_le (M_radius N a ha b))).analyticAt

lemma pSum_Q (ha : a < N) (b : ℤ) (τ : ℍ) : pSum N a b (Q N τ) =
    Q N τ ^ a * jacobiTheta₂ (shiftedPoint N a b τ) τ := by
  rw [pSum, FormalMultilinearSeries.ofScalars_sum_eq]
  simpa only [smul_eq_mul] using (P_hasSum N a ha b τ).tsum_eq

lemma mSum_Q (ha : a < N) (b : ℤ) (τ : ℍ) : mSum N a b (Q N τ) =
    Q N τ ^ a * (jacobiTheta₂' (shiftedPoint N a b τ) τ /
      (2 * (Real.pi : ℂ) * Complex.I)) := by
  rw [mSum, FormalMultilinearSeries.ofScalars_sum_eq]
  simpa only [smul_eq_mul] using (M_hasSum N a ha b τ).tsum_eq

/-- The actual cusp-function germ is obtained from any continuous scalar representation. -/
lemma cusp_germ {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} {G : ℂ → ℂ}
    (hrep : ∀ τ : ℍ, f τ = G (Function.Periodic.qParam h τ)) (hG : ContinuousAt G 0) :
    cuspFunction h f =ᶠ[𝓝 0] G := by
  have hnonzero : ∀ z : ℂ, z ≠ 0 → ‖z‖ < 1 → cuspFunction h f z = G z := by
    intro z hz hz1
    rw [UpperHalfPlane.cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hz]
    have him : 0 < (Function.Periodic.invQParam h z).im :=
      Function.Periodic.im_invQParam_pos_of_norm_lt_one hh hz1 hz
    change f (ofComplex (Function.Periodic.invQParam h z)) = G z
    rw [hrep]
    congr 1
    rw [ofComplex_apply_of_im_pos him]
    exact Function.Periodic.qParam_right_inv hh.ne' hz
  have hball : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < 1 := by
    change {z : ℂ | ‖z‖ < 1} ∈ 𝓝 0
    have hs : {z : ℂ | ‖z‖ < 1} = Metric.ball 0 1 := by ext z; simp
    rw [hs]
    exact Metric.ball_mem_nhds (0 : ℂ) one_pos
  have hpunct : cuspFunction h f =ᶠ[𝓝[≠] 0] G := by
    filter_upwards [hball.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hz0
    exact hnonzero z hz0 hz
  have hzero : cuspFunction h f 0 = G 0 := by
    change Function.Periodic.cuspFunction h (f ∘ ofComplex) 0 = G 0
    rw [Function.Periodic.cuspFunction_zero_eq_limUnder_nhds_ne]
    exact ((hG.tendsto.mono_left nhdsWithin_le_nhds).congr' hpunct.symm).limUnder_eq
  filter_upwards [hball] with z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · exact hzero
  · exact hnonzero z hz0 hz

lemma P_qExpansion (ha : a < N) (b : ℤ) :
    qExpansion (N : ℝ) (fun τ : ℍ => Q N τ ^ a * jacobiTheta₂ (shiftedPoint N a b τ) τ) =
      P N a (w N b) := by
  have han : AnalyticAt ℂ (cuspFunction (N : ℝ) (fun τ : ℍ =>
      Q N τ ^ a * jacobiTheta₂ (shiftedPoint N a b τ) τ)) 0 :=
    (pSum_analytic N a ha b).congr (cusp_germ (by exact_mod_cast NeZero.pos N)
      (fun τ => (pSum_Q N a ha b τ).symm) (pSum_analytic N a ha b).continuousAt).symm
  ext m
  symm
  exact TauCeti.UpperHalfPlane.qExpansion_coeff_unique
    (c := fun n => (P N a (w N b)).coeff n) (by exact_mod_cast NeZero.pos N) han
    (fun τ => by simpa only [Q, smul_eq_mul] using P_hasSum N a ha b τ) m

lemma M_qExpansion (ha : a < N) (b : ℤ) :
    qExpansion (N : ℝ) (fun τ : ℍ => Q N τ ^ a * (jacobiTheta₂' (shiftedPoint N a b τ) τ /
      (2 * (Real.pi : ℂ) * Complex.I))) = M N a (w N b) := by
  have han : AnalyticAt ℂ (cuspFunction (N : ℝ) (fun τ : ℍ =>
      Q N τ ^ a * (jacobiTheta₂' (shiftedPoint N a b τ) τ /
        (2 * (Real.pi : ℂ) * Complex.I)))) 0 :=
    (mSum_analytic N a ha b).congr (cusp_germ (by exact_mod_cast NeZero.pos N)
      (fun τ => (mSum_Q N a ha b τ).symm) (mSum_analytic N a ha b).continuousAt).symm
  ext m
  symm
  exact TauCeti.UpperHalfPlane.qExpansion_coeff_unique
    (c := fun n => (M N a (w N b)).coeff n) (by exact_mod_cast NeZero.pos N) han
    (fun τ => by simpa only [Q, smul_eq_mul] using M_hasSum N a ha b τ) m

lemma P_constant_ne_zero (ha : a < N) (b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ (a : ℤ) ∧ (N : ℤ) ∣ b)) :
    PowerSeries.constantCoeff (P N a (w N b)) ≠ 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, P_zero (NeZero.pos N) ha]
  split_ifs with hz
  · subst a
    have hb : ¬ (N : ℤ) ∣ b := by simpa using hg
    intro h
    have hi : (w N b)⁻¹ = 1 := by linear_combination -h
    have hw : w N b = 1 := by simpa using congrArg Inv.inv hi
    exact hb ((ZInQ.Contrib.HeckePrimeRationality.AllLevelTorsionCoefficients.w_eq_one_iff N b).mp hw)
  · exact neg_ne_zero.mpr (inv_ne_zero
      (ZInQ.Contrib.HeckePrimeRationality.AllLevelTorsionCoefficients.w_ne_zero N b))

lemma pSum_zero_ne (ha : a < N) (b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ (a : ℤ) ∧ (N : ℤ) ∣ b)) : pSum N a b 0 ≠ 0 := by
  have he : pSum N a b 0 = PowerSeries.constantCoeff (P N a (w N b)) := by
    simp [pSum, FormalMultilinearSeries.ofScalarsSum_zero]
  rw [he]
  exact P_constant_ne_zero N a ha b hg

lemma torsion_rep (ha : a < N) (b : ℤ) (τ : ℍ) :
    torsionLogDerivative N a b τ = completion N a + mSum N a b (Q N τ) / pSum N a b (Q N τ) := by
  rw [mSum_Q N a ha b τ, pSum_Q N a ha b τ]
  have hQ0 : Q N τ ^ a ≠ 0 := pow_ne_zero _ (Q_ne_zero N τ)
  simp only [torsionLogDerivative, completion, Int.cast_natCast]
  rw [mul_div_mul_left _ _ hQ0]
  rw [div_div]

lemma torsion_cusp_analytic (ha : a < N) (b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ (a : ℤ) ∧ (N : ℤ) ∣ b)) :
    AnalyticAt ℂ (cuspFunction (N : ℝ) (torsionLogDerivative N a b)) 0 := by
  have hG : AnalyticAt ℂ (fun z => (completion N a : ℂ) + mSum N a b z / pSum N a b z) 0 :=
    analyticAt_const.add ((mSum_analytic N a ha b).div (pSum_analytic N a ha b)
      (pSum_zero_ne N a ha b hg))
  exact hG.congr (cusp_germ (by exact_mod_cast NeZero.pos N)
    (torsion_rep N a ha b) hG.continuousAt).symm

lemma qExpansion_eq_of_cusp_germ {h : ℝ} {f g : ℍ → ℂ}
    (he : cuspFunction h f =ᶠ[𝓝 0] cuspFunction h g) : qExpansion h f = qExpansion h g := by
  ext n
  rw [UpperHalfPlane.qExpansion_coeff, UpperHalfPlane.qExpansion_coeff,
    Filter.EventuallyEq.iteratedDeriv_eq n he]

lemma torsion_product_cusp_germ (ha : a < N) (b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ (a : ℤ) ∧ (N : ℤ) ∣ b)) :
    cuspFunction (N : ℝ) (torsionLogDerivative N a b *
      (fun τ : ℍ => Q N τ ^ a * jacobiTheta₂ (shiftedPoint N a b τ) τ)) =ᶠ[𝓝 0]
    cuspFunction (N : ℝ) ((completion N a : ℂ) •
      (fun τ : ℍ => Q N τ ^ a * jacobiTheta₂ (shiftedPoint N a b τ) τ) +
      (fun τ : ℍ => Q N τ ^ a * (jacobiTheta₂' (shiftedPoint N a b τ) τ /
        (2 * (Real.pi : ℂ) * Complex.I)))) := by
  let pf : ℍ → ℂ := fun τ => Q N τ ^ a * jacobiTheta₂ (shiftedPoint N a b τ) τ
  let mf : ℍ → ℂ := fun τ => Q N τ ^ a * (jacobiTheta₂' (shiftedPoint N a b τ) τ /
    (2 * (Real.pi : ℂ) * Complex.I))
  have hh : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hpG := cusp_germ hh (fun τ => (pSum_Q N a ha b τ).symm)
    (pSum_analytic N a ha b).continuousAt
  have hmG := cusp_germ hh (fun τ => (mSum_Q N a ha b τ).symm)
    (mSum_analytic N a ha b).continuousAt
  have hp : AnalyticAt ℂ (cuspFunction (N : ℝ) pf) 0 :=
    (pSum_analytic N a ha b).congr hpG.symm
  have hm : AnalyticAt ℂ (cuspFunction (N : ℝ) mf) 0 :=
    (mSum_analytic N a ha b).congr hmG.symm
  have hf := torsion_cusp_analytic N a ha b hg
  have hsp : AnalyticAt ℂ (cuspFunction (N : ℝ) ((completion N a : ℂ) • pf)) 0 := by
    rw [UpperHalfPlane.cuspFunction_smul hp.continuousAt]
    exact hp.const_smul
  have hG : AnalyticAt ℂ (fun z => (completion N a : ℂ) + mSum N a b z / pSum N a b z) 0 :=
    analyticAt_const.add ((mSum_analytic N a ha b).div (pSum_analytic N a ha b)
      (pSum_zero_ne N a ha b hg))
  have hfG := cusp_germ hh (torsion_rep N a ha b) hG.continuousAt
  have hpne : ∀ᶠ z in 𝓝 0, pSum N a b z ≠ 0 :=
    (pSum_analytic N a ha b).continuousAt.eventually_ne (pSum_zero_ne N a ha b hg)
  change cuspFunction (N : ℝ) (torsionLogDerivative N a b * pf) =ᶠ[𝓝 0]
    cuspFunction (N : ℝ) ((completion N a : ℂ) • pf + mf)
  rw [UpperHalfPlane.cuspFunction_mul hf.continuousAt hp.continuousAt,
    UpperHalfPlane.cuspFunction_add hsp.continuousAt hm.continuousAt,
    UpperHalfPlane.cuspFunction_smul hp.continuousAt]
  filter_upwards [hpG, hmG, hfG, hpne] with z hpz hmz hfz hnez
  change cuspFunction (N : ℝ) (torsionLogDerivative N a b) z * cuspFunction (N : ℝ) pf z =
    completion N a * cuspFunction (N : ℝ) pf z + cuspFunction (N : ℝ) mf z
  rw [hpz, hmz, hfz]
  field_simp [hnez]

/-- Actual full-row quotient expansion in the principal-level period-N parameter. -/
theorem torsion_qExpansion (ha : a < N) (b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ (a : ℤ) ∧ (N : ℤ) ∣ b)) :
    qExpansion (N : ℝ) (torsionLogDerivative N a b) = R N a (w N b) := by
  let pf : ℍ → ℂ := fun τ => Q N τ ^ a * jacobiTheta₂ (shiftedPoint N a b τ) τ
  let mf : ℍ → ℂ := fun τ => Q N τ ^ a * (jacobiTheta₂' (shiftedPoint N a b τ) τ /
    (2 * (Real.pi : ℂ) * Complex.I))
  have hh : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hp : AnalyticAt ℂ (cuspFunction (N : ℝ) pf) 0 :=
    (pSum_analytic N a ha b).congr (cusp_germ hh
      (fun τ => (pSum_Q N a ha b τ).symm) (pSum_analytic N a ha b).continuousAt).symm
  have hm : AnalyticAt ℂ (cuspFunction (N : ℝ) mf) 0 :=
    (mSum_analytic N a ha b).congr (cusp_germ hh
      (fun τ => (mSum_Q N a ha b τ).symm) (mSum_analytic N a ha b).continuousAt).symm
  have hf := torsion_cusp_analytic N a ha b hg
  have hsp : AnalyticAt ℂ (cuspFunction (N : ℝ) ((completion N a : ℂ) • pf)) 0 := by
    rw [UpperHalfPlane.cuspFunction_smul hp.continuousAt]
    exact hp.const_smul
  have hpoint : qExpansion (N : ℝ) (torsionLogDerivative N a b * pf) =
      qExpansion (N : ℝ) ((completion N a : ℂ) • pf + mf) :=
    qExpansion_eq_of_cusp_germ (torsion_product_cusp_germ N a ha b hg)
  have hq : qExpansion (N : ℝ) (torsionLogDerivative N a b) * P N a (w N b) =
      (completion N a : ℂ) • P N a (w N b) + M N a (w N b) := by
    rw [← P_qExpansion N a ha b, ← M_qExpansion N a ha b,
      ← UpperHalfPlane.qExpansion_mul hf hp, hpoint,
      UpperHalfPlane.qExpansion_add hsp hm, UpperHalfPlane.qExpansion_smul hp]
  have hC : (completion N a : ℂ) • P N a (w N b) =
      PowerSeries.C (completion N a) * P N a (w N b) := by ext n; simp [smul_eq_mul]
  rw [hC] at hq
  have hmul : (qExpansion (N : ℝ) (torsionLogDerivative N a b) -
      PowerSeries.C (completion N a)) * P N a (w N b) = M N a (w N b) := by
    linear_combination hq
  have hquot := (PowerSeries.eq_mul_inv_iff_mul_eq (P_constant_ne_zero N a ha b hg)).mpr hmul
  dsimp [R]
  linear_combination hquot

section FieldMaps
variable {K L : Type*} [Field K] [Field L]

lemma map_completion (φ : K →+* L) (N a : ℕ) :
    φ (completion N a : K) = (completion N a : L) := by
  simp only [completion, map_add, map_div₀, map_natCast, map_one, map_ofNat]

lemma map_R (φ : K →+* L) (N a : ℕ) (v : K)
    (hv : PowerSeries.constantCoeff (P N a v) ≠ 0) :
    PowerSeries.map φ (R N a v) = R N a (φ v) := by
  have hmap : PowerSeries.constantCoeff (P N a (φ v)) ≠ 0 := by
    rw [← map_P φ N a v, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact fun h => hv (φ.injective (by simpa using h))
  have hinv : PowerSeries.map φ ((P N a v)⁻¹) = (P N a (φ v))⁻¹ := by
    apply (PowerSeries.eq_inv_iff_mul_eq_one hmap).mpr
    rw [← map_P φ N a v, ← map_mul, PowerSeries.inv_mul_cancel _ hv, map_one]
  simp only [R, map_add, PowerSeries.map_C, map_mul, map_M, hinv, map_completion]

end FieldMaps

open ZInQ.Contrib.HeckePrimeRationality.AllLevelTorsionCoefficients
  (zetaInField wInField wInField_coe)

lemma P_field_constant_ne (ha : a < N) (b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ (a : ℤ) ∧ (N : ℤ) ∣ b)) :
    PowerSeries.constantCoeff (P N a (wInField N b)) ≠ 0 := by
  intro h
  have h' := congrArg (algebraMap (coefficientField N) ℂ) h
  have hmap : PowerSeries.constantCoeff (P N a (w N b)) =
      (algebraMap (coefficientField N) ℂ) (PowerSeries.constantCoeff (P N a (wInField N b))) := by
    rw [← wInField_coe N b]
    change PowerSeries.constantCoeff (P N a ((algebraMap (coefficientField N) ℂ) (wInField N b))) = _
    rw [← map_P (algebraMap (coefficientField N) ℂ) N a (wInField N b),
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact P_constant_ne_zero N a ha b hg (by rw [hmap]; simpa using h')

/-- Coefficients computed inside the actual coefficient field. -/
def coefficientInField (b : ℤ) (n : ℕ) : coefficientField N := (R N a (wInField N b)).coeff n

lemma coefficientInField_coe (ha : a < N) (b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ (a : ℤ) ∧ (N : ℤ) ∣ b)) (n : ℕ) :
    (coefficientInField N a b n : ℂ) =
      (qExpansion (N : ℝ) (torsionLogDerivative N a b)).coeff n := by
  rw [torsion_qExpansion N a ha b hg]
  change (algebraMap (coefficientField N) ℂ) ((R N a (wInField N b)).coeff n) =
    (R N a (w N b)).coeff n
  rw [← PowerSeries.coeff_map, map_R (algebraMap (coefficientField N) ℂ) N a (wInField N b)
    (P_field_constant_ne N a ha b hg)]
  rw [IntermediateField.algebraMap_apply, wInField_coe]

/-- Full-row coefficients, at the same period N, lie in the actual cyclotomic coefficient field. -/
theorem torsion_coeff_mem (ha : a < N) (b : ℤ)
    (hg : ¬ ((N : ℤ) ∣ (a : ℤ) ∧ (N : ℤ) ∣ b)) (n : ℕ) :
    (qExpansion (N : ℝ) (torsionLogDerivative N a b)).coeff n ∈ coefficientField N := by
  rw [← coefficientInField_coe N a ha b hg n]
  exact (coefficientInField N a b n).property

lemma good_automorphism (ha : a < N) (b t : ℤ)
    (hg : ¬ ((N : ℤ) ∣ (a : ℤ) ∧ (N : ℤ) ∣ b))
    (σ : coefficientField N ≃ₐ[ℚ] coefficientField N)
    (hσ : σ (zetaInField N) = zetaInField N ^ t) :
    ¬ ((N : ℤ) ∣ (a : ℤ) ∧ (N : ℤ) ∣ t * b) := by
  rintro ⟨hNa, hNtb⟩
  have ha0 : a = 0 := Nat.eq_zero_of_dvd_of_lt (by exact_mod_cast hNa) ha
  subst a
  have hb : ¬ (N : ℤ) ∣ b := by simpa using hg
  exact ZInQ.Contrib.HeckePrimeRationality.AllLevelTorsionCoefficients.automorphism_admissible
    N b t hb σ hσ hNtb

lemma coefficientInField_galois (ha : a < N) (b t : ℤ)
    (hg : ¬ ((N : ℤ) ∣ (a : ℤ) ∧ (N : ℤ) ∣ b))
    (σ : coefficientField N ≃ₐ[ℚ] coefficientField N)
    (hσ : σ (zetaInField N) = zetaInField N ^ t) (n : ℕ) :
    σ (coefficientInField N a b n) = coefficientInField N a (t * b) n := by
  change σ.toRingHom ((R N a (wInField N b)).coeff n) =
    (R N a (wInField N (t * b))).coeff n
  rw [← PowerSeries.coeff_map, map_R σ.toRingHom N a (wInField N b)
    (P_field_constant_ne N a ha b hg)]
  rw [show σ.toRingHom (wInField N b) = wInField N (t * b) from
    ZInQ.Contrib.HeckePrimeRationality.AllLevelTorsionCoefficients.automorphism_w N σ t b hσ]

/-- Galois covariance for all normalized torsion rows, without a restriction on the second coordinate. -/
theorem torsion_coeff_galois (ha : a < N) (b t : ℤ)
    (hg : ¬ ((N : ℤ) ∣ (a : ℤ) ∧ (N : ℤ) ∣ b))
    (σ : coefficientField N ≃ₐ[ℚ] coefficientField N)
    (hσ : σ (zetaInField N) = zetaInField N ^ t) (n : ℕ) :
    ((σ ⟨(qExpansion (N : ℝ) (torsionLogDerivative N a b)).coeff n,
        torsion_coeff_mem N a ha b hg n⟩ : coefficientField N) : ℂ) =
      (qExpansion (N : ℝ) (torsionLogDerivative N a (t * b))).coeff n := by
  have hcoef : (⟨(qExpansion (N : ℝ) (torsionLogDerivative N a b)).coeff n,
      torsion_coeff_mem N a ha b hg n⟩ : coefficientField N) = coefficientInField N a b n := by
    apply Subtype.ext
    exact (coefficientInField_coe N a ha b hg n).symm
  rw [hcoef, coefficientInField_galois N a ha b t hg σ hσ n]
  exact coefficientInField_coe N a ha (t * b) (good_automorphism N a ha b t hg σ hσ) n

/-- The membership theorem with the exact integer normalized-coordinate convention. -/
theorem torsion_coeff_mem_int (A b : ℤ) (hA0 : 0 ≤ A) (hAN : A < N)
    (hg : ¬ ((N : ℤ) ∣ A ∧ (N : ℤ) ∣ b)) (n : ℕ) :
    (qExpansion (N : ℝ) (torsionLogDerivative N A b)).coeff n ∈ coefficientField N := by
  have he : (A.toNat : ℤ) = A := Int.toNat_of_nonneg hA0
  have ha : A.toNat < N := by omega
  have hg' : ¬ ((N : ℤ) ∣ (A.toNat : ℤ) ∧ (N : ℤ) ∣ b) := by rwa [he]
  simpa only [he] using torsion_coeff_mem N A.toNat ha b hg' n

/-- Actual full-row covariance in normalized integer coordinates at period N. -/
theorem torsion_coeff_galois_int (A b t : ℤ) (hA0 : 0 ≤ A) (hAN : A < N)
    (hg : ¬ ((N : ℤ) ∣ A ∧ (N : ℤ) ∣ b))
    (σ : coefficientField N ≃ₐ[ℚ] coefficientField N)
    (hσ : σ (zetaInField N) = zetaInField N ^ t) (n : ℕ) :
    ((σ ⟨(qExpansion (N : ℝ) (torsionLogDerivative N A b)).coeff n,
        torsion_coeff_mem_int N A b hA0 hAN hg n⟩ : coefficientField N) : ℂ) =
      (qExpansion (N : ℝ) (torsionLogDerivative N A (t * b))).coeff n := by
  have he : (A.toNat : ℤ) = A := Int.toNat_of_nonneg hA0
  have ha : A.toNat < N := by omega
  have hg' : ¬ ((N : ℤ) ∣ (A.toNat : ℤ) ∧ (N : ℤ) ∣ b) := by rwa [he]
  simpa only [he] using torsion_coeff_galois N A.toNat ha b t hg' σ hσ n

end ZInQ.Contrib.HeckePrimeRationality.AllLevelPrincipalCoefficients

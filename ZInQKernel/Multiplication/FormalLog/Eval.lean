import ZInQKernel.Multiplication.FormalLog.Relations
import ZInQKernel.Multiplication.Local.Analytic

/-!
# Evaluating power series in two variables at points of the maximal ideal

Let `K` be a complete `ℤᵐ⁰`-valued field. A power series `f ∈ K⟦T₁, T₂⟧` with coefficients in
the valuation ring (`MvIntegral f`) converges at every `(t₁, t₂)` with `v(tᵢ) ≥ 1`: the term
`f_n t₁^{n₀} t₂^{n₁}` has valuation `≥ n₀ + n₁`. The value `ev2 t₁ t₂ f` is additive and
multiplicative (`ev2_add`, `ev2_mul`, the Cauchy product over the antidiagonals of
`Fin 2 →₀ ℕ`), so evaluation is a ring homomorphism on integral series.
-/

namespace ZInQ.Mult

open MvPowerSeries Filter WithZero

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

/-- The coefficients of `f ∈ K⟦T₁, T₂⟧` lie in the valuation ring. -/
def MvIntegral (f : MvPowerSeries (Fin 2) K) : Prop := ∀ n, 0 ≤ vK K (coeff n f)

/-- The monomial value `t₁^{n₀} t₂^{n₁}`. -/
def monoVal (t₁ t₂ : K) (n : Fin 2 →₀ ℕ) : K := t₁ ^ n 0 * t₂ ^ n 1

/-- The value `f(t₁, t₂) = Σ_n f_n t₁^{n₀} t₂^{n₁}`. -/
noncomputable def ev2 (t₁ t₂ : K) (f : MvPowerSeries (Fin 2) K) : K :=
  ∑' n, coeff n f * monoVal t₁ t₂ n

/-! ### Integral series -/

namespace MvIntegral

variable {f g : MvPowerSeries (Fin 2) K}

theorem vge (hf : MvIntegral f) (n : Fin 2 →₀ ℕ) : Vge (vK K) 0 (coeff n f) := hf n

theorem zero : MvIntegral (0 : MvPowerSeries (Fin 2) K) := fun n => by
  rw [map_zero]; exact Vge.zero 0

theorem one : MvIntegral (1 : MvPowerSeries (Fin 2) K) := fun n => by
  classical
  rw [coeff_one]
  split_ifs
  · show ((0 : ℤ) : WithTop ℤ) ≤ vK K 1; rw [(vK K).map_one]; rfl
  · exact Vge.zero 0

theorem add (hf : MvIntegral f) (hg : MvIntegral g) : MvIntegral (f + g) := fun n => by
  rw [map_add]; exact Vge.add (hf n) (hg n)

theorem neg (hf : MvIntegral f) : MvIntegral (-f) := fun n => by
  rw [map_neg]; exact Vge.neg (hf n)

theorem sub (hf : MvIntegral f) (hg : MvIntegral g) : MvIntegral (f - g) := fun n => by
  rw [map_sub]; exact Vge.sub (hf n) (hg n)

theorem mul (hf : MvIntegral f) (hg : MvIntegral g) : MvIntegral (f * g) := fun n => by
  rw [coeff_mul]
  exact Vge.sum_of_le fun x _ => ((hf.vge x.1).mul (hg.vge x.2)).mono (by simp)

theorem pow (hf : MvIntegral f) (k : ℕ) : MvIntegral (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact one
  | succ k ih => rw [pow_succ]; exact ih.mul hf

theorem C {a : K} (ha : 0 ≤ vK K a) : MvIntegral (MvPowerSeries.C a : MvPowerSeries (Fin 2) K) :=
  fun n => by
  classical
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact Vge.zero 0

theorem X (i : Fin 2) : MvIntegral (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) := fun n => by
  classical
  rw [coeff_X]
  split_ifs
  · show ((0 : ℤ) : WithTop ℤ) ≤ vK K 1; rw [(vK K).map_one]; rfl
  · exact Vge.zero 0

theorem ofNat (k : ℕ) : MvIntegral (k : MvPowerSeries (Fin 2) K) := by
  rw [← map_natCast (MvPowerSeries.C (σ := Fin 2) (R := K))]
  exact C (vge_natCast k)

theorem pderiv (hf : MvIntegral f) (i : Fin 2) : MvIntegral (MvPowerSeries.pderiv i f) :=
  fun n => by
  rw [coeff_pderiv]
  have h2 : Vge (vK K) 0 ((n i : K) + 1) := by
    have := vge_natCast (v := vK K) (n i + 1); push_cast at this; exact this
  exact ((hf.vge _).mul h2).mono (by simp)

end MvIntegral

/-! ### Convergence -/

theorem vge_monoVal {t₁ t₂ : K} (h₁ : 1 ≤ vK K t₁) (h₂ : 1 ≤ vK K t₂) (n : Fin 2 →₀ ℕ) :
    Vge (vK K) ((n 0 + n 1 : ℕ) : ℤ) (monoVal t₁ t₂ n) := by
  have := ((show Vge (vK K) 1 t₁ from h₁).pow (n 0)).mul ((show Vge (vK K) 1 t₂ from h₂).pow (n 1))
  exact this.mono (by push_cast; omega)

omit [Valued K ℤᵐ⁰] in
theorem monoVal_add (t₁ t₂ : K) (n m : Fin 2 →₀ ℕ) :
    monoVal t₁ t₂ (n + m) = monoVal t₁ t₂ n * monoVal t₁ t₂ m := by
  simp only [monoVal, Finsupp.coe_add, Pi.add_apply, pow_add]; ring

theorem finite_degree_lt (M : ℕ) : Set.Finite {n : Fin 2 →₀ ℕ | n 0 + n 1 < M} := by
  refine (Set.finite_Iic (Finsupp.single 0 M + Finsupp.single 1 M)).subset fun n hn => ?_
  simp only [Set.mem_ofPred_eq] at hn
  simp only [Set.mem_Iic, Finsupp.le_def, Fin.forall_fin_two, Finsupp.coe_add, Pi.add_apply]
  simp
  omega

/-- A family on `Fin 2 →₀ ℕ` whose `n`-th term has valuation `≥ n₀ + n₁ - c` is summable. -/
theorem summable_of_vge_degree [CompleteSpace K] {g : (Fin 2 →₀ ℕ) → K} (c : ℤ)
    (h : ∀ n, Vge (vK K) ((n 0 + n 1 : ℕ) - c) (g n)) : Summable g := by
  refine summable_of_vK_cofinite fun M => ?_
  rw [Filter.eventually_cofinite]
  refine (finite_degree_lt (M + c).toNat).subset fun n hn => ?_
  simp only [Set.mem_ofPred_eq] at hn ⊢
  by_contra hc
  exact hn ((h n).mono (by omega))

theorem summable_ev2 [CompleteSpace K] {t₁ t₂ : K} (h₁ : 1 ≤ vK K t₁) (h₂ : 1 ≤ vK K t₂)
    {f : MvPowerSeries (Fin 2) K} (hf : MvIntegral f) :
    Summable fun n => coeff n f * monoVal t₁ t₂ n :=
  summable_of_vge_degree 0 fun n => ((hf.vge n).mul (vge_monoVal h₁ h₂ n)).mono (by simp)

theorem hasSum_ev2 [CompleteSpace K] {t₁ t₂ : K} (h₁ : 1 ≤ vK K t₁) (h₂ : 1 ≤ vK K t₂)
    {f : MvPowerSeries (Fin 2) K} (hf : MvIntegral f) :
    HasSum (fun n => coeff n f * monoVal t₁ t₂ n) (ev2 t₁ t₂ f) :=
  (summable_ev2 h₁ h₂ hf).hasSum

/-! ### Evaluation is a ring homomorphism -/

theorem ev2_one : ev2 t₁ t₂ (1 : MvPowerSeries (Fin 2) K) = 1 := by
  classical
  rw [ev2, tsum_eq_single 0]
  · simp [monoVal]
  · intro n hn; rw [coeff_one, ite_eq_right hn, zero_mul]

theorem ev2_C (a : K) : ev2 t₁ t₂ (MvPowerSeries.C a : MvPowerSeries (Fin 2) K) = a := by
  classical
  rw [ev2, tsum_eq_single 0]
  · simp [monoVal]
  · intro n hn; rw [coeff_C, ite_eq_right hn, zero_mul]

theorem ev2_X_zero : ev2 t₁ t₂ (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = t₁ := by
  classical
  rw [ev2, tsum_eq_single (Finsupp.single 0 1)]
  · simp [monoVal]
  · intro n hn; rw [coeff_X, ite_eq_right hn, zero_mul]

theorem ev2_X_one : ev2 t₁ t₂ (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = t₂ := by
  classical
  rw [ev2, tsum_eq_single (Finsupp.single 1 1)]
  · simp [monoVal]
  · intro n hn; rw [coeff_X, ite_eq_right hn, zero_mul]

section Hom

variable [CompleteSpace K] {t₁ t₂ : K} (h₁ : 1 ≤ vK K t₁) (h₂ : 1 ≤ vK K t₂)
include h₁ h₂

theorem ev2_add {f g : MvPowerSeries (Fin 2) K} (hf : MvIntegral f) (hg : MvIntegral g) :
    ev2 t₁ t₂ (f + g) = ev2 t₁ t₂ f + ev2 t₁ t₂ g := by
  refine ((hasSum_ev2 h₁ h₂ hf).add (hasSum_ev2 h₁ h₂ hg)).tsum_eq ▸ ?_
  simp only [ev2, map_add, add_mul]

theorem ev2_neg {f : MvPowerSeries (Fin 2) K} (hf : MvIntegral f) :
    ev2 t₁ t₂ (-f) = -ev2 t₁ t₂ f := by
  refine ((hasSum_ev2 h₁ h₂ hf).neg).tsum_eq ▸ ?_
  simp only [ev2, map_neg, neg_mul]

theorem ev2_sub {f g : MvPowerSeries (Fin 2) K} (hf : MvIntegral f) (hg : MvIntegral g) :
    ev2 t₁ t₂ (f - g) = ev2 t₁ t₂ f - ev2 t₁ t₂ g := by
  rw [sub_eq_add_neg, ev2_add h₁ h₂ hf hg.neg, ev2_neg h₁ h₂ hg, sub_eq_add_neg]

theorem ev2_mul {f g : MvPowerSeries (Fin 2) K} (hf : MvIntegral f) (hg : MvIntegral g) :
    ev2 t₁ t₂ (f * g) = ev2 t₁ t₂ f * ev2 t₁ t₂ g := by
  have hprod : Summable fun x : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) =>
      (coeff x.1 f * monoVal t₁ t₂ x.1) * (coeff x.2 g * monoVal t₁ t₂ x.2) := by
    refine summable_of_vK_cofinite fun M => ?_
    rw [Filter.eventually_cofinite]
    refine ((finite_degree_lt M.toNat).prod (finite_degree_lt M.toNat)).subset ?_
    rintro ⟨n, m⟩ hnm
    simp only [Set.mem_ofPred_eq, Set.mem_prod] at hnm ⊢
    by_contra hc
    apply hnm
    have := ((hf.vge n).mul (vge_monoVal h₁ h₂ n)).mul ((hg.vge m).mul (vge_monoVal h₁ h₂ m))
    refine this.mono ?_
    rcases not_and_or.mp hc with h | h <;> omega
  rw [ev2, ev2, ev2, (summable_ev2 h₁ h₂ hf).tsum_mul_tsum_eq_tsum_sum_antidiagonal
    (summable_ev2 h₁ h₂ hg) hprod]
  congr 1; funext n
  rw [coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hx, monoVal_add]; ring

theorem ev2_pow {f : MvPowerSeries (Fin 2) K} (hf : MvIntegral f) (k : ℕ) :
    ev2 t₁ t₂ (f ^ k) = ev2 t₁ t₂ f ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, ev2_one]
  | succ k ih => rw [pow_succ, pow_succ, ev2_mul h₁ h₂ (hf.pow k) hf, ih]

end Hom

end ZInQ.Mult

namespace ZInQ.Mult

open MvPowerSeries WithZero

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

/-! ### Series in one of the two variables -/

/-- A series `g(T₁)` evaluates to `g(t₁)`. -/
theorem hasSum_ev2_subst_X_zero {g : PowerSeries K} {t₁ t₂ s : K}
    (hg : HasSum (fun k => PowerSeries.coeff k g * t₁ ^ k) s) :
    HasSum (fun n => coeff n (PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) g) *
      monoVal t₁ t₂ n) s := by
  classical
  rw [← (Finsupp.single_injective (0 : Fin 2)).hasSum_iff]
  · convert hg using 1
    funext k
    simp [PowerSeries.coeff_subst_single, monoVal]
  · intro n hn
    rw [PowerSeries.coeff_subst_single, ite_eq_right, zero_mul]
    exact fun h => hn ⟨n 0, h.symm⟩

/-- A series `g(T₂)` evaluates to `g(t₂)`. -/
theorem hasSum_ev2_subst_X_one {g : PowerSeries K} {t₁ t₂ s : K}
    (hg : HasSum (fun k => PowerSeries.coeff k g * t₂ ^ k) s) :
    HasSum (fun n => coeff n (PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) g) *
      monoVal t₁ t₂ n) s := by
  classical
  rw [← (Finsupp.single_injective (1 : Fin 2)).hasSum_iff]
  · convert hg using 1
    funext k
    simp [PowerSeries.coeff_subst_single, monoVal]
  · intro n hn
    rw [PowerSeries.coeff_subst_single, ite_eq_right, zero_mul]
    exact fun h => hn ⟨n 1, h.symm⟩

/-! ### The pieces of the formal group law are integral -/

variable {A : K}

theorem MvIntegral.chordSlope (hA : 0 ≤ vK K A) : MvIntegral (chordSlope A) := fun n => by
  rw [coeff_chordSlope, ← coeff_omegaSeries]; exact omegaSeries_integral hA _

theorem MvIntegral.omegaFst (hA : 0 ≤ vK K A) : MvIntegral (omegaFst A) := fun n => by
  rw [coeff_omegaFst]
  split_ifs
  · rw [← coeff_omegaSeries]; exact omegaSeries_integral hA _
  · exact Vge.zero 0

theorem MvIntegral.omegaSnd (hA : 0 ≤ vK K A) : MvIntegral (omegaSnd A) := fun n => by
  rw [coeff_omegaSnd]
  split_ifs
  · rw [← coeff_omegaSeries]; exact omegaSeries_integral hA _
  · exact Vge.zero 0

theorem MvIntegral.subst_X_derivative_omega (hA : 0 ≤ vK K A) (i : Fin 2) :
    MvIntegral (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K)
      (PowerSeries.derivative (R := K) (omegaSeries A))) := fun n => by
  classical
  rw [PowerSeries.coeff_subst_single]
  split_ifs
  · rw [PowerSeries.coeff_derivative]
    have h2 : Vge (vK K) 0 ((n i : K) + 1) := by
      have := vge_natCast (v := vK K) (n i + 1); push_cast at this; exact this
    exact ((show Vge (vK K) 0 _ from omegaSeries_integral hA (n i + 1)).mul h2).mono (by simp)
  · exact Vge.zero 0

theorem MvIntegral.chordInv (hA : 0 ≤ vK K A) : MvIntegral (chordInv A) := by
  classical
  have hD : MvIntegral (1 + MvPowerSeries.C A * ZInQ.Mult.chordSlope A ^ 2) :=
    MvIntegral.one.add ((MvIntegral.C hA).mul ((MvIntegral.chordSlope hA).pow 2))
  intro n
  induction n using WellFoundedLT.induction with
  | _ n ih =>
    rw [ZInQ.Mult.chordInv, coeff_invOfUnit, inv_one, Units.val_one]
    split_ifs
    · show ((0 : ℤ) : WithTop ℤ) ≤ vK K 1; rw [(vK K).map_one]; rfl
    · rw [neg_one_mul]
      refine Vge.neg (Vge.sum_of_le fun x _ => ?_)
      split_ifs with hlt
      · exact ((hD.vge x.1).mul (show Vge (vK K) 0 _ from ih x.2 hlt)).mono (by simp)
      · exact Vge.zero 0

theorem MvIntegral.formalAdd (hA : 0 ≤ vK K A) : MvIntegral (formalAdd A) := by
  rw [formalAdd_eq]
  exact (((MvIntegral.X 0).add (MvIntegral.X 1)).add
    (((((MvIntegral.ofNat 2).mul (MvIntegral.C hA)).mul (MvIntegral.chordSlope hA)).mul
      ((MvIntegral.omegaFst hA).sub ((MvIntegral.chordSlope hA).mul (MvIntegral.X 0)))).mul
        (MvIntegral.chordInv hA)))

end ZInQ.Mult

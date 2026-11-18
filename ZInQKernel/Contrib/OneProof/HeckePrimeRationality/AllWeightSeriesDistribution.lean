import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllWeightSeriesLevelMaps

/-!
# Absolute complete-fibre distribution and congruence covariance

The genuine Euclidean residue-grid bijection reindexes the absolutely
convergent class series. A complete t²-point fibre sums to t^k times the lower
series. Integral row covariance is proved on the unchanged summands.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups Matrix ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.AllWeightSeriesTrace
open AllWeightPrincipalEisensteinForms AllWeightLatticeEisenstein EisensteinWeightTwo

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- Absolute reindexing of the entire translated class into its complete fibre. -/
theorem class_fiber_sum (t N k : ℕ) (ht : 0 < t) (hN : 0 < N) (hk : 3 ≤ k)
    (a b : ℤ) (τ : ℍ) :
    (∑ R : Fin t × Fin t, ∑' q : ℤ × ℤ,
      EisensteinSeries.eisSummand (k : ℤ)
        ![a+N*(R.1 : ℕ)+(t*N : ℕ)*q.1,b+N*(R.2 : ℕ)+(t*N : ℕ)*q.2] τ) =
      ∑' q : ℤ × ℤ, EisensteinSeries.eisSummand (k : ℤ) ![a+N*q.1,b+N*q.2] τ := by
  have hs := congruence_summable_all N hN k hk a b τ
  have hg := (residueGridEquiv t ht).hasSum_iff.mpr hs.hasSum
  have he := hg.summable.tsum_prod
  rw [hg.tsum_eq] at he
  conv_rhs at he => rw [tsum_fintype]
  have hterm (R : Fin t × Fin t) (q : ℤ × ℤ) :
      (![a+(N : ℤ)*(residueGridEquiv t ht (R,q)).1,
         b+(N : ℤ)*(residueGridEquiv t ht (R,q)).2] : Fin 2 → ℤ) =
      ![a+N*(R.1 : ℕ)+(t*N : ℕ)*q.1,b+N*(R.2 : ℕ)+(t*N : ℕ)*q.2] := by
    rw [residueGridEquiv_apply]
    ext i
    fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one] <;> push_cast <;> ring
  simp only [Function.comp_apply] at he
  simp_rw [hterm] at he
  exact he.symm

def completeFiberK (t N : ℕ) (ht : 0 < t) (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k) (a b : ℤ) :
    _root_.ModularForm (ΓP (t*N)) (k : ℤ) :=
  ∑ R : Fin t × Fin t, seriesForm (t*N) (by nlinarith) k hk
    ![a+N*(R.1 : ℕ),b+N*(R.2 : ℕ)]

/-- Literal all-weight distribution, with the exact t^k normalization. -/
theorem completeFiberK_restriction (t N : ℕ) (ht : 0 < t) (h3 : 3 ≤ N)
    (k : ℕ) (hk : 3 ≤ k) (a b : ℤ) :
    completeFiberK t N ht h3 k hk a b = restrictionK N (t*N) k (dvd_mul_left N t)
      ((t : ℂ)^k • seriesForm N h3 k hk ![a,b]) := by
  apply _root_.ModularForm.ext
  intro τ
  rw [restrictionK_apply]
  simp only [completeFiberK, sum_apply, smul_apply, smul_eq_mul, seriesForm_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, seriesValue, ← Finset.mul_sum]
  rw [class_fiber_sum t N k ht (by omega) hk a b τ, Nat.cast_mul, mul_pow, mul_assoc]

theorem normalizedTraceK_completeFiber (t N : ℕ) (ht : 0 < t) (h3 : 3 ≤ N)
    (k : ℕ) (hk : 3 ≤ k) (a b : ℤ) :
    normalizedTraceK N (t*N) k (Nat.mul_pos ht (by omega)) (completeFiberK t N ht h3 k hk a b) =
      (t : ℂ)^k • seriesForm N h3 k hk ![a,b] := by
  rw [completeFiberK_restriction, normalizedTraceK_restriction]

/-- Vector-indexed actual class summand. -/
def classTerm (N k : ℕ) (a q : Fin 2 → ℤ) (τ : ℍ) : ℂ :=
  EisensteinSeries.eisSummand (k : ℤ) (a + (N : ℤ) • q) τ

theorem seriesValue_vector (N k : ℕ) (a : Fin 2 → ℤ) (τ : ℍ) :
    seriesValue N k (a 0) (a 1) τ = (N : ℂ)^k * ∑' q : Fin 2 → ℤ, classTerm N k a q τ := by
  unfold seriesValue
  rw [← (finTwoArrowEquiv ℤ).tsum_eq]
  congr 1

/-- Actual all-weight special-linear covariance by the integral grid equivalence. -/
theorem seriesValue_SL (N k : ℕ) (a : Fin 2 → ℤ) (γ : SL(2, ℤ)) (τ : ℍ) :
    seriesValue N k (a 0) (a 1) (γ • τ) = (slDenom γ τ)^k *
      seriesValue N k ((a ᵥ* γ.1) 0) ((a ᵥ* γ.1) 1) τ := by
  rw [seriesValue_vector, seriesValue_vector]
  have ht (q : Fin 2 → ℤ) : classTerm N k a q (γ • τ) = (slDenom γ τ)^k *
      classTerm N k (a ᵥ* γ.1) (vecMulEquiv γ q) τ := by
    rw [classTerm, EisensteinSeries.eisSummand_SL2_apply, Matrix.add_vecMul, Matrix.smul_vecMul]
    rfl
  simp_rw [ht, tsum_mul_left]
  have he := (vecMulEquiv γ).tsum_eq (fun q => classTerm N k (a ᵥ* γ.1) q τ)
  change (∑' q, classTerm N k (a ᵥ* γ.1) (vecMulEquiv γ q) τ) = _ at he
  rw [he]
  ring

theorem seriesForm_slash (N : ℕ) (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (a : Fin 2 → ℤ) (γ : SL(2, ℤ)) :
    ⇑(seriesForm N h3 k hk a) ∣[(k : ℤ)] γ = ⇑(seriesForm N h3 k hk (a ᵥ* γ.1)) := by
  have hl : ⇑(seriesForm N h3 k hk a) = fun τ => seriesValue N k (a 0) (a 1) τ :=
    funext fun τ => seriesForm_apply N h3 k hk a τ
  have hr : ⇑(seriesForm N h3 k hk (a ᵥ* γ.1)) =
      fun τ => seriesValue N k ((a ᵥ* γ.1) 0) ((a ᵥ* γ.1) 1) τ :=
    funext fun τ => seriesForm_apply N h3 k hk _ τ
  rw [hl,hr]
  funext τ
  rw [ModularForm.SL_slash_apply, seriesValue_SL]
  have hd : slDenom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
  change (slDenom γ τ)^k * _ * (slDenom γ τ)^(-(k : ℤ)) = _
  rw [_root_.zpow_neg, _root_.zpow_natCast]
  field_simp

/-- Congruent all-label series forms agree by an actual translated-grid bijection. -/
theorem seriesForm_eq_of_congr (N : ℕ) (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (a b c d : ℤ) (ha : (a : ZMod N) = c) (hb : (b : ZMod N) = d) :
    seriesForm N h3 k hk ![a,b] = seriesForm N h3 k hk ![c,d] := by
  have hd0 : (N : ℤ) ∣ a-c := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
    simp only [Int.cast_sub, ha, sub_self]
  have hd1 : (N : ℤ) ∣ b-d := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
    simp only [Int.cast_sub, hb, sub_self]
  obtain ⟨r,hr⟩ := hd0
  obtain ⟨s,hs⟩ := hd1
  have ha0 : a = c+N*r := by linarith
  have hb0 : b = d+N*s := by linarith
  apply _root_.ModularForm.ext
  intro τ
  rw [seriesForm_apply, seriesForm_apply]
  unfold seriesValue
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ha0,hb0]
  have he := (Equiv.addLeft (r,s)).tsum_eq (fun q : ℤ × ℤ =>
    EisensteinSeries.eisSummand (k : ℤ) ![c+N*q.1,d+N*q.2] τ)
  congr 1
  rw [← he]
  apply tsum_congr
  intro q
  have hvec : (![c+N*r+N*q.1,d+N*s+N*q.2] : Fin 2 → ℤ) =
      ![c+N*((Equiv.addLeft (r,s)) q).1,d+N*((Equiv.addLeft (r,s)) q).2] := by
    ext i
    have heq : (Equiv.addLeft (r,s)) q = (r+q.1,s+q.2) := rfl
    rw [heq]
    fin_cases i <;> dsimp <;> ring
  rw [hvec]

end ZInQ.Contrib.HeckePrimeRationality.AllWeightSeriesTrace

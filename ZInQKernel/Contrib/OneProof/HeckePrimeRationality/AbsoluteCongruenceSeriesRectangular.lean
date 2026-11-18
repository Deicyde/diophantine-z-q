import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllWeightRawSeriesBridge
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelPrincipalRationalGL2Transport

/-!
# Absolute congruence-grid rectangular identities

All lattice rearrangements are preceded by the actual all-label absolute
summability theorem at weights k≥3. The unscaled inverse-power grid is kept
literal, including its zero argument and even bad classes. One-dimensional
residue partitions give both diagonal laws, while the full finite grid gives
honest level refinement. No weight-two absolute convergence is asserted.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

open Complex Filter Set Function
open scoped Real UpperHalfPlane BigOperators MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.AbsoluteCongruenceSeries

open RectangularThetaLattice AllWeightSeriesTrace AllWeightLatticeEisenstein
open AllWeightPrincipalEisensteinForms EisensteinWeightTwo
open CongruenceSubgroup Matrix.SpecialLinearGroup

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (Matrix.SpecialLinearGroup.mapGL ℝ)

/-- The actual unscaled congruence-grid inverse-power value at every integer label. -/
def rawValue (N k : ℕ) (P : ℤ × ℤ) (τ : ℍ) : ℂ :=
  ∑' q : ℤ × ℤ,EisensteinSeries.eisSummand (k : ℤ) ![P.1+N*q.1,P.2+N*q.2] τ

def rawFun (N k : ℕ) (P : ℤ × ℤ) : ℍ → ℂ := rawValue N k P

lemma raw_summable (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k) (P : ℤ × ℤ) (τ : ℍ) :
    Summable (fun q : ℤ × ℤ => EisensteinSeries.eisSummand (k : ℤ) ![P.1+N*q.1,P.2+N*q.2] τ) :=
  congruence_summable_all N hN k hk P.1 P.2 τ

/-- Split only the second integer coordinate into a guarded finite residue and quotient. -/
def secondResidue (n : ℕ) (hn : 0<n) : (Fin n × (ℤ × ℤ)) ≃ (ℤ × ℤ) where
  toFun p := (p.2.1,residueEquiv n hn (p.1,p.2.2))
  invFun p := ((residueEquiv n hn).symm p.2 |>.1,(p.1,(residueEquiv n hn).symm p.2 |>.2))
  left_inv := by
    rintro ⟨j,c,d⟩
    simp
  right_inv := by
    intro p
    apply Prod.ext
    · rfl
    · exact (residueEquiv n hn).apply_symm_apply p.2

lemma secondResidue_apply (n : ℕ) (hn : 0<n) (p : Fin n × (ℤ × ℤ)) :
    secondResidue n hn p=(p.2.1,(p.1 : ℕ)+(n : ℤ)*p.2.2) := rfl

/-- The corresponding first-coordinate residue partition. -/
def firstResidue (n : ℕ) (hn : 0<n) : (Fin n × (ℤ × ℤ)) ≃ (ℤ × ℤ) where
  toFun p := (residueEquiv n hn (p.1,p.2.1),p.2.2)
  invFun p := ((residueEquiv n hn).symm p.1 |>.1,((residueEquiv n hn).symm p.1 |>.2,p.2))
  left_inv := by
    rintro ⟨j,c,d⟩
    simp
  right_inv := by
    intro p
    apply Prod.ext
    · exact (residueEquiv n hn).apply_symm_apply p.1
    · rfl

lemma firstResidue_apply (n : ℕ) (hn : 0<n) (p : Fin n × (ℤ × ℤ)) :
    firstResidue n hn p=((p.1 : ℕ)+(n : ℤ)*p.2.1,p.2.2) := rfl

lemma summand_up (n : ℕ) (hn : 0<n) (k : ℕ) (a b : ℤ) (τ : ℍ) :
    EisensteinSeries.eisSummand (k : ℤ) ![a,b] (upTau n hn τ)=
      EisensteinSeries.eisSummand (k : ℤ) ![(n : ℤ)*a,b] τ := by
  simp only [EisensteinSeries.eisSummand,Matrix.cons_val_zero,Matrix.cons_val_one,upTau_coe]
  congr 1
  push_cast
  ring

/-- Inverse scaling is a literal term identity, also when the integer vector is zero. -/
lemma summand_down (n : ℕ) (hn : 0<n) (k : ℕ) (a b : ℤ) (τ : ℍ) :
    EisensteinSeries.eisSummand (k : ℤ) ![a,b] (downTau n hn τ)=
      (n : ℂ)^k*EisensteinSeries.eisSummand (k : ℤ) ![a,(n : ℤ)*b] τ := by
  have h := scaled_summand n hn k a b (downTau n hn τ)
  have hnC : (n : ℂ)≠0 := by exact_mod_cast hn.ne'
  have he : EisensteinSeries.eisSummand (k : ℤ) ![(n : ℤ)*a,(n : ℤ)*b] (downTau n hn τ)=
      EisensteinSeries.eisSummand (k : ℤ) ![a,(n : ℤ)*b] τ := by
    simp only [EisensteinSeries.eisSummand,Matrix.cons_val_zero,Matrix.cons_val_one,downTau_coe]
    congr 1
    push_cast
    field_simp [hnC]
  rw [he] at h
  exact h.symm

/-- Actual n-point real rectangular partition, not an n² square-grid shortcut. -/
theorem raw_up (n N k : ℕ) (hn : 0<n) (hN : 0<N) (hk : 3≤k) (P : ℤ × ℤ) (τ : ℍ) :
    rawValue N k P (upTau n hn τ)=
      ∑ j : Fin n,rawValue (n*N) k ((n : ℤ)*P.1,P.2+(N : ℤ)*(j : ℕ)) τ := by
  have hs := raw_summable N hN k hk P (upTau n hn τ)
  have hg := (secondResidue n hn).hasSum_iff.mpr hs.hasSum
  have he := hg.summable.tsum_prod
  rw [hg.tsum_eq] at he
  conv_rhs at he => rw [tsum_fintype]
  have ht (j : Fin n) (q : ℤ × ℤ) :
      EisensteinSeries.eisSummand (k : ℤ)
        ![P.1+N*(secondResidue n hn (j,q)).1,P.2+N*(secondResidue n hn (j,q)).2] (upTau n hn τ)=
      EisensteinSeries.eisSummand (k : ℤ)
        ![(n : ℤ)*P.1+(n*N : ℕ)*q.1,P.2+(N : ℤ)*(j : ℕ)+(n*N : ℕ)*q.2] τ := by
    rw [summand_up,secondResidue_apply]
    congr 1
    ext i
    fin_cases i <;> dsimp <;> ring
  simp only [Function.comp_apply] at he
  simp_rw [ht] at he
  exact he

/-- Actual inverse rectangular partition, with its derived n^k function-value factor. -/
theorem raw_down (n N k : ℕ) (hn : 0<n) (hN : 0<N) (hk : 3≤k) (P : ℤ × ℤ) (τ : ℍ) :
    rawValue N k P (downTau n hn τ)=
      (n : ℂ)^k*∑ j : Fin n,rawValue (n*N) k (P.1+(N : ℤ)*(j : ℕ),(n : ℤ)*P.2) τ := by
  have hs := raw_summable N hN k hk P (downTau n hn τ)
  have hg := (firstResidue n hn).hasSum_iff.mpr hs.hasSum
  have he := hg.summable.tsum_prod
  rw [hg.tsum_eq] at he
  conv_rhs at he => rw [tsum_fintype]
  have ht (j : Fin n) (q : ℤ × ℤ) :
      EisensteinSeries.eisSummand (k : ℤ)
        ![P.1+N*(firstResidue n hn (j,q)).1,P.2+N*(firstResidue n hn (j,q)).2] (downTau n hn τ)=
      (n : ℂ)^k*EisensteinSeries.eisSummand (k : ℤ)
        ![P.1+(N : ℤ)*(j : ℕ)+(n*N : ℕ)*q.1,(n : ℤ)*P.2+(n*N : ℕ)*q.2] τ := by
    rw [summand_down,firstResidue_apply]
    congr 2
    ext i
    fin_cases i <;> dsimp <;> ring
  simp only [Function.comp_apply] at he
  simp_rw [ht,tsum_mul_left] at he
  rw [← Finset.mul_sum] at he
  exact he

/-- Absolute full-grid refinement retains every congruence class. -/
theorem raw_refine (t N k : ℕ) (ht : 0<t) (hN : 0<N) (hk : 3≤k) (P : ℤ × ℤ) (τ : ℍ) :
    (∑ R : Fin t × Fin t,rawValue (t*N) k
      (P.1+(N : ℤ)*(R.1 : ℕ),P.2+(N : ℤ)*(R.2 : ℕ)) τ)=rawValue N k P τ :=
  class_fiber_sum t N k ht hN hk P.1 P.2 τ

/-- Signed label periodicity comes from an actual translated absolute grid. -/
theorem raw_shift (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k) (P S : ℤ × ℤ) (τ : ℍ) :
    rawValue N k (P.1+(N : ℤ)*S.1,P.2+(N : ℤ)*S.2) τ=rawValue N k P τ := by
  have hs := raw_summable N hN k hk P τ
  have hg := (Equiv.addLeft S).hasSum_iff.mpr hs.hasSum
  have ht (q : ℤ × ℤ) :
      EisensteinSeries.eisSummand (k : ℤ)
        ![P.1+N*(Equiv.addLeft S q).1,P.2+N*(Equiv.addLeft S q).2] τ =
      EisensteinSeries.eisSummand (k : ℤ)
        ![P.1+(N : ℤ)*S.1+N*q.1,P.2+(N : ℤ)*S.2+N*q.2] τ := by
    have heq : Equiv.addLeft S q=(S.1+q.1,S.2+q.2) := rfl
    rw [heq]
    congr 1
    ext i
    fin_cases i <;> dsimp <;> ring
  have he := hg.tsum_eq
  simp only [Function.comp_apply] at he
  simp_rw [ht] at he
  exact he

/-- Integral covariance of the unchanged all-label raw series. -/
theorem raw_SL_value (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k) (P : ℤ × ℤ)
    (γ : SL(2,ℤ)) (τ : ℍ) :
    rawValue N k P (γ • τ)=(slDenom γ τ)^k*rawValue N k (ThetaFiveTorsion.act P γ) τ := by
  have hs := raw_summable N hN k hk P (γ • τ)
  have h := seriesValue_SL N k ![P.1,P.2] γ τ
  have hr : Matrix.vecMul ![P.1,P.2] γ.1 = ![(ThetaFiveTorsion.act P γ).1,(ThetaFiveTorsion.act P γ).2] := by
    ext i
    fin_cases i <;> simp [Matrix.vecMul,Matrix.vecHead,Matrix.vecTail,ThetaFiveTorsion.act]
  rw [hr] at h
  change (N : ℂ)^k*rawValue N k P (γ • τ)=
    (slDenom γ τ)^k*((N : ℂ)^k*rawValue N k (ThetaFiveTorsion.act P γ) τ) at h
  have hc : (N : ℂ)^k≠0 := pow_ne_zero k (by exact_mod_cast hN.ne')
  have he : rawValue N k P (γ • τ)=(slDenom γ τ)^k*rawValue N k (ThetaFiveTorsion.act P γ) τ := by
    apply mul_left_cancel₀ hc
    simpa only [mul_assoc,mul_left_comm] using h
  have hsum := hs.hasSum
  change HasSum (fun q : ℤ × ℤ => EisensteinSeries.eisSummand (k : ℤ)
    ![P.1+N*q.1,P.2+N*q.2] (γ • τ)) (rawValue N k P (γ • τ)) at hsum
  rw [he] at hsum
  exact hs.hasSum.unique hsum

theorem raw_SL (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k) (P : ℤ × ℤ) (γ : SL(2,ℤ)) :
    rawFun N k P ∣[(k : ℤ)] γ=rawFun N k (ThetaFiveTorsion.act P γ) := by
  funext τ
  simp only [rawFun]
  rw [_root_.ModularForm.SL_slash_apply,raw_SL_value N hN k hk P γ τ]
  have hd : slDenom γ τ≠0 := UpperHalfPlane.denom_ne_zero _ τ
  change (slDenom γ τ)^k*_*(slDenom γ τ)^(-(k : ℤ))=_
  rw [_root_.zpow_neg,_root_.zpow_natCast]
  field_simp

theorem raw_Gamma (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k) (P : ℤ × ℤ)
    (γ : GL (Fin 2) ℝ) (hγ : γ∈(ΓP N)) : rawFun N k P ∣[(k : ℤ)] γ=rawFun N k P := by
  obtain ⟨g,hg,rfl⟩ := hγ
  change g∈CongruenceSubgroup.Gamma N at hg
  have hm : mapGL ℝ g=(g : GL (Fin 2) ℝ) := by ext i j;rfl
  rw [hm,← _root_.ModularForm.SL_slash,raw_SL N hN k hk P g]
  obtain ⟨⟨r,hr⟩,⟨s,hs⟩⟩ := AllLevelPrincipal.congr_act_Gamma hg P
  have he : ThetaFiveTorsion.act P g=(P.1+N*r,P.2+N*s) := Prod.ext (by linarith) (by linarith)
  funext τ
  rw [he]
  exact raw_shift N hN k hk P (r,s) τ

/-- At level 3N all needed modular fields already exist; the absolute finite
partition gives precisely the unscaled level-N function. -/
def upperRawForm (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k) (P : ℤ × ℤ) :
    _root_.ModularForm (ΓP (3*N)) (k : ℤ) :=
  ∑ R : Fin 3 × Fin 3,rawClassForm (3*N) (by omega) k hk
    ![P.1+(N : ℤ)*(R.1 : ℕ),P.2+(N : ℤ)*(R.2 : ℕ)]

lemma upperRawForm_apply (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k) (P : ℤ × ℤ) (τ : ℍ) :
    upperRawForm N hN k hk P τ=rawValue N k P τ := by
  simp only [upperRawForm,_root_.sum_apply,rawClassForm_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact class_fiber_sum 3 N k (by omega) hN hk P.1 P.2 τ

/-- Genuine actual raw-series form for every positive level, including N=1,2.
The modular extension uses proved invariance and the arithmetic cusp relation,
not a trace-image or a wanted modularity premise. -/
def absoluteClassForm (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k) (P : ℤ × ℤ) :
    _root_.ModularForm (ΓP N) (k : ℤ) := by
  let _ : NeZero N := ⟨hN.ne'⟩
  let _ : NeZero (3*N) := ⟨(Nat.mul_pos (by omega) hN).ne'⟩
  let F := upperRawForm N hN k hk P
  have he : (⇑F : ℍ → ℂ)=rawFun N k P := funext (upperRawForm_apply N hN k hk P)
  refine _root_.ModularForm.ofSlashInvariant Subgroup.IsArithmetic.isCusp_of_isCusp F ?_
  intro γ hγ
  rw [he]
  exact raw_Gamma N hN k hk P γ hγ

lemma absoluteClassForm_apply (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k) (P : ℤ × ℤ) (τ : ℍ) :
    absoluteClassForm N hN k hk P τ=rawValue N k P τ := by
  unfold absoluteClassForm
  rw [_root_.ModularForm.coe_ofSlashInvariant]
  exact upperRawForm_apply N hN k hk P τ

/-- The independently generated absolute congruence-series subspace. -/
def absoluteSeriesSpan (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k) :
    Submodule ℂ (_root_.ModularForm (ΓP N) (k : ℤ)) :=
  Submodule.span ℂ (Set.range (absoluteClassForm N hN k hk))

lemma absoluteClassForm_mem (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k) (P : ℤ × ℤ) :
    absoluteClassForm N hN k hk P∈absoluteSeriesSpan N hN k hk := Submodule.subset_span ⟨P,rfl⟩

/-- Bad congruence classes retain the actual lattice G_k, with the exact raw
N^-k factor. In particular, no even bad class is set to zero. -/
theorem absoluteClassForm_bad_apply (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k)
    (P : ℤ × ℤ) (hP : (N : ℤ)∣P.1 ∧ (N : ℤ)∣P.2) (τ : ℍ) :
    absoluteClassForm N hN k hk P τ=((N : ℂ)^k)⁻¹*(ThetaWeierstrass.periodPair τ).G k := by
  rw [absoluteClassForm_apply]
  have h := bad_row_eq_lattice N hN k hk P.1 P.2 hP τ
  change (N : ℂ)^k*rawValue N k P τ=(ThetaWeierstrass.periodPair τ).G k at h
  have hc : (N : ℂ)^k≠0 := pow_ne_zero k (by exact_mod_cast hN.ne')
  calc
    rawValue N k P τ=((N : ℂ)^k)⁻¹*((N : ℂ)^k*rawValue N k P τ) := by
      rw [← mul_assoc,inv_mul_cancel₀ hc,one_mul]
    _ = _ := by rw [h]

/-- Odd bad classes vanish by the actual lattice-negation theorem. -/
theorem absoluteClassForm_bad_odd_zero (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k)
    (hodd : Odd k) (P : ℤ × ℤ) (hP : (N : ℤ)∣P.1 ∧ (N : ℤ)∣P.2) :
    absoluteClassForm N hN k hk P=0 := by
  apply _root_.ModularForm.ext
  intro τ
  rw [absoluteClassForm_bad_apply N hN k hk P hP τ,PeriodPair.G_eq_zero_of_odd _ k hodd,mul_zero]
  rfl

/-- Exact finite-grid restriction of the raw modular generator. -/
theorem absoluteClassForm_refine (t N k : ℕ) (ht : 0<t) (hN : 0<N) (hk : 3≤k) (P : ℤ × ℤ) :
    restrictionK N (t*N) k (Nat.dvd_mul_left N t) (absoluteClassForm N hN k hk P)=
      ∑ R : Fin t × Fin t,absoluteClassForm (t*N) (Nat.mul_pos ht hN) k hk
        (P.1+(N : ℤ)*(R.1 : ℕ),P.2+(N : ℤ)*(R.2 : ℕ)) := by
  apply _root_.ModularForm.ext
  intro τ
  rw [restrictionK_apply,absoluteClassForm_apply]
  simp only [_root_.sum_apply,absoluteClassForm_apply]
  exact (raw_refine t N k ht hN hk P τ).symm

/-- Honest forward restriction preserves the absolute-grid series span. -/
theorem restriction_absoluteSeriesSpan (t N k : ℕ) (ht : 0<t) (hN : 0<N) (hk : 3≤k)
    {f : _root_.ModularForm (ΓP N) (k : ℤ)} (hf : f∈absoluteSeriesSpan N hN k hk) :
    restrictionK N (t*N) k (Nat.dvd_mul_left N t) f∈absoluteSeriesSpan (t*N) (Nat.mul_pos ht hN) k hk := by
  have hle : absoluteSeriesSpan N hN k hk ≤
      (absoluteSeriesSpan (t*N) (Nat.mul_pos ht hN) k hk).comap
        (restrictionK N (t*N) k (Nat.dvd_mul_left N t)) := by
    apply Submodule.span_le.mpr
    rintro F ⟨P,rfl⟩
    change restrictionK N (t*N) k (Nat.dvd_mul_left N t) (absoluteClassForm N hN k hk P)∈
      absoluteSeriesSpan (t*N) (Nat.mul_pos ht hN) k hk
    rw [absoluteClassForm_refine t N k ht hN hk P]
    exact Submodule.sum_mem _ fun R _ => absoluteClassForm_mem _ _ _ _ _
  exact hle hf

end ZInQ.Contrib.HeckePrimeRationality.AbsoluteCongruenceSeries

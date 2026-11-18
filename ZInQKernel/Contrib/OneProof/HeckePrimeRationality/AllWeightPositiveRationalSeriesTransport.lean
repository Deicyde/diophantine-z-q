import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AbsoluteCongruenceSeriesRectangular
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ActualMixedSpanBridge

/-!
# Positive rational transport of actual absolute congruence-series spans

The space is generated independently by the literal absolutely convergent
raw class series at every positive level and weight k≥3. All positive-rational
matrix atoms have actual modular representatives and finite constant
coefficients. Bridges identify the established normalized series span and
its actual unscaled weight-three class-series counterpart; none is replaced
by a homogeneous torsion-product span.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

open Complex Function Set
open scoped Real UpperHalfPlane BigOperators MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.AbsoluteSeriesRationalTransport

open AbsoluteCongruenceSeries RationalGaussian RationalPrincipalTransport
open TorsionRectangularHomogeneous TorsionRectangularScale AllWeightSeriesTrace
open CongruenceSubgroup Matrix.SpecialLinearGroup

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (Matrix.SpecialLinearGroup.mapGL ℝ)

/-- Exact binding to the frozen N^-k raw normalization bridge. -/
theorem absoluteClassForm_eq_rawClassForm (N : ℕ) (h3 : 3≤N) (k : ℕ) (hk : 3≤k) (P : ℤ × ℤ) :
    absoluteClassForm N (by omega) k hk P=rawClassForm N h3 k hk ![P.1,P.2] := by
  apply _root_.ModularForm.ext
  intro τ
  rw [absoluteClassForm_apply,rawClassForm_apply]
  rfl

/-- The established normalized form is N^k times the actual unscaled form. -/
theorem seriesForm_eq_scale_absolute (N : ℕ) (h3 : 3≤N) (k : ℕ) (hk : 3≤k) (a : Fin 2 → ℤ) :
    seriesForm N h3 k hk a=(N : ℂ)^k • absoluteClassForm N (by omega) k hk (a 0,a 1) := by
  apply _root_.ModularForm.ext
  intro τ
  rw [seriesForm_apply,_root_.smul_apply,smul_eq_mul,absoluteClassForm_apply]
  rfl

/-- Produced equality with the established absolute-series generator space. -/
theorem absoluteSeriesSpan_eq_seriesSpanK (N : ℕ) (h3 : 3≤N) (k : ℕ) (hk : 3≤k) :
    absoluteSeriesSpan N (by omega) k hk=seriesSpanK N h3 k hk := by
  rw [← rawClassForm_span_eq]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro F ⟨P,rfl⟩
    rw [absoluteClassForm_eq_rawClassForm N h3 k hk P]
    exact Submodule.subset_span ⟨![P.1,P.2],rfl⟩
  · apply Submodule.span_le.mpr
    rintro F ⟨a,rfl⟩
    have he : rawClassForm N h3 k hk a=absoluteClassForm N (by omega) k hk (a 0,a 1) := by
      apply _root_.ModularForm.ext
      intro τ
      rw [rawClassForm_apply,absoluteClassForm_apply]
      rfl
    rw [he]
    exact absoluteClassForm_mem _ _ _ _ _

/-- The established weight-three class form is literally the unscaled raw sum. -/
theorem absoluteClassForm_three_eq_classSeriesForm (N : ℕ) (hN : 0<N) (P : ℤ × ℤ) :
    absoluteClassForm N hN 3 (by omega) P=MixedWeightThreeAddition.classSeriesForm N hN P.1 P.2 := by
  apply _root_.ModularForm.ext
  intro τ
  rw [absoluteClassForm_apply,MixedWeightThreeAddition.classSeriesForm_apply]
  rfl

/-- The true classSeriesSpan, with no product-span or desired EqSpan assumption. -/
theorem absoluteSeriesSpan_three_eq_classSeriesSpan (N : ℕ) (hN : 0<N) :
    absoluteSeriesSpan N hN 3 (by omega)=MixedWeightThreeAddition.classSeriesSpan N hN := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro F ⟨P,rfl⟩
    rw [absoluteClassForm_three_eq_classSeriesForm]
    exact Submodule.subset_span ⟨P,rfl⟩
  · apply Submodule.span_le.mpr
    rintro F ⟨P,rfl⟩
    change MixedWeightThreeAddition.classSeriesForm N hN P.1 P.2∈absoluteSeriesSpan N hN 3 (by omega)
    rw [← absoluteClassForm_three_eq_classSeriesForm N hN P]
    exact absoluteClassForm_mem _ _ _ _ _

/-- The actual integral translate/restrict sends raw generators through the row action. -/
theorem integral_absoluteClassForm (γ : SL(2,ℤ)) (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k) (P : ℤ × ℤ) :
    integralMap γ N k (absoluteClassForm N hN k hk P)=
      absoluteClassForm N hN k hk (ThetaFiveTorsion.act P γ) := by
  apply _root_.ModularForm.ext
  intro τ
  rw [integralMap_apply]
  have hm : mapGL ℝ γ=(γ : GLR) := by ext i j;rfl
  have hs := congrFun (raw_SL N hN k hk P γ) τ
  rw [_root_.ModularForm.SL_slash,← hm] at hs
  have hl : (absoluteClassForm N hN k hk P : ℍ → ℂ)=rawFun N k P := funext (absoluteClassForm_apply N hN k hk P)
  have hr : (absoluteClassForm N hN k hk (ThetaFiveTorsion.act P γ) : ℍ → ℂ)=rawFun N k (ThetaFiveTorsion.act P γ) :=
    funext (absoluteClassForm_apply N hN k hk (ThetaFiveTorsion.act P γ))
  rw [hl,hr]
  exact hs

theorem integral_absoluteSeriesSpan (γ : SL(2,ℤ)) (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k)
    {f : _root_.ModularForm (ΓP N) (k : ℤ)} (hf : f∈absoluteSeriesSpan N hN k hk) :
    integralMap γ N k f∈absoluteSeriesSpan N hN k hk := by
  have hle : absoluteSeriesSpan N hN k hk ≤ (absoluteSeriesSpan N hN k hk).comap (integralMap γ N k) := by
    apply Submodule.span_le.mpr
    rintro F ⟨P,rfl⟩
    change integralMap γ N k (absoluteClassForm N hN k hk P)∈absoluteSeriesSpan N hN k hk
    rw [integral_absoluteClassForm]
    exact absoluteClassForm_mem _ _ _ _ _
  exact hle hf

/-- The actual raw forward slash has coefficient n^(k-1) on the n-point residue sum. -/
theorem forward_absoluteClassForm (n : ℕ) [NeZero n] (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k) (P : ℤ × ℤ) :
    forwardWeightMap (n := n) N k (absoluteClassForm N hN k hk P)=
      (n : ℂ)^((k : ℤ)-1) • ∑ j : Fin n,absoluteClassForm (n*N) (Nat.mul_pos (NeZero.pos n) hN) k hk
        ((n : ℤ)*P.1,P.2+(N : ℤ)*(j : ℕ)) := by
  apply _root_.ModularForm.ext
  intro τ
  rw [forwardWeightMap_apply,TauCeti.slash_scaleGL_apply,scale_upTau,absoluteClassForm_apply]
  simp only [_root_.smul_apply,smul_eq_mul,_root_.sum_apply,absoluteClassForm_apply]
  rw [raw_up n N k (NeZero.pos n) hN hk P τ]

/-- Inverse raw-series slash has the derived coefficient n, for all k≥3. -/
theorem inverse_absoluteClassForm (n : ℕ) [NeZero n] (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k) (P : ℤ × ℤ) :
    inverseWeightMap (n := n) N k (absoluteClassForm N hN k hk P)=
      (n : ℂ) • ∑ j : Fin n,absoluteClassForm (n*N) (Nat.mul_pos (NeZero.pos n) hN) k hk
        (P.1+(N : ℤ)*(j : ℕ),(n : ℤ)*P.2) := by
  have hnC : (n : ℂ)≠0 := by exact_mod_cast NeZero.ne n
  have hp : (n : ℂ)^(1-(k : ℤ))*(n : ℂ)^k=(n : ℂ) := by
    rw [← zpow_natCast,← zpow_add₀ hnC,show (1-(k : ℤ))+(k : ℤ)=1 by ring,zpow_one]
  apply _root_.ModularForm.ext
  intro τ
  rw [inverseWeightMap_apply,inverse_slash_weight,scale_downTau,absoluteClassForm_apply]
  simp only [_root_.smul_apply,smul_eq_mul,_root_.sum_apply,absoluteClassForm_apply]
  rw [raw_down n N k (NeZero.pos n) hN hk P τ,← mul_assoc,hp]

theorem forward_absoluteSeriesSpan (n : ℕ) [NeZero n] (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k)
    {f : _root_.ModularForm (ΓP N) (k : ℤ)} (hf : f∈absoluteSeriesSpan N hN k hk) :
    forwardWeightMap (n := n) N k f∈absoluteSeriesSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN) k hk := by
  have hle : absoluteSeriesSpan N hN k hk ≤
      (absoluteSeriesSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN) k hk).comap (forwardWeightMap (n := n) N k) := by
    apply Submodule.span_le.mpr
    rintro F ⟨P,rfl⟩
    change forwardWeightMap (n := n) N k (absoluteClassForm N hN k hk P)∈
      absoluteSeriesSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN) k hk
    rw [forward_absoluteClassForm]
    apply Submodule.smul_mem
    exact Submodule.sum_mem _ fun j _ => absoluteClassForm_mem _ _ _ _ _
  exact hle hf

theorem inverse_absoluteSeriesSpan (n : ℕ) [NeZero n] (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k)
    {f : _root_.ModularForm (ΓP N) (k : ℤ)} (hf : f∈absoluteSeriesSpan N hN k hk) :
    inverseWeightMap (n := n) N k f∈absoluteSeriesSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN) k hk := by
  have hle : absoluteSeriesSpan N hN k hk ≤
      (absoluteSeriesSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN) k hk).comap (inverseWeightMap (n := n) N k) := by
    apply Submodule.span_le.mpr
    rintro F ⟨P,rfl⟩
    change inverseWeightMap (n := n) N k (absoluteClassForm N hN k hk P)∈
      absoluteSeriesSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN) k hk
    rw [inverse_absoluteClassForm]
    apply Submodule.smul_mem
    exact Submodule.sum_mem _ fun j _ => absoluteClassForm_mem _ _ _ _ _
  exact hle hf

/-- Concrete actual absolute-series modular representation, at its true weight. -/
def RepresentsSeriesAt (M : ℕ) (hM : 0<M) (k : ℕ) (hk : 3≤k) (u : ℍ → ℂ) : Prop :=
  ∃ F : _root_.ModularForm (ΓP M) (k : ℤ),F∈absoluteSeriesSpan M hM k hk ∧ ∀ τ : ℍ,F τ=u τ

lemma representsSeriesAt_level {M L : ℕ} {hM : 0<M} {hL : 0<L} {k : ℕ} {hk : 3≤k} {u : ℍ → ℂ}
    (hlevel : M=L) (h : RepresentsSeriesAt M hM k hk u) : RepresentsSeriesAt L hL k hk u := by
  cases hlevel
  exact h

/-- The positive integer multiplier is chosen before N, k or f. -/
def UniformSeriesTransport (g : GLR) : Prop :=
  ∃ (D : ℕ) (hD : 0<D),∀ (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k)
    (f : _root_.ModularForm (ΓP N) (k : ℤ)),f∈absoluteSeriesSpan N hN k hk →
      RepresentsSeriesAt (D*N) (Nat.mul_pos hD hN) k hk (⇑f ∣[(k : ℤ)] g)

theorem uniform_series_mul {g h : GLR} (hg : UniformSeriesTransport g) (hh : UniformSeriesTransport h) :
    UniformSeriesTransport (g*h) := by
  obtain ⟨D,hD,hg⟩ := hg
  obtain ⟨E,hE,hh⟩ := hh
  refine ⟨E*D,Nat.mul_pos hE hD,?_⟩
  intro N hN k hk f hf
  obtain ⟨F,hF,hFeq⟩ := hg N hN k hk f hf
  obtain ⟨G,hG,hGeq⟩ := hh (D*N) (Nat.mul_pos hD hN) k hk F hF
  have hrep : (⇑F : ℍ → ℂ)=(⇑f ∣[(k : ℤ)] g) := funext hFeq
  have hout : RepresentsSeriesAt (E*(D*N)) (Nat.mul_pos hE (Nat.mul_pos hD hN)) k hk
      (⇑f ∣[(k : ℤ)] (g*h)) := by
    refine ⟨G,hG,?_⟩
    intro τ
    rw [hGeq τ,hrep,← SlashAction.slash_mul]
  exact representsSeriesAt_level (Nat.mul_assoc E D N).symm hout

theorem uniform_series_integral (γ : SL(2,ℤ)) : UniformSeriesTransport (mapGL ℝ γ) := by
  refine ⟨1,by omega,?_⟩
  intro N hN k hk f hf
  have hrep : RepresentsSeriesAt N hN k hk (⇑f ∣[(k : ℤ)] mapGL ℝ γ) :=
    ⟨integralMap γ N k f,integral_absoluteSeriesSpan γ N hN k hk hf,integralMap_apply γ N k f⟩
  exact representsSeriesAt_level (Nat.one_mul N).symm hrep

theorem uniform_series_integer_diagonal (n : ℕ) [NeZero n] : UniformSeriesTransport (TauCeti.scaleGL n) := by
  refine ⟨n,NeZero.pos n,?_⟩
  intro N hN k hk f hf
  exact ⟨forwardWeightMap (n := n) N k f,forward_absoluteSeriesSpan n N hN k hk hf,forwardWeightMap_apply N k f⟩

theorem uniform_series_inverse_integer_diagonal (n : ℕ) [NeZero n] : UniformSeriesTransport ((TauCeti.scaleGL n)⁻¹) := by
  refine ⟨n,NeZero.pos n,?_⟩
  intro N hN k hk f hf
  exact ⟨inverseWeightMap (n := n) N k f,inverse_absoluteSeriesSpan n N hN k hk hf,inverseWeightMap_apply N k f⟩

theorem uniform_series_scalar (t : ℚ) (ht : 0<t) : UniformSeriesTransport (mapR (scalarQ t ht)) := by
  refine ⟨1,by omega,?_⟩
  intro N hN k hk f hf
  have hrep : RepresentsSeriesAt N hN k hk (⇑f ∣[(k : ℤ)] mapR (scalarQ t ht)) := by
    refine ⟨(t : ℂ)^((k : ℤ)-2) • f,Submodule.smul_mem _ _ hf,?_⟩
    intro τ
    rw [_root_.smul_apply,smul_eq_mul,scalar_slash_apply]
  exact representsSeriesAt_level (Nat.one_mul N).symm hrep

theorem uniform_series_upper (x : ℚ) : UniformSeriesTransport (mapR (upperQ x)) := by
  let _ : NeZero x.den := ⟨(Rat.den_pos x).ne'⟩
  have hq : (TauCeti.scaleGLRat x.den)⁻¹*mapGL ℚ (ModularGroup.T^x.num)*TauCeti.scaleGLRat x.den=upperQ x := by
    simpa only [Rat.num_div_den] using upperQ_fraction x.num x.den
  have hr : (TauCeti.scaleGL x.den)⁻¹*mapGL ℝ (ModularGroup.T^x.num)*TauCeti.scaleGL x.den=mapR (upperQ x) := by
    simpa only [map_mul,map_inv,mapR_integer_diagonal,mapR_sl] using congrArg mapR hq
  rw [← hr]
  exact uniform_series_mul (uniform_series_mul (uniform_series_inverse_integer_diagonal x.den)
    (uniform_series_integral (ModularGroup.T^x.num))) (uniform_series_integer_diagonal x.den)

theorem uniform_series_lower (x : ℚ) : UniformSeriesTransport (mapR (lowerQ x)) := by
  have hr : mapGL ℝ ModularGroup.S*mapR (upperQ (-x))*mapGL ℝ (ModularGroup.S⁻¹)=mapR (lowerQ x) := by
    simpa only [map_mul,map_inv,mapR_sl] using congrArg mapR (lowerQ_S x)
  rw [← hr]
  exact uniform_series_mul (uniform_series_mul (uniform_series_integral ModularGroup.S) (uniform_series_upper (-x)))
    (uniform_series_integral ModularGroup.S⁻¹)

theorem uniform_series_positive_diagonal (q : ℚ) (hq : 0<q) : UniformSeriesTransport (mapR (diagonalQ q hq)) := by
  obtain ⟨m,n,hm,hn,hEq⟩ := diagonalQ_fraction q hq
  let _ : NeZero m := ⟨hm.ne'⟩
  let _ : NeZero n := ⟨hn.ne'⟩
  have hr : TauCeti.scaleGL m*(TauCeti.scaleGL n)⁻¹=mapR (diagonalQ q hq) := by
    simpa only [map_mul,map_inv,mapR_integer_diagonal] using congrArg mapR hEq
  rw [← hr]
  exact uniform_series_mul (uniform_series_integer_diagonal m) (uniform_series_inverse_integer_diagonal n)

/-- Full positive-rational transport with every series atom supplied by actual series proofs. -/
theorem uniform_series_positive_rational (A : GLQ) (hA : 0<detQ A) : UniformSeriesTransport (mapR A) := by
  obtain ⟨γ,x,y,t,q,ht,hq,hEq⟩ := exists_positive_gaussian A hA
  have hr : mapR A=mapGL ℝ γ*mapR (lowerQ x)*mapR (scalarQ t ht)*mapR (diagonalQ q hq)*mapR (upperQ y) := by
    simpa only [map_mul,mapR_sl] using congrArg mapR hEq
  rw [hr]
  exact uniform_series_mul (uniform_series_mul (uniform_series_mul
    (uniform_series_mul (uniform_series_integral γ) (uniform_series_lower x)) (uniform_series_scalar t ht))
    (uniform_series_positive_diagonal q hq)) (uniform_series_upper y)

/-- Every positive original level and every weight k≥3 have an actual absolute-
series common-level representative for each positive-determinant rational matrix. -/
theorem actual_positive_rational_series_transport (N : ℕ) (hN : 0<N) (k : ℕ) (hk : 3≤k)
    (f : _root_.ModularForm (ΓP N) (k : ℤ)) (hf : f∈absoluteSeriesSpan N hN k hk)
    (A : GLQ) (hA : 0<(A.det : ℚ)) :
    ∃ (M : ℕ) (hM : 0<M),N∣M ∧
      ∃ F : _root_.ModularForm (ΓP M) (k : ℤ),F∈absoluteSeriesSpan M hM k hk ∧
        ∀ τ : ℍ,F τ=(⇑f ∣[(k : ℤ)] Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) A) τ := by
  obtain ⟨D,hD,htransport⟩ := uniform_series_positive_rational A hA
  obtain ⟨F,hF,hFeq⟩ := htransport N hN k hk f hf
  exact ⟨D*N,Nat.mul_pos hD hN,Nat.dvd_mul_left N D,F,hF,hFeq⟩

/-- The endpoint on the unchanged established all-weight seriesSpanK. -/
theorem actual_positive_rational_seriesSpanK_transport (N : ℕ) (h3 : 3≤N) (k : ℕ) (hk : 3≤k)
    (f : _root_.ModularForm (ΓP N) (k : ℤ)) (hf : f∈seriesSpanK N h3 k hk)
    (A : GLQ) (hA : 0<(A.det : ℚ)) :
    ∃ (M : ℕ) (_hM : 0<M) (hM3 : 3≤M),N∣M ∧
      ∃ F : _root_.ModularForm (ΓP M) (k : ℤ),F∈seriesSpanK M hM3 k hk ∧
        ∀ τ : ℍ,F τ=(⇑f ∣[(k : ℤ)] mapR A) τ := by
  have hgood : f∈absoluteSeriesSpan N (by omega) k hk := by
    rw [absoluteSeriesSpan_eq_seriesSpanK N h3 k hk]
    exact hf
  obtain ⟨M,hM,hNM,F,hF,hFeq⟩ := actual_positive_rational_series_transport N (by omega) k hk f hgood A hA
  have hM3 : 3≤M := h3.trans (Nat.le_of_dvd hM hNM)
  refine ⟨M,hM,hM3,hNM,F,?_,?_⟩
  · rw [← absoluteSeriesSpan_eq_seriesSpanK M hM3 k hk]
    exact hF
  · intro τ
    simpa only [mapR] using hFeq τ

/-- A uniform true classSeriesSpan transport follows from the actual raw weight-three bridge. -/
theorem uniform_classSeries_transport (A : GLQ) (hA : 0<(A.det : ℚ)) :
    ∃ (D : ℕ) (hD : 0<D),∀ (N : ℕ) (hN : 0<N)
      (f : TorsionWeightThree.Weight N 3),f∈MixedWeightThreeAddition.classSeriesSpan N hN →
        ∃ F : TorsionWeightThree.Weight (D*N) 3,F∈MixedWeightThreeAddition.classSeriesSpan (D*N) (Nat.mul_pos hD hN) ∧
          ∀ τ : ℍ,F τ=(⇑f ∣[(3 : ℤ)] mapR A) τ := by
  obtain ⟨D,hD,htransport⟩ := uniform_series_positive_rational A hA
  refine ⟨D,hD,?_⟩
  intro N hN f hf
  have hgood : f∈absoluteSeriesSpan N hN 3 (by omega) := by
    rw [absoluteSeriesSpan_three_eq_classSeriesSpan]
    exact hf
  obtain ⟨F,hF,hFeq⟩ := htransport N hN 3 (by omega) f hgood
  refine ⟨F,?_,hFeq⟩
  rw [← absoluteSeriesSpan_three_eq_classSeriesSpan]
  exact hF

/-- Forward restriction of the true class-series span uses actual finite grid refinement. -/
theorem restriction_classSeriesSpan (t N : ℕ) (ht : 0<t) (hN : 0<N)
    {f : TorsionWeightThree.Weight N 3} (hf : f∈MixedWeightThreeAddition.classSeriesSpan N hN) :
    restrictionK N (t*N) 3 (Nat.dvd_mul_left N t) f∈
      MixedWeightThreeAddition.classSeriesSpan (t*N) (Nat.mul_pos ht hN) := by
  rw [← absoluteSeriesSpan_three_eq_classSeriesSpan] at hf ⊢
  exact restriction_absoluteSeriesSpan t N 3 ht hN (by omega) hf

end ZInQ.Contrib.HeckePrimeRationality.AbsoluteSeriesRationalTransport

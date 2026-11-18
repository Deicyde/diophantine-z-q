import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllWeightRawSeriesBridge

set_option autoImplicit false
set_option pp.universes true
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm
open ZInQ.Contrib.HeckePrimeRationality

#check @AllWeightSeriesTrace.restrictionK
#check @AllWeightSeriesTrace.normalizedTraceK
#check @AllWeightSeriesTrace.traceK_generator_all
#check @AllWeightSeriesTrace.traceK_seriesSpan_all
#check @AllWeightSeriesTrace.invariant_seriesK_descent
#check @AllWeightSeriesTrace.completeFiberK_restriction
#check @AllWeightSeriesTrace.repeated_primitive_traceK
#check @AllWeightSeriesTrace.coprime_primitive_traceK
#print AllWeightSeriesTrace.seriesSpanK
#print AllWeightSeriesTrace.normalizedTraceK
#print AllWeightSeriesTrace.seriesForm

#print axioms AllWeightSeriesTrace.restrictionK
#print axioms AllWeightSeriesTrace.restrictionK_apply
#print axioms AllWeightSeriesTrace.restrictionK_injective
#print axioms AllWeightSeriesTrace.normalizedTraceK
#print axioms AllWeightSeriesTrace.normalizedTraceK_apply
#print axioms AllWeightSeriesTrace.normalizedTraceK_restriction
#print axioms AllWeightSeriesTrace.restrictionK_trans
#print axioms AllWeightSeriesTrace.restrictionK_self
#print axioms AllWeightSeriesTrace.seriesForm
#print axioms AllWeightSeriesTrace.seriesSpanK
#print axioms AllWeightSeriesTrace.generator_mem_seriesSpanK
#print axioms AllWeightSeriesTrace.seriesValue
#print axioms AllWeightSeriesTrace.seriesForm_apply
#print axioms AllWeightSeriesTrace.scaled_summand
#print axioms AllWeightSeriesTrace.seriesValue_scale
#print axioms AllWeightSeriesTrace.restrictionK_generator_mul
#print axioms AllWeightSeriesTrace.class_fiber_sum
#print axioms AllWeightSeriesTrace.completeFiberK
#print axioms AllWeightSeriesTrace.completeFiberK_restriction
#print axioms AllWeightSeriesTrace.normalizedTraceK_completeFiber
#print axioms AllWeightSeriesTrace.classTerm
#print axioms AllWeightSeriesTrace.seriesValue_vector
#print axioms AllWeightSeriesTrace.seriesValue_SL
#print axioms AllWeightSeriesTrace.seriesForm_slash
#print axioms AllWeightSeriesTrace.seriesForm_eq_of_congr
#print axioms AllWeightSeriesTrace.normalizedTraceK_series_SL
#print axioms AllWeightSeriesTrace.actual_descentK
#print axioms AllWeightSeriesTrace.restrictionK_trace_invariant
#print axioms AllWeightSeriesTrace.restrictionK_trace_mem_upper
#print axioms AllWeightSeriesTrace.traceK_motion
#print axioms AllWeightSeriesTrace.repeated_point_traceK
#print axioms AllWeightSeriesTrace.repeated_primitive_traceK
#print axioms AllWeightSeriesTrace.coprime_point_traceK
#print axioms AllWeightSeriesTrace.coprime_primitive_traceK
#print axioms AllWeightSeriesTrace.traceK_prime_generator_mem
#print axioms AllWeightSeriesTrace.traceK_prime_span
#print axioms AllWeightSeriesTrace.invariant_seriesK_prime
#print axioms AllWeightSeriesTrace.invariant_seriesK_descent
#print axioms AllWeightSeriesTrace.traceK_seriesSpan_all
#print axioms AllWeightSeriesTrace.traceK_generator_all
#print axioms AllWeightSeriesTrace.rawClassForm
#print axioms AllWeightSeriesTrace.rawClassForm_apply
#print axioms AllWeightSeriesTrace.rawClassForm_mem
#print axioms AllWeightSeriesTrace.rawClassForm_span_eq
#print axioms AllWeightSeriesTrace.raw_weight_three_bundle
#check @AllWeightSeriesTrace.raw_weight_three_bundle
#check @AllWeightSeriesTrace.rawClassForm_span_eq

/-- The literal variable-weight all-label series generator trace contract. -/
example (N M k : ℕ) (hN : 3 ≤ N) (hM : 0 < M) (hNM : N ∣ M) (hk : 3 ≤ k) (a b : ℤ) :
    AllWeightSeriesTrace.normalizedTraceK N M k hM
      (AllWeightPrincipalEisensteinForms.principalEisensteinForm M
        (hN.trans (Nat.le_of_dvd hM hNM)) k hk a b) ∈ AllWeightSeriesTrace.seriesSpanK N hN k hk :=
  AllWeightSeriesTrace.traceK_generator_all hN hM hNM k hk ![a,b]

example (f : _root_.ModularForm ((CongruenceSubgroup.Gamma 30).map (mapGL ℝ)) (3 : ℤ))
    (hf : f ∈ AllWeightSeriesTrace.seriesSpanK 30 (by omega) 3 (by omega)) :
    AllWeightSeriesTrace.normalizedTraceK 3 30 3 (by omega) f ∈
      AllWeightSeriesTrace.seriesSpanK 3 (by omega) 3 (by omega) :=
  AllWeightSeriesTrace.traceK_seriesSpan_all (by omega) (by omega) (by omega) 3 (by omega) hf

/-- The bad even row retains its actual G4 value rather than a zero convention. -/
example (τ : ℍ) : AllWeightSeriesTrace.seriesForm 3 (by omega) 4 (by omega) ![0,0] τ =
    (ThetaWeierstrass.periodPair τ).G 4 :=
  AllWeightPrincipalEisensteinForms.principalEisensteinForm_bad_apply 3 (by omega) 4 (by omega)
    0 0 ⟨dvd_zero _,dvd_zero _⟩ τ

example : AllWeightSeriesTrace.normalizedTraceK 3 6 4 (by omega)
    (AllWeightSeriesTrace.seriesForm 6 (by omega) 4 (by omega) ![0,0]) ∈
      AllWeightSeriesTrace.seriesSpanK 3 (by omega) 4 (by omega) :=
  AllWeightSeriesTrace.traceK_generator_all (by omega) (by omega) (by omega) 4 (by omega) ![0,0]

example : AllWeightSeriesTrace.normalizedTraceK 4 8 3 (by omega)
    (AllWeightSeriesTrace.seriesForm 8 (by omega) 3 (by omega) ![-7,4]) ∈
      AllWeightSeriesTrace.seriesSpanK 4 (by omega) 3 (by omega) :=
  AllWeightSeriesTrace.traceK_generator_all (by omega) (by omega) (by omega) 3 (by omega) ![-7,4]

example : ¬ (3 ≤ (2 : ℕ)) := by omega

/-- The genuine invariant descent endpoint retains its actual span input. -/
example (N M k : ℕ) (hN : 3 ≤ N) (hM : 0 < M) (hNM : N ∣ M) (hk : 3 ≤ k)
    (f : _root_.ModularForm ((CongruenceSubgroup.Gamma M).map (mapGL ℝ)) (k : ℤ))
    (hf : f ∈ AllWeightSeriesTrace.seriesSpanK M (hN.trans (Nat.le_of_dvd hM hNM)) k hk)
    (hi : ∀ γ ∈ (CongruenceSubgroup.Gamma N).map (mapGL ℝ), ⇑f ∣[(k : ℤ)] γ = ⇑f) :
    ∃ g : _root_.ModularForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (k : ℤ),
      g ∈ AllWeightSeriesTrace.seriesSpanK N hN k hk ∧ AllWeightSeriesTrace.restrictionK N M k hNM g = f :=
  AllWeightSeriesTrace.invariant_seriesK_descent M N hN hM hNM k hk f hf hi

/-- The repeated-prime weight-three factor is p, not p cubed. -/
example (a b : ℤ) (hi : (a : ZMod 2) ≠ 0 ∨ (b : ZMod 2) ≠ 0) :
    AllWeightSeriesTrace.normalizedTraceK 4 8 3 (by omega)
      (AllWeightSeriesTrace.seriesForm 8 (by omega) 3 (by omega) ![a,b]) =
      (2 : ℂ) • AllWeightSeriesTrace.seriesForm 4 (by omega) 3 (by omega) ![a,b] := by
  have h := AllWeightSeriesTrace.repeated_primitive_traceK 2 4 (by omega) (by omega) 3 (by omega) a b hi
  norm_num at h
  exact h

/-- The complete fibre at k=4 has the exact fourth-power scaling. -/
example (a b : ℤ) : AllWeightSeriesTrace.completeFiberK 2 3 (by omega) (by omega) 4 (by omega) a b =
    AllWeightSeriesTrace.restrictionK 3 6 4 (by omega)
      ((16 : ℂ) • AllWeightSeriesTrace.seriesForm 3 (by omega) 4 (by omega) ![a,b]) := by
  have h := AllWeightSeriesTrace.completeFiberK_restriction 2 3 (by omega) (by omega) 4 (by omega) a b
  norm_num at h
  exact h

set_option pp.notation false in
#check @AllWeightSeriesTrace.traceK_generator_all
set_option pp.notation false in
#check @AllWeightSeriesTrace.coprime_primitive_traceK

import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Nilpotent
import ZInQKernel.Contrib.OneProof.RC.LocalWeights.Compact

/-! The determinant, scaling, and congruence rules at (p ∣ m),
tex 8536–8549, 8563–8566. The bound (p^2) is provenance (c). -/

namespace ZInQ.Manuscript.RC.LocalWeights

open Matrix

variable {p : ℕ} [Fact p.Prime]

local notation "res" => (PadicInt.toZMod : ℤ_[p] →+* ZMod p)
local notation "red" => PadicInt.toZModPow

/-- Exact divisibility is the valuation-one condition in tex 8536. Mathlib's
numeric valuation returns zero at zero, which is excluded by the condition. -/
theorem nilSupport_valuation (x : TraceZero ℤ_[p]) :
    NilSupport p x ↔ x.val.det.valuation = 1 := by
  by_cases hz : x.val.det = 0
  · simp [NilSupport, hz]
  · have hd (n : ℕ) : (p : ℤ_[p]) ^ n ∣ x.val.det ↔ n ≤ x.val.det.valuation := by
      rw [← Ideal.mem_span_singleton, PadicInt.mem_span_pow_iff_le_valuation _ hz]
    have hp := hd 1
    rw [pow_one] at hp
    rw [NilSupport, hp, hd]
    omega

theorem nilWeight_nonzero_iff {O : Type*} [Ring O] [Nontrivial O]
    (x : TraceZero ℤ_[p]) : (nilWeight p x : O) ≠ 0 ↔ NilSupport p x := by
  by_cases h : NilSupport p x
  · obtain ⟨ht, hd, hn⟩ := nilSupport_reduction p x h
    obtain ⟨g, hg⟩ := nilBasis_exists (x.val.map res) ht hd hn
    rw [nilWeight, ite_eq_left h, nilSign_of_basis hg]
    rcases quadraticChar_dichotomy (Matrix.isUnits_det_units g).ne_zero with h' | h' <;>
      simp [h, h']
  · simp [nilWeight, h]

/-- The inverse conjugation rule at an integral maximal split order. -/
theorem nilWeight_conj {O : Type*} [Ring O] (u : GL (Fin 2) ℤ_[p]) (x : TraceZero ℤ_[p]) :
    nilWeight p ⟨(↑u⁻¹ : Mat ℤ_[p]) * x.val * (u : Mat ℤ_[p]),
      (Matrix.trace_units_conj' u x.val).trans x.property⟩ =
      (quadraticChar (ZMod p) (res (u : Mat ℤ_[p]).det) : O) * nilWeight p x := by
  let y : TraceZero ℤ_[p] := ⟨(↑u⁻¹ : Mat ℤ_[p]) * x.val * (u : Mat ℤ_[p]),
    (Matrix.trace_units_conj' u x.val).trans x.property⟩
  change nilWeight p y = _
  have ha : NilSupport p y ↔ NilSupport p x := by
    simp only [NilSupport, y, Matrix.det_units_conj']
  have hb : y.val.map res = (↑(GeneralLinearGroup.map res u)⁻¹ : Mat (ZMod p)) *
      x.val.map res * (GeneralLinearGroup.map res u : Mat (ZMod p)) := by
    change (res).mapMatrix ((↑u⁻¹ : Mat ℤ_[p]) * x.val * (u : Mat ℤ_[p])) = _
    rw [map_mul, map_mul]
    rfl
  have hdet : (GeneralLinearGroup.map res u : Mat (ZMod p)).det = res (u : Mat ℤ_[p]).det := by
    change ((u : Mat ℤ_[p]).map res).det = _
    simp only [Matrix.det_fin_two, Matrix.map_apply, map_mul, map_sub]
  unfold nilWeight
  rw [ha]
  split
  · rw [hb, nilSign_conj, hdet, Int.cast_mul]
  · rw [mul_zero]

theorem nilWeight_scale {O : Type*} [Ring O] (v : ℤ_[p]ˣ) (x : TraceZero ℤ_[p]) :
    nilWeight p ⟨v.val • x.val, by rw [Matrix.trace_smul, x.property, smul_zero]⟩ =
      (quadraticChar (ZMod p) (res v.val) : O) * nilWeight p x := by
  let y : TraceZero ℤ_[p] := ⟨v.val • x.val, by rw [Matrix.trace_smul, x.property, smul_zero]⟩
  change nilWeight p y = _
  have hu : IsUnit (v.val ^ 2) := v.isUnit.pow 2
  have ha : NilSupport p y ↔ NilSupport p x := by
    simp only [NilSupport, y, Matrix.det_smul, Fintype.card_fin, hu.dvd_mul_left]
  have hb : y.val.map res = (res v.val) • (x.val.map res) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, y, map_mul]
  unfold nilWeight
  rw [ha]
  split
  · rw [hb]
    rw [← Int.cast_mul]
    exact congrArg (Int.castRingHom O) (nilSign_scale (Units.map (res).toMonoidHom v) (x.val.map res))
  · rw [mul_zero]

/-- The weight at (p∣m) depends only on the order coordinates modulo (p^2). -/
theorem nilWeight_congr {O : Type*} [Ring O] (x y : TraceZero ℤ_[p])
    (h : redMat p 2 x.val = redMat p 2 y.val) : (nilWeight p x : O) = nilWeight p y := by
  have he (i j : Fin 2) : red 2 (x.val i j) = red 2 (y.val i j) :=
    congrFun (congrFun h i) j
  have hdown (a b : ℤ_[p]) (h' : red 2 a = red 2 b) : red 1 a = red 1 b := by
    rw [← PadicInt.cast_toZModPow 1 2 (by decide) a,
      ← PadicInt.cast_toZModPow 1 2 (by decide) b, h']
  have hd : red 2 x.val.det = red 2 y.val.det := by
    simp only [Matrix.det_fin_two, map_mul, map_sub, he]
  have hker (a : ℤ_[p]) : res a = 0 ↔ (p : ℤ_[p]) ∣ a := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton]
  have hred (k : ℕ) (a : ℤ_[p]) : red k a = 0 ↔ (p : ℤ_[p]) ^ k ∣ a := by
    simpa using red_eq_iff p k a 0
  have hs : NilSupport p x ↔ NilSupport p y := by
    unfold NilSupport
    have hone (a : ℤ_[p]) : red 1 a = 0 ↔ (p : ℤ_[p]) ∣ a := by
      simpa only [pow_one] using hred 1 a
    rw [← hone, ← hred, ← hone, ← hred, hd, hdown _ _ hd]
  have hm : x.val.map res = y.val.map res := by
    ext i j
    simp only [Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub, hker]
    simpa only [pow_one] using (red_eq_iff p 1 _ _).mp (hdown _ _ (he i j))
  unfold nilWeight
  rw [hm]
  by_cases h' : NilSupport p x
  · rw [ite_eq_left h', ite_eq_left (hs.mp h')]
  · rw [ite_eq_right h', ite_eq_right (mt hs.mpr h')]

theorem nilWeight_compactOpen {O : Type*} [Ring O] :
    IsLocallyConstant (nilWeight p : TraceZero ℤ_[p] → O) ∧
      IsCompact (Function.support (nilWeight p : TraceZero ℤ_[p] → O)) ∧
      IsOpen (Function.support (nilWeight p : TraceZero ℤ_[p] → O)) := by
  have ht : Continuous (fun x : Mat ℤ_[p] => x.trace) := by
    simp only [Matrix.trace_fin_two]
    exact (continuous_apply_apply 0 0).add (continuous_apply_apply 1 1)
  let : CompactSpace (TraceZero ℤ_[p]) :=
    isCompact_iff_compactSpace.mp (isClosed_singleton.preimage ht).isCompact
  have hl : IsLocallyConstant (nilWeight p : TraceZero ℤ_[p] → O) :=
    locallyConstant_of_factors ((redMat_locallyConstant p 2).comp_continuous continuous_subtype_val)
      (nilWeight_congr (p := p))
  exact ⟨hl, compactOpen_support hl⟩

end ZInQ.Manuscript.RC.LocalWeights

open ZInQ.Manuscript.RC.LocalWeights
#print axioms nilWeight_nonzero_iff
#print axioms nilSupport_valuation
#print axioms nilWeight_conj
#print axioms nilWeight_scale
#print axioms nilWeight_congr
#print axioms nilWeight_compactOpen

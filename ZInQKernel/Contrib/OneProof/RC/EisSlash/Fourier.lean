import ZInQKernel.Contrib.OneProof.RC.EisSlash.Mean
import ZInQKernel.Contrib.OneProof.RC.EisSlash.Regroup
import ZInQKernel.Contrib.OneProof.RC.EisSlash.Reduction

/-! Fourier normalization of the lattice construction. The regrouping and
Gauss normalization are on-the-spot (c) for the divisor sums at tex
9862–9864 and the constituents at tex 9647–9654 and 9762–9764. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EisSlash

open Matrix UpperHalfPlane EisensteinSeries O12Eisenstein O12EisConst EisForm

variable {m₁ m₂ N : ℕ} [NeZero m₂] [NeZero N]

private theorem rowWeight_mul (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂)
    (k n : ℤ) :
    rowWeight a b ![(m₂ : ℤ) * k, n] = a (k : ZMod m₁) * b⁻¹ (n : ZMod m₂) := by
  have hm : (m₂ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m₂
  simp [rowWeight, Int.mul_ediv_cancel_left _ hm]

private theorem weightedRow_mul (hN : N = m₂ * m₁)
    (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂) (z : ℍ) (k : ℤ) :
    weightedRow N (characterWeight a b) z ((m₂ : ℤ) * k) =
      a (k : ZMod m₁) * ∑' n : ℤ, b⁻¹ (n : ZMod m₂) * eisSummand 2 ![(m₂ : ℤ) * k, n] z := by
  simp_rw [weightedRow, characterWeight_on_row hN, rowWeight_mul, mul_assoc, tsum_mul_left]

private theorem weightedRow_zero (hN : N = m₂ * m₁)
    (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂) (z w : ℍ) :
    weightedRow N (characterWeight a b) z 0 = weightedRow N (characterWeight a b) w 0 := by
  have hz := weightedRow_mul hN a b z 0
  have hw := weightedRow_mul hN a b w 0
  simp only [mul_zero, eisSummand, cons_val_zero, cons_val_one, Int.cast_zero, zero_mul,
    zero_add] at hz hw
  exact hz.trans hw.symm

private theorem weightedRow_even (hN : N = m₂ * m₁)
    (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂)
    (he : a (-1) * b⁻¹ (-1) = 1) (z : ℍ) :
    Function.Even (fun k : ℤ => weightedRow N (characterWeight a b) z ((m₂ : ℤ) * k)) := by
  intro k
  simp only [weightedRow_mul hN, ← tsum_mul_left]
  rw [← tsum_comp_neg (fun n : ℤ => a ((-k : ℤ) : ZMod m₁) *
    (b⁻¹ (n : ZMod m₂) * eisSummand 2 ![(m₂ : ℤ) * -k, n] z))]
  refine tsum_congr fun n => ?_
  have h (v : ℂ) : (-v) ^ (-(2 : ℤ)) = v ^ (-(2 : ℤ)) := by
    simp [_root_.zpow_neg, zpow_ofNat]
  simp only [eisSummand, cons_val_zero, cons_val_one, Int.mul_neg, Int.cast_neg, neg_mul, ← neg_add, h]
  rw [show -(k : ZMod m₁) = -1 * (k : ZMod m₁) by ring,
    show -(n : ZMod m₂) = -1 * (n : ZMod m₂) by ring, map_mul, map_mul]
  calc
    _ = (a (-1) * b⁻¹ (-1)) *
        (a (k : ZMod m₁) * (b⁻¹ (n : ZMod m₂) *
          ((↑((m₂ : ℤ) * k) * (z : ℂ) + n) ^ (-(2 : ℤ))))) := by ring
    _ = _ := by rw [he, one_mul]

private theorem weightedRows_restrict (hN : N = m₂ * m₁)
    (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂) (z : ℍ)
    (hs : Summable (weightedRow N (characterWeight a b) z)) :
    (∑' k : ℤ, weightedRow N (characterWeight a b) z k) =
      ∑' k : ℤ, weightedRow N (characterWeight a b) z ((m₂ : ℤ) * k) := by
  classical
  have hj (r : ZMod m₂) : Function.Injective (fun k : ℤ => (m₂ : ℤ) * k + r.val) := by
    intro k l h
    exact mul_left_cancel₀ (by exact_mod_cast NeZero.ne m₂) (add_right_cancel h)
  rw [(sum_residue_rows m₂ _ (fun r => hs.comp_injective (hj r))).2,
    Finset.sum_eq_single (0 : ZMod m₂)]
  · simp
  · intro r _ hr
    have hz (k : ℤ) : ¬ (m₂ : ℤ) ∣ (m₂ : ℤ) * k + r.val := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simpa using hr
    simp only [weightedRow, characterWeight_on_row hN, rowWeight, cons_val_zero, hz,
      ite_false, zero_mul, tsum_zero]
  · simp

private theorem weightedRow_positive (hN : N = m₂ * m₁)
    (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂) (z : ℍ) (k : ℕ+) :
    weightedRow N (characterWeight a b) z ((m₂ : ℤ) * (k.val : ℤ)) =
      ((m₂ : ℂ)^2)⁻¹ * (a (k.val : ZMod m₁) * lipschitzRow b z k) := by
  rw [weightedRow_mul hN]
  let f (n : ℤ) := b⁻¹ (n : ZMod m₂) * eisSummand 2 ![(m₂ : ℤ) * (k.val : ℤ), n] z
  have hf : ∀ r : ZMod m₂, Summable (fun n : ℤ => f ((m₂ : ℤ) * n + r.val)) := by
    intro r
    have hr (n : ℤ) : (((m₂ : ℤ) * n + (r.val : ℤ) : ℤ) : ZMod m₂) = r := by simp
    have hg (n : ℤ) : grid m₂ ![0, (r.val : ℤ)] ![(k.val : ℤ), n] =
        ![(m₂ : ℤ) * (k.val : ℤ), (m₂ : ℤ) * n + r.val] := by
      funext i
      fin_cases i
      · change (m₂ : ℤ) * (k.val : ℤ) + 0 = (m₂ : ℤ) * (k.val : ℤ)
        exact add_zero _
      · rfl
    simpa only [f, hr, hg] using
      (summable_gridRow_inner m₂ ![0, (r.val : ℤ)] z k.val).mul_left (b⁻¹ r)
  rw [(sum_residue_rows m₂ f hf).2]
  have hh (r : ZMod m₂) :
      (∑' n : ℤ, f ((m₂ : ℤ) * n + r.val)) =
        ((m₂ : ℂ)^2)⁻¹ * (b⁻¹ r *
          ∑' n : ℤ, 1 / ((((k.val : ℂ) * z + (↑((r.val : ℝ) / m₂) : ℂ)) + n) ^ 2)) := by
    rw [← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [f, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
      zero_mul, zero_add, ZMod.natCast_zmod_val, eisSummand, cons_val_zero, cons_val_one,
      _root_.zpow_neg, zpow_ofNat, one_div]
    have hm : (m₂ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m₂
    have h : (m₂ : ℂ) * (k.val : ℂ) * (z : ℂ) + ((m₂ : ℂ) * n + r.val) =
        (m₂ : ℂ) * (((k.val : ℂ) * z + (↑((r.val : ℝ) / m₂) : ℂ)) + n) := by
      push_cast
      field_simp
      ring
    rw [h, mul_pow, mul_inv]
    ring
  simp_rw [hh, ← Finset.mul_sum, Int.cast_natCast]
  change _ = _ * (a _ * ∑ r : ZMod m₂, b⁻¹ r * ∑' n : ℤ,
    1 / ((((k.val : ℂ) * z + (↑((r.val : ℝ) / m₂) : ℂ)) + n) ^ 2))
  ring

/-- For an even pair with a nontrivial factor the indicated Gauss
normalization gives the entire width-one series, including one constant. -/
theorem ordered_grid_fourier [NeZero m₁] (hN : N = m₂ * m₁)
    (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂)
    (hb : b.IsPrimitive) (hn : a ≠ 1 ∨ b ≠ 1) (he : a (-1) * b⁻¹ (-1) = 1) :
    ∃ C : ℂ, gridCombination N (characterWeight a b) = orderedScale b • series a b C := by
  let w : ℍ := ⟨Complex.I, by simp⟩
  let A := weightedRow N (characterWeight a b) w 0
  let S := orderedScale b
  let G := (-2 * Real.pi * Complex.I)^2 * gaussSum b⁻¹ ZMod.stdAddChar
  have hS : S ≠ 0 := orderedScale_ne_zero b hb
  have hG : G ≠ 0 := by
    intro h
    apply hS
    change (2 / (m₂ : ℂ)^2) * G = 0
    rw [h, mul_zero]
  refine ⟨A / S, funext fun z => ?_⟩
  obtain ⟨hs, hz⟩ := gridCombination_eq_weightedRows N (characterWeight a b) z
    (characterWeight_sum_zero hN a b hn)
  have hm : (m₂ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m₂
  have hi : Function.Injective (fun k : ℤ => (m₂ : ℤ) * k) :=
    fun _ _ h => mul_left_cancel₀ hm h
  rw [hz, weightedRows_restrict hN a b z hs,
    tsum_int_eq_zero_add_two_mul_tsum_pnat (weightedRow_even hN a b he z)
      (hs.comp_injective hi), mul_zero, weightedRow_zero hN a b z w]
  have hp (k : ℕ+) : weightedRow N (characterWeight a b) z ((m₂ : ℤ) * (k.val : ℤ)) =
      (S / 2) * (a (k.val : ZMod m₁) * (lipschitzRow b z k / G)) := by
    rw [weightedRow_positive hN]
    change _ = (((2 / (m₂ : ℂ)^2) * G) / 2) * (a _ * (lipschitzRow b z k / G))
    have hm' : (m₂ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m₂
    field_simp
  simp_rw [hp, tsum_mul_left]
  rw [Pi.smul_apply, smul_eq_mul, series_eq_lipschitz a b hb, lipschitzSeries, mul_add]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  change A + 2 * (S / 2 * _) = S * (A / S) + S * _
  have hA : S * (A / S) = A := by field_simp
  rw [hA]
  ring

private theorem inv_apply_neg_one {m : ℕ} (b : DirichletCharacter ℂ m) :
    b⁻¹ (-1) = b (-1) := by
  rw [MulChar.inv_apply_eq_inv']
  have h : b (-1) * b (-1) = 1 := by rw [← map_mul]; simp
  have hn : b (-1) ≠ 0 := by
    intro hn
    simp [hn] at h
  field_simp
  simpa only [pow_two] using h.symm

variable {D : Type*} [Field D] {p : ℕ} [Fact p.Prime]

private theorem ramified_complex_ne_one (E : CharacterPair D p) (c : D →+* ℂ)
    (hr : E.ramified.IsPrimitive) : E.ramified.ringHomComp c ≠ 1 := by
  intro h
  have hc : DirichletCharacter.IsPrimitive (E.ramified.ringHomComp c) := primitive_ringHomComp _ c hr
  rw [h, DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at hc
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hA : 0 < E.awayLevel := NeZero.pos _
  have := Nat.le_mul_of_pos_right p hA
  omega

/-- The lattice sum is the normalized explicit series for either Fourier
order of the actual ramified pair. -/
theorem pair_grid_fourier (E : CharacterPair D p) (c : D →+* ℂ)
    (hu : E.unram.IsPrimitive) (hr : E.ramified.IsPrimitive)
    (he : E.unram (-1) * E.ramified (-1) = 1) : PairGridFourier E c := by
  have h := ramified_complex_ne_one E c hr
  have hEven : (E.unram.ringHomComp c) (-1) * (E.ramified.ringHomComp c) (-1) = 1 := by
    simp only [MulChar.ringHomComp_apply, ← map_mul, he, map_one]
  unfold PairGridFourier
  cases ht : E.twistUnramified
  · simp only [pairWeight, pairScale, pairSeries, ht, Bool.false_eq_true, ite_false]
    exact ordered_grid_fourier rfl _ _ (primitive_ringHomComp _ c hr) (.inr h)
      (by rw [inv_apply_neg_one]; exact hEven)
  · simp only [pairWeight, pairScale, pairSeries, ht, ite_true]
    exact ordered_grid_fourier (mul_comm _ _) _ _ (primitive_ringHomComp _ c hu) (.inl h)
      (by rw [inv_apply_neg_one, mul_comm]; exact hEven)

/-- The normalized series satisfies the two analytic checks with one constant. -/
theorem pair_modularity (E : CharacterPair D p) (c : D →+* ℂ)
    (hu : E.unram.IsPrimitive) (hr : E.ramified.IsPrimitive)
    (he : E.unram (-1) * E.ramified (-1) = 1) : MissingModularity E c :=
  missingModularity_of_gridFourier E c hu hr (pair_grid_fourier E c hu hr he)

/-- The exact predecessor form at the product level with its product
nebentypus and ordered positive divisor sums. -/
theorem pair_baseForm (E : CharacterPair D p) (c : D →+* ℂ)
    (hu : E.unram.IsPrimitive) (hr : E.ramified.IsPrimitive)
    (he : E.unram (-1) * E.ramified (-1) = 1) : Nonempty (BaseForm E c) :=
  baseForm_of_gridFourier E c hu hr (pair_grid_fourier E c hu hr he)


end ZInQ.Manuscript.RC.EisSlash

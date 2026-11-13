import ZInQKernel.HDecomp.Analytic.QMLattice
set_option linter.unusedSimpArgs false

open BPAnalytic.QM Matrix

noncomputable section

namespace FQMNorm

def qmMatB (x : B) : Matrix (Fin 2) (Fin 2) ℂ := (iota x).map (fun r : ℝ => (r : ℂ))

def qmOrbit (w : Fin 2 → ℂ) : Submodule ℤ (Fin 2 → ℂ) :=
  Submodule.span ℤ (Set.range fun k : Fin 4 => (qmMatB (oBasis k)).mulVec w)

theorem qmLattice_eq_orbit {τ : ℂ} (hτ : τ.im ≠ 0) : qmLattice hτ = qmOrbit ![τ, 1] := by
  rw [qmLattice_eq]; rfl

/-- The four generators, explicitly. -/
theorem gen_eq (a b : ℂ) : (fun k : Fin 4 => (qmMatB (oBasis k)).mulVec ![a, b]) =
    ![![a, b], ![√2 * a, -(√2 * b)], ![(a - 3 * b) / 2, (a + b) / 2],
      ![√2 * (a - 3 * b) / 2, -(√2 * (a + b)) / 2]] := by
  funext k; ext i
  fin_cases k <;> fin_cases i <;>
    simp [qmMatB, iota, oBasis, Mi, Mj, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

def smulMap (c : ℂ) : (Fin 2 → ℂ) →ₗ[ℤ] (Fin 2 → ℂ) :=
  ((c • LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))).restrictScalars ℤ

theorem qmOrbit_smul (c : ℂ) (v : Fin 2 → ℂ) : qmOrbit (c • v) = (qmOrbit v).map (smulMap c) := by
  unfold qmOrbit
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext k
  simp [smulMap, Matrix.mulVec_smul]

theorem sqrt2_sq' : (√2 : ℂ) * √2 = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num

/-- The unit `1 + i` (reduced norm `−1`) does not change the orbit. -/
theorem qmOrbit_unit (τ : ℂ) : qmOrbit ![τ, 1] = qmOrbit ![(1 + √2) * τ, 1 - √2] := by
  have s := sqrt2_sq'
  apply le_antisymm
  · unfold qmOrbit
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [gen_eq, gen_eq]
    set S := Submodule.span ℤ (Set.range ![![((1 + √2) * τ), (1 - √2)], ![√2 * ((1 + √2) * τ), -(√2 * (1 - √2))], ![(((1 + √2) * τ) - 3 * (1 - √2)) / 2, (((1 + √2) * τ) + (1 - √2)) / 2], ![√2 * (((1 + √2) * τ) - 3 * (1 - √2)) / 2, -(√2 * (((1 + √2) * τ) + (1 - √2))) / 2]]) with hS
    have m : ∀ j : Fin 4, (![![((1 + √2) * τ), (1 - √2)], ![√2 * ((1 + √2) * τ), -(√2 * (1 - √2))], ![(((1 + √2) * τ) - 3 * (1 - √2)) / 2, (((1 + √2) * τ) + (1 - √2)) / 2], ![√2 * (((1 + √2) * τ) - 3 * (1 - √2)) / 2, -(√2 * (((1 + √2) * τ) + (1 - √2))) / 2]] : Fin 4 → Fin 2 → ℂ) j ∈ S := fun j => Submodule.subset_span ⟨j, rfl⟩
    fin_cases k
    · have e : (![τ, 1] : Fin 2 → ℂ) = -(![((1 + √2) * τ), (1 - √2)] : Fin 2 → ℂ) + (![√2 * ((1 + √2) * τ), -(√2 * (1 - √2))] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (-τ) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (-1) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.add_mem (S.neg_mem (m 0)) (m 1))
    · have e : (![√2 * τ, -(√2 * 1)] : Fin 2 → ℂ) = ((![((1 + √2) * τ), (1 - √2)] + ![((1 + √2) * τ), (1 - √2)] : Fin 2 → ℂ) : Fin 2 → ℂ) - (![√2 * ((1 + √2) * τ), -(√2 * (1 - √2))] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (τ) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (1) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.sub_mem (S.add_mem (m 0) (m 0)) (m 1))
    · have e : (![(τ - 3 * 1) / 2, (τ + 1) / 2] : Fin 2 → ℂ) = (![√2 * ((1 + √2) * τ), -(√2 * (1 - √2))] : Fin 2 → ℂ) - (![(((1 + √2) * τ) - 3 * (1 - √2)) / 2, (((1 + √2) * τ) + (1 - √2)) / 2] : Fin 2 → ℂ) - (![√2 * (((1 + √2) * τ) - 3 * (1 - √2)) / 2, -(√2 * (((1 + √2) * τ) + (1 - √2))) / 2] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (-(τ - 3)/2) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (-(τ + 1)/2) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.sub_mem (S.sub_mem (m 1) (m 2)) (m 3))
    · have e : (![√2 * (τ - 3 * 1) / 2, -(√2 * (τ + 1)) / 2] : Fin 2 → ℂ) = ((![((1 + √2) * τ), (1 - √2)] + ![((1 + √2) * τ), (1 - √2)] : Fin 2 → ℂ) : Fin 2 → ℂ) - ((![(((1 + √2) * τ) - 3 * (1 - √2)) / 2, (((1 + √2) * τ) + (1 - √2)) / 2] + ![(((1 + √2) * τ) - 3 * (1 - √2)) / 2, (((1 + √2) * τ) + (1 - √2)) / 2] : Fin 2 → ℂ) : Fin 2 → ℂ) - (![√2 * (((1 + √2) * τ) - 3 * (1 - √2)) / 2, -(√2 * (((1 + √2) * τ) + (1 - √2))) / 2] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination ((τ + 3)/2) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (-(τ - 1)/2) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.sub_mem (S.sub_mem (S.add_mem (m 0) (m 0)) (S.add_mem (m 2) (m 2))) (m 3))
  · unfold qmOrbit
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [gen_eq, gen_eq]
    set S := Submodule.span ℤ (Set.range ![![τ, 1], ![√2 * τ, -(√2 * 1)], ![(τ - 3 * 1) / 2, (τ + 1) / 2], ![√2 * (τ - 3 * 1) / 2, -(√2 * (τ + 1)) / 2]]) with hS
    have m : ∀ j : Fin 4, (![![τ, 1], ![√2 * τ, -(√2 * 1)], ![(τ - 3 * 1) / 2, (τ + 1) / 2], ![√2 * (τ - 3 * 1) / 2, -(√2 * (τ + 1)) / 2]] : Fin 4 → Fin 2 → ℂ) j ∈ S := fun j => Submodule.subset_span ⟨j, rfl⟩
    fin_cases k
    · have e : (![((1 + √2) * τ), (1 - √2)] : Fin 2 → ℂ) = (![τ, 1] : Fin 2 → ℂ) + (![√2 * τ, -(√2 * 1)] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (0) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (0) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.add_mem (m 0) (m 1))
    · have e : (![√2 * ((1 + √2) * τ), -(√2 * (1 - √2))] : Fin 2 → ℂ) = ((![τ, 1] + ![τ, 1] : Fin 2 → ℂ) : Fin 2 → ℂ) + (![√2 * τ, -(√2 * 1)] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (τ) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (1) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.add_mem (S.add_mem (m 0) (m 0)) (m 1))
    · have e : (![(((1 + √2) * τ) - 3 * (1 - √2)) / 2, (((1 + √2) * τ) + (1 - √2)) / 2] : Fin 2 → ℂ) = (![√2 * τ, -(√2 * 1)] : Fin 2 → ℂ) + (![(τ - 3 * 1) / 2, (τ + 1) / 2] : Fin 2 → ℂ) - (![√2 * (τ - 3 * 1) / 2, -(√2 * (τ + 1)) / 2] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (0) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (0) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.sub_mem (S.add_mem (m 1) (m 2)) (m 3))
    · have e : (![√2 * (((1 + √2) * τ) - 3 * (1 - √2)) / 2, -(√2 * (((1 + √2) * τ) + (1 - √2))) / 2] : Fin 2 → ℂ) = ((![τ, 1] + ![τ, 1] : Fin 2 → ℂ) : Fin 2 → ℂ) - ((![(τ - 3 * 1) / 2, (τ + 1) / 2] + ![(τ - 3 * 1) / 2, (τ + 1) / 2] : Fin 2 → ℂ) : Fin 2 → ℂ) + (![√2 * (τ - 3 * 1) / 2, -(√2 * (τ + 1)) / 2] : Fin 2 → ℂ) := by
        ext i; fin_cases i
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination ((τ + 3)/2) * s
        · simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Int.cast_ofNat]; linear_combination (-(τ - 1)/2) * s
      show _ ∈ S
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val, Fin.isValue] at e ⊢
      rw [e]; exact (S.add_mem (S.sub_mem (S.add_mem (m 0) (m 0)) (S.add_mem (m 2) (m 2))) (m 3))


theorem smulMap_comp (a b : ℂ) : smulMap a ∘ₗ smulMap b = smulMap (a * b) := by
  ext v i; simp [smulMap, mul_smul]

theorem one_sub_sqrt2_ne : (1 - (√2 : ℂ)) ≠ 0 := by
  have h : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rw [show (1 - (√2 : ℂ)) = ((1 - √2 : ℝ) : ℂ) by push_cast; ring]
  exact Complex.ofReal_ne_zero.mpr (by linarith)

/-- **Normalization (proved):** if `w` is not a complex multiple of a real vector, `ι(𝒪)w` is a
nonzero multiple of `Λ_τ` for some `τ ∈ ℍ` (using the unit `1 + i` of reduced norm `−1` when
`Im(w₀/w₁) < 0`). -/
theorem normalize (w : Fin 2 → ℂ) (hw : ¬ ∃ (c : ℂ) (r : Fin 2 → ℝ), w = c • (fun i => (r i : ℂ))) :
    ∃ (τ : ℂ) (hτ : 0 < τ.im) (c : ℂ), c ≠ 0 ∧ qmOrbit w = (qmLattice hτ.ne').map (smulMap c) := by
  have hw2 : w 1 ≠ 0 := by
    intro h0; apply hw; refine ⟨w 0, ![1, 0], ?_⟩; ext i; fin_cases i <;> simp [h0]
  set t := w 0 / w 1 with ht_def
  have hwt : w = w 1 • ![t, 1] := by
    ext i; fin_cases i
    · simp [t]; field_simp
    · simp
  have ht : t.im ≠ 0 := by
    intro h0; apply hw; refine ⟨w 1, ![t.re, 1], ?_⟩
    rw [hwt]; ext i; fin_cases i
    · simp; left; exact Complex.ext (by simp) (by simp [h0])
    · simp
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · set k : ℝ := (1 + √2) / (1 - √2) with hk
    have hk0 : k < 0 := by
      have h1 : (1 : ℝ) < √2 := by
        rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      exact div_neg_of_pos_of_neg (by positivity) (by linarith)
    set τ' : ℂ := (k : ℂ) * t with hτ'_def
    have hτ' : 0 < τ'.im := by
      rw [hτ'_def, Complex.im_ofReal_mul]; exact mul_pos_of_neg_of_neg hk0 hneg
    refine ⟨τ', hτ', w 1 * (1 - √2), mul_ne_zero hw2 one_sub_sqrt2_ne, ?_⟩
    have hv : (![(1 + √2) * t, 1 - √2] : Fin 2 → ℂ) = (1 - √2 : ℂ) • ![τ', 1] := by
      have hs := one_sub_sqrt2_ne
      ext i; fin_cases i
      · simp only [hτ'_def, hk, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.smul_apply,
          smul_eq_mul]
        push_cast
        field_simp
      · simp
    rw [hwt, qmOrbit_smul, qmOrbit_unit, hv, qmOrbit_smul, ← qmLattice_eq_orbit hτ'.ne',
      ← Submodule.map_comp, smulMap_comp]
    simp
  · refine ⟨t, hpos, w 1, hw2, ?_⟩
    rw [hwt, qmOrbit_smul, ← qmLattice_eq_orbit hpos.ne']
    simp

end FQMNorm

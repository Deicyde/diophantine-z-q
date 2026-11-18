import ZInQKernel.Contrib.OneProof.RC.O12Local.Convention

/-! The normalized vector in the lower-right convention (tex 9819–9820,
9836). The two possible comparisons of the norms of the bottom-row entries
give the two cells needed here. The cell calculation is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Local

open Matrix

variable {p : ℕ} [Fact p.Prime]

private def lower (x : ℚ_[p]) : GL (Fin 2) ℚ_[p] :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 0; x, 1] (by simp [det_fin_two])

private def weyl : GL (Fin 2) ℚ_[p] :=
  GeneralLinearGroup.mkOfDetNeZero !![0, -1; 1, 0] (by simp [det_fin_two])

private theorem lower_atK1 {x : ℚ_[p]} (hx : ‖x‖ < 1) : atK1 p 1 (lower x) := by
  refine ⟨?_, ?_, Or.inr ⟨?_, ?_⟩⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [lower, hx.le]
  · simp [lower, det_fin_two]
  · have h := (Padic.norm_lt_pow_iff_norm_le_pow_sub_one x 0).mp (by simpa using hx)
    simpa [lower] using h
  · simp [lower]

private theorem upper_atK1 {u : ℚ_[p]ˣ} (hu : ‖(u : ℚ_[p])‖ = 1)
    {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) : atK1 p 1 (upper u 1 x) := by
  refine ⟨?_, ?_, Or.inr ⟨?_, ?_⟩⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [upper, hu, hx]
  · simp [upper, det_fin_two, hu]
  · simp [upper]
  · simp [upper]

private theorem swap_diagonal (u : ℚ_[p]ˣ) :
    (weyl : GL (Fin 2) ℚ_[p]) * upper u 1 0 = upper 1 u 0 * weyl := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [weyl, upper, Matrix.mul_apply, Fin.sum_univ_two]

/-- The open cell (BK_0(p)), using explicit factors in the two entry tests. -/
def InBorelK0 (g : GL (Fin 2) ℚ_[p]) : Prop :=
  ∃ (a d : ℚ_[p]ˣ) (x : ℚ_[p]) (k : GL (Fin 2) ℚ_[p]),
    atK0 p 1 k ∧ g = upper a d x * k

/-- A lower row with (|c|<|d|) factors using a lower unipotent in the fixed group. -/
theorem factor_in_open_cell (g : GL (Fin 2) ℚ_[p])
    (h : ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0‖ < ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1‖) :
    ∃ (a d : ℚ_[p]ˣ) (x : ℚ_[p]) (k : GL (Fin 2) ℚ_[p]),
      atK1 p 1 k ∧ g = upper a d x * k := by
  let A : Matrix (Fin 2) (Fin 2) ℚ_[p] := g
  let c := A 1 0
  let d := A 1 1
  have hdet : A.det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  change ‖c‖ < ‖d‖ at h
  have hn : d ≠ 0 := by
    intro e
    exact (not_lt_of_ge (norm_nonneg c)) (by simpa [e] using h)
  let a := Units.mk0 (A.det / d) (div_ne_zero hdet hn)
  let du := Units.mk0 d hn
  let k : GL (Fin 2) ℚ_[p] := lower (c / d)
  have hk : atK1 p 1 k := lower_atK1
    (by rwa [norm_div, div_lt_one (norm_pos_iff.mpr hn)])
  refine ⟨a, du, A 0 1, k, hk, ?_⟩
  apply GeneralLinearGroup.ext
  intro i j
  change A i j = _
  fin_cases i <;> fin_cases j <;>
    simp [a, du, k, c, d, lower, upper, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two] <;>
    field_simp [d, hn]
  all_goals ring

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V]
variable {π : LocalAction p E V} {halfMod μ₁ μ₂ : LocalCharacter p E}

/-- The inducing function of a fixed vector vanishes on the second cell.
The character on the lower diagonal forces this because it is ramified. -/
theorem InducedModel.vanishes_on_weyl (M : InducedModel p π halfMod μ₁ μ₂)
    (hhalf : charTrivialAt p halfMod 0) (h₂ : charConductor p μ₂ 1)
    {v : V} (hv : v ∈ levelSpace p π 1) :
    M.realize v (weyl : GL (Fin 2) ℚ_[p]) = 0 := by
  classical
  have hn : ¬ charTrivialAt p μ₂ 0 := h₂.2 0 Nat.zero_lt_one
  obtain ⟨u, hu, hne⟩ : ∃ u, unitAtLevel p 0 u ∧ μ₂ u ≠ 1 := by
    by_contra! h
    exact hn h
  have hinv : unitAtLevel p 0 u⁻¹ := ⟨by simpa [norm_inv] using congrArg Inv.inv hu.1, Or.inl rfl⟩
  have he := M.right_translate v weyl (upper u 1 0)
  rw [hv _ (upper_atK1 hu.1 (by simp)), swap_diagonal, M.covariance] at he
  simp only [map_one, Units.val_one, one_div, hhalf _ hinv, one_mul, mul_one] at he
  by_contra h
  apply hne
  apply Units.ext
  exact mul_right_cancel₀ h (he.symm.trans (one_mul _).symm)

/-- Outside (BK_0(p)) the lower row has (|d|le|c|) and the induced function
vanishes. On the other cell its value is given by upper covariance from (1). -/
theorem InducedModel.support_and_evaluation (M : InducedModel p π halfMod μ₁ μ₂)
    (hhalf : charTrivialAt p halfMod 0) (h₂ : charConductor p μ₂ 1)
    {v : V} (hv : v ∈ levelSpace p π 1) (g : GL (Fin 2) ℚ_[p]) :
    (‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1‖ ≤ ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 0‖ ∨
      M.realize v 1 = 0) → M.realize v g = 0 := by
  let A : Matrix (Fin 2) (Fin 2) ℚ_[p] := g
  let c := A 1 0
  let d := A 1 1
  have hdet : A.det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  intro hor
  by_cases hdc : ‖d‖ ≤ ‖c‖
  · have hn : c ≠ 0 := by
      intro h
      have hd : d = 0 := norm_le_zero_iff.mp (by simpa [h] using hdc)
      apply hdet
      rw [det_fin_two, show A 1 0 = 0 from h, show A 1 1 = 0 from hd]
      ring
    let a := Units.mk0 (A.det / c) (div_ne_zero hdet hn)
    let cu := Units.mk0 c hn
    let k : GL (Fin 2) ℚ_[p] := upper 1 1 (d / c)
    have hk : atK1 p 1 k := upper_atK1 (by simp)
      (by rwa [norm_div, div_le_one (norm_pos_iff.mpr hn)])
    have e : g = upper a cu (A 0 0) * ((weyl : GL (Fin 2) ℚ_[p]) * k) := by
      apply GeneralLinearGroup.ext
      intro i j
      change A i j = _
      fin_cases i <;> fin_cases j <;>
        simp [a, cu, k, c, d, weyl, upper, Matrix.mul_apply, Fin.sum_univ_two, det_fin_two] <;>
        field_simp [c, hn]
      all_goals ring
    rw [e, M.covariance, ← M.right_translate v weyl k, hv _ hk,
      M.vanishes_on_weyl hhalf h₂ hv, mul_zero]
  · obtain ⟨a, du, x, k, hk, e⟩ := factor_in_open_cell g (lt_of_not_ge hdc)
    have hz : M.realize v 1 = 0 := hor.resolve_left hdc
    rw [e, M.covariance, ← one_mul k, ← M.right_translate v 1 k, hv _ hk, hz, mul_zero]

/-- The induced function is supported on the cell needed in tex 9836
(vanishing outside (BK_0(p))). -/
theorem InducedModel.supported_BorelK0 (M : InducedModel p π halfMod μ₁ μ₂)
    (hhalf : charTrivialAt p halfMod 0) (h₂ : charConductor p μ₂ 1)
    {v : V} (hv : v ∈ levelSpace p π 1) {g : GL (Fin 2) ℚ_[p]} (hg : ¬ InBorelK0 g) :
    M.realize v g = 0 := by
  apply M.support_and_evaluation hhalf h₂ hv g
  left
  apply le_of_not_gt
  intro h
  obtain ⟨a, d, x, k, hk, e⟩ := factor_in_open_cell g h
  have hk₀ := ((switchMatrix_atK1 p 1 k).mp hk).1
  rw [switchMatrix_atK0] at hk₀
  exact hg ⟨a, d, x, k, hk₀, e⟩

/-- The fixed vector has the lower-right (K_0(p)) character of tex 9820.
Dividing by the central scalar with value (g_{22}) leaves an element of (K_1(p)). -/
theorem InducedModel.right_equivariantK0 (M : InducedModel p π halfMod μ₁ μ₂)
    {χ : LocalCharacter p E} (hcentral : centralAction p π χ) (hχ : χ = μ₁ * μ₂)
    (h₁ : charTrivialAt p μ₁ 0) {v : V} (hv : v ∈ levelSpace p π 1)
    {g : GL (Fin 2) ℚ_[p]} (hg : atK0 p 1 g) :
    ∃ d : ℚ_[p]ˣ, (d : ℚ_[p]) = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 ∧
      ∀ t, M.realize v (t * g) = (μ₂ d : E) * M.realize v t := by
  let A : Matrix (Fin 2) (Fin 2) ℚ_[p] := g
  obtain ⟨hint, hdet, hc⟩ := hg
  simp only [pow_one] at hc
  have hinvp : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by
    exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hd : ‖A 1 1‖ = 1 := by
    apply le_antisymm (hint 1 1)
    by_contra! h
    have hab : ‖A 0 0 * A 1 1‖ < 1 := by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hint 0 0)).trans_lt h
    have hbc : ‖A 0 1 * A 1 0‖ < 1 := by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hint 0 1)).trans_lt (hc.trans_lt hinvp)
    have hlt : ‖A.det‖ < 1 := by
      rw [det_fin_two, sub_eq_add_neg]
      exact (Padic.nonarchimedean _ _).trans_lt (by simpa using max_lt hab hbc)
    exact hlt.ne hdet
  let d : ℚ_[p]ˣ := Units.mk0 (A 1 1) (norm_ne_zero_iff.mp (by simp [hd]))
  let k := upper d⁻¹ d⁻¹ 0 * g
  have e : (k : Matrix (Fin 2) (Fin 2) ℚ_[p]) = ((d⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) • A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [k, upper, A, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
  have hdn : ‖((d⁻¹ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by simp [d, hd]
  have hk : atK1 p 1 k := by
    have hn (i j : Fin 2) : ‖(k : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ = ‖A i j‖ := by
      rw [e, Matrix.smul_apply, smul_eq_mul, norm_mul, hdn, one_mul]
    refine ⟨fun i j => (hn i j).trans_le (hint i j), ?_, Or.inr ⟨?_, ?_⟩⟩
    · change ‖(k : Matrix (Fin 2) (Fin 2) ℚ_[p]).det‖ = 1
      rw [e, Matrix.det_smul, norm_mul, norm_pow, hdn, one_pow, one_mul]
      exact hdet
    · simpa only [pow_one, hn] using hc
    · change ‖(k : Matrix (Fin 2) (Fin 2) ℚ_[p]) 1 1 - 1‖ ≤ _
      rw [e, Matrix.smul_apply, smul_eq_mul]
      have hn : A 1 1 ≠ 0 := d.ne_zero
      simp [d, hn]
  have hi : upper d d 0 * upper d⁻¹ d⁻¹ 0 = 1 := by
    apply GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [upper, Matrix.mul_apply, Fin.sum_univ_two, d.ne_zero]
  have hfactor : upper d d 0 * k = g := by rw [show k = upper d⁻¹ d⁻¹ 0 * g from rfl, ← mul_assoc,
    hi, one_mul]
  have hchar : χ d = μ₂ d := by
    have hu : unitAtLevel p 0 d := ⟨hd, Or.inl rfl⟩
    simp [hχ, h₁ d hu]
  have hπ : π g v = (μ₂ d : E) • v := by
    rw [← hfactor, map_mul]
    change π (upper d d 0) (π k v) = _
    rw [hv _ hk, hcentral, hchar]
  refine ⟨d, rfl, fun t => ?_⟩
  rw [← M.right_translate, hπ, map_smul, Pi.smul_apply, smul_eq_mul]

/-- A nonzero conductor-one fixed vector can be normalized to evaluation (1). -/
theorem InducedModel.normalized_generator (M : InducedModel p π halfMod μ₁ μ₂)
    (hhalf : charTrivialAt p halfMod 0) (h₂ : charConductor p μ₂ 1)
    (hlevel : hasLevel p π 1) : ∃ v ∈ levelSpace p π 1, M.realize v 1 = 1 := by
  obtain ⟨v, hv, hn⟩ := hlevel
  have he : M.realize v 1 ≠ 0 := by
    intro h
    apply hn
    apply M.injective
    rw [map_zero]
    funext g
    exact M.support_and_evaluation hhalf h₂ hv g (Or.inr h)
  refine ⟨(M.realize v 1)⁻¹ • v, Submodule.smul_mem _ _ hv, ?_⟩
  simp [he]

#print axioms lower_atK1
#print axioms upper_atK1
#print axioms swap_diagonal
#print axioms InducedModel.vanishes_on_weyl
#print axioms factor_in_open_cell
#print axioms InducedModel.support_and_evaluation
#print axioms InducedModel.supported_BorelK0
#print axioms InducedModel.right_equivariantK0
#print axioms InducedModel.normalized_generator

end ZInQ.Manuscript.RC.O12Local

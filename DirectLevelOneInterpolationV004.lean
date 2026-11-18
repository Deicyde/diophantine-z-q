import DirectOrbitInterpolationV001

/-!
# Level-one coefficients in the actual orbit interpolant

Integral slashing permutes both actual orbit columns. The two determinant
signs cancel, so the squared denominator and every interpolation
coefficient are genuinely invariant under the full modular group.
Normalized actual trace then supplies their level-one modular-form fields.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Pointwise BigOperators

namespace DirectLevelOneInterpolation

open DirectTorsionOrbit DirectOrbitAlgebra DirectOrbitInterpolation DirectWeightedDeterminant

/-- Scaling the columns has the ordinary product-of-scalars determinant factor. -/
theorem determinant_scale_columns {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (d : Fin r → ℂ) :
    Matrix.det (fun i j => d j * M i j) = (∏ j, d j) * Matrix.det M := by
  have he : (fun i j => d j * M i j) = M * Matrix.diagonal d := by
    funext i j
    simp only [Matrix.mul_diagonal]
    ring
  rw [he, Matrix.det_mul, Matrix.det_diagonal]
  ring

/-- The finite product of nonzero integer powers has exactly the sum exponent. -/
theorem product_zpow {ι : Type*} (s : Finset ι) (w : ι → ℤ) (d : ℂ) (hd : d ≠ 0) :
    (∏ i ∈ s, d ^ w i) = d ^ (∑ i ∈ s, w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hd]

/-- Slashing a homogeneous determinant slashes every actual matrix entry in its column weight. -/
theorem determinant_slash_value {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    {r : ℕ} (w : Fin r → ℤ) (F : (i j : Fin r) → ModularForm Γ (w j))
    (γ : SL(2, ℤ)) (τ : ℍ) :
    (⇑(determinantForm w F) ∣[∑ j, w j] γ) τ =
      Matrix.det (fun i j => (⇑(F i j) ∣[w j] γ) τ) := by
  rw [ModularForm.SL_slash_apply, determinantForm_apply]
  have he : (fun i j => (⇑(F i j) ∣[w j] γ) τ) =
      (fun i j => denom γ τ ^ (-w j) * F i j (γ • τ)) := by
    funext i j
    rw [ModularForm.SL_slash_apply]
    ring
  rw [he, determinant_scale_columns]
  have hp := product_zpow Finset.univ (fun j => -w j) (denom γ τ) (denom_ne_zero γ τ)
  simp only [Finset.sum_neg_distrib] at hp
  rw [hp]
  ring

/-- Taking a power of a weight-one form commutes with the actual integral slash. -/
theorem weight_one_power_slash {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    (f : ModularForm Γ 1) (n : ℕ) (γ : SL(2, ℤ)) :
    ⇑(f.pow n) ∣[(n : ℤ)] γ = (⇑f ∣[(1 : ℤ)] γ) ^ n := by
  funext τ
  simp [ModularForm.SL_slash_apply, ModularForm.coe_pow, Pi.pow_apply, mul_pow,
    zpow_neg, zpow_natCast]

/-- The column replacement has the same actual row-permutation law. -/
theorem replacedEntry_slash (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (γ : SL(2, ℤ))
    (j i c : Fin (orbitLength N)) :
    ⇑(replacedEntry N hN k f j i c) ∣[replacedWeight k j c] γ =
      ⇑(replacedEntry N hN k f j (cosetPermutation N γ i) c) := by
  classical
  by_cases hc : c = j
  · have hw : replacedWeight k j c = k := by simp [replacedWeight, hc]
    simp only [replacedEntry, dif_pos hc, ModularForm.coe_mcast, hw]
    exact formOrbit_slash N k f γ i
  · have hw : replacedWeight k j c = (c : ℤ) := by simp [replacedWeight, hc]
    simp only [replacedEntry, dif_neg hc, ModularForm.coe_mcast, hw]
    rw [weight_one_power_slash, torsionOrbit_slash]
    simp only [ModularForm.coe_pow]

/-- The actual Vandermonde denominator transforms by the derived permutation sign. -/
theorem denominator_slash (N : ℕ) [NeZero N] (hN : 3 ≤ N) (γ : SL(2, ℤ)) :
    ⇑(orbitDenominator N hN) ∣[orbitWeight N] γ =
      Equiv.Perm.sign (cosetPermutation N γ) • ⇑(orbitDenominator N hN) := by
  funext τ
  unfold orbitDenominator vandermondeForm
  change (⇑(determinantForm (fun j : Fin (orbitLength N) => (j : ℤ))
    (fun i j => ModularForm.mcast (by ring) ((torsionOrbit N hN i).pow (j : ℕ))))
      ∣[∑ j : Fin (orbitLength N), (j : ℤ)] γ) τ = _
  rw [determinant_slash_value]
  have he : (fun (i j : Fin (orbitLength N)) =>
      (⇑(ModularForm.mcast (by ring) ((torsionOrbit N hN i).pow (j : ℕ))) ∣[(j : ℤ)] γ) τ) =
      (fun (i j : Fin (orbitLength N)) =>
        (ModularForm.mcast (by ring) ((torsionOrbit N hN (cosetPermutation N γ i)).pow (j : ℕ))) τ) := by
    funext i j
    simp only [ModularForm.coe_mcast]
    rw [weight_one_power_slash, torsionOrbit_slash]
    simp only [ModularForm.coe_pow, Pi.pow_apply]
  rw [he]
  let M : Matrix (Fin (orbitLength N)) (Fin (orbitLength N)) ℂ := fun i j =>
    (ModularForm.mcast (by ring) ((torsionOrbit N hN i).pow (j : ℕ))) τ
  have h := Matrix.det_permute (cosetPermutation N γ) M
  have hm : M.submatrix (cosetPermutation N γ) id =
      (fun (i j : Fin (orbitLength N)) =>
        (ModularForm.mcast (by ring) ((torsionOrbit N hN (cosetPermutation N γ i)).pow (j : ℕ))) τ) := by
    funext i j
    simp only [Matrix.submatrix_apply, id_eq, M]
  rw [hm] at h
  simpa only [M, Units.smul_def, FunLike.coe_smul, Pi.smul_apply,
    zsmul_eq_mul, orbitWeight, orbitDenominator, vandermondeForm, determinantForm_apply] using h

/-- The cofactor transforms by the very same actual sign. -/
theorem cofactor_slash (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (γ : SL(2, ℤ))
    (j : Fin (orbitLength N)) :
    ⇑(cofactorForm N hN k f j) ∣[k + orbitWeight N - (j : ℤ)] γ =
      Equiv.Perm.sign (cosetPermutation N γ) • ⇑(cofactorForm N hN k f j) := by
  have hw : (∑ c : Fin (orbitLength N), replacedWeight k j c) =
      k + orbitWeight N - (j : ℤ) := by
    simp only [replacedWeight, Finset.sum_add_distrib]
    simp [orbitWeight]
    ring
  funext τ
  simp only [cofactorForm, ModularForm.coe_mcast]
  rw [← hw, determinant_slash_value]
  have he : (fun i c => (⇑(replacedEntry N hN k f j i c) ∣[replacedWeight k j c] γ) τ) =
      (fun i c => replacedEntry N hN k f j (cosetPermutation N γ i) c τ) := by
    funext i c
    rw [replacedEntry_slash]
  rw [he]
  have h := congrArg
    (fun F : ModularForm ((Gamma N).map (mapGL ℝ)) (∑ c, replacedWeight k j c) => F τ)
    (determinantForm_row_permute (replacedWeight k j) (replacedEntry N hN k f j)
      (cosetPermutation N γ))
  simpa only [determinantForm_apply, Units.smul_def, FunLike.coe_smul, Pi.smul_apply,
    zsmul_eq_mul] using h

/-- Every coefficient in the pole-free interpolant is actually level-one invariant. -/
theorem coefficient_slash_invariant (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (γ : SL(2, ℤ))
    (j : Fin (orbitLength N)) :
    ⇑(coefficientForm N hN k f j) ∣[k + 2 * orbitWeight N - (j : ℤ)] γ =
      ⇑(coefficientForm N hN k f j) := by
  have hw : k + 2 * orbitWeight N - (j : ℤ) =
      orbitWeight N + (k + orbitWeight N - (j : ℤ)) := by ring
  have he : ⇑(coefficientForm N hN k f j) =
      ⇑(orbitDenominator N hN) * ⇑(cofactorForm N hN k f j) := by
    funext τ
    exact coefficientForm_apply N hN k f j τ
  rw [he, hw, ModularForm.mul_slash_SL2, denominator_slash, cofactor_slash]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (cosetPermutation N γ)) with hs | hs
  · simp [hs, Units.smul_def]
  · simp [hs, Units.smul_def]

/-- The actual squared denominator is likewise level-one invariant. -/
theorem squared_denominator_slash_invariant (N : ℕ) [NeZero N] (hN : 3 ≤ N) (γ : SL(2, ℤ)) :
    (⇑(orbitDenominator N hN) * ⇑(orbitDenominator N hN)) ∣[2 * orbitWeight N] γ =
      ⇑(orbitDenominator N hN) * ⇑(orbitDenominator N hN) := by
  rw [show 2 * orbitWeight N = orbitWeight N + orbitWeight N by ring,
    ModularForm.mul_slash_SL2, denominator_slash]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (cosetPermutation N γ)) with hs | hs
  · simp [hs, Units.smul_def]
  · simp [hs, Units.smul_def]

/-- A genuine level-one form obtained from actual normalized trace. -/
def toLevelOne (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm ((Gamma N).map (mapGL ℝ)) k) : ModularForm 𝒮ℒ k :=
  (Nat.card (𝒮ℒ ⧸ ((Gamma N).map (mapGL ℝ)).subgroupOf 𝒮ℒ) : ℂ)⁻¹ •
    ModularForm.trace 𝒮ℒ f

/-- For a proved invariant input, the normalized trace has exactly the original function. -/
theorem toLevelOne_coe (N : ℕ) [NeZero N] (k : ℤ)
    (f : ModularForm ((Gamma N).map (mapGL ℝ)) k)
    (hf : ∀ γ : SL(2, ℤ), ⇑f ∣[k] γ = ⇑f) : ⇑(toLevelOne N k f) = ⇑f := by
  classical
  let Q := 𝒮ℒ ⧸ ((Gamma N).map (mapGL ℝ)).subgroupOf 𝒮ℒ
  letI : Fintype Q := Fintype.ofFinite Q
  have hq (q : Q) : SlashInvariantForm.quotientFunc f q = ⇑f := by
    induction q using QuotientGroup.induction_on' with
    | H g =>
        obtain ⟨γ, hγ⟩ := g.property
        rw [SlashInvariantForm.quotientFunc_mk]
        change ⇑f ∣[k] g.val⁻¹ = ⇑f
        rw [← hγ, ← map_inv]
        have he : ⇑f ∣[k] mapGL ℝ γ⁻¹ = ⇑f ∣[k] γ⁻¹ := by
          rw [ModularForm.SL_slash]
          rfl
        rw [he]
        exact hf γ⁻¹
  have hcard : (Nat.card Q : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold toLevelOne
  rw [FunLike.coe_smul, ModularForm.coe_trace]
  simp_rw [hq]
  rw [Finset.sum_const, Finset.card_univ]
  change (Nat.card Q : ℂ)⁻¹ • (Fintype.card Q • ⇑f) = ⇑f
  rw [← Nat.cast_smul_eq_nsmul ℂ, Fintype.card_eq_nat_card, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

/-- The interpolant coefficient has genuine level-one modular-form fields. -/
def levelOneCoefficient (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (j : Fin (orbitLength N)) :
    ModularForm 𝒮ℒ (k + 2 * orbitWeight N - (j : ℤ)) :=
  toLevelOne N _ (coefficientForm N hN k f j)

/-- Its underlying function equals the concrete pole-free determinant coefficient. -/
theorem levelOneCoefficient_coe (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (j : Fin (orbitLength N)) :
    ⇑(levelOneCoefficient N hN k f j) = ⇑(coefficientForm N hN k f j) :=
  toLevelOne_coe N _ _ (fun γ => coefficient_slash_invariant N hN k f γ j)

end DirectLevelOneInterpolation

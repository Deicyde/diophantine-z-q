import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionForms

/-!
# Torsion forms on the principal congruence subgroup, and residue-label transport

1. For a positive level `N` and every admissible pair `(a, b)` (not both divisible by `N`), the
   function `Torsion.torsionLogDerivative N a b` is a weight-one modular form on `Γ(N)`
   (`principalForm`). Slash invariance comes from the `SL(2, ℤ)`-covariance `F_v ∣ γ = F_{v γ}`
   and `v γ ≡ v (mod N)` for `γ ∈ Γ(N)`; holomorphy and boundedness at every cusp are those of
   the family `F_v`. No claim that the form is nonzero is made.

2. Finite integer identities for the residue-label map `δ_t (a, b) = (a, t b)`:
   * `δ_t (v T^n) = (δ_t v) T^(t n)` exactly;
   * for `γ ∈ Γ₀(N)` and `γ_t = T^n γ` with `n = (t - 1) γ₀₀ γ₀₁`, the rows `δ_t (v γ)` and
     `(δ_t v) γ_t` agree modulo `N`; `γ_t ∈ Γ₀(N)` has the same `Γ₀(N)`-label as `γ`, and
     `T^n ∈ Γ₁(N)`.
   These are statements about actual matrices; no global commutation of `δ_t` with the action
   is claimed.
-/

noncomputable section

open Complex ModularGroup
open scoped Real UpperHalfPlane MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.AllLevelPrincipal

open Torsion AllLevelForms
open ThetaFiveTorsion (act act_mul act_one)

variable {N : ℕ}

/-! ### Congruence of index pairs -/

/-- Congruence of index pairs modulo `N`. -/
def CongrN (N : ℕ) (v w : ℤ × ℤ) : Prop := (N : ℤ) ∣ v.1 - w.1 ∧ (N : ℤ) ∣ v.2 - w.2

theorem F_eq_of_congr (hN : 0 < N) {v w : ℤ × ℤ} (hw : Good N w) (h : CongrN N v w) :
    F N v = F N w := by
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := h
  obtain ⟨a, b⟩ := w
  have hv : v = (a + N * m, b + N * n) := Prod.ext (by simp at hm ⊢; linarith)
    (by simp at hn ⊢; linarith)
  funext τ
  rw [hv]
  exact F_shift hN hw m n τ

theorem good_of_congr {v w : ℤ × ℤ} (hw : Good N w) (h : CongrN N v w) : Good N v := by
  rintro ⟨h1, h2⟩
  apply hw
  exact ⟨by simpa using dvd_sub h1 h.1, by simpa using dvd_sub h2 h.2⟩

/-! ### Modular forms on `Γ(N)` for every admissible pair -/

theorem congr_act_Gamma {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) (v : ℤ × ℤ) :
    CongrN N (act v γ) v := by
  rw [CongruenceSubgroup.Gamma_mem] at hγ
  obtain ⟨h00, h01, h10, h11⟩ := hγ
  have e00 : ((γ 0 0 : ℤ) : ZMod N) = ((1 : ℤ) : ZMod N) := by simpa using h00
  have e11 : ((γ 1 1 : ℤ) : ZMod N) = ((1 : ℤ) : ZMod N) := by simpa using h11
  obtain ⟨p, hp⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).mp e00
  obtain ⟨q, hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp h01
  obtain ⟨r, hr⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp h10
  obtain ⟨s, hs⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).mp e11
  obtain ⟨a, b⟩ := v
  refine ⟨⟨-(a * p) + b * r, ?_⟩, ⟨a * q - b * s, ?_⟩⟩
  · dsimp only [act]; rw [hr]; linear_combination (-a) * hp
  · dsimp only [act]; rw [hq]; linear_combination (-b) * hs

theorem F_slash_Gamma (hN : 0 < N) {v : ℤ × ℤ} (hv : Good N v) (γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) : F N v ∣[(1 : ℤ)] γ = F N v := by
  rw [F_slash hN γ v hv]
  exact F_eq_of_congr hN hv (congr_act_Gamma hγ v)

theorem F_bdd_cusp_Gamma (hN : 0 < N) {v : ℤ × ℤ} (hv : Good N v) {c : OnePoint ℝ}
    (hc : IsCusp c ((CongruenceSubgroup.Gamma N).map (Matrix.SpecialLinearGroup.mapGL ℝ))) :
    c.IsBoundedAt (F N v) 1 := by
  have hc' : IsCusp c 𝒮ℒ := IsCusp.mono (Subgroup.map_le_range _ _) hc
  rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc']
  intro γ _
  rw [F_slash hN γ v hv]
  exact F_isBoundedAtImInfty hN (good_act hv γ)

/-- **The weight-one modular form on `Γ(N)`** with underlying function
`torsionLogDerivative N a b`, for any pair `(a, b)` not both divisible by `N`. -/
def principalForm (N : ℕ) (hN : 0 < N) (a b : ℤ) (h : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    ModularForm ((CongruenceSubgroup.Gamma N).map (Matrix.SpecialLinearGroup.mapGL ℝ)) 1 where
  toFun := F N (a, b)
  slash_action_eq' γ hγ := by
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
    have := F_slash_Gamma hN (v := (a, b)) h g hg
    rwa [ModularForm.SL_slash] at this
  holo' := UpperHalfPlane.mdifferentiable_iff.mpr (F_diffOn hN h)
  bdd_at_cusps' hc := F_bdd_cusp_Gamma hN (v := (a, b)) h hc

theorem principalForm_apply (N : ℕ) (hN : 0 < N) (a b : ℤ)
    (h : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) (τ : ℍ) :
    principalForm N hN a b h τ = torsionLogDerivative N a b τ := rfl

/-! ### Residue-label transport -/

/-- The residue-label map `δ_t (a, b) = (a, t b)`. -/
def delta (t : ℤ) (v : ℤ × ℤ) : ℤ × ℤ := (v.1, t * v.2)

theorem T_zpow_apply (n : ℤ) (i j : Fin 2) :
    (T ^ n) i j = (!![1, n; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j := by
  rw [← ModularGroup.coe_T_zpow]

/-- `δ_t (v T^n) = (δ_t v) T^(t n)`. -/
theorem delta_act_T_zpow (t n : ℤ) (v : ℤ × ℤ) :
    delta t (act v (T ^ n)) = act (delta t v) (T ^ (t * n)) := by
  obtain ⟨a, b⟩ := v
  refine Prod.ext (by simp [delta, act, T_zpow_apply]) (by simp [delta, act, T_zpow_apply]; ring)

/-- The corrected representative `γ_t = T^n γ` with `n = (t - 1) γ₀₀ γ₀₁`. -/
def gammaT (t : ℤ) (γ : SL(2, ℤ)) : SL(2, ℤ) := T ^ ((t - 1) * γ 0 0 * γ 0 1) * γ

theorem gammaT_apply (t : ℤ) (γ : SL(2, ℤ)) :
    gammaT t γ 0 0 = γ 0 0 + (t - 1) * γ 0 0 * γ 0 1 * γ 1 0 ∧
    gammaT t γ 0 1 = γ 0 1 + (t - 1) * γ 0 0 * γ 0 1 * γ 1 1 ∧
    gammaT t γ 1 0 = γ 1 0 ∧ gammaT t γ 1 1 = γ 1 1 := by
  simp only [gammaT, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    T_zpow_apply]
  simp

theorem T_zpow_mem_Gamma1 (n : ℤ) : T ^ n ∈ CongruenceSubgroup.Gamma1 N := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [T_zpow_apply]

theorem gammaT_mem_Gamma0 (t : ℤ) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    gammaT t γ ∈ CongruenceSubgroup.Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
  rw [(gammaT_apply t γ).2.2.1]
  exact hγ

/-- `γ_t` has the same `Γ₀(N)`-label (lower-right entry modulo `N`) as `γ`. -/
theorem gammaT_label (t : ℤ) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    CongruenceSubgroup.Gamma0Map N ⟨gammaT t γ, gammaT_mem_Gamma0 t hγ⟩ =
      CongruenceSubgroup.Gamma0Map N ⟨γ, hγ⟩ := by
  change ((gammaT t γ 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N)
  rw [(gammaT_apply t γ).2.2.2]

theorem gammaT_label_units (t : ℤ) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    (CongruenceSubgroup.Gamma0Map N).toHomUnits ⟨gammaT t γ, gammaT_mem_Gamma0 t hγ⟩ =
      (CongruenceSubgroup.Gamma0Map N).toHomUnits ⟨γ, hγ⟩ := by
  ext
  simpa using gammaT_label t hγ

/-- **Residue transport.** For `γ ∈ Γ₀(N)`, `δ_t (v γ) ≡ (δ_t v) γ_t (mod N)`. -/
theorem delta_act_congr (t : ℤ) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (v : ℤ × ℤ) : CongrN N (delta t (act v γ)) (act (delta t v) (gammaT t γ)) := by
  rw [CongruenceSubgroup.Gamma0_mem] at hγ
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hγ
  obtain ⟨h00, h01, h10, h11⟩ := gammaT_apply t γ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  obtain ⟨a, b⟩ := v
  refine ⟨⟨c * (b - a * ((t - 1) * γ 0 0 * γ 0 1) - t * b), ?_⟩,
    ⟨-(a * (t - 1) * γ 0 1 ^ 2 * c), ?_⟩⟩
  · simp only [delta, act, h00, h10]
    rw [hc]; ring
  · simp only [delta, act, h01, h11]
    linear_combination (-(a * (t - 1) * γ 0 1)) * hdet - (a * (t - 1) * γ 0 1 ^ 2) * hc

end ZInQ.Contrib.HeckePrimeRationality.AllLevelPrincipal

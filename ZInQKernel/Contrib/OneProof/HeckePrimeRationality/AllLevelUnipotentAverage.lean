import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelPrincipalForms
import Mathlib.NumberTheory.ModularForms.NormTrace

/-!
# The unipotent average from `Γ(N)` to `Γ₁(N)`

For a positive level `N`, an integer weight `k` and a modular form `f` on `Γ(N)`, the average
`τ ↦ N⁻¹ Σ_{j < N} (f ∣[k] T^j)(τ)` over the translates by `T^j`, `0 ≤ j < N`, is a modular form
on `Γ₁(N)` (`avg`). It restricts to the identity on forms of level `Γ₁(N)`
(`avg_restrict`), so it is a projection.

Proof of `Γ₁(N)`-invariance: for `γ ∈ Γ₁(N)` with upper-right entry `β`, each
`T^j γ T^-(j+β)` lies in `Γ(N)` (all four entries), so `f ∣ T^j γ = f ∣ T^(j+β)`; and
`m ↦ f ∣ T^m` is `N`-periodic because `T^N ∈ Γ(N)`, so the shifted sum over a full period is
unchanged. Holomorphy comes from the translates, and boundedness at a cusp `c` from
boundedness of `f` at the cusps `T^j • c`.
-/

noncomputable section

open ModularGroup
open scoped Real UpperHalfPlane MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.AllLevelAverage

open CongruenceSubgroup Matrix.SpecialLinearGroup
open AllLevelPrincipal (T_zpow_apply)

set_option quotPrecheck false in
local notation "ΓP" N => (Gamma N).map (mapGL ℝ)

set_option quotPrecheck false in
local notation "Γ1P" N => (Gamma1 N).map (mapGL ℝ)

variable {N : ℕ} {k : ℤ}

theorem Gamma_le_Gamma1' : Gamma N ≤ Gamma1 N := by
  intro γ hγ
  rw [Gamma_mem] at hγ
  rw [Gamma1_mem]
  exact ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩

theorem Gamma_map_le_Gamma1_map : (ΓP N) ≤ (Γ1P N) :=
  Subgroup.map_mono Gamma_le_Gamma1'

theorem T_zpow_N_mem_Gamma : T ^ (N : ℤ) ∈ Gamma N := by
  rw [Gamma_mem, T_zpow_apply, T_zpow_apply, T_zpow_apply, T_zpow_apply]
  simp

theorem T_zpow_mem_Gamma1' (n : ℤ) : T ^ n ∈ Gamma1 N := by
  rw [Gamma1_mem]
  simp [T_zpow_apply]

theorem slash_SL_of_mem_Gamma (f : ModularForm (ΓP N) k) {g : SL(2, ℤ)} (hg : g ∈ Gamma N) :
    ⇑f ∣[k] g = ⇑f :=
  f.slash_action_eq' (mapGL ℝ g) ⟨g, hg, rfl⟩

/-- `m ↦ f ∣ T^m` is `N`-periodic. -/
theorem slash_T_zpow_add_N (f : ModularForm (ΓP N) k) (m : ℤ) :
    ⇑f ∣[k] (T ^ (m + N) : SL(2, ℤ)) = ⇑f ∣[k] (T ^ m : SL(2, ℤ)) := by
  rw [show m + (N : ℤ) = (N : ℤ) + m by ring, zpow_add, SlashAction.slash_mul,
    slash_SL_of_mem_Gamma f T_zpow_N_mem_Gamma]

/-- Shift invariance of a full-period sum of an `N`-periodic function. -/
theorem sum_range_shift {M : Type*} [AddCommGroup M] (h : ℤ → M)
    (hper : ∀ m, h (m + N) = h m) (c : ℤ) :
    ∑ j ∈ Finset.range N, h ((j : ℤ) + c) = ∑ j ∈ Finset.range N, h j := by
  have step : ∀ c : ℤ, ∑ j ∈ Finset.range N, h ((j : ℤ) + (c + 1)) =
      ∑ j ∈ Finset.range N, h ((j : ℤ) + c) := by
    intro c
    have h1 := Finset.sum_range_succ' (fun j : ℕ => h ((j : ℤ) + c)) N
    have h2 := Finset.sum_range_succ (fun j : ℕ => h ((j : ℤ) + c)) N
    have h3 : ∑ j ∈ Finset.range N, h (((j + 1 : ℕ) : ℤ) + c) =
        ∑ j ∈ Finset.range N, h ((j : ℤ) + (c + 1)) :=
      Finset.sum_congr rfl fun j _ => by push_cast; ring_nf
    have h4 : h ((N : ℤ) + c) = h (((0 : ℕ) : ℤ) + c) := by
      rw [show (N : ℤ) + c = c + N by ring, hper]; simp
    rw [← h3]
    have := h1.symm.trans h2
    rw [h4] at this
    exact add_right_cancel this
  induction c using Int.induction_on with
  | zero => simp
  | succ n ih => rw [step, ih]
  | pred n ih =>
    rw [← ih, ← step]
    congr 1
    ext j
    ring_nf

/-- For `g ∈ Γ₁(N)`, `T^j g T^-(j + g₀₁) ∈ Γ(N)`. -/
theorem conj_mem_Gamma {g : SL(2, ℤ)} (hg : g ∈ Gamma1 N) (j : ℤ) :
    T ^ j * g * T ^ (-(j + g 0 1)) ∈ Gamma N := by
  rw [Gamma1_mem] at hg
  obtain ⟨h00, h11, h10⟩ := hg
  rw [Gamma_mem]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    T_zpow_apply]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [h00, h11, h10] <;> ring

/-- For `g ∈ Γ₁(N)`, `f ∣ T^j g = f ∣ T^(j + g₀₁)`. -/
theorem slash_T_zpow_mul (f : ModularForm (ΓP N) k) {g : SL(2, ℤ)} (hg : g ∈ Gamma1 N) (j : ℤ) :
    ⇑f ∣[k] (T ^ j * g) = ⇑f ∣[k] (T ^ (j + g 0 1) : SL(2, ℤ)) := by
  have hu := conj_mem_Gamma hg j
  have e : T ^ j * g = (T ^ j * g * T ^ (-(j + g 0 1))) * T ^ (j + g 0 1) := by
    rw [mul_assoc (T ^ j * g), ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  rw [e, SlashAction.slash_mul, slash_SL_of_mem_Gamma f hu]

/-- The averaged function. -/
def avgFun (N : ℕ) (k : ℤ) (f : ModularForm (ΓP N) k) : ℍ → ℂ :=
  ∑ j : Fin N, ⇑((N : ℂ)⁻¹ • f) ∣[k] mapGL ℝ (T ^ (j : ℤ))

theorem avgFun_apply (f : ModularForm (ΓP N) k) (τ : ℍ) :
    avgFun N k f τ = (N : ℂ)⁻¹ * ∑ j : Fin N, (⇑f ∣[k] mapGL ℝ (T ^ (j : ℤ))) τ := by
  rw [avgFun, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change (⇑((N : ℂ)⁻¹ • f) ∣[k] (T ^ (j : ℤ) : SL(2, ℤ))) τ =
    (N : ℂ)⁻¹ * (⇑f ∣[k] (T ^ (j : ℤ) : SL(2, ℤ))) τ
  rw [show ⇑((N : ℂ)⁻¹ • f) = (N : ℂ)⁻¹ • ⇑f from rfl, ModularForm.SL_smul_slash]
  rfl

theorem avgFun_slash (f : ModularForm (ΓP N) k) {g : SL(2, ℤ)} (hg : g ∈ Gamma1 N) :
    avgFun N k f ∣[k] g = avgFun N k f := by
  set f' := (N : ℂ)⁻¹ • f
  have hA : avgFun N k f = ∑ j : Fin N, ⇑f' ∣[k] (T ^ (j : ℤ) : SL(2, ℤ)) := rfl
  rw [hA, SlashAction.sum_slash]
  have hterm : ∀ j : Fin N, (⇑f' ∣[k] (T ^ (j : ℤ) : SL(2, ℤ))) ∣[k] g =
      ⇑f' ∣[k] (T ^ ((j : ℤ) + g 0 1) : SL(2, ℤ)) := fun j => by
    rw [← SlashAction.slash_mul, slash_T_zpow_mul f' hg]
  simp_rw [hterm]
  have hper : ∀ m : ℤ, ⇑f' ∣[k] (T ^ (m + N) : SL(2, ℤ)) = ⇑f' ∣[k] (T ^ m : SL(2, ℤ)) :=
    slash_T_zpow_add_N f'
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ⇑f' ∣[k] (T ^ ((j : ℤ) + g 0 1) : SL(2, ℤ))) N,
    Fin.sum_univ_eq_sum_range (fun j : ℕ => ⇑f' ∣[k] (T ^ (j : ℤ) : SL(2, ℤ))) N]
  exact sum_range_shift (fun m : ℤ => ⇑f' ∣[k] (T ^ m : SL(2, ℤ))) hper (g 0 1)

theorem isCusp_T_zpow_smul {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) (j : ℤ) :
    IsCusp (mapGL ℝ (T ^ j) • c) 𝒮ℒ := by
  obtain ⟨g, rfl⟩ := isCusp_SL2Z_iff'.mp hc
  rw [isCusp_SL2Z_iff']
  exact ⟨T ^ j * g, by rw [map_mul, mul_smul]⟩

/-- **The unipotent average** `N⁻¹ Σ_{j < N} f ∣ T^j`, a modular form on `Γ₁(N)`. -/
def avg (N : ℕ) (hN : 0 < N) (k : ℤ) (f : ModularForm (ΓP N) k) : ModularForm (Γ1P N) k where
  toFun := avgFun N k f
  slash_action_eq' γ hγ := by
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
    exact avgFun_slash f hg
  holo' := by
    have h := MDifferentiable.sum (t := (Finset.univ : Finset (Fin N))) fun j _ =>
      (ModularFormClass.holo ((N : ℂ)⁻¹ • f)).slash k (mapGL ℝ (T ^ (j : ℤ)))
    exact h
  bdd_at_cusps' {c} hc := by
    have : NeZero N := ⟨hN.ne'⟩
    have hcSL : IsCusp c 𝒮ℒ := IsCusp.mono (Subgroup.map_le_range _ _) hc
    intro γ hγ
    subst hγ
    have hA : avgFun N k f = ∑ j : Fin N, ⇑((N : ℂ)⁻¹ • f) ∣[k] mapGL ℝ (T ^ (j : ℤ)) := rfl
    change UpperHalfPlane.IsBoundedAtImInfty (avgFun N k f ∣[k] γ)
    rw [hA, SlashAction.sum_slash, UpperHalfPlane.IsBoundedAtImInfty, Filter.BoundedAtFilter,
      Finset.sum_fn]
    refine .fun_sum fun j _ => ?_
    have hcj : IsCusp ((mapGL ℝ (T ^ (j : ℤ)) * γ) • OnePoint.infty) (ΓP N) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, mul_smul]
      exact isCusp_T_zpow_smul hcSL _
    have hb := ((N : ℂ)⁻¹ • f).bdd_at_cusps' hcj (mapGL ℝ (T ^ (j : ℤ)) * γ) rfl
    rw [SlashAction.slash_mul] at hb
    exact hb

theorem avg_apply (N : ℕ) (hN : 0 < N) (k : ℤ) (f : ModularForm (ΓP N) k) (τ : ℍ) :
    avg N hN k f τ = (N : ℂ)⁻¹ * ∑ j : Fin N, (⇑f ∣[k] mapGL ℝ (T ^ (j : ℤ))) τ :=
  avgFun_apply f τ

/-- **Projection.** The average is the identity on forms of level `Γ₁(N)`. -/
theorem avg_restrict (N : ℕ) (hN : 0 < N) (k : ℤ) (g : ModularForm (Γ1P N) k) :
    avg N hN k (ModularForm.restrict Gamma_map_le_Gamma1_map g) = g := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  ext τ
  rw [avg_apply]
  have hterm : ∀ j : Fin N,
      (⇑(ModularForm.restrict Gamma_map_le_Gamma1_map g) ∣[k] mapGL ℝ (T ^ (j : ℤ))) τ = g τ :=
    fun j => by
      have := g.slash_action_eq' (mapGL ℝ (T ^ (j : ℤ))) ⟨_, T_zpow_mem_Gamma1' _, rfl⟩
      exact congr_fun this τ
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end ZInQ.Contrib.HeckePrimeRationality.AllLevelAverage

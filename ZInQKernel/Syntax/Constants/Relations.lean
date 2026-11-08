import ZInQKernel.Syntax.Constants.Fixed

/-!
# Structural facts about the fixed constants

Blueprint: `syntax/constants/fixed-constants.md`.

Positivity, divisibility and order relations between the named constants, and their
identification with the catalogue of the hypothesis file and with upstream's
`ExplicitCutoffBounds`. Everything is proved from the defining equations `Ps_eq`, `W_eq`, …;
no constant is unfolded or evaluated (see the note in `Fixed.lean`).
-/

namespace ZInQ.Syntax

/-! ### The primorial constants -/

theorem Ps_eq_literal : Ps =
    19361386640700823163471425054312320082662897612571563761906962414215012369856637179096947335243680669607531475629148240284399976570 := by
  rw [Ps_eq, primorial_324_eq]

theorem W_eq_literal : W =
    77445546562803292653885700217249280330651590450286255047627849656860049479426548716387789340974722678430125902516592961137599906280 := by
  rw [W_eq, Ps_eq, four_mul_primorial_324_eq]

theorem Ps_pos : 0 < Ps := by rw [Ps_eq]; exact primorial_pos 324

theorem W_pos : 0 < W := by rw [W_eq]; exact Nat.mul_pos (by norm_num) Ps_pos

theorem Ps_dvd_W : Ps ∣ W := by rw [W_eq]; exact Dvd.intro_left 4 rfl

/-- `W` is the modulus `catalogueModulus` of the hypothesis file. -/
theorem W_eq_catalogueModulus : W = catalogueModulus := by
  rw [W_eq, Ps_eq]
  let p := primorial 324
  exact (show catalogueModulus = 4 * p from rfl).symm

/-! ### The catalogue -/

theorem Hcat_eq_catalogueModulus : Hcat = catalogueProduct catalogueModulus 22 324 := by
  rw [Hcat_eq, W_eq_catalogueModulus]

theorem Hmax_eq_catalogueModulus : Hmax = catalogueMax catalogueModulus 22 324 := by
  rw [Hmax_eq, W_eq_catalogueModulus]

theorem Hcat_pos : 0 < Hcat := by rw [Hcat_eq]; exact catalogueProduct_pos _ _ _

/-- `H_cat` is the product of the catalogue `𝓗` of the hypothesis file. -/
theorem Hcat_eq_prod_catalogueSet :
    Hcat = ∏ h ∈ catalogueFinset catalogueModulus 22 324, h ∧
      catalogueSet = ↑(catalogueFinset catalogueModulus 22 324) :=
  ⟨by rw [Hcat_eq_catalogueModulus]; exact catalogueProduct_eq_prod_catalogueFinset _ _ _,
    catalogueSet_eq⟩

theorem dvd_Hcat_of_mem_catalogueSet {h : ℕ} (hh : h ∈ catalogueSet) : h ∣ Hcat := by
  obtain ⟨r, i, hr, hcop, hi, rfl⟩ := hh
  rw [Hcat_eq_catalogueModulus, cataloguePrime_catalogueModulus]
  exact cataloguePrime_dvd_catalogueProduct (mem_unitResidues_catalogueModulus.2 ⟨hr, hcop⟩) hi

theorem le_Hmax_of_mem_catalogueSet {h : ℕ} (hh : h ∈ catalogueSet) : h ≤ Hmax := by
  obtain ⟨r, i, hr, hcop, hi, rfl⟩ := hh
  rw [Hmax_eq_catalogueModulus, cataloguePrime_catalogueModulus]
  exact cataloguePrime_le_catalogueMax (mem_unitResidues_catalogueModulus.2 ⟨hr, hcop⟩) hi

theorem Hmax_le_Hcat : Hmax ≤ Hcat := by
  rw [Hmax_eq, Hcat_eq]; exact catalogueMax_le_catalogueProduct _ _ _

/-- `H_max > 324`: the class of `1` contains a catalogue prime. -/
theorem lt_Hmax : 324 < Hmax := by
  have h1 : 1 ∈ unitResidues catalogueModulus :=
    mem_unitResidues_catalogueModulus.2 ⟨two_le_catalogueModulus, Nat.coprime_one_left _⟩
  rw [Hmax_eq_catalogueModulus]
  exact (lt_cataloguePrime h1 0).trans_le (cataloguePrime_le_catalogueMax h1 (by norm_num))

theorem Hmax_pos : 0 < Hmax := (Nat.zero_lt_succ 323).trans lt_Hmax

/-- Hypothesis CAT₈ gives `H_max < 2^(W⁸)`. -/
theorem Hmax_lt_of_catalogueBound8 (hCAT : CatalogueBound8) : Hmax < 2 ^ W ^ 8 := by
  rw [Hmax_eq_catalogueModulus, W_eq_catalogueModulus]
  exact catalogueMax_lt_of_catalogueBound8 hCAT

theorem coprime_Ps_Hcat : Nat.Coprime Ps Hcat := by
  rw [Ps_eq, Hcat_eq]; exact coprime_primorial_catalogueProduct _ _ _

/-! ### `N_s`, `M₀`, `c_*` and `ℓ` -/

theorem Ns_pos : 0 < Ns := by rw [Ns_eq]; exact Nat.mul_pos Ps_pos Hcat_pos

theorem Ps_dvd_Ns : Ps ∣ Ns := by rw [Ns_eq]; exact Dvd.intro _ rfl

theorem Hcat_dvd_Ns : Hcat ∣ Ns := by rw [Ns_eq]; exact Dvd.intro_left _ rfl

/-- If some index succeeds for `N_s`, then `M₀` is the least one. -/
theorem M0_spec (h : ∃ m, 1 ≤ m ∧ FormalCondition Ns m) :
    1 ≤ M0 ∧ FormalCondition Ns M0 ∧ ∀ m, 1 ≤ m → FormalCondition Ns m → M0 ≤ m := by
  rw [M0_eq]; exact leastFormalMultiple_spec h

/-- `M₀ = 0` if no index succeeds (the size chapter proves that one does). -/
theorem M0_eq_zero (h : ¬∃ m, 1 ≤ m ∧ FormalCondition Ns m) : M0 = 0 := by
  rw [M0_eq]; exact leastFormalMultiple_eq_zero h

theorem cstar_pos_iff : 0 < cstar ↔ 0 < M0 := by
  rw [cstar_eq]; omega

theorem ell_pos : 0 < ell := by
  rw [ell_eq]; exact Nat.mul_pos (by norm_num) (Nat.mul_pos (pow_pos Ps_pos _) (pow_pos Hcat_pos _))

/-! ### `F`, `D`, `G₀`, `E₀` -/

theorem F_pos : 0 < F := by rw [F_eq]; exact Nat.factorial_pos 324

theorem D_pos : 0 < D := by
  rw [D_eq]; exact Nat.mul_pos F_pos (pow_pos (by norm_num) _)

theorem F_dvd_D : F ∣ D := by rw [D_eq]; exact Dvd.intro _ rfl

theorem F_le_D : F ≤ D := Nat.le_of_dvd D_pos F_dvd_D

theorem G0_pos : 0 < G0 := by rw [G0_eq]; norm_num

theorem E0_pos : 0 < E0 := by
  rw [E0_eq]; exact Nat.mul_pos (by norm_num) (pow_pos (Nat.mul_pos D_pos G0_pos) _)

/-- `F` is upstream's `ExplicitCutoffBounds.factorialBase`. -/
theorem F_eq_factorialBase : F = ExplicitCutoffBounds.factorialBase := by
  rw [F_eq]; rfl

/-- `D` is upstream's `ExplicitCutoffBounds.d`. -/
theorem D_eq_explicitCutoffBounds_d : D = ExplicitCutoffBounds.d := by
  rw [D_eq, F_eq_factorialBase]
  let f := ExplicitCutoffBounds.factorialBase
  exact (show ExplicitCutoffBounds.d = f * 3 ^ (256 * f ^ 4) from rfl).symm

/-- `G₀` is upstream's `ExplicitCutoffBounds.g0`. -/
theorem G0_eq_g0 : G0 = ExplicitCutoffBounds.g0 := by rw [G0_eq]; rfl

/-! ### `R`, `Q` -/

theorem D_le_R : D ≤ R := by
  rw [R_eq]; exact (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem Hmax_le_R : Hmax ≤ R := by
  rw [R_eq]; exact (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))

theorem cstar_le_R : cstar ≤ R := by
  rw [R_eq]; exact (le_max_right _ _).trans (le_max_left _ _)

theorem ten_pow_twelve_le_R : 10 ^ 12 ≤ R := by
  rw [R_eq]; exact le_max_right _ _

theorem R_pos : 0 < R := (pow_pos (by norm_num) 12).trans_le ten_pow_twelve_le_R

theorem Q_pos : 0 < Q := by rw [Q_eq]; exact pow_pos R_pos _

theorem R_le_Q : R ≤ Q := by
  rw [Q_eq]
  exact le_self_pow₀ (Nat.one_le_iff_ne_zero.2 R_pos.ne') (Nat.mul_pos R_pos E0_pos).ne'

/-! ### `B_cm`, `C_cm`, `A_ht`, `T` -/

theorem Bcm_pos : 0 < Bcm := by rw [Bcm_eq]; exact Nat.pos_of_ne_zero (Nat.add_one_ne_zero _)

theorem Ccm_pos : 0 < Ccm := by
  rw [Ccm_eq]; exact Nat.add_pos_left (Nat.mul_pos (by norm_num) Bcm_pos) _

theorem two_mul_ten_pow_thirteen_le_Aht : 2 * 10 ^ 13 ≤ Aht := by
  rw [Aht_eq]
  exact Nat.le_mul_of_pos_right _ ((Nat.one_pos).trans_le ((le_max_left _ _).trans (le_max_left _ _)))

theorem Ccm_mul_le_Aht : 2 * 10 ^ 13 * Ccm ≤ Aht := by
  rw [Aht_eq]; exact Nat.mul_le_mul_left _ ((le_max_right _ _).trans (le_max_left _ _))

theorem Q_pow_mul_le_Aht : 2 * 10 ^ 13 * Q ^ 17 ≤ Aht := by
  rw [Aht_eq]; exact Nat.mul_le_mul_left _ (le_max_right _ _)

theorem Aht_pos : 0 < Aht := (by norm_num : 0 < 2 * 10 ^ 13).trans_le two_mul_ten_pow_thirteen_le_Aht

theorem T_pos : 0 < T := by rw [T_eq]; exact pow_pos (Nat.mul_pos (by norm_num) Aht_pos) _

theorem Aht_le_T : Aht ≤ T := by
  rw [T_eq]
  calc Aht ≤ 48 * Aht := Nat.le_mul_of_pos_left _ (by norm_num)
    _ ≤ (48 * Aht) ^ 13 :=
      le_self_pow₀ (Nat.one_le_iff_ne_zero.2 (Nat.mul_pos (by norm_num) Aht_pos).ne') (by norm_num)

end ZInQ.Syntax

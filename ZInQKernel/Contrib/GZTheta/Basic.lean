import ZInQKernel.Contrib.GZDecomp.Decomp
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Coefficient
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.TrivialNebentypus

/-!
# gz-theta: the theta series of `ψ_d` as a twist of the level-32 form

Task gz-theta. Toward the leaf `ZInQ.GZDecomp.HeckeThetaNewform` (L1 of gz-decomp).

* `heckeCoeff d n = (n/d) · heckeCoeff 1 n` (`heckeCoeff_eq_jacobiSym_mul`).
* `jacobiChar d`: the Jacobi symbol `n ↦ (n/d)` as a Dirichlet character modulo `d`.
* `CMForm32`: the theta series `∑ heckeCoeff 1 n qⁿ` of `ψ₁` is a cusp form on `Γ₀(32)`
  (Hecke; modularity of `y² = x³ − x`). Not proved here.
* `cmForm hF d`: from such a form `F`, the twist `F ⊗ (·/d)` (Tau Ceti `CuspForm.twist`), a cusp
  form on `Γ₁(32 d²)` with trivial nebentypus and coefficients `heckeCoeff d n`.
-/

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2 ModularForm Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace ZInQ.GZTheta

open ZInQ.Contrib.HeckeFE

/-! ### The coefficients factor through the Jacobi symbol -/

theorem heckeCoeff_eq_jacobiSym_mul (d n : ℕ) :
    heckeCoeff d n = (jacobiSym (n : ℤ) d : ℂ) * heckeCoeff 1 n := by
  unfold heckeCoeff
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hn : p.1 ^ 2 + p.2 ^ 2 = (n : ℤ) := mem_normFiber.mp hp
  rw [hn, jacobiSym.one_right]
  push_cast
  ring

/-! ### The Jacobi symbol as a Dirichlet character -/

theorem jacobiSym_val_natCast (d : ℕ) [NeZero d] (n : ℕ) :
    jacobiSym (((n : ZMod d).val : ℕ) : ℤ) d = jacobiSym (n : ℤ) d := by
  rw [ZMod.val_natCast, Int.natCast_mod, ← jacobiSym.mod_left]

theorem jacobiSym_val_mul (d : ℕ) [NeZero d] (x y : ZMod d) :
    jacobiSym (((x * y).val : ℕ) : ℤ) d =
      jacobiSym ((x.val : ℕ) : ℤ) d * jacobiSym ((y.val : ℕ) : ℤ) d := by
  rw [← jacobiSym.mul_left, ZMod.val_mul, Int.natCast_mod, ← jacobiSym.mod_left]
  push_cast
  rfl

/-- **The Jacobi symbol `n ↦ (n/d)` as a Dirichlet character modulo `d`.** -/
noncomputable def jacobiChar (d : ℕ) [NeZero d] : DirichletCharacter ℂ d where
  toFun x := (jacobiSym ((x.val : ℕ) : ℤ) d : ℂ)
  map_one' := by
    show (jacobiSym (((1 : ZMod d).val : ℕ) : ℤ) d : ℂ) = 1
    have := jacobiSym_val_natCast d 1
    rw [Nat.cast_one] at this
    rw [this, Nat.cast_one, jacobiSym.one_left, Int.cast_one]
  map_mul' x y := by
    show (jacobiSym (((x * y).val : ℕ) : ℤ) d : ℂ) =
      (jacobiSym ((x.val : ℕ) : ℤ) d : ℂ) * (jacobiSym ((y.val : ℕ) : ℤ) d : ℂ)
    rw [jacobiSym_val_mul, Int.cast_mul]
  map_nonunit' x hx := by
    show (jacobiSym ((x.val : ℕ) : ℤ) d : ℂ) = 0
    have h : ¬ Nat.Coprime x.val d := by
      intro hc
      apply hx
      have := (ZMod.isUnit_iff_coprime x.val d).mpr hc
      rwa [ZMod.natCast_zmod_val] at this
    have h0 : jacobiSym ((x.val : ℕ) : ℤ) d = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime]
      intro hg
      apply h
      have : Int.gcd ((x.val : ℕ) : ℤ) (d : ℤ) = 1 := hg
      rwa [Int.gcd_natCast_natCast] at this
    rw [h0, Int.cast_zero]

theorem jacobiChar_apply (d : ℕ) [NeZero d] (x : ZMod d) :
    jacobiChar d x = (jacobiSym ((x.val : ℕ) : ℤ) d : ℂ) := rfl

theorem jacobiChar_natCast (d : ℕ) [NeZero d] (n : ℕ) :
    jacobiChar d n = (jacobiSym (n : ℤ) d : ℂ) := by
  rw [jacobiChar_apply, jacobiSym_val_natCast]

/-- `(u/d)² = 1` on units. -/
theorem jacobiChar_sq_unit (d : ℕ) [NeZero d] (u : (ZMod d)ˣ) :
    jacobiChar d (u : ZMod d) ^ 2 = 1 := by
  rw [jacobiChar_apply]
  have hc : Nat.Coprime (u : ZMod d).val d := by
    have := ZMod.val_coe_unit_coprime u
    exact this
  have : jacobiSym (((u : ZMod d).val : ℕ) : ℤ) d ^ 2 = 1 :=
    jacobiSym.sq_one (by
      rw [Int.gcd_natCast_natCast]; exact hc)
  exact_mod_cast this


/-! ### The level-32 input and the twisted form -/

/-- **Hecke's theorem for `ψ₁` (modularity of `y² = x³ − x`).** The theta series
`∑_{n ≥ 1} heckeCoeff 1 n qⁿ = ¼ ∑_{α ∈ ℤ[i]} ψ₁(α) q^{N α}` of the Hecke character `ψ₁` of
`ℚ(i)` of conductor `(1 + i)³` is a cusp form of weight 2 on `Γ₀(32)` (it is `η(4τ)²η(8τ)²`).
Literature: Hecke (1936-37); Schoeneberg, *Elliptic modular functions*, Ch. IX; Miyake,
*Modular forms*, Thm 4.8.2 (UNVERIFIED locators). Not proved here. -/
def CMForm32 : Prop :=
  ∃ F : CuspForm ((Gamma0 32).map (mapGL ℝ)) 2, ∀ n : ℕ, (qExpansion 1 F).coeff n = heckeCoeff 1 n

theorem dvd_level_left (d : ℕ) : 32 * d ∣ 32 * d ^ 2 := ⟨d, by ring⟩

theorem dvd_level_right (d : ℕ) : d * d ∣ 32 * d ^ 2 := ⟨32, by ring⟩

/-- A level-32 cusp form, restricted to `Γ₁(32)`. -/
noncomputable def restrict32 (F : CuspForm ((Gamma0 32).map (mapGL ℝ)) 2) :
    CuspForm ((Gamma1 32).map (mapGL ℝ)) 2 :=
  CuspForm.restrict (Gamma1_map_le_Gamma0_map 32) F

theorem qExpansion_restrict32 (F : CuspForm ((Gamma0 32).map (mapGL ℝ)) 2) :
    qExpansion 1 (restrict32 F) = qExpansion 1 F := rfl

/-- **The theta series of `ψ_d`**, built from a level-32 form `F` as the twist `F ⊗ (·/d)`, a cusp
form on `Γ₁(32 d²)`. -/
noncomputable def cmForm (F : CuspForm ((Gamma0 32).map (mapGL ℝ)) 2) (d : ℕ) [NeZero d] :
    CuspForm ((Gamma1 (32 * d ^ 2)).map (mapGL ℝ)) 2 :=
  CuspForm.twist (jacobiChar d) (dvd_level_left d) (dvd_level_right d) (restrict32 F)

theorem qExpansion_cmForm_coeff {F : CuspForm ((Gamma0 32).map (mapGL ℝ)) 2}
    (hF : ∀ n : ℕ, (qExpansion 1 F).coeff n = heckeCoeff 1 n) (d : ℕ) [NeZero d] (n : ℕ) :
    (qExpansion 1 (cmForm F d)).coeff n = heckeCoeff d n := by
  rw [cmForm, CuspForm.qExpansion_twist_coeff, qExpansion_restrict32, hF, jacobiChar_natCast,
    heckeCoeff_eq_jacobiSym_mul d n]

/-- The twisted character `1 · (·/d)²` is trivial. -/
theorem twistChar_eq_one (d : ℕ) [NeZero d] :
    ((1 : (ZMod 32)ˣ →* ℂˣ).comp (ZMod.unitsMap (dvd_of_mul_right_dvd (dvd_level_left d))) *
        ((jacobiChar d).toUnitHom.comp
          (ZMod.unitsMap (dvd_of_mul_left_dvd (dvd_level_right d)))) ^ 2) = 1 := by
  ext u
  simp only [MonoidHom.mul_apply, MonoidHom.one_comp, MonoidHom.one_apply, one_mul,
    MonoidHom.pow_apply, MonoidHom.comp_apply, Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom,
    Units.val_one]
  exact jacobiChar_sq_unit d _

theorem cmForm_mem_cuspFormCharSpace (F : CuspForm ((Gamma0 32).map (mapGL ℝ)) 2) (d : ℕ)
    [NeZero d] : cmForm F d ∈ cuspFormCharSpace 2 (1 : (ZMod (32 * d ^ 2))ˣ →* ℂˣ) := by
  have h := CuspForm.twist_mem_cuspFormCharSpace (jacobiChar d) (dvd_level_left d)
    (dvd_level_right d) (TauCeti.restrict_mem_cuspFormCharSpace_one (N := 32) (k := 2) F)
  rw [twistChar_eq_one] at h
  exact h

theorem cmForm_ne_zero {F : CuspForm ((Gamma0 32).map (mapGL ℝ)) 2}
    (hF : ∀ n : ℕ, (qExpansion 1 F).coeff n = heckeCoeff 1 n) (d : ℕ) [NeZero d] :
    cmForm F d ≠ 0 := by
  intro h0
  have h1 := qExpansion_cmForm_coeff hF d 1
  rw [h0, heckeCoeff_one] at h1
  simp [qExpansion_zero] at h1


/-! ### Hecke eigenform -/

theorem odd_of_mod_four {d : ℕ} (hd4 : d % 4 = 1) : Odd d := Nat.odd_iff.mpr (by omega)

theorem not_dvd_two_mul_of_coprime {d p : ℕ} (hp : p.Prime) (hpN : Nat.Coprime p (32 * d ^ 2)) :
    ¬ p ∣ 2 * d := by
  intro h
  have h2 : 2 * d ∣ 32 * d ^ 2 := ⟨16 * d, by ring⟩
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp (hpN.coprime_dvd_right h2) h

theorem dvd_two_mul_iff_not_coprime {d p : ℕ} (hp : p.Prime) :
    p ∣ 2 * d ↔ ¬ Nat.Coprime p (32 * d ^ 2) := by
  constructor
  · intro h hc
    exact not_dvd_two_mul_of_coprime hp hc h
  · intro h
    rw [Nat.Prime.coprime_iff_not_dvd hp, not_not] at h
    have h32 : (32 * d ^ 2 : ℕ) = 2 ^ 5 * d ^ 2 := by ring
    rw [h32] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h2 | hd
    · exact dvd_mul_of_dvd_left (hp.dvd_of_dvd_pow h2) d
    · exact dvd_mul_of_dvd_right (hp.dvd_of_dvd_pow hd) 2

/-- The prime-power recursion of `heckeCoeff d` for odd squarefree `d` (from `HeckeFE`). -/
theorem heckePrimePow' {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) : HeckePrimePow d :=
  heckePrimePow_of_split (odd_of_mod_four hd4) hsq (heckePrimePowSplit d)

/-- **The theta series of `ψ_d` is an eigenform of the good Hecke operators**, given `CMForm32`. -/
theorem exists_eigenformAway_cmForm {F : CuspForm ((Gamma0 32).map (mapGL ℝ)) 2}
    (hF : ∀ n : ℕ, (qExpansion 1 F).coeff n = heckeCoeff 1 n) (d : ℕ) [NeZero d]
    (hd4 : d % 4 = 1) (hsq : Squarefree d) :
    ∃ E : EigenformAwayFromLevel (32 * d ^ 2) 2, E.toCuspForm = cmForm F d ∧ E.χ = 1 := by
  refine EigenformAwayFromLevel.exists_toCuspForm_eq_and_χ_eq_of_qExpansion_coeff_mul_of_prime_pow_add_two
    (cmForm_mem_cuspFormCharSpace F d) (cmForm_ne_zero hF d) (fun u v huv => ?_)
    (fun p hp hpN r => ?_)
  · simp only [qExpansion_cmForm_coeff hF d]
    exact heckeMult d u v huv
  · simp only [qExpansion_cmForm_coeff hF d]
    rw [heckePrimePow' hd4 hsq p hp r, ite_eq_right (not_dvd_two_mul_of_coprime hp hpN)]
    simp only [MonoidHom.one_apply, Units.val_one, one_mul]
    norm_num

/-- **The theta series of `ψ_d` is an eigenform of every Hecke operator `T_n`** (bad `n`
included), given `CMForm32`. -/
theorem exists_eigenform_cmForm {F : CuspForm ((Gamma0 32).map (mapGL ℝ)) 2}
    (hF : ∀ n : ℕ, (qExpansion 1 F).coeff n = heckeCoeff 1 n) (d : ℕ) [NeZero d]
    (hd4 : d % 4 = 1) (hsq : Squarefree d) :
    ∃ E : Eigenform (32 * d ^ 2) 2, E.toCuspForm = cmForm F d ∧ E.χ = 1 := by
  refine Eigenform.exists_toCuspForm_eq_and_χ_eq_of_qExpansion_coeff_mul_of_prime_pow_add_two
    (cmForm_mem_cuspFormCharSpace F d) (cmForm_ne_zero hF d) (fun u v huv => ?_)
    (fun p hp r => ?_)
  · simp only [qExpansion_cmForm_coeff hF d]
    exact heckeMult d u v huv
  · simp only [qExpansion_cmForm_coeff hF d]
    rw [heckePrimePow' hd4 hsq p hp r]
    by_cases hpN : Nat.Coprime p (32 * d ^ 2)
    · rw [ite_eq_right (not_dvd_two_mul_of_coprime hp hpN), ← ZMod.coe_unitOfCoprime p hpN,
        MulChar.ofUnitHom_coe]
      simp only [MonoidHom.one_apply, Units.val_one, one_mul]
      norm_num
    · rw [ite_eq_left ((dvd_two_mul_iff_not_coprime hp).mpr hpN),
        MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
      ring

/-! ### Newness, and the leaf -/

/-- **Newness of the theta series of `ψ_d` at level `32 d²`.** Every cusp form on `Γ₁(32 d²)`
with coefficients `heckeCoeff d n` lies in Tau Ceti's new subspace. (`ψ_d` is primitive of
conductor `(1+i)³ d`, and `|d_K| N(𝔣) = 32 d²`: Miyake, *Modular forms*, Thm 4.8.2; Shimura 1971
§3.6; Iwaniec, *Topics*, Thm 12.5; UNVERIFIED locators.) Not proved here. -/
def NewCM : Prop :=
  ∀ (d : ℕ) [NeZero d], d % 4 = 1 → Squarefree d →
    ∀ F : CuspForm ((Gamma1 (32 * d ^ 2)).map (mapGL ℝ)) 2,
      (∀ n : ℕ, (qExpansion 1 F).coeff n = heckeCoeff d n) → F ∈ TauCeti.cuspFormsNew (32 * d ^ 2) 2

/-- **`HeckeThetaNewform` from modularity of the level-32 form and newness.** -/
theorem heckeThetaNewform_of_cmForm32_newCM (h32 : CMForm32) (hnew : NewCM) :
    ZInQ.GZDecomp.HeckeThetaNewform := by
  intro d hd4 hsq
  have : NeZero d := ⟨by omega⟩
  obtain ⟨F, hF⟩ := h32
  obtain ⟨E, hE, hEχ⟩ := exists_eigenformAway_cmForm hF d hd4 hsq
  refine ⟨32 * d ^ 2, inferInstance, ⟨E, ?_, ?_⟩, hEχ, fun n _ => ?_⟩
  · rw [hE]
    exact hnew d hd4 hsq _ (qExpansion_cmForm_coeff hF d)
  · rw [hE, qExpansion_cmForm_coeff hF d 1, heckeCoeff_one]
  · show (qExpansion 1 E.toCuspForm).coeff n = _
    rw [hE, qExpansion_cmForm_coeff hF d n]

end ZInQ.GZTheta

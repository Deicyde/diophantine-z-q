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

end ZInQ.GZTheta

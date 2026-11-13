import ZInQKernel.Model.DivisionPolynomials.NonTorsion

/-!
# Jacobian representatives of multiples

The triple `jac n = (4φ_n, 4c_n, 2ψ_n) = 2 • (φ_n, ω_n, ψ_n)` with `φ_n = xψ_n² - ψ_{n+1}ψ_{n-1}`,
`c_n = ψ_{2n}/ψ_n` (Mathlib's `complEDS₂`) and `ω_n = c_n/2`, and the two identities
`dblXYZ (jac n) = 8 • jac (2n)` and `addXYZ (jac (n+1)) (jac n) = (-8) • jac (2n+1)`,
proved here at a point where no `ψ_n` (`n ≠ 0`) vanishes.
-/

namespace ZInQ.DivisionPolynomials

open WeierstrassCurve WeierstrassCurve.Jacobian Polynomial
open ZInQ.Syntax (WA divF3 divF4)

local notation3 "X" => (0 : Fin 3)
local notation3 "Y" => (1 : Fin 3)
local notation3 "Z" => (2 : Fin 3)

section CommRing

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `c_n = ψ_{2n}/ψ_n`, i.e. `2ω_n`. -/
noncomputable def cw (A x y : R) (n : ℤ) : R :=
  complEDS₂ (2 * y) ((divF3 A).eval x) ((divF4 A).eval x) n

lemma w_mul_cw (A x y : R) (n : ℤ) : w A x y n * cw A x y n = w A x y (2 * n) :=
  normEDS_mul_complEDS₂ ..

/-- `φ_n = xψ_n² - ψ_{n+1}ψ_{n-1}`. -/
noncomputable def phiw (A x y : R) (n : ℤ) : R :=
  x * w A x y n ^ 2 - w A x y (n + 1) * w A x y (n - 1)

/-- The Jacobian representative `(4φ_n, 4c_n, 2ψ_n)` of `[n]P`. -/
noncomputable def jac (A x y : R) (n : ℤ) : Fin 3 → R :=
  ![4 * phiw A x y n, 4 * cw A x y n, 2 * w A x y n]

lemma WA_map (A : R) (f : R →+* S) : (WA A).map f = WA (f A) := by
  ext <;> simp [WA]

lemma map_w (f : R →+* S) (A x y : R) (n : ℤ) : f (w A x y n) = w (f A) (f x) (f y) n := by
  simp only [w, map_normEDS, map_mul, map_ofNat, ZInQ.Syntax.divF3, ZInQ.Syntax.divF4, eval_sub,
    eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat, map_sub, map_add, map_pow]

lemma map_cw (f : R →+* S) (A x y : R) (n : ℤ) : f (cw A x y n) = cw (f A) (f x) (f y) n := by
  simp only [cw, map_complEDS₂, map_mul, map_ofNat, ZInQ.Syntax.divF3, ZInQ.Syntax.divF4, eval_sub,
    eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_ofNat, map_sub, map_add, map_pow]

lemma map_jac (f : R →+* S) (A x y : R) (n : ℤ) : f ∘ jac A x y n = jac (f A) (f x) (f y) n := by
  ext i
  fin_cases i <;> simp [jac, phiw, map_w, map_cw, map_ofNat]

lemma addZ_jac (A x y : R) (n : ℤ) :
    addZ (jac A x y (n + 1)) (jac A x y n) = -8 * (2 * w A x y (2 * n + 1)) := by
  have e := w_odd A x y n
  simp only [addZ, jac, phiw, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, show n + 1 + 1 = n + 2 by ring, show n + 1 - 1 = n by ring]
  linear_combination 16 * e

lemma dblZ_jac (A x y : R) (n : ℤ) :
    (WA A).toJacobian.dblZ (jac A x y n) = 8 * (2 * w A x y (2 * n)) := by
  have e := w_mul_cw A x y n
  simp only [dblZ, negY, jac, WA, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  linear_combination 16 * e

end CommRing

section Field

variable {F : Type*} [Field F] {A : F}

lemma jac_div_X (h2 : (2 : F) ≠ 0) {x y : F} {n : ℤ} (hw0 : w A x y n ≠ 0) :
    jac A x y n X / jac A x y n Z ^ 2 = xmul A x y n := by
  simp only [jac, phiw, xmul, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  field_simp
  ring

lemma jac_div_Y (h2 : (2 : F) ≠ 0) {x y : F} {n : ℤ} (hw0 : w A x y n ≠ 0) :
    jac A x y n Y / jac A x y n Z ^ 3 = ymul A x y n := by
  simp only [jac, ymul, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, Matrix.cons_val_zero, ← w_mul_cw A x y n]
  field_simp
  ring

lemma jac_Z (A x y : F) (n : ℤ) : jac A x y n Z = 2 * w A x y n := rfl

/-- Two nonsingular representatives with the same nonzero `Z` and the same affine point
are equal. -/
lemma eq_of_toAffine_eq {P Q : Fin 3 → F} (hP : (WA A).toJacobian.Nonsingular P)
    (hQ : (WA A).toJacobian.Nonsingular Q) (hz : P Z = Q Z) (hQz : Q Z ≠ 0)
    (h : Point.toAffine (WA A).toJacobian P = Point.toAffine (WA A).toJacobian Q) : P = Q := by
  have hPz : P Z ≠ 0 := hz ▸ hQz
  rw [Point.toAffine_of_Z_ne_zero hP hPz, Point.toAffine_of_Z_ne_zero hQ hQz,
    Affine.Point.some.injEq, hz] at h
  obtain ⟨hx, hy⟩ := h
  rw [div_left_inj' (pow_ne_zero 2 hQz)] at hx
  rw [div_left_inj' (pow_ne_zero 3 hQz)] at hy
  ext i
  fin_cases i
  · exact hx
  · exact hy
  · exact hz

variable [DecidableEq F]

/-- At a point where no `ψ_n` (`n ≠ 0`) vanishes, `jac n` represents `[n]P` for `n ≥ 1`. -/
lemma jac_spec_of_ne_zero (h2 : (2 : F) ≠ 0) {x y : F} (h : (WA A).toAffine.Nonsingular x y)
    (hw : ∀ n : ℤ, n ≠ 0 → w A x y n ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    (WA A).toJacobian.Nonsingular (jac A x y n) ∧
      Point.toAffine (WA A).toJacobian (jac A x y n) = n • Affine.Point.some x y h := by
  obtain ⟨h', e⟩ := exists_nsmul_eq h2 h hw n hn
  have hw0 := hw n (by omega)
  have hz : jac A x y n Z ≠ 0 := mul_ne_zero h2 hw0
  have ns : (WA A).toJacobian.Nonsingular (jac A x y n) := by
    rw [nonsingular_of_Z_ne_zero hz, jac_div_X h2 hw0, jac_div_Y h2 hw0]; exact h'
  refine ⟨ns, ?_⟩
  rw [Point.toAffine_of_Z_ne_zero ns hz, e]
  simp only [jac_div_X h2 hw0, jac_div_Y h2 hw0]

/-- The doubling and addition identities at a point where no `ψ_n` (`n ≠ 0`) vanishes. -/
theorem jac_identities_of_ne_zero (h2 : (2 : F) ≠ 0) {x y : F}
    (h : (WA A).toAffine.Nonsingular x y) (hw : ∀ n : ℤ, n ≠ 0 → w A x y n ≠ 0) (n : ℕ)
    (hn : 1 ≤ n) :
    (WA A).toJacobian.dblXYZ (jac A x y n) = (8 : F) • jac A x y (2 * n) ∧
      (WA A).toJacobian.addXYZ (jac A x y (n + 1)) (jac A x y n) =
        (-8 : F) • jac A x y (2 * n + 1) := by
  have h8 : (8 : F) ≠ 0 := by
    rw [show (8 : F) = 2 * 2 * 2 by norm_num]; exact mul_ne_zero (mul_ne_zero h2 h2) h2
  obtain ⟨ns, e⟩ := jac_spec_of_ne_zero h2 h hw n hn
  obtain ⟨ns1, e1⟩ := jac_spec_of_ne_zero h2 h hw (n + 1) (by omega)
  obtain ⟨ns2, e2⟩ := jac_spec_of_ne_zero h2 h hw (2 * n) (by omega)
  obtain ⟨ns3, e3⟩ := jac_spec_of_ne_zero h2 h hw (2 * n + 1) (by omega)
  push_cast at ns1 e1 ns2 e2 ns3 e3
  constructor
  · have hD := nonsingular_add ns ns
    rw [add_self] at hD
    refine eq_of_toAffine_eq hD ((nonsingular_smul _ h8.isUnit).mpr ns2) ?_ ?_ ?_
    · rw [dblXYZ_Z, dblZ_jac, (smul_fin3_ext _ _).2.2]; rfl
    · rw [(smul_fin3_ext _ _).2.2, jac_Z]; exact mul_ne_zero h8 (mul_ne_zero h2 (hw _ (by omega)))
    · rw [← add_self, Point.toAffine_add ns ns, e, Point.toAffine_smul _ h8.isUnit, e2,
        ← add_nsmul, two_mul]
  · have hne : ¬ jac A x y (n + 1) ≈ jac A x y n := by
      intro hc
      have := Point.toAffine_of_equiv (W := (WA A).toJacobian) hc
      rw [e1, e, succ_nsmul, add_eq_left] at this
      exact Affine.Point.some_ne_zero h this
    have hS := nonsingular_add ns1 ns
    rw [add_of_not_equiv hne] at hS
    have h8' : IsUnit (-8 : F) := (neg_ne_zero.mpr h8).isUnit
    refine eq_of_toAffine_eq hS ((nonsingular_smul _ h8').mpr ns3) ?_ ?_ ?_
    · rw [addXYZ_Z, addZ_jac, (smul_fin3_ext _ _).2.2]; rfl
    · rw [(smul_fin3_ext _ _).2.2, jac_Z]
      exact mul_ne_zero (neg_ne_zero.mpr h8) (mul_ne_zero h2 (hw _ (by omega)))
    · rw [← add_of_not_equiv hne, Point.toAffine_add ns1 ns, e1, e, Point.toAffine_smul _ h8', e3,
        ← add_nsmul]
      congr 1
      ring

end Field

end ZInQ.DivisionPolynomials

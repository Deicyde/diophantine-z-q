/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup (git blob 7f760edfba66daa24f2949d5363307b660044d05, sha256 76c64696304a381061d711e0ad18b9626076d9493972bba2f43d219b6e42880b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ComplexIwasawa
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_ComplexIwasawa_kC_mem_specialUnitaryGroup

open AutomorphicForm.ComplexIwasawa

noncomputable section

namespace RhoTwoAux

variable {g : Matrix (Fin 2) (Fin 2) ℂ}

private theorem radC_sq_aux (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    radC g z ^ 2 = Complex.normSq (botP g z) + Complex.normSq (botQ g z) := by
  rw [radC, Real.sq_sqrt (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))]

private theorem radC_pos_aux (hg : g.det ≠ 0) (z : ℂ) : 0 < radC g z := by
  rw [radC]
  apply Real.sqrt_pos.2
  rcases (add_nonneg (Complex.normSq_nonneg (botP g z)) (Complex.normSq_nonneg (botQ g z))).lt_or_eq
    with h | h
  · exact h
  · exfalso
    have hP : Complex.normSq (botP g z) = 0 := by
      nlinarith [Complex.normSq_nonneg (botP g z), Complex.normSq_nonneg (botQ g z)]
    have hQ : Complex.normSq (botQ g z) = 0 := by
      nlinarith [Complex.normSq_nonneg (botP g z), Complex.normSq_nonneg (botQ g z)]
    have hP0 := Complex.normSq_eq_zero.1 hP
    have hQ0 := Complex.normSq_eq_zero.1 hQ
    rw [botP] at hP0
    rw [botQ] at hQ0
    apply hg
    rw [Matrix.det_fin_two]
    have ha : g 0 0 = -(z * g 1 0) := by linear_combination hP0
    have hb : g 0 1 = -(z * g 1 1) := by linear_combination hQ0
    rw [ha, hb]
    ring

private theorem key_aux (g : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    botP g z * (starRingEnd ℂ) (botP g z) + botQ g z * (starRingEnd ℂ) (botQ g z)
      = (radC g z : ℂ) * (radC g z : ℂ) := by
  rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add, ← Complex.ofReal_mul]
  norm_cast
  rw [← pow_two]
  linarith [radC_sq_aux g z]

private theorem weylUnip_eq_aux (z : ℂ) :
    !![(0 : ℂ), 1; 1, 0] * !![1, z; 0, 1] * g
      = !![g 1 0, g 1 1; g 0 0 + z * g 1 0, g 0 1 + z * g 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem conjTranspose_mul_kC_aux (hg : g.det ≠ 0) (z : ℂ) :
    (kC g z).conjTranspose * kC g z = 1 := by
  have hr : (radC g z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radC_pos_aux hg z).ne'
  have key := key_aux g z
  rw [kC, Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two, map_div₀, map_neg,
      Complex.conj_ofReal] <;>
    (try field_simp) <;>
    first
    | linear_combination key
    | ring

private theorem det_kC_aux (hg : g.det ≠ 0) (z : ℂ) : (kC g z).det = 1 := by
  have hr : (radC g z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (radC_pos_aux hg z).ne'
  have e : (kC g z).det = (botQ g z * (starRingEnd ℂ) (botQ g z)
      + botP g z * (starRingEnd ℂ) (botP g z)) / ((radC g z : ℂ) * (radC g z : ℂ)) := by
    rw [kC, Matrix.det_fin_two_of]
    ring
  have num : ((Complex.normSq (botQ g z) + Complex.normSq (botP g z) : ℝ) : ℂ)
      = (radC g z : ℂ) * (radC g z : ℂ) := by
    rw [← Complex.ofReal_mul]
    norm_cast
    rw [← pow_two]
    linarith [radC_sq_aux g z]
  rw [e, Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add, num,
    div_self (mul_ne_zero hr hr)]

end RhoTwoAux

end

open RhoTwoAux in
theorem solution
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) (z : ℂ) :
    kC g z ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
  exact ⟨by rw [Matrix.star_eq_conjTranspose]; exact conjTranspose_mul_kC_aux hg z, det_kC_aux hg z⟩

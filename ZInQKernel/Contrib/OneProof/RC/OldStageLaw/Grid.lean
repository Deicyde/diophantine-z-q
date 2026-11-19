import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Coset
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! The rectangular lattice `ℤ³` for `∑ aᵢ xᵢ²` has polar dual
`∏ (2aᵢ)⁻¹ ℤ`. On its finite quotient the real Poisson formula is a finite
Fourier transform. This works with arbitrary complex weights on the cosets,
including a finite character times a fixed sieve. -/

noncomputable section

set_option maxHeartbeats 800000

namespace ZInQ.Manuscript.RC.OldStageLaw

open Complex
open UpperHalfPlane hiding I
open scoped BigOperators Real MatrixGroups Manifold

/-- The discriminant group of the chosen rectangular sublattice. -/
abbrev Grid (a : Fin 3 → ℕ) := (i : Fin 3) → ZMod (2 * a i)

variable {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)]

def offset (r : Grid a) (i : Fin 3) : ℝ := (r i).val / (2 * a i : ℝ)

def gridTheta (w : Grid a → ℂ) (z : ℂ) : ℂ := cosetSum (fun i => a i) offset w z

/-- Value of the quadratic form modulo integers on a coset representative. -/
def energy (r : Grid a) : ℝ := ∑ i, (a i : ℝ) * offset r i ^ 2

/-- Action of the translation `z ↦ z + n`. -/
def twist (n : ℤ) (w : Grid a → ℂ) (r : Grid a) : ℂ :=
  kernel (n : ℂ) (energy r) * w r

/-- Negative pairing phase for the finite action of the inverse, in the
convention of tex 8640–8647 and 8741–8744. -/
def pairing (r s : Grid a) : ℂ := ∏ i, ZMod.stdAddChar (-(r i * s i))

/-- Normalized finite Fourier matrix. -/
def finiteFourier (w : Grid a → ℂ) (s : Grid a) : ℂ :=
  (∏ i, 1 / (2 * (a i : ℂ)) ^ (1 / 2 : ℂ)) * ∑ r, w r * pairing r s

/-- The common real inversion factor, independent of the diagonal form. -/
def inversionFactor (z : ℂ) : ℂ := (1 / (I / z) ^ (1 / 2 : ℂ)) ^ (3 : ℕ)

theorem gridTheta_holo (ha : ∀ i, 0 < a i) (w : Grid a → ℂ) :
    MDiff (fun z : ℍ => gridTheta w z) :=
  cosetSum_holo (fun i => Nat.cast_pos.mpr (ha i)) offset w

private theorem line_translate (a : ℕ) (ha : 0 < a) (r : ZMod (2 * a))
    (k : ℤ) (z : ℍ) :
    line (a : ℝ) ((r.val : ℝ) / (2 * a)) ((z : ℂ) + (k : ℂ)) =
      kernel (k : ℂ) ((a : ℝ) * ((r.val : ℝ) / (2 * a)) ^ 2) *
        line (a : ℝ) ((r.val : ℝ) / (2 * a)) (z : ℂ) := by
  let t : ℝ := (r.val : ℝ) / (2 * a)
  let v : ℍ := ⟨(z : ℂ) + (k : ℂ), by simpa using z.im_pos⟩
  have hap : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  apply (line_hasSum hap t v).unique
  convert (line_hasSum hap t z).mul_left (kernel (k : ℂ) ((a : ℝ) * t ^ 2)) using 1
  funext n
  have hq : (a : ℝ) * ((n : ℝ) + t) ^ 2 = (a : ℝ) * t ^ 2 + ↑((a : ℤ) * n ^ 2 + r.val * n) := by
    dsimp [t]
    push_cast
    field_simp
    ring
  change kernel ((z : ℂ) + (k : ℂ)) ((a : ℝ) * ((n : ℝ) + t) ^ 2) = _
  unfold kernel
  rw [← exp_add]
  have he : 2 * π * I * ((z : ℂ) + k) * ((a : ℝ) * ((n : ℝ) + t) ^ 2 : ℝ) =
      2 * π * I * (k : ℂ) * ((a : ℝ) * t ^ 2 : ℝ) +
        2 * π * I * (z : ℂ) * ((a : ℝ) * ((n : ℝ) + t) ^ 2 : ℝ) +
        ((k * ((a : ℤ) * n ^ 2 + r.val * n) : ℤ) : ℂ) * (2 * π * I) := by
    push_cast
    have hq' := congrArg (fun x : ℝ => (x : ℂ)) hq
    push_cast at hq'
    linear_combination (2 * (π : ℂ) * I * (k : ℂ)) * hq'
  rw [he, exp_add, exp_int_mul_two_pi_mul_I, mul_one]

theorem gridTheta_translate (ha : ∀ i, 0 < a i) (w : Grid a → ℂ) (k : ℤ) (z : ℍ) :
    gridTheta w ((z : ℂ) + (k : ℂ)) = gridTheta (twist k w) z := by
  unfold gridTheta cosetSum
  refine Finset.sum_congr rfl fun r _ => ?_
  have hl (i : Fin 3) := line_translate (a i) (ha i) (r i) k z
  change w r * (∏ i, line (a i) (offset r i) ((z : ℂ) + (k : ℂ))) =
    twist k w r * ∏ i, line (a i) (offset r i) z
  have he : (∏ i, kernel (k : ℂ) ((a i : ℝ) * offset r i ^ 2)) = kernel (k : ℂ) (energy r) := by
    simp only [kernel, energy, ← Complex.exp_sum, ofReal_sum, Finset.mul_sum]
  simp_rw [show ∀ i, line (a i) (offset r i) ((z : ℂ) + (k : ℂ)) =
    kernel (k : ℂ) ((a i : ℝ) * offset r i ^ 2) * line (a i) (offset r i) z from hl]
  rw [Finset.prod_mul_distrib, he, twist]
  ring

omit [∀ i, NeZero (2 * a i)] in
/-- Integral support makes the translation operator act as the identity. -/
theorem twist_eq_of_integral (w : Grid a → ℂ)
    (hs : ∀ r, w r ≠ 0 → ∃ n : ℤ, energy r = n) (k : ℤ) : twist k w = w := by
  funext r
  by_cases h : w r = 0
  · simp [twist, h]
  obtain ⟨n, hn⟩ := hs r h
  rw [twist, hn, kernel, ofReal_intCast,
    show 2 * π * I * (k : ℂ) * (n : ℂ) = ((k * n : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
    exp_int_mul_two_pi_mul_I, one_mul]

def intResidues (C : ℕ) [NeZero C] : ℤ ≃ (ZMod C × ℤ) where
  toFun n := (n, n / C)
  invFun p := p.1.val + (C : ℤ) * p.2
  left_inv n := by
    change ((n : ZMod C).val : ℤ) + (C : ℤ) * (n / C) = n
    rw [ZMod.val_intCast, Int.emod_add_mul_ediv]
  right_inv p := by
    have hC : (C : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne C)
    have hr : (p.1.val : ℤ) / C = 0 := Int.ediv_eq_zero_of_lt_abs
      (by positivity) (by
        rw [Int.abs_natCast]
        exact_mod_cast p.1.val_lt)
    apply Prod.ext
    · simp
    · change ((p.1.val : ℤ) + C * p.2) / C = p.2
      rw [Int.add_mul_ediv_left _ _ hC, hr, zero_add]

private theorem jacobi_residues (C : ℕ) [NeZero C] (r : ZMod C) (z : ℍ) :
    jacobiTheta₂ (-(r.val : ℂ) / C) ((z : ℂ) / C) =
      ∑ s : ZMod C, ZMod.stdAddChar (-(r * s)) * line ((C : ℝ) / 2) (s.val / (C : ℝ)) z := by
  classical
  have hC := NeZero.pos C
  have hC' : (C : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hC.ne'
  let f := fun n : ℤ => jacobiTheta₂_term n (-(r.val : ℂ) / C) ((z : ℂ) / C)
  have hf : Summable f := (summable_jacobiTheta₂_term_iff _ _).mpr <| by
    rw [← ofReal_natCast, div_ofReal_im]
    exact div_pos z.im_pos (Nat.cast_pos.mpr hC)
  let e := (intResidues C).symm
  have he : Summable (fun p : ZMod C × ℤ => f (e p)) := e.summable_iff.mpr hf
  change (∑' n, f n) = _
  rw [← e.tsum_eq f, he.tsum_prod, tsum_fintype]
  refine Finset.sum_congr rfl fun s _ => ?_
  have ha : 0 < (C : ℝ) / 2 := by positivity
  rw [← (line_hasSum ha (s.val / (C : ℝ)) z).tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have hphase : (-(r * s) : ZMod C) = ((-(↑r.val * ↑s.val) : ℤ) : ZMod C) := by simp
  rw [hphase, ZMod.stdAddChar_coe, kernel, ← exp_add]
  dsimp [e, intResidues, f, jacobiTheta₂_term]
  have hperiod := exp_int_mul_two_pi_mul_I (-(r.val : ℤ) * n)
  nth_rw 2 [← mul_one (exp _)]
  rw [← hperiod, ← exp_add]
  congr 1
  push_cast
  field_simp
  ring

private theorem split_inversionFactor {a : ℝ} (ha : 0 < a) (z : ℍ) :
    1 / (2 * (a : ℂ) * I / (z : ℂ)) ^ (1 / 2 : ℂ) =
      (1 / (I / (z : ℂ)) ^ (1 / 2 : ℂ)) * (1 / (2 * (a : ℂ)) ^ (1 / 2 : ℂ)) := by
  have h : (0 : ℝ) < 2 * a := by positivity
  have hx : I / (z : ℂ) ≠ 0 := div_ne_zero I_ne_zero z.ne_zero
  have h' : ((2 * a : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h.ne'
  rw [mul_div_assoc, ← ofReal_ofNat, ← ofReal_mul,
    cpow_def_of_ne_zero (mul_ne_zero h' hx), log_ofReal_mul h hx,
    cpow_def_of_ne_zero hx, cpow_def_of_ne_zero h', ofReal_log h.le, add_mul, exp_add]
  simp only [one_div, mul_inv_rev]

theorem gridTheta_inversion (ha : ∀ i, 0 < a i) (w : Grid a → ℂ) (z : ℍ) :
    gridTheta w (-1 / (z : ℂ)) = inversionFactor z * gridTheta (finiteFourier w) z := by
  classical
  have hs (i : Fin 3) (r : ZMod (2 * a i)) :
      jacobiTheta₂ ((r.val : ℂ) / (2 * a i)) ((z : ℂ) / (2 * a i)) =
        ∑ s : ZMod (2 * a i), ZMod.stdAddChar (-(r * s)) * line (a i : ℝ) (s.val / (2 * a i)) z := by
    rw [← jacobiTheta₂_neg_left]
    have h := jacobi_residues (2 * a i) r z
    push_cast at h
    simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), neg_div] using h
  unfold gridTheta
  rw [cosetSum_inversion (fun i => Nat.cast_pos.mpr (ha i))]
  have hoff (r : Grid a) (i : Fin 3) : (offset r i : ℂ) = (r i).val / (2 * a i) := by
    unfold offset
    push_cast
    rfl
  have hf (i : Fin 3) : 1 / (2 * (a i : ℂ) * I / (z : ℂ)) ^ (1 / 2 : ℂ) =
      (1 / (I / (z : ℂ)) ^ (1 / 2 : ℂ)) * (1 / (2 * (a i : ℂ)) ^ (1 / 2 : ℂ)) := by
    simpa only [ofReal_natCast] using split_inversionFactor (Nat.cast_pos.mpr (ha i)) z
  simp only [hoff, ofReal_natCast, hs, hf, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  unfold cosetSum finiteFourier inversionFactor
  rw [mul_assoc]
  congr 1
  simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ, pairing, Finset.prod_mul_distrib,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold offset
  ring

#print axioms gridTheta_holo
#print axioms line_translate
#print axioms gridTheta_translate
#print axioms twist_eq_of_integral
#print axioms jacobi_residues
#print axioms split_inversionFactor
#print axioms gridTheta_inversion

end ZInQ.Manuscript.RC.OldStageLaw

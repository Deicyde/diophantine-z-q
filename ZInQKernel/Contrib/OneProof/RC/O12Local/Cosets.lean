import ZInQKernel.Contrib.OneProof.RC.O12Local.Conductor
import Mathlib.NumberTheory.Padics.RingHoms

/-! The (K_1(p)) stability of the finite sum (tex 9828–9835).
The permutation of its representatives is the affine map (bmapsto ab+x)
modulo (p); all remaining factors are in (K_1(p)). -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Local

open Matrix

variable {p : ℕ} [Fact p.Prime]

private theorem red_zero_iff (z : ℤ_[p]) :
    PadicInt.toZMod z = 0 ↔ ‖(z : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  change z ∈ RingHom.ker PadicInt.toZMod ↔ _
  rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
  change ‖(z : ℚ_[p])‖ < 1 ↔ _
  have h := Padic.norm_lt_pow_iff_norm_le_pow_sub_one (z : ℚ_[p]) 0
  rw [zpow_zero, show (0 : ℤ) - 1 = -1 by decide, zpow_neg_one] at h
  exact h

private theorem permute_residues (a x : ZMod p) (ha : a ≠ 0) :
    ∃ s : Equiv.Perm (Fin p), ∀ b, ((s b).val : ZMod p) = a * (b.val : ZMod p) + x := by
  let f : Fin p → Fin p := fun b => ⟨(a * (b.val : ZMod p) + x).val, ZMod.val_lt _⟩
  have hf (b : Fin p) : ((f b).val : ZMod p) = a * (b.val : ZMod p) + x :=
    ZMod.natCast_zmod_val _
  have hinj : Function.Injective f := by
    intro b c h
    have e := congrArg (fun i : Fin p => (i.val : ZMod p)) h
    rw [hf, hf, add_left_inj, mul_right_inj' ha] at e
    apply Fin.ext
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt b.isLt, Nat.mod_eq_of_lt c.isLt]
      using congrArg ZMod.val e
  exact ⟨Equiv.ofBijective f hinj.bijective_of_finite, hf⟩

/-- Left multiplication by an element of (K_1(p)) permutes the (p) terms
up to right factors in (K_1(p)). -/
theorem level_one_permutes {g : GL (Fin 2) ℚ_[p]} (hg : atK1 p 1 g) :
    ∃ s : Equiv.Perm (Fin p), ∀ b, ∃ k : GL (Fin 2) ℚ_[p],
      atK1 p 1 k ∧ g * representative p b = representative p (s b) * k := by
  let A : Matrix (Fin 2) (Fin 2) ℚ_[p] := g
  obtain ⟨hint, hdet, hcd⟩ := hg
  obtain ⟨hc, hd⟩ := hcd.resolve_left (by decide)
  simp only [pow_one] at hc hd
  let a : ℤ_[p] := ⟨A 0 0, hint 0 0⟩
  let x : ℤ_[p] := ⟨A 0 1, hint 0 1⟩
  let c : ℤ_[p] := ⟨A 1 0, hint 1 0⟩
  let d : ℤ_[p] := ⟨A 1 1, hint 1 1⟩
  have ea : (a : ℚ_[p]) = A 0 0 := rfl
  have ex : (x : ℚ_[p]) = A 0 1 := rfl
  have ec : (c : ℚ_[p]) = A 1 0 := rfl
  have ed : (d : ℚ_[p]) = A 1 1 := rfl
  let red : ℤ_[p] →+* ZMod p := PadicInt.toZMod
  have hc' : red c = 0 := (red_zero_iff c).mpr hc
  have hd' : red d = 1 := by
    have h : red (d - 1) = 0 := (red_zero_iff (d - 1)).mpr hd
    simpa only [map_sub, map_one, sub_eq_zero] using h
  have ha' : red a ≠ 0 := by
    intro h
    have hz : red (a * d - x * c) = 0 := by simp [h, hc']
    have hsmall := (red_zero_iff _).mp hz
    have e : ((a * d - x * c : ℤ_[p]) : ℚ_[p]) = A.det := by
      simp [ea, ex, ec, ed, det_fin_two]
    rw [e, hdet] at hsmall
    exact (not_le_of_gt (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt))) hsmall
  obtain ⟨s, hs⟩ := permute_residues (red a) (red x) ha'
  refine ⟨s, fun b => ?_⟩
  let b₀ : ℤ_[p] := b.val
  let b₁ : ℤ_[p] := (s b).val
  let ap : ℤ_[p] := a - b₁ * c
  let dp : ℤ_[p] := c * b₀ + d
  let num : ℤ_[p] := a * b₀ + x - b₁ * dp
  have hred : red b₁ = red a * red b₀ + red x := by
    simpa [b₀, b₁] using hs b
  have hdp : red dp = 1 := by simp [dp, hc', hd']
  have hnum : red num = 0 := by simp [num, hdp, hred]
  have hdp₁ : red (dp - 1) = 0 := by simp [hdp]
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let M : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
    !![(ap : ℚ_[p]), (num : ℚ_[p]) / (p : ℚ_[p]);
      (p : ℚ_[p]) * (c : ℚ_[p]), (dp : ℚ_[p])]
  have hMdet : M.det = A.det := by
    simp [M, ap, num, dp, ea, ex, ec, ed, b₀, b₁, det_fin_two]
    field_simp [hp]
    ring
  have hMnonzero : M.det ≠ 0 := hMdet ▸ (isUnits_det_units g).ne_zero
  let k : GL (Fin 2) ℚ_[p] := GeneralLinearGroup.mkOfDetNeZero M hMnonzero
  have hbound (z : ℤ_[p]) : ‖(z : ℚ_[p])‖ ≤ 1 := z.2
  have hinvp : (p : ℝ)⁻¹ ≤ 1 := (inv_lt_one_of_one_lt₀ (by
    exact_mod_cast (Fact.out : p.Prime).one_lt)).le
  have hnormPC : ‖(p : ℚ_[p]) * (c : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_mul, Padic.norm_p]
    exact mul_le_of_le_one_right (inv_nonneg.mpr (Nat.cast_nonneg _)) (hbound c)
  have hnormNum : ‖(num : ℚ_[p]) / (p : ℚ_[p])‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr hp), Padic.norm_p]
    exact (red_zero_iff _).mp hnum
  refine ⟨k, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro i j
    change ‖M i j‖ ≤ 1
    fin_cases i <;> fin_cases j <;>
      first | exact hbound ap | exact hnormNum | exact hnormPC.trans hinvp | exact hbound dp
  · change ‖M.det‖ = 1
    rwa [hMdet]
  · refine Or.inr ⟨?_, ?_⟩
    · change ‖M 1 0‖ ≤ _
      simpa [M] using hnormPC
    · change ‖M 1 1 - 1‖ ≤ _
      simpa [M] using (red_zero_iff _).mp hdp₁
  · apply GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [k, M, ap, num, dp, ea, ex, ec, ed, b₀, b₁, representative, uniformizer, upper,
        Matrix.mul_apply, Fin.sum_univ_two, A] <;>
      field_simp [hp] <;> ring

#print axioms red_zero_iff
#print axioms permute_residues
#print axioms level_one_permutes

end ZInQ.Manuscript.RC.O12Local

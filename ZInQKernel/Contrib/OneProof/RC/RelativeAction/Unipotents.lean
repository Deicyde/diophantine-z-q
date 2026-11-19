import ZInQKernel.Contrib.OneProof.RC.RelativeAction.Fourier
import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Transform

/-! Concrete relative word actions for tex 8627–8634 and 8658–8663.
Word bookkeeping is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.RelativeAction

open OldStageLaw CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups

variable {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)]

private theorem reference_energy (s : Grid referenceForm) : ∃ n : ℤ, 4 * energy s = n := by
  refine ⟨∑ i, ((s i).val : ℤ) ^ 2, ?_⟩
  simp only [energy, offset, referenceForm, Nat.cast_one, one_mul, mul_one, Finset.mul_sum,
    Int.cast_sum, Int.cast_pow, Int.cast_natCast]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Depth two at the dyadic reference is enough: the quadratic phase
for every multiple of four fixes its entire Fourier transform. -/
theorem twist_finiteFourier_reference (k : ℤ) (hk : (4 : ℤ) ∣ k) :
    twist k (finiteFourier referenceWeight) = finiteFourier referenceWeight := by
  apply twist_finiteFourier_eq _ ⊥
  · intro u hu r
    rw [show u = 0 from hu, add_zero]
  · intro s _
    obtain ⟨n, hn⟩ := reference_energy s
    obtain ⟨j, rfl⟩ := hk
    refine ⟨j * n, ?_⟩
    push_cast
    linear_combination (j : ℝ) * hn

/-- Use the actual inverse of the Weyl step, with no scalar in conjugation. -/
def lowerWord (k : ℤ) : List Step := [.inv, .trans (-k), .inv, .inv, .inv]

theorem lowerWord_matrix (k : ℤ) :
    (wordMatrix (lowerWord k)).val = !![1, 0; k, 1] := by
  simp only [lowerWord, wordMatrix, Step.matrix, mul_one, coe_mul, ModularGroup.coe_S,
    ModularGroup.coe_T_zpow, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- A lower unipotent at a phase integral on the annihilator fixes the
table, with scalar exactly one for this concrete word. -/
theorem lowerWord_fixes (w : Grid a → ℂ) (H : AddSubgroup (Grid a)) (k : ℤ)
    (htrans : ∀ u ∈ H, ∀ r, w (r + u) = w r)
    (hk : ∀ s, (∀ u ∈ H, pairing u s = 1) → ∃ n : ℤ, (-k : ℝ) * energy s = n) :
    wordAction (lowerWord k) w = w := by
  simp only [lowerWord, wordAction]
  rw [twist_finiteFourier_eq w H htrans]
  · exact finiteFourier_four w
  · simpa using hk

/-- The exact single-word condition: only the actual Fourier support is
relevant. The annihilator test in lowerWord_fixes is sufficient for it. -/
theorem lowerWord_fixes_iff (w : Grid a → ℂ) (k : ℤ) :
    wordAction (lowerWord k) w = w ↔
      ∀ s, finiteFourier w s ≠ 0 → kernel ((-k : ℤ) : ℂ) (energy s) = 1 := by
  let F3 (v : Grid a → ℂ) := finiteFourier (finiteFourier (finiteFourier v))
  have hF : F3 (finiteFourier w) = w := finiteFourier_four w
  have hI : Function.Injective F3 := by
    intro v t he
    simpa only [F3, finiteFourier_four] using congrArg finiteFourier he
  change F3 (twist (-k) (finiteFourier w)) = w ↔ _
  constructor
  · intro h s hs
    have he := congrFun (hI (h.trans hF.symm)) s
    change kernel ((-k : ℤ) : ℂ) (energy s) * finiteFourier w s = _ at he
    apply mul_right_cancel₀ hs
    simpa only [one_mul] using he
  · intro h
    refine (congrArg F3 ?_).trans hF
    funext s
    by_cases hs : finiteFourier w s = 0
    · simp [twist, hs]
    · rw [twist, h s hs, one_mul]

theorem lowerWord_reference (k : ℤ) (hk : (4 : ℤ) ∣ k) :
    wordAction (lowerWord k) referenceWeight = referenceWeight := by
  simp only [lowerWord, wordAction]
  rw [twist_finiteFourier_reference (-k) (dvd_neg.mpr hk)]
  exact finiteFourier_four _

theorem twist_reference (k : ℤ) : twist k referenceWeight = referenceWeight := by
  classical
  apply twist_eq_of_integral
  intro r hr
  by_cases h : r = 0
  · subst r
    exact ⟨0, by simp [energy, offset]⟩
  · exact (hr (by simp [referenceWeight, h])).elim

/-- The relative finite action at a single word, including subgroup membership. -/
def PairedActionAt {N : ℕ} (ξ : (ZMod N)ˣ →* ℂˣ) (w : Grid a → ℂ) (l : List Step) : Prop :=
  ∃ h : wordMatrix l ∈ Gamma0 N, ∃ c : ℂ,
    wordAction l referenceWeight = c • referenceWeight ∧
    wordAction l w = ((ξ ((Gamma0Map N).toHomUnits ⟨wordMatrix l, h⟩) : ℂ) * c) • w

theorem paired_upper {N : ℕ} (ξ : (ZMod N)ˣ →* ℂˣ) (w : Grid a → ℂ) (k : ℤ)
    (hw : twist k w = w) : PairedActionAt ξ w [.trans k] := by
  have hM : (wordMatrix [.trans k]).val = !![1, k; 0, 1] := by
    simpa only [wordMatrix, Step.matrix, mul_one] using ModularGroup.coe_T_zpow k
  have h : wordMatrix [.trans k] ∈ Gamma0 N := by
    rw [Gamma0_mem, hM]
    simp
  have hd : (Gamma0Map N).toHomUnits ⟨wordMatrix [.trans k], h⟩ = 1 := by
    apply Units.ext
    rw [MonoidHom.coe_toHomUnits, Gamma0Map_apply]
    change ((wordMatrix [.trans k]).val 1 1 : ZMod N) = 1
    rw [hM]
    simp
  exact ⟨h, 1, by simp [wordAction, twist_reference], by simp [wordAction, hw, hd]⟩

theorem paired_lower {N : ℕ} (ξ : (ZMod N)ˣ →* ℂˣ) (w : Grid a → ℂ)
    (H : AddSubgroup (Grid a)) (k : ℤ) (hk : (N : ℤ) ∣ k) (hfour : 4 ∣ N)
    (htrans : ∀ u ∈ H, ∀ r, w (r + u) = w r)
    (hdepth : ∀ s, (∀ u ∈ H, pairing u s = 1) → ∃ n : ℤ, (-k : ℝ) * energy s = n) :
    PairedActionAt ξ w (lowerWord k) := by
  have h : wordMatrix (lowerWord k) ∈ Gamma0 N := by
    rw [Gamma0_mem, lowerWord_matrix]
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd k N).mpr hk
  have hd : (Gamma0Map N).toHomUnits ⟨wordMatrix (lowerWord k), h⟩ = 1 := by
    apply Units.ext
    rw [MonoidHom.coe_toHomUnits, Gamma0Map_apply]
    change ((wordMatrix (lowerWord k)).val 1 1 : ZMod N) = 1
    rw [lowerWord_matrix]
    simp
  have hk4 : (4 : ℤ) ∣ k := dvd_trans (by exact_mod_cast hfour) hk
  exact ⟨h, 1, by simp [lowerWord_reference k hk4], by simp [lowerWord_fixes w H k htrans hdepth, hd]⟩

/-- The word of length two above minus the identity acts by reflection.
On even weights the expected character value at minus one is one. -/
theorem paired_neg_one {N : ℕ} (ξ : (ZMod N)ˣ →* ℂˣ) (w : Grid a → ℂ)
    (hξ : ξ (-1) = 1) (hw : ∀ r, w (-r) = w r) : PairedActionAt ξ w [.inv, .inv] := by
  have hM : (wordMatrix [.inv, .inv]).val = !![-1, 0; 0, -1] := by decide
  have h : wordMatrix [.inv, .inv] ∈ Gamma0 N := by
    rw [Gamma0_mem, hM]
    simp
  have hd : (Gamma0Map N).toHomUnits ⟨wordMatrix [.inv, .inv], h⟩ = -1 := by
    apply Units.ext
    rw [MonoidHom.coe_toHomUnits, Gamma0Map_apply]
    change ((wordMatrix [.inv, .inv]).val 1 1 : ZMod N) = ↑(-1 : (ZMod N)ˣ)
    rw [hM]
    simp
  refine ⟨h, 1, ?_, ?_⟩
  · rw [wordAction, wordAction, wordAction, finiteFourier_sq, one_smul]
    classical
    funext r
    simp [referenceWeight]
  · simp only [wordAction, finiteFourier_sq, hd, hξ, Units.val_one, mul_one, one_smul]
    exact funext hw

theorem matrix_append (l r : List Step) : wordMatrix (l ++ r) = wordMatrix l * wordMatrix r := by
  induction l with
  | nil => simp [wordMatrix]
  | cons g l ih => simp [wordMatrix, ih, mul_assoc]

theorem action_append (l r : List Step) (w : Grid a → ℂ) :
    wordAction (l ++ r) w = wordAction r (wordAction l w) := by
  induction l generalizing w with
  | nil => rfl
  | cons g l ih => cases g <;> simp [wordAction, ih]

theorem action_smul (l : List Step) (c : ℂ) (w : Grid a → ℂ) :
    wordAction l (c • w) = c • wordAction l w := by
  have hf (v : Grid a → ℂ) : finiteFourier (c • v) = c • finiteFourier v := by
    funext r
    simp only [finiteFourier, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    ring
  have ht (n : ℤ) (v : Grid a → ℂ) : twist n (c • v) = c • twist n v := by
    funext r
    simp only [twist, Pi.smul_apply, smul_eq_mul]
    ring
  induction l generalizing w with
  | nil => rfl
  | cons g l ih => cases g <;> simp [wordAction, hf, ht, ih]

/-- Character multiplication glues the exact assertions for concatenations. -/
theorem PairedActionAt.append {N : ℕ} {ξ : (ZMod N)ˣ →* ℂˣ} {w : Grid a → ℂ}
    {l r : List Step} (hl : PairedActionAt ξ w l) (hr : PairedActionAt ξ w r) :
    PairedActionAt ξ w (l ++ r) := by
  obtain ⟨hL, cL, hL₀, hLw⟩ := hl
  obtain ⟨hR, cR, hR₀, hRw⟩ := hr
  have h : wordMatrix (l ++ r) ∈ Gamma0 N :=
    matrix_append l r ▸ (Gamma0 N).mul_mem hL hR
  have hγ : (⟨wordMatrix (l ++ r), h⟩ : Gamma0 N) = ⟨wordMatrix l, hL⟩ * ⟨wordMatrix r, hR⟩ :=
    Subtype.ext (matrix_append l r)
  refine ⟨h, cL * cR, ?_, ?_⟩
  · rw [action_append, hL₀, action_smul, hR₀, smul_smul]
  · rw [action_append, hLw, action_smul, hRw, smul_smul, hγ, map_mul, map_mul, Units.val_mul]
    congr 1
    ring

#print axioms reference_energy
#print axioms twist_finiteFourier_reference
#print axioms lowerWord_matrix
#print axioms lowerWord_fixes
#print axioms lowerWord_fixes_iff
#print axioms lowerWord_reference
#print axioms twist_reference
#print axioms paired_upper
#print axioms paired_lower
#print axioms paired_neg_one
#print axioms matrix_append
#print axioms action_append
#print axioms action_smul
#print axioms PairedActionAt.append

end ZInQ.Manuscript.RC.RelativeAction

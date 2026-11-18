import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinConstantLimits

/-!
# The actual two-axis primitive Eisenstein constant profile

In the gcd-one gamma set, a vector with first coordinate zero has second
coordinate exactly 1 or −1. This finite support reduces the independently
proved actual vertical limit to the two literal residue indicators. No
constant-term, summability or classification hypothesis is supplied.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open Complex Filter Set UpperHalfPlane EisensteinSeries Matrix.SpecialLinearGroup
open scoped Topology MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinConstants

def positiveIntegerRow : Fin 2 → ℤ := ![0,1]
def negativeIntegerRow : Fin 2 → ℤ := ![0,-1]
def positiveRow (N : ℕ) : Fin 2 → ZMod N := ![0,1]
def negativeRow (N : ℕ) : Fin 2 → ZMod N := ![0,-1]

lemma axis_rows_ne : positiveIntegerRow ≠ negativeIntegerRow := by
  intro h
  have he := congrFun h 1
  norm_num [positiveIntegerRow,negativeIntegerRow] at he

lemma positive_gamma_iff (N : ℕ) (a : Fin 2 → ZMod N) :
    positiveIntegerRow ∈ EisensteinSeries.gammaSet N 1 a ↔ a = positiveRow N := by
  have he : ((↑) : ℤ → ZMod N) ∘ positiveIntegerRow = positiveRow N := by
    funext i
    fin_cases i <;> simp [Function.comp_def,positiveIntegerRow,positiveRow]
  change ((((↑) : ℤ → ZMod N) ∘ positiveIntegerRow = a) ∧
    (positiveIntegerRow 0).gcd (positiveIntegerRow 1) = 1) ↔ a = positiveRow N
  rw [he]
  simp only [positiveIntegerRow,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Int.gcd_zero_left,Int.natAbs_one,and_true]
  exact eq_comm

lemma negative_gamma_iff (N : ℕ) (a : Fin 2 → ZMod N) :
    negativeIntegerRow ∈ EisensteinSeries.gammaSet N 1 a ↔ a = negativeRow N := by
  have he : ((↑) : ℤ → ZMod N) ∘ negativeIntegerRow = negativeRow N := by
    funext i
    fin_cases i <;> simp [Function.comp_def,negativeIntegerRow,negativeRow]
  change ((((↑) : ℤ → ZMod N) ∘ negativeIntegerRow = a) ∧
    (negativeIntegerRow 0).gcd (negativeIntegerRow 1) = 1) ↔ a = negativeRow N
  rw [he]
  simp only [negativeIntegerRow,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Int.gcd_zero_left,Int.natAbs_neg,Int.natAbs_one,and_true]
  exact eq_comm

/-- Gcd-one makes the zero-first-coordinate fibre exactly the two integer axes. -/
lemma gamma_zero_first_axis (N : ℕ) (a : Fin 2 → ZMod N) (v : Fin 2 → ℤ)
    (hv : v ∈ EisensteinSeries.gammaSet N 1 a) (h0 : v 0 = 0) :
    v = positiveIntegerRow ∨ v = negativeIntegerRow := by
  have hc := Int.isCoprime_iff_gcd_eq_one.mpr hv.2
  have h1 : v 1 = 1 ∨ v 1 = -1 := by
    simpa only [h0,isCoprime_zero_left,Int.isUnit_iff] using hc
  rcases h1 with h1 | h1
  · left
    funext i
    fin_cases i <;> simp [positiveIntegerRow,h0,h1]
  · right
    funext i
    fin_cases i <;> simp [negativeIntegerRow,h0,h1]

lemma rowLimit_support (N : ℕ) (a : Fin 2 → ZMod N) (k : ℕ) (v : Fin 2 → ℤ)
    (hv : v ∉ ({positiveIntegerRow,negativeIntegerRow} : Finset (Fin 2 → ℤ))) :
    rowLimit N a k v = 0 := by
  unfold rowLimit
  by_cases hγ : v ∈ EisensteinSeries.gammaSet N 1 a
  · rw [ite_eq_left hγ]
    by_cases h0 : v 0 = 0
    · have he := gamma_zero_first_axis N a v hγ h0
      exact (hv (by simpa only [Finset.mem_insert,Finset.mem_singleton] using he)).elim
    · rw [ite_eq_right h0]
  · rw [ite_eq_right hγ]

lemma rowLimit_positive (N : ℕ) (a : Fin 2 → ZMod N) (k : ℕ) :
    rowLimit N a k positiveIntegerRow = if a = positiveRow N then 1 else 0 := by
  unfold rowLimit
  rw [positive_gamma_iff]
  simp [positiveIntegerRow]

lemma rowLimit_negative (N : ℕ) (a : Fin 2 → ZMod N) (k : ℕ) :
    rowLimit N a k negativeIntegerRow = if a = negativeRow N then (-1 : ℂ)^k else 0 := by
  have he : (-1 : ℂ)^(-(k : ℤ)) = (-1 : ℂ)^k := by
    rw [_root_.zpow_neg,_root_.zpow_natCast,← inv_pow]
    simp
  unfold rowLimit
  rw [negative_gamma_iff]
  simp [negativeIntegerRow,he]

/-- The genuine unscaled primitive constant profile. -/
def constantProfile (N : ℕ) (k : ℕ) (a : Fin 2 → ZMod N) : ℂ :=
  (if a = positiveRow N then 1 else 0) + (if a = negativeRow N then (-1 : ℂ)^k else 0)

lemma limit_sum_eq_profile (N : ℕ) (a : Fin 2 → ZMod N) (k : ℕ) :
    (∑' v : Fin 2 → ℤ, rowLimit N a k v) = constantProfile N k a := by
  rw [tsum_eq_sum (s := {positiveIntegerRow,negativeIntegerRow}) (rowLimit_support N a k),
    Finset.sum_pair axis_rows_ne,rowLimit_positive,rowLimit_negative]
  rfl

/-- The actual Mathlib primitive modular form has the produced two-axis constant
coefficient, with neither a half nor an N^k scaling. -/
theorem actual_primitive_constant_coefficient (N : ℕ) [NeZero N]
    (k : ℕ) (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    (UpperHalfPlane.qExpansion (N : ℝ)
      (ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) a)).coeff 0 =
      constantProfile N k a := by
  rw [primitive_coefficient_zero_eq_limit_sum N k hk a,limit_sum_eq_profile]

/-- The global at-infinity limit follows with the actual produced profile. -/
theorem actual_primitive_tendsto_profile (N : ℕ) [NeZero N]
    (k : ℕ) (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    Tendsto (eisensteinSeries a (k : ℤ)) UpperHalfPlane.atImInfty (𝓝 (constantProfile N k a)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have he := ModularFormClass.tendsto_atImInfty
    (ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k) a) hN (level_period N)
  rw [actual_primitive_constant_coefficient N k hk a] at he
  exact he

end ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinConstants

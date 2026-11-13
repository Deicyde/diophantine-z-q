import ZInQKernel.Size.Majorants.RecipeHeights
import ZInQKernel.Size.Constants
import ZInQKernel.Size.Norms

/-!
# The cutoff is an admissible bound

Blueprint: `size/majorants/admissible-cutoff.md`.

Under the catalogue bound, `B = T + 1` satisfies `B ≥ 2^20` and the hypotheses of the template
majorant for the constructed library with the constructors of the specification
(`admissible_cutoff`):

1. every literal constant of the templates is below `2^69 < T` (`two_pow_sixtynine_lt_T`); in the
   Lean development the constants need no hypothesis of the majorant;
2. the fixed value `ℓ` has `1 ≤ ℓ ≤ T`;
3. every psi index `n` has `|n| + 1 ≤ T + 1`: the indices are `ε`, `ε ± 1`, `2ε` for
   `ε ∈ {c_*, 4, 2, 3, c₃, 1399}`, and `c_* < 2^(2^4617)`, `|c₃| < 2^(2^24)` give
   `|n| + 1 ≤ 2^(2^4618) < D ≤ T`;
4. the guard has cutoff `T`, `0 ≤ T ≤ B - 1`;

and the constructors of the specification satisfy the uniform bounds at `T + 1` (size-norms'
`psi_uniform`, `guard_uniform`).

The program literal `c₃` is a parameter of the specified polynomial (it is built by the
compiler chapter); its size `|c₃| < 2^(2^24)` (the compiler chapter's `code_lt_of_small` for the
wrapper program) is a hypothesis. Nothing is evaluated: every comparison is between symbolic
bounds, proved for variables before it is applied to the named constants.
-/

namespace ZInQ.Size

open MvPolynomial ZInQ.Syntax AmbientPow

/-- `2 · 2^(2^k) ≤ 2^(2^(k+1))`. -/
theorem two_mul_two_pow_two_pow_le (k : ℕ) : 2 * 2 ^ 2 ^ k ≤ 2 ^ 2 ^ (k + 1) := by
  have h1 : 1 ≤ 2 ^ k := one_le_natPow (by norm_num) k
  calc 2 * 2 ^ 2 ^ k = 2 ^ (2 ^ k + 1) := by rw [natPow_add, pow_one, mul_comm]
    _ ≤ 2 ^ 2 ^ (k + 1) := natPow_le_natPow_right (by norm_num) (by rw [pow_succ]; omega)

theorem two_pow_two_pow_mono {j k : ℕ} (h : j ≤ k) : 2 ^ 2 ^ j ≤ 2 ^ 2 ^ k :=
  natPow_le_natPow_right (by norm_num) (natPow_le_natPow_right (by norm_num) h)

/-- `D ≤ T`, through `D ≤ R ≤ Q ≤ 2·10^13 Q^17 ≤ A_ht ≤ T`. -/
theorem D_le_T : Syntax.D ≤ Syntax.T :=
  calc Syntax.D ≤ Syntax.R := D_le_R
    _ ≤ Syntax.Q := R_le_Q
    _ ≤ Syntax.Q ^ 17 := le_self_natPow (by norm_num)
    _ ≤ 2 * 10 ^ 13 * Syntax.Q ^ 17 := Nat.le_mul_of_pos_left _ (by norm_num)
    _ ≤ Aht := Q_pow_mul_le_Aht
    _ ≤ Syntax.T := Aht_le_T

theorem two_pow_two_pow_lt_T {k : ℕ} (hk : k ≤ 8008) : 2 ^ 2 ^ k < Syntax.T :=
  (two_pow_two_pow_lt_D hk).trans_le D_le_T

theorem two_pow_twenty_le_T_add_one : 2 ^ 20 ≤ Syntax.T + 1 :=
  ((show 2 ^ 20 ≤ 2 ^ 2 ^ 5 by norm_num).trans (two_pow_two_pow_lt_T (by norm_num)).le).trans
    (Nat.le_add_right _ 1)

/-- The literal constants of the templates are below `2^69 < T`. -/
theorem two_pow_sixtynine_lt_T : 2 ^ 69 < Syntax.T :=
  (show 2 ^ 69 ≤ 2 ^ 2 ^ 7 by norm_num).trans_lt (two_pow_two_pow_lt_T (by norm_num))

/-- The constructors of the specification satisfy the uniform bounds at every `B ≥ 2^20`. -/
theorem specConstructors_bounds {B : ℕ} (hB : 2 ^ 20 ≤ B) : ConstructorBounds specConstructors B :=
  ⟨fun n hn c => psi_uniform hB n hn c, fun T h0 hT => guard_uniform hB T h0 (by omega)⟩

theorem natAbs_psi_le {ε n : ℤ} (hn : n ∈ [ε, ε + 1, ε + -1, 2 * ε]) :
    n.natAbs + 1 ≤ 2 * ε.natAbs + 2 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> omega

/-- The guard condition for a natural cutoff `t` and `B = t + 1` (proved for a variable, so
that the kernel never meets `T` in two different forms). -/
theorem guard_cond_of (t : ℕ) : 0 ≤ (t : ℤ) ∧ (t : ℤ).natAbs + 1 ≤ t + 1 :=
  ⟨Int.natCast_nonneg t, by rw [Int.natAbs_natCast]⟩

theorem fixed_cond_of {l t : ℕ} (h : l ≤ t) : (l : ℤ).natAbs + 1 ≤ t + 1 := by
  rw [Int.natAbs_natCast]; omega

theorem two_mul_add_two_le {a X : ℕ} (h : a < X) : 2 * a + 2 ≤ 2 * X := by omega

/-- **The cutoff is an admissible bound.** Under the catalogue bound and for a program literal
`|c₃| < 2^(2^24)`, `B = T + 1` satisfies the hypotheses of the template majorant for the
constructed library with the constructors of the specification. -/
theorem admissible_cutoff (hCAT : CatalogueBound8) {c3 : ℤ} (hc3 : c3.natAbs < 2 ^ 2 ^ 24) :
    LibraryAdmissible (Syntax.T + 1) specConstructors FixedConst.cstar.value FixedConst.ell.value
      FixedConst.T.value c3 := by
  have hT := two_pow_twenty_le_T_add_one
  refine ⟨hT, specConstructors_bounds hT, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨ε, hε, hn⟩ := List.mem_flatMap.1 hn
    have hεX : ε.natAbs < 2 ^ 2 ^ 4617 := by
      simp only [integerConstants, List.mem_cons, List.not_mem_nil, or_false] at hε
      rcases hε with rfl | rfl | rfl | rfl | rfl | rfl
      · rewrite [FixedConst.value_cstar, Int.natAbs_natCast]; exact cstar_lt hCAT
      · exact (show (4 : ℤ).natAbs < 2 ^ 2 ^ 4 by norm_num).trans_le (two_pow_two_pow_mono (by norm_num))
      · exact (show (2 : ℤ).natAbs < 2 ^ 2 ^ 4 by norm_num).trans_le (two_pow_two_pow_mono (by norm_num))
      · exact (show (3 : ℤ).natAbs < 2 ^ 2 ^ 4 by norm_num).trans_le (two_pow_two_pow_mono (by norm_num))
      · exact hc3.trans_le (two_pow_two_pow_mono (by norm_num))
      · exact (show (1399 : ℤ).natAbs < 2 ^ 2 ^ 4 by norm_num).trans_le
          (two_pow_two_pow_mono (by norm_num))
    calc n.natAbs + 1 ≤ 2 * ε.natAbs + 2 := natAbs_psi_le hn
      _ ≤ 2 * 2 ^ 2 ^ 4617 := two_mul_add_two_le hεX
      _ ≤ 2 ^ 2 ^ (4617 + 1) := two_mul_two_pow_two_pow_le 4617
      _ ≤ Syntax.T + 1 := (two_pow_two_pow_lt_T (by norm_num)).le.trans (Nat.le_add_right _ 1)
  · rewrite [FixedConst.value_ell]
    exact fixed_cond_of ((ell_lt hCAT).trans (two_pow_two_pow_lt_T (by norm_num))).le
  · rewrite [FixedConst.value_T]
    exact guard_cond_of Syntax.T

/-- The fixed value `ℓ` is positive. -/
theorem one_le_ell_value : 1 ≤ FixedConst.ell.value := by
  rewrite [FixedConst.value_ell]; exact_mod_cast ell_pos

end ZInQ.Size

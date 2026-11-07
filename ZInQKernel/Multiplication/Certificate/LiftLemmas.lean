import ZInQKernel.Syntax.Templates.Certificate
import ZInQKernel.Multiplication.Certificate.LocalTemplates
import ZInQKernel.Model.Generator

/-!
# Unfolding lifted formulas

Generic lemmas for reading `φ^*(y)` (`Formula.Lift`) of the certificate templates atom by atom:
conjunctions over appended lists, pair equations, inverse atoms, `fin`, and the values of the
parameter lists of the calls. Values of pairs of consecutive variables are written
`pr y k = (y k) + (y (k + 1)) s ∈ K₀` and points of consecutive variables `pt y k`.
-/

namespace ZInQ.Mult

open MvPolynomial Syntax

/-- The rational pair `(y k, y (k + 1))`. -/
def prv (y : ℕ → ℚ) (k : ℕ) : Fin 2 → ℚ := ![y k, y (k + 1)]

/-- The element `y k + y (k + 1) s` of `K₀`. -/
def pr (y : ℕ → ℚ) (k : ℕ) : K0 := ⟨y k, y (k + 1)⟩

/-- The point code `(y k, …, y (k + 4))`. -/
def pt (y : ℕ → ℚ) (k : ℕ) : Fin 5 → ℚ := fun i => y (k + i)

theorem pairK_prv (y : ℕ → ℚ) (k : ℕ) : pairK (prv y k) = pr y k := rfl

theorem val_varPair (y : ℕ → ℚ) (k : ℕ) : Pair.val y (varPair k) = pr y k := by
  ext <;> simp [pr]

theorem evCode_varPoint (y : ℕ → ℚ) (k : ℕ) : evCode y (varPoint k) = pt y k := by
  funext i; simp [evCode, pt]

theorem ev_comp_varPoint (y : ℕ → ℚ) (k : ℕ) : (fun i => ev y (varPoint k i)) = pt y k :=
  evCode_varPoint y k

theorem ev_comp_pairArgs (y : ℕ → ℚ) (k : ℕ) : (fun i => ev y ((varPair k).args i)) = prv y k := by
  funext i; fin_cases i <;> simp [Pair.args, varPair, prv]

theorem ev_comp_neg (y : ℕ → ℚ) (p : Code) :
    (fun i => ev y (Code.neg p i)) = negCode (fun i => ev y (p i)) := by
  funext i; fin_cases i <;> simp [Code.neg, negCode]

theorem lift_and_nil (y : ℕ → ℚ) : (Formula.and []).Lift y ↔ True := by simp

theorem lift_and_cons (y : ℕ → ℚ) (φ : Formula) (l : List Formula) :
    (Formula.and (φ :: l)).Lift y ↔ φ.Lift y ∧ (Formula.and l).Lift y := by
  simp only [Formula.lift_and, List.forall_mem_cons]

theorem lift_and_append (y : ℕ → ℚ) (l₁ l₂ : List Formula) :
    (Formula.and (l₁ ++ l₂)).Lift y ↔ (Formula.and l₁).Lift y ∧ (Formula.and l₂).Lift y := by
  simp only [Formula.lift_and, List.forall_mem_append]

theorem lift_and_singleton (y : ℕ → ℚ) (φ : Formula) : (Formula.and [φ]).Lift y ↔ φ.Lift y := by
  simp

/-- `NZ_K(λ)` at a pair of consecutive variables says `[λ] ≠ 0`. -/
theorem lift_nz_norm_imp (y : ℕ → ℚ) (k c : ℕ) :
    (nzFormula (varPair k).norm c).Lift y → pr y k ≠ 0 := by
  rw [lift_nzFormula, Pair.ev_norm, ev_varPair_fst, ev_varPair_snd]
  intro h
  exact (exists_mul_pairNorm_eq_one_iff _ _).1 ⟨_, h⟩

/-! ### Codes of multiples of `P₀` -/

theorem iota_zero_coord (n : ℤ) : iota n 0 = if n = 0 then 1 else 0 := by
  rw [iota_def, pointCode_apply_zero]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, zsmul_genP0_ne_zero hn]

theorem iota_zero_coord_eq_zero_iff (n : ℤ) : iota n 0 = 0 ↔ n ≠ 0 := by
  rw [iota_zero_coord]; split_ifs with h <;> simp [h]

/-- `neg(ι(c)) = ι(-c)`. -/
theorem negCode_iota (c : ℤ) : negCode (iota c) = iota (-c) := (iota_neg c).symm

/-- Membership and raw addition on a shift by a canonical code: `member(F)` and
`raw_add(F, neg(ι(c)), V)` hold exactly when `F = ι(f)` and `V = ι(f - c)`. -/
theorem member_rawAdd_iff (F V : Fin 5 → ℚ) (c : ℤ) :
    memberTemplate.Rel F ∧ rawAddTemplate.Rel (Fin.append (Fin.append F (negCode (iota c))) V) ↔
      ∃ f : ℤ, F = iota f ∧ V = iota (f - c) := by
  rw [rel_member_iff_iota, negCode_iota]
  constructor
  · rintro ⟨⟨f, rfl⟩, h⟩
    rw [rel_rawAdd_iota] at h
    exact ⟨f, rfl, by rw [h, sub_eq_add_neg]⟩
  · rintro ⟨f, rfl, rfl⟩
    exact ⟨⟨f, rfl⟩, by rw [rel_rawAdd_iota, sub_eq_add_neg]⟩

end ZInQ.Mult

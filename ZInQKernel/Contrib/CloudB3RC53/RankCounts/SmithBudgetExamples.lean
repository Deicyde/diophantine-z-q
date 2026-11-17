import ZInQKernel.Contrib.CloudB3RC53.RankCounts.SmithBudget

/-!
# RankCounts: a non-vacuity instance for the budget (5.7) node

`FixedFieldBudgetSmith` (`SmithBudget.lean`, tex 5355–5387) has many hypotheses; this file
discharges all of them at one explicit, non-degenerate instance (one Smith disk, nonzero torsion,
nonzero `J_r`), so the node is not vacuous. Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.RankCounts.Examples

open ZInQ.Contrib.CloudB3RC53.RankCounts ZInQ.Contrib.CloudB3RC53.RankCounts.SmithCx
/-- One central Smith disk `[ℤ₂ --2--> ℤ₂]` in degree zero (`n = 1`, `m = 1`, `s = 2`). -/
def B1 : SmithBlocks Lam Lam where
  n := 1
  m := fun _ => 1
  A := fun _ => 0
  A0 := fun _ => Matrix.diagonal fun _ => PowerSeries.C (2 : ℤ_[2])
  s := fun _ _ => 2
  s_ne := fun _ _ => two_ne_zero
  central := fun i => by
    rw [Matrix.diagonal_map (by simp)]
    simp
/-- Free generators `(0, 1, 1, 0)`, one in each of degrees one and two (tex 5379–5380). -/
def fr1 : ℕ → ℕ := fun i => if i = 1 ∨ i = 2 then 1 else 0
theorem v2 : (2 : ℤ_[2]).valuation = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact_mod_cast PadicInt.valuation_p (p := 2)
theorem mTot1 : B1.mTot = 1 := rfl
theorem hSmith1 : B1.hSmith = 1 := by
  simp [SmithBlocks.hSmith, B1, v2]; rfl
/-- `ℤ₂ / 2`, a module of length one. -/
abbrev T3 : Type := ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2])}
theorem length_T3 : Module.length ℤ_[2] T3 = 1 := by
  have := ord_eq_valuation (p := 2) (x := 2) two_ne_zero
  rw [v2] at this
  exact_mod_cast this

/-- **Non-vacuity of `FixedFieldBudgetSmith` (PROVED).** Every hypothesis of
`fixedFieldBudgetSmith_proof` is discharged for a non-degenerate instance: one central Smith disk of
valuation one (`B1`), free generators `(0, 1, 1, 0)`, `dK = 0` with `HC` of dimensions
`(2, 0, 0, 2)`, `HQ = HD` (`gm = id`, `fm = 0`), `H¹C = H¹(D_c)`, `H²C = H²(D_c)`,
`J = H³C = ℤ₂/2` (so `t_K = c_E = 1`, `h_K = 0`), `i = δ = id`, `j = l = 0`. The conclusion is
`m = 1 ≤ 5` and `h₁ = 1 ≤ 4`. -/
theorem fixedFieldBudgetSmith_nonvacuous : B1.mTot ≤ 0 + 5 ∧ B1.hSmith ≤ 0 + 2 * 1 + 2 * 1 := by
  have hn : B1.n ≤ 3 := by decide
  have hpos : ∀ i j, 1 ≤ (B1.s i j).valuation := fun _ _ => by simp [B1, v2]
  refine fixedFieldBudgetSmith_proof Lam Lam B1 fr1 hn hpos
    (fun k => Fin ((![2, 0, 0, 2] : Fin 4 → ℕ) k) → ZMod 2) (fun k => B1.centralRed fr1 k)
    (fun _ => 0) (fun _ => LinearMap.id) (fun k => ?_) 0 (fun k => by simp) ?_
    (B1.centralH fr1 1) (B1.centralH fr1 2) T3 T3 (LinearEquiv.refl _ _) LinearMap.id 0
    LinearMap.id 0 ⟨Function.injective_id, ?_, ?_, ?_, ?_⟩ 1 0 1 ?_ length_T3 ?_ ?_ ?_ ?_
  · intro x
    simp only [LinearMap.id_apply, Set.mem_range, LinearMap.zero_apply]
    exact ⟨fun h => ⟨0, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩
  · rw [B1.sum_finrank_centralRed fr1 hn hpos, mTot1]
    decide
  · intro x; simp
  · intro x
    simp only [LinearMap.id_apply, Set.mem_range, LinearMap.zero_apply]
    exact ⟨fun h => ⟨0, h.symm⟩, fun ⟨_, h⟩ => h.symm⟩
  · intro x; simp
  · intro x
    have h3 : Subsingleton (B1.centralH fr1 3) := by
      have e := Hequiv (f := fr1) B1.σ B1.σ_ne 3
      have : Subsingleton ((Fin (fr1 3) → ℤ_[2]) × Q B1.σ 3) := by
        have h1 : Subsingleton (Fin (fr1 3) → ℤ_[2]) :=
          ⟨fun a b => funext fun j => (show Fin 0 from j).elim0⟩
        have h2 : Subsingleton (Q B1.σ 3) := by
          refine ⟨fun a b => ?_⟩
          obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ a
          obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ b
          congr 1
          funext j; exact (show Fin 0 from j).elim0
        infer_instance
      exact e.toEquiv.subsingleton
    exact ⟨0, Subsingleton.elim _ _⟩
  · rw [length_torsion_H B1.σ B1.σ_ne 1, length_Q_succ B1.σ B1.σ_ne 0,
      B1.sum_val_σ 0 (by decide)]
    simp [B1, v2]; rfl
  · rw [length_torsion_H B1.σ B1.σ_ne 2, length_Q_succ B1.σ B1.σ_ne 1,
      B1.sum_val_σ_ge 1 (by decide)]
  · rw [length_T3]; norm_num
  · simp [B1.finrank_centralH, fr1]
  · simp [B1.finrank_centralH, fr1]

end ZInQ.Contrib.CloudB3RC53.RankCounts.Examples

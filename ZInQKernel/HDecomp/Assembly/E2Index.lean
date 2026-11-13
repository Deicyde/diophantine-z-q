import Mathlib

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt2 from
`scratch/glue-assembly/E2Index.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# E2 glue: `[SL₂(ℤ) : Γ₁(N)] ≤ N²` (N5 L871: "The index of `Γ₁(N)` is at most `N²`")

The first column modulo `N` separates the left cosets of `Γ₁(N)`.
-/

namespace GlueAssembly

open Matrix CongruenceSubgroup
open scoped MatrixGroups

/-- The first column of `γ ∈ SL₂(ℤ)` modulo `N`. -/
def firstColMod (N : ℕ) (γ : SL(2, ℤ)) : ZMod N × ZMod N :=
  (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ), ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ))

/-- The algebra of `firstColMod_eq_iff`, over variables. -/
theorem firstCol_algebra {N : ℕ} (A B C : Matrix (Fin 2) (Fin 2) ℤ)
    (hda : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1) (hdet : C 0 0 * C 1 1 - C 0 1 * C 1 0 = 1)
    (c00 : C 0 0 = A 1 1 * B 0 0 - A 0 1 * B 1 0) (c10 : C 1 0 = -A 1 0 * B 0 0 + A 0 0 * B 1 0)
    (b00 : B 0 0 = A 0 0 * C 0 0 + A 0 1 * C 1 0) (b10 : B 1 0 = A 1 0 * C 0 0 + A 1 1 * C 1 0) :
    ((A 0 0 : ZMod N), (A 1 0 : ZMod N)) = ((B 0 0 : ZMod N), (B 1 0 : ZMod N)) ↔
      (C 0 0 : ZMod N) = 1 ∧ (C 1 1 : ZMod N) = 1 ∧ (C 1 0 : ZMod N) = 0 := by
  rw [Prod.mk.injEq]
  have hdaN := congrArg (fun x : ℤ => (x : ZMod N)) hda
  have hdetN := congrArg (fun x : ℤ => (x : ZMod N)) hdet
  push_cast at hdaN hdetN
  constructor
  · rintro ⟨h0, h1⟩
    have e00 : (C 0 0 : ZMod N) = 1 := by
      rw [c00]; push_cast; rw [← h0, ← h1]; linear_combination hdaN
    have e10 : (C 1 0 : ZMod N) = 0 := by
      rw [c10]; push_cast; rw [← h0, ← h1]; ring
    refine ⟨e00, ?_, e10⟩
    rw [e00, e10] at hdetN
    linear_combination hdetN
  · rintro ⟨e00, _, e10⟩
    constructor
    · rw [b00]; push_cast; rw [e00, e10]; ring
    · rw [b10]; push_cast; rw [e00, e10]; ring

theorem firstColMod_eq_iff (N : ℕ) (a b : SL(2, ℤ)) :
    firstColMod N a = firstColMod N b ↔ a⁻¹ * b ∈ Gamma1 N := by
  have hCe : ((a⁻¹ * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(a : Matrix (Fin 2) (Fin 2) ℤ) 1 1, -(a : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
        -(a : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (a : Matrix (Fin 2) (Fin 2) ℤ) 0 0] *
        (b : Matrix (Fin 2) (Fin 2) ℤ) := by
    have e1 : ((a⁻¹ * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        Matrix.adjugate (a : Matrix (Fin 2) (Fin 2) ℤ) * (b : Matrix (Fin 2) (Fin 2) ℤ) := rfl
    rw [e1, Matrix.adjugate_fin_two]
  have hBe : (b : Matrix (Fin 2) (Fin 2) ℤ) =
      (a : Matrix (Fin 2) (Fin 2) ℤ) * ((a⁻¹ * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
    have e2 : ((a * (a⁻¹ * b) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        (a : Matrix (Fin 2) (Fin 2) ℤ) * ((a⁻¹ * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := rfl
    rw [← e2, mul_inv_cancel_left]
  have hdet := (a⁻¹ * b).det_coe
  have hda := a.det_coe
  rw [Matrix.det_fin_two] at hdet hda
  rw [Gamma1_mem]
  refine firstCol_algebra _ _ _ hda hdet ?_ ?_ ?_ ?_
  · rw [hCe]; simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  · rw [hCe]; simp [Matrix.mul_apply, Fin.sum_univ_two]
  · conv_lhs => rw [hBe]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · conv_lhs => rw [hBe]
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **`[SL₂(ℤ) : Γ₁(N)] ≤ N²`.** -/
theorem index_Gamma1_le (N : ℕ) [NeZero N] : (Gamma1 N).index ≤ N ^ 2 := by
  classical
  let g : SL(2, ℤ) ⧸ Gamma1 N → ZMod N × ZMod N :=
    Quotient.lift (firstColMod N) fun a b hab =>
      (firstColMod_eq_iff N a b).2 (QuotientGroup.leftRel_apply.mp hab)
  have hg : Function.Injective g := by
    intro x y hxy
    induction x using QuotientGroup.induction_on
    induction y using QuotientGroup.induction_on
    exact QuotientGroup.eq.mpr ((firstColMod_eq_iff N _ _).1 hxy)
  rw [Subgroup.index_eq_card]
  calc Nat.card (SL(2, ℤ) ⧸ Gamma1 N) ≤ Nat.card (ZMod N × ZMod N) :=
        Nat.card_le_card_of_injective g hg
    _ = N ^ 2 := by rw [Nat.card_prod, Nat.card_zmod]; ring

end GlueAssembly

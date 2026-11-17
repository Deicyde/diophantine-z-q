import ZInQKernel.Contrib.OneProof.RC.Determinant.Genuine
import ZInQKernel.Contrib.OneProof.RC.Determinant.Budget

/-!
# Non-vacuity of the (5.9) and (5.8) statements (Lane RC7)

The hypotheses of `clearing_nodes_genuine` are jointly satisfiable with a nontrivial Smith block:
one central Smith disk `[ℤ₂ --2--> ℤ₂]` in degree zero (so `Δ = 2`, `h₁ = 1`, `c = 4`), the rank-one
pattern at every address, and the coordinate `ũ_x = 2` forced by Elliot's formula
`ũ_x = η κ α (2^{-a} β) T` with `η = κ = ε = 1`, `a = 0`, `α = β = 1`, `T = δ_0 = 2`.
The conclusion then provides genuine coefficient data with `BaseRegular C 4`.
The hypotheses of `newLocal_inv_pole_genuine` are satisfiable by the residual block of tex 5456–5463
in the simplest case `A_q = 1` (`d_q = 0`).
Everything here is PROVED.
-/

namespace ZInQ.Manuscript.RC.Determinant

open Matrix Finset

section Example

variable (b : ℕ)

/-- The example's central Smith data: one `1 × 1` Smith disk `[ℤ₂ --2--> ℤ₂]` in each of the degrees
`0, 1, 2` (`A_i = (2)`). -/
noncomputable def exBlocks : SmithBlocks (MonoidAlgebra OO (SignGroup b)) OO where
  n := 3
  m _ := 1
  A _ := (2 : MonoidAlgebra OO (SignGroup b)) • (1 : Matrix (Fin 1) (Fin 1) _)
  A0 _ := (2 : Lam) • (1 : Matrix (Fin 1) (Fin 1) Lam)
  s _ _ := 2
  s_ne _ _ := two_ne_zero
  central _ := Matrix.ext fun j k => by
    fin_cases j; fin_cases k
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Matrix.diagonal_apply_eq, map_ofNat]

theorem exBlocks_n : (exBlocks b).n = 3 := rfl

theorem exBlocks_δ (i : ℕ) : (exBlocks b).δ i = 2 := by
  show ((2 : MonoidAlgebra OO (SignGroup b)) • (1 : Matrix (Fin 1) (Fin 1) _)).det = 2
  rw [Matrix.det_smul, det_one, mul_one, Fintype.card_fin, pow_one]

theorem exBlocks_mTot : (exBlocks b).mTot = 3 := rfl

theorem exBlocks_A_apply (i : ℕ) : ∀ j k : Fin ((exBlocks b).m i), (exBlocks b).A i j k = 2 := by
  dsimp only [exBlocks]
  intro j k
  fin_cases j; fin_cases k
  simp

theorem exBlocks_A0_apply (i : ℕ) : ∀ j k : Fin ((exBlocks b).m i), (exBlocks b).A0 i j k = 2 := by
  dsimp only [exBlocks]
  intro j k
  fin_cases j; fin_cases k
  simp

theorem exBlocks_hSmith : (exBlocks b).hSmith = 3 := by
  have h2 : (2 : ℤ_[2]).valuation = 1 := by
    have := PadicInt.valuation_p (p := 2); simpa using this
  show (∑ i ∈ range 3, ∑ j : Fin 1, (2 : ℤ_[2]).valuation) = 3
  simp [h2]

/-- The example's transported cycle and functional: `z_H = μ_H = 1`, all other coordinates zero. -/
noncomputable def exScalars : ScalarData (exBlocks b) where
  zH := 1
  zB := 0
  C := 0
  μH := 1
  μE := 0
  BH := 0

/-- **Non-vacuity of (5.9) (PROVED).**  All hypotheses of `clearing_nodes_genuine` hold for the
example (`Δ = 8`, `T = δ₀ δ₁⁻¹ δ₂ = 2`, `ũ_x = 2`, `m = h₁ = 3`), which therefore yields genuine
coefficient data with `ClearingIdentity`, `PoleBound` for `L_T(M) = 16·5·M` and `BaseRegular C 12`. -/
theorem clearing_nodes_genuine_nonvacuous :
    ∃ C : ZInQ.Contrib.CloudB3RC53.CoordData b,
      (C.u = fun _ j => ((PowerSeries.coeff j (2 : Lam) : ℤ_[2]) : ℚ_[2]) / 2 ^ 0) ∧
      ZInQ.Contrib.CloudB3RC53.ClearingIdentity C ∧
      (∀ M : ℕ, ZInQ.Contrib.CloudB3RC53.PoleBound C (16 * (0 + 5) * M) M) ∧
      ZInQ.Contrib.CloudB3RC53.BaseRegular C (0 + 4 * (exBlocks b).hSmith) ∧
      0 + 4 * (exBlocks b).hSmith ≤ 0 + 4 * (3 + 2 * 0 + 2 * 0) := by
  refine clearing_nodes_genuine (exBlocks b) (by rw [exBlocks_n]; norm_num) ?_ (exScalars b) 1 1 1 0
    _ (fun _ => 0) (fun _ => 2) (fun _ _ => rfl) (fun _ => True) (fun _ => False)
    (fun _ => Or.inl trivial) ?_ (fun _ _ h => h.elim) ?_ 0 3 0 0
    (by rw [exBlocks_mTot]; norm_num) (by rw [exBlocks_hSmith])
  · intro i
    refine Matrix.ext fun j k => ?_
    rw [Matrix.map_apply, Matrix.map_apply, exBlocks_A_apply, exBlocks_A0_apply, map_ofNat,
      map_ofNat]
  · intro x _ _
    have hδ : ∀ i, evK (sgnChar x) ((exBlocks b).δ i) = (2 : FractionRing OO) := by
      intro i; rw [exBlocks_δ, map_ofNat]
    simp only [uK, cleanT, ScalarData.αK, ScalarData.βK, exScalars, hδ, map_one, map_ofNat,
      pow_zero, inv_one, one_mul, mul_one, exBlocks_n, Finset.prod_range_succ,
      Finset.prod_range_zero]
    simp
  · intro x M i j k
    refine genuinePole.poleLE_le_poleModLE M _ (genuinePole.poleLE_mono (Nat.zero_le _) ?_)
    have : ((exBlocks b).A i).map (signEval (sgnChar x)) j k = algebraMap Lam OO 2 := by
      rw [Matrix.map_apply, exBlocks_A_apply, map_ofNat, map_ofNat]
    rw [this]; exact genuinePole.algebraMap_mem_poleLE 2

end Example

/-- **Non-vacuity of (5.8) (PROVED).**  The hypotheses of `newLocal_inv_pole_genuine` hold for
`A_q = 1` (`d_q = 0`, `v_q = 1`, `w_q = 0`) and any `V`. -/
theorem newLocal_inv_pole_genuine_nonvacuous (M : ℕ) :
    let Bx : Matrix (Fin 4 × Fin 1) (Fin 4 × Fin 1) OO :=
      (Matrix.blockDiagonal fun _ => (1 : Matrix (Fin 4) (Fin 4) Lam)).map (algebraMap Lam OO) +
        (2 : OO) • (0 : Matrix (Fin 4 × Fin 1) (Fin 4 × Fin 1) Lam).map (algebraMap Lam OO)
    IsUnit Bx.det ∧ ∀ i j, Bx⁻¹ i j ∈ genuinePole.poleModLE M (4 * M) :=
  newLocal_inv_pole_genuine (fun _ => 1) (fun _ => 0) (fun _ => Nat.zero_le 4) (fun _ => 1)
    (fun _ => 0) (fun _ => by simp) 0 M

end ZInQ.Manuscript.RC.Determinant

namespace ZInQ.Manuscript.RC.Determinant

open Matrix Finset

/-- Empty Smith data (no central disks), used to show that the hypotheses of the budget are
consistent. -/
noncomputable def emptyBlocks : SmithBlocks OO OO where
  n := 0
  m _ := 0
  A _ := 0
  A0 _ := 0
  s _ := Fin.elim0
  s_ne _ j := Fin.elim0 j
  central _ := Matrix.ext fun j => Fin.elim0 j

/-- The Frobenius matrix of the example, trace `1` and determinant `1`. -/
noncomputable def exFrob : Matrix (Fin 2) (Fin 2) ℤ_[2] := !![0, -1; 1, 1]

theorem exFrob_sub_isUnit :
    IsUnit (exFrob - (1 : ℤ_[2]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have : (exFrob - (1 : ℤ_[2]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).det = 1 := by
    simp [exFrob, Matrix.det_fin_two]
  rw [this]; exact isUnit_one

instance exCoker_subsingleton :
    Subsingleton ((Fin 2 → ℤ_[2]) ⧸ LinearMap.range
      (exFrob - (1 : ℤ_[2]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[2])).mulVecLin) := by
  rw [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]
  exact Matrix.mulVec_surjective_iff_isUnit.2 exFrob_sub_isUnit

/-- **Non-vacuity of the budget `budget_57` (PROVED).**  Its hypotheses are jointly satisfiable:
`H^*(C_K ⊗ 𝔽₂) = (𝔽₂², 0, 0, 𝔽₂²)` (`d_K = 0`), `D_c ⊗ 𝔽₂` the same, no singular contribution,
all integral torsion zero, and the moving Frobenius `Φ` with trace `1` and determinant `r = 1`
(`v₂(r + 1 - a) = 0`). -/
theorem budget_57_nonvacuous : emptyBlocks.mTot ≤ 0 + 5 ∧ emptyBlocks.hSmith ≤ 0 + 2 * 0 + 2 * 0 := by
  let HC : Fin 4 → Type := fun n => Fin ((![2, 0, 0, 2] : Fin 4 → ℕ) n) → ZMod 2
  have hfin : ∀ n, Module.finrank (ZMod 2) (HC n) = (![2, 0, 0, 2] : Fin 4 → ℕ) n := fun n =>
    Module.finrank_fin_fun (ZMod 2)
  refine budget_57 (k := ZMod 2) (HC := HC) (HD := HC) (HQ := fun _ => Fin 0 → ZMod 2)
    (fun n => LinearMap.id) (fun n => 0) (fun n => ?_) hfin (by simp) emptyBlocks
    (rankTotal := 2) (by rw [Fin.sum_univ_four]; simp only [hfin]; simp) rfl
    (H0D := PUnit.{1}) (H1C := PUnit.{1}) (H1D := PUnit.{1}) (H2C := PUnit.{1}) (H2D := PUnit.{1})
    (J := PUnit.{1})
    (H3C := PUnit.{1}) (H3D := PUnit.{1}) (LinearEquiv.ofSubsingleton _ _) 0 0 0 0
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩,
      fun _ => Subsingleton.elim _ _⟩, fun _ => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩,
      fun _ => Subsingleton.elim _ _⟩, fun _ => ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩,
      fun _ => Subsingleton.elim _ _⟩, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
    (tK := 0) (hK := 0) (cE := 0) Module.length_eq_zero Module.length_eq_zero
    Module.length_eq_zero exFrob exFrob 1 1 1 isUnit_one ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (LinearEquiv.ofSubsingleton _ _) ?_
  · intro x; simp
  · simp [exFrob, Matrix.trace_fin_two]
  · simp [exFrob, Matrix.det_fin_two]
  · simp [exFrob, Matrix.trace_fin_two]
  · simp [exFrob, Matrix.det_fin_two]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · simp [emptyBlocks, Module.length_eq_zero]

end ZInQ.Manuscript.RC.Determinant

import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.NewLocalModel

/-!
# The central complex of the budget is the central fibre of the old complex

Manuscript `diophantine_zq.tex`, tex L5355–5392 and L5522–5532. The (5.7) counts of
`Identification2.budget` are stated (in the form of RankCounts' `budget_rank`) for RankCounts'
central complex `centralCx B fr₀` of the Smith data `B` at the free ranks `fr₀ = (0, 1, 1, 0)`:
`D_c^k = ℤ₂^{f_k} × ℤ₂^{m_{k−1}} × ℤ₂^{m_k}` with differential the Smith disks. This file proves
that this complex IS the central fibre of the old complex: by `Identification2.central_full` the
central reduction of the old complex is `smithForm`, and

* `cfe0, …, cfe3`: degreewise linear isomorphisms `centralCx B fr₀ k ≃ (smithForm)^k`
  (`(H, B, E)` coordinates);
* `cfe_comm0, cfe_comm1, cfe_comm2`: they commute with the differentials.

Hence the modules `H¹_C ≅ H¹(D_c)`, `H²_C ↪ H²(D_c)`, `H³_C ↠ H³(D_c)` of the budget are
identified with the cohomology of the actual central fibre (PROVED).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ClearingComplex

open Matrix
open ZInQ.Manuscript.RC.Determinant (Lam OO SmithBlocks)
open ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Contrib.CloudB3RC53.RankCounts.SmithCx

variable {S : Type} [CommRing S] (D : BlockComplex S)
  (A0 : (i : ℕ) → Matrix (Fin (D.mi i)) (Fin (D.mi i)) Lam)
  (s : (i : ℕ) → Fin (D.mi i) → ℤ_[2]) (s_ne : ∀ i j, s i j ≠ 0)
  (central : ∀ i, (A0 i).map PowerSeries.constantCoeff = Matrix.diagonal (s i))

/-- The Smith data. -/
abbrev Bsm : SmithBlocks S OO := D.toSmithBlocks (O := OO) A0 s s_ne central

/-- The central fibre (the central Smith form). -/
abbrev Fc : BlockComplex ℤ_[2] := smithForm D.m0 D.m1 D.m2 (s 0) (s 1) (s 2)

theorem cf_σ0 (j : Fin D.m0) : σ (Bsm D A0 s s_ne central) 0 j = s 0 j := rfl
theorem cf_σ1 (j : Fin D.m1) : σ (Bsm D A0 s s_ne central) 1 j = s 1 j := rfl
theorem cf_σ2 (j : Fin D.m2) : σ (Bsm D A0 s s_ne central) 2 j = s 2 j := rfl

/-- Degree zero: `D_c^0 = E₀`. -/
def cfe0 : centralCx (Bsm D A0 s s_ne central) fr₀ 0 ≃ₗ[ℤ_[2]] (Fin D.m0 → ℤ_[2]) where
  toFun c := c.2.2
  invFun v := (0, 0, v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv c := by
    refine Prod.ext (funext fun j => (show Fin 0 from j).elim0) (Prod.ext
      (funext fun j => (show Fin 0 from j).elim0) rfl)
  right_inv _ := rfl

/-- Degree one: `D_c^1 = B₁ ⊕ H₁ ⊕ E₁`. -/
def cfe1 : centralCx (Bsm D A0 s s_ne central) fr₀ 1 ≃ₗ[ℤ_[2]]
    (Fin D.m0 ⊕ Unit ⊕ Fin D.m1 → ℤ_[2]) where
  toFun c := Sum.elim c.2.1 (Sum.elim (fun _ => c.1 ⟨0, by decide⟩) c.2.2)
  invFun v := (fun _ => v (Sum.inr (Sum.inl ())), fun j => v (Sum.inl j),
    fun k => v (Sum.inr (Sum.inr k)))
  map_add' c c' := by funext x; rcases x with x | x | x <;> rfl
  map_smul' r c := by funext x; rcases x with x | x | x <;> rfl
  left_inv c := by
    refine Prod.ext (funext fun j => ?_) rfl
    change c.1 ⟨0, _⟩ = c.1 j
    refine congrArg c.1 (Fin.ext ?_)
    have h := j.isLt
    change j.val < 1 at h
    change 0 = j.val
    omega
  right_inv v := by funext x; rcases x with x | x | x <;> rfl

/-- Degree two: `D_c^2 = B₂ ⊕ H₂ ⊕ E₂`. -/
def cfe2 : centralCx (Bsm D A0 s s_ne central) fr₀ 2 ≃ₗ[ℤ_[2]]
    (Fin D.m1 ⊕ Unit ⊕ Fin D.m2 → ℤ_[2]) where
  toFun c := Sum.elim c.2.1 (Sum.elim (fun _ => c.1 ⟨0, by decide⟩) c.2.2)
  invFun v := (fun _ => v (Sum.inr (Sum.inl ())), fun j => v (Sum.inl j),
    fun k => v (Sum.inr (Sum.inr k)))
  map_add' c c' := by funext x; rcases x with x | x | x <;> rfl
  map_smul' r c := by funext x; rcases x with x | x | x <;> rfl
  left_inv c := by
    refine Prod.ext (funext fun j => ?_) rfl
    change c.1 ⟨0, _⟩ = c.1 j
    refine congrArg c.1 (Fin.ext ?_)
    have h := j.isLt
    change j.val < 1 at h
    change 0 = j.val
    omega
  right_inv v := by funext x; rcases x with x | x | x <;> rfl

/-- Degree three: `D_c^3 = B₃`. -/
def cfe3 : centralCx (Bsm D A0 s s_ne central) fr₀ 3 ≃ₗ[ℤ_[2]] (Fin D.m2 → ℤ_[2]) where
  toFun c := c.2.1
  invFun v := (0, v, 0)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv c := by
    refine Prod.ext (funext fun j => (show Fin 0 from j).elim0) (Prod.ext rfl
      (funext fun j => (show Fin 0 from j).elim0))
  right_inv _ := rfl

theorem comm0_aux (m0 m1 : ℕ) (s0 : Fin m0 → ℤ_[2]) (v : Fin m0 → ℤ_[2]) :
    (Sum.elim (diagonal s0 *ᵥ v) (Sum.elim (fun _ : Unit => (0 : ℤ_[2])) (fun _ : Fin m1 => 0)) :
      Fin m0 ⊕ Unit ⊕ Fin m1 → ℤ_[2]) =
      fromRows (diagonal s0) (0 : Matrix (Unit ⊕ Fin m1) (Fin m0) ℤ_[2]) *ᵥ v := by
  rw [fromRows_mulVec, zero_mulVec]
  funext x; rcases x with x | x | x <;> rfl

theorem comm1_aux (m0 m1 m2 : ℕ) (s1 : Fin m1 → ℤ_[2]) (bv : Fin m0 → ℤ_[2]) (h : ℤ_[2])
    (e : Fin m1 → ℤ_[2]) :
    (Sum.elim (diagonal s1 *ᵥ e) (Sum.elim (fun _ : Unit => (0 : ℤ_[2])) (fun _ : Fin m2 => 0)) :
      Fin m1 ⊕ Unit ⊕ Fin m2 → ℤ_[2]) =
      fromBlocks (0 : Matrix (Fin m1) (Fin m0) ℤ_[2]) (fromCols (0 : Matrix (Fin m1) Unit ℤ_[2])
        (diagonal s1)) (0 : Matrix (Unit ⊕ Fin m2) (Fin m0) ℤ_[2]) 0 *ᵥ
        Sum.elim bv (Sum.elim (fun _ => h) e) := by
  rw [fromBlocks_mulVec]
  funext x
  rcases x with x | x | x
  · simp [fromCols_mulVec_sumElim]
  · simp
  · simp

theorem comm2_aux (m0 m1 m2 : ℕ) (s2 : Fin m2 → ℤ_[2]) (bv : Fin m1 → ℤ_[2]) (h : ℤ_[2])
    (e : Fin m2 → ℤ_[2]) :
    diagonal s2 *ᵥ e = fromCols (0 : Matrix (Fin m2) (Fin m1) ℤ_[2])
      (fromCols (0 : Matrix (Fin m2) Unit ℤ_[2]) (diagonal s2)) *ᵥ
        Sum.elim bv (Sum.elim (fun _ => h) e) := by
  rw [fromCols_mulVec_sumElim, fromCols_mulVec_sumElim]
  simp

/-- **The isomorphism commutes with the differentials in degree zero.** -/
theorem cfe_comm0 (c : centralCx (Bsm D A0 s s_ne central) fr₀ 0) :
    cfe1 D A0 s s_ne central (dif (σ (Bsm D A0 s s_ne central)) 0 c) =
      (Fc D s).d0 *ᵥ cfe0 D A0 s s_ne central c :=
  comm0_aux D.m0 D.m1 (s 0) c.2.2

/-- **The isomorphism commutes with the differentials in degree one.** -/
theorem cfe_comm1 (c : centralCx (Bsm D A0 s s_ne central) fr₀ 1) :
    cfe2 D A0 s s_ne central (dif (σ (Bsm D A0 s s_ne central)) 1 c) =
      (Fc D s).d1 *ᵥ cfe1 D A0 s s_ne central c :=
  comm1_aux D.m0 D.m1 D.m2 (s 1) c.2.1 (c.1 ⟨0, by decide⟩) c.2.2

/-- **The isomorphism commutes with the differentials in degree two.** -/
theorem cfe_comm2 (c : centralCx (Bsm D A0 s s_ne central) fr₀ 2) :
    cfe3 D A0 s s_ne central (dif (σ (Bsm D A0 s s_ne central)) 2 c) =
      (Fc D s).d2 *ᵥ cfe2 D A0 s s_ne central c :=
  comm2_aux D.m0 D.m1 D.m2 (s 2) c.2.1 (c.1 ⟨0, by decide⟩) c.2.2

end ZInQ.Contrib.CloudB3RC53.ClearingComplex

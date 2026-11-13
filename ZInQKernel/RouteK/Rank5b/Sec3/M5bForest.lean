import ZInQKernel.RouteK.Rank5b.Sec3.DetForest

/-!
# `det M₁` and `det M_5b` as forest sums (tyz-5b Propositions 3.3 and 3.4, forest form)

* `M1G a y z`, `M5bG a y z`: Smith's `M₁` and `M_5b` built from bits (`M5b d = M5bG (aBit d) (yBit d)
  (zBit d)`, `M5b_eq_M5bG`);
* `det_M1G`: `det M₁ = (1 + y(V)) det P(z, y)` (`M₁ = P + w wᵀ` with `P (𝟏, 0) = w = (y, 0)`);
* `det_M5bG`: `det M_5b = (1 + y(V)) Σ_k y_k (det P(z[k↦1], y) + det P(z[k↦0], y))`;
* `det_M5bG_forest`: `det M_5b = (1 + y(V)) Σ_F (Σ_{k∈F} y_k z^{F∖k}) Σ_{f rooted at F} wt(f) Π_{ρ∈F} y(T_ρ)`.
-/

namespace ZInQ.RouteK.Rank5b.Sec3

open Finset Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Smith's `M₁ = [[L + Lᵀ, Lᵀ], [L, D_z]]` from bits. -/
def M1G (a : ι → ι → ZMod 2) (z : ι → ZMod 2) : Matrix (ι ⊕ ι) (ι ⊕ ι) (ZMod 2) :=
  fromBlocks (lapl a univ + (lapl a univ)ᵀ) (lapl a univ)ᵀ (lapl a univ) (diagonal z)

/-- Smith's `M_5b = [[M₁, (0, y)], [(0, y)ᵀ, 0]]` from bits. -/
def M5bG (a : ι → ι → ZMod 2) (y z : ι → ZMod 2) : Matrix ((ι ⊕ ι) ⊕ Unit) ((ι ⊕ ι) ⊕ Unit) (ZMod 2) :=
  border (M1G a z) (Sum.elim 0 y)

theorem M5b_eq_M5bG (d : ℕ) : M5b d = M5bG (aBit d) (yBit d) (zBit d) := rfl

theorem lapl_rowSum (a : ι → ι → ZMod 2) (k : ι) : ∑ j, lapl a univ k j = 0 := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  have h1 : lapl a univ k k = ∑ j ∈ univ.erase k, a k j := by simp [lapl]
  have h2 : ∑ j ∈ univ.erase k, lapl a univ k j = ∑ j ∈ univ.erase k, a k j :=
    Finset.sum_congr rfl fun j hj => by simp [lapl, Ne.symm (Finset.ne_of_mem_erase hj)]
  rw [h1, h2, CharTwo.add_self_eq_zero]

theorem M1G_eq {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y) (z : ι → ZMod 2) :
    M1G a z = Pmat a z y + replicateCol Unit (Sum.elim y 0) * replicateRow Unit (Sum.elim y 0) := by
  funext x x'
  rcases x with i | i <;> rcases x' with j | j
  · simp only [M1G, Pmat, Matrix.add_apply, fromBlocks_apply₁₁, transpose_apply, Matrix.mul_apply,
      replicateCol_apply, replicateRow_apply, Sum.elim_inl, Finset.univ_unique,
      Finset.sum_singleton]
    by_cases hij : i = j
    · subst hij
      rw [CharTwo.add_self_eq_zero, diagonal_apply_eq, zmod2_mul_self, CharTwo.add_self_eq_zero]
    · rw [diagonal_apply_ne _ hij, zero_add]
      simp only [lapl, hij, Ne.symm hij, if_false]
      exact hrec i j hij
  · simp [M1G, Pmat, replicateCol, replicateRow, Matrix.mul_apply]
  · simp [M1G, Pmat, replicateCol, replicateRow, Matrix.mul_apply]
  · simp [M1G, Pmat, replicateCol, replicateRow, Matrix.mul_apply]

theorem Pmat_mulVec (a : ι → ι → ZMod 2) (c d : ι → ZMod 2) :
    Pmat a c d *ᵥ Sum.elim 1 0 = Sum.elim d 0 := by
  funext x
  rcases x with i | k
  · simp [Pmat, mulVec, dotProduct, Fintype.sum_sum_type, diagonal_apply]
  · simp only [Pmat, mulVec, dotProduct, Fintype.sum_sum_type, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, Pi.one_apply, Pi.zero_apply, mul_one,
      mul_zero, Finset.sum_const_zero, add_zero]
    exact lapl_rowSum a k

theorem dot_elim (y : ι → ZMod 2) : (Sum.elim y 0 : ι ⊕ ι → ZMod 2) ⬝ᵥ Sum.elim 1 0 = ∑ i, y i := by
  simp [dotProduct, Fintype.sum_sum_type]

/-- `det M₁ = (1 + y(V)) det P(z, y)` (first step of tyz-5b Proposition 3.3). -/
theorem det_M1G {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y) (z : ι → ZMod 2) :
    (M1G a z).det = (Pmat a z y).det * (1 + ∑ i, y i) := by
  rw [M1G_eq hrec, det_add_col_mul_row_of_mulVec _ (Pmat_mulVec a z y), dot_elim]

theorem col_row_mulVec {n : Type*} [Fintype n] (v x : n → ZMod 2) :
    (replicateCol Unit v * replicateRow Unit v) *ᵥ x = fun i => v i * (v ⬝ᵥ x) := by
  funext i
  simp [mulVec, dotProduct, Matrix.mul_apply, replicateCol, replicateRow, Finset.mul_sum, mul_assoc]

/-- `adj(P)_{(k',k')} = det P(z[k↦1], y) + det P(z[k↦0], y)`. -/
theorem adjugate_Pmat_inr (a : ι → ι → ZMod 2) (c d : ι → ZMod 2) (k : ι) :
    adjugate (Pmat a c d) (Sum.inr k) (Sum.inr k) =
      (Pmat a (Function.update c k 1) d).det + (Pmat a (Function.update c k 0) d).det := by
  rw [adjugate_apply]
  set P0 := Pmat a (Function.update c k 0) d
  have h1 : Pmat a (Function.update c k 1) d =
      P0.updateRow (Sum.inr k) (P0 (Sum.inr k) + Pi.single (Sum.inr k) 1) := by
    funext x x'
    rcases x with i | i <;> rcases x' with j | j <;>
      simp [P0, Pmat, updateRow_apply, Function.update_apply, diagonal_apply, Pi.single_apply] <;>
      aesop
  have h2 : (Pmat a c d).updateRow (Sum.inr k) (Pi.single (Sum.inr k) 1) =
      P0.updateRow (Sum.inr k) (Pi.single (Sum.inr k) 1) := by
    funext x x'
    rcases x with i | i <;> rcases x' with j | j <;>
      simp [P0, Pmat, updateRow_apply, Function.update_apply, diagonal_apply, Pi.single_apply] <;>
      aesop
  rw [h1, det_updateRow_add, updateRow_eq_self, h2, add_comm, ← add_assoc, CharTwo.add_self_eq_zero,
    zero_add]

/-- `det M_5b = (1 + y(V)) Σ_k y_k (det P(z[k↦1], y) + det P(z[k↦0], y))`. -/
theorem det_M5bG {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y) (z : ι → ZMod 2) :
    (M5bG a y z).det = (1 + ∑ i, y i) * ∑ k, y k *
      ((Pmat a (Function.update z k 1) y).det + (Pmat a (Function.update z k 0) y).det) := by
  set P := Pmat a z y
  set v : ι ⊕ ι → ZMod 2 := Sum.elim 0 y
  set w : ι ⊕ ι → ZMod 2 := Sum.elim y 0
  set x : ι ⊕ ι → ZMod 2 := Sum.elim 1 0
  have hPx : P *ᵥ x = w := Pmat_mulVec a z y
  have hvx : v ⬝ᵥ x = 0 := by simp [v, x, dotProduct, Fintype.sum_sum_type]
  have hwx : w ⬝ᵥ x = ∑ i, y i := dot_elim y
  have hPvx : (P + replicateCol Unit v * replicateRow Unit v) *ᵥ x = w := by
    rw [Matrix.add_mulVec, hPx, col_row_mulVec, hvx]
    funext i; simp
  rw [M5bG, det_border_zmod2, M1G_eq hrec, add_right_comm,
    det_add_col_mul_row_of_mulVec _ hPvx, det_add_col_mul_row_of_mulVec _ hPx, hwx,
    det_add_col_mul_row, ← add_mul, add_right_comm, CharTwo.add_self_eq_zero, zero_add, mul_comm]
  congr 1
  -- `Σ_j v_j det (P.updateCol j v) = Σ_k y_k adj(P)_{(k',k')}`
  have hPsymm : Pᵀ = P := by
    simp only [P, Pmat, fromBlocks_transpose, transpose_transpose, diagonal_transpose]
  have hcol : ∀ j, (P.updateCol j v).det = ∑ i, v i * adjugate P i j := by
    intro j
    have hv : v = ∑ i, v i • Pi.single i (1 : ZMod 2) := by
      funext t; simp [Finset.sum_apply, Pi.single_apply]
    calc (P.updateCol j v).det = (P.updateCol j (∑ i, v i • Pi.single i (1 : ZMod 2))).det := by
          rw [← hv]
      _ = ∑ i, v i * adjugate P i j := by
        rw [det_updateCol_finset_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [det_updateCol_smul, adjugate_apply, ← det_transpose, ← updateRow_transpose, hPsymm]
  simp_rw [hcol, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hadj : (adjugate P)ᵀ = adjugate P := by rw [adjugate_transpose, hPsymm]
  have := quad_symm_zmod2 (adjugate P) hadj v
  simp_rw [← mul_assoc]
  rw [show (∑ i, ∑ j, v j * v i * adjugate P i j) = ∑ i, ∑ j, v i * v j * adjugate P i j from
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring]
  rw [this, Fintype.sum_sum_type]
  simp only [v, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    zero_add]
  exact Finset.sum_congr rfl fun k _ => by rw [adjugate_Pmat_inr]

/-- **Proposition 3.4, forest form**: `det M_5b = (1 + y(V)) Σ_F (Σ_{k∈F} y_k z^{F∖k})
Σ_{f rooted at F} wt(f) Π_{ρ∈F} y(T_ρ)`. -/
theorem det_M5bG_forest {a : ι → ι → ZMod 2} {y : ι → ZMod 2} (hrec : Recip a y)
    (z : ι → ZMod 2) :
    (M5bG a y z).det = (1 + ∑ i, y i) * ∑ F ∈ (univ : Finset ι).powerset,
      (∑ k ∈ F, y k * ∏ ρ ∈ F.erase k, z ρ) *
        ∑ f ∈ forests univ F, wt a (univ \ F) f *
          ∏ ρ ∈ F, ∑ v ∈ univ.filter (fun v => root f v = ρ), y v := by
  rw [det_M5bG hrec]
  simp_rw [det_Pmat]
  congr 1
  have hupd : ∀ (k : ι) (F : Finset ι),
      (∏ ρ ∈ F, Function.update z k 1 ρ) + ∏ ρ ∈ F, Function.update z k 0 ρ =
        if k ∈ F then ∏ ρ ∈ F.erase k, z ρ else 0 := by
    intro k F
    split_ifs with hk
    · rw [← Finset.mul_prod_erase F _ hk, ← Finset.mul_prod_erase F _ hk,
        Function.update_self, Function.update_self, zero_mul, add_zero, one_mul]
      exact Finset.prod_congr rfl fun ρ hρ => Function.update_of_ne (Finset.ne_of_mem_erase hρ) _ _
    · have : ∀ t : ZMod 2, ∏ ρ ∈ F, Function.update z k t ρ = ∏ ρ ∈ F, z ρ := fun t =>
        Finset.prod_congr rfl fun ρ hρ => Function.update_of_ne (fun h : ρ = k => hk (h ▸ hρ)) _ _
      rw [this, this, CharTwo.add_self_eq_zero]
  have : ∀ k, y k * ((∑ F ∈ (univ : Finset ι).powerset, (∏ ρ ∈ F, Function.update z k 1 ρ) *
      ∑ f ∈ forests univ F, wt a (univ \ F) f *
        ∏ ρ ∈ F, ∑ v ∈ univ.filter (fun v => root f v = ρ), y v) +
      ∑ F ∈ (univ : Finset ι).powerset, (∏ ρ ∈ F, Function.update z k 0 ρ) *
      ∑ f ∈ forests univ F, wt a (univ \ F) f *
        ∏ ρ ∈ F, ∑ v ∈ univ.filter (fun v => root f v = ρ), y v) =
      ∑ F ∈ (univ : Finset ι).powerset, (if k ∈ F then y k * ∏ ρ ∈ F.erase k, z ρ else 0) *
      ∑ f ∈ forests univ F, wt a (univ \ F) f *
        ∏ ρ ∈ F, ∑ v ∈ univ.filter (fun v => root f v = ρ), y v := by
    intro k
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [← add_mul, hupd]
    split_ifs <;> ring
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [← Finset.sum_mul, Finset.sum_ite_mem, Finset.univ_inter]

end ZInQ.RouteK.Rank5b.Sec3

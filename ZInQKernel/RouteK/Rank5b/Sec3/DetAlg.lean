import ZInQKernel.RouteK.Rank5b.Sec3.Redei

/-!
# Determinant algebra for `M₁` and `M_5b`

* `det_add_col_mul_row`: `det (A + u wᵀ) = det A + Σ_j w_j det (A with column j replaced by u)` (the
  matrix determinant lemma without invertibility);
* `det_add_col_mul_row_of_mulVec`: if `A x = u`, then `det (A + u wᵀ) = det A (1 + w·x)`;
* `det_border_zmod2`: over `𝔽₂`, `det [[A, v], [vᵀ, 0]] = det (A + v vᵀ) + det A`;
* `quad_adjugate_zmod2`: over `𝔽₂`, for symmetric `A`, `Σ_{i,j} v_i v_j adj(A)_{ji} = Σ_i v_i adj(A)_{ii}`.

These replace the generalized Laplace expansion (tyz-5b Lemma 3.2) and the involution expansion of
Proposition 3.4: with `P = [[D_y, Lᵀ], [L, D_z]]`, `M₁ = P + w wᵀ` for `w = (y, 0)` (reciprocity), and
`P (𝟏, 0) = (y, 0)` (rows of `L` sum to zero), so `det M₁ = (1 + y(V)) det P` and
`det M_5b = (1 + y(V)) Σ_k y_k adj(P)_{(k',k')}` (`det_M5bG_eq`).
-/

namespace ZInQ.RouteK.Rank5b.Sec3

open Finset Matrix

section General

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

theorem det_updateCol_finset_sum (A : Matrix n n K) (j : n) {κ : Type*} (s : Finset κ)
    (f : κ → n → K) : (A.updateCol j (∑ i ∈ s, f i)).det = ∑ i ∈ s, (A.updateCol j (f i)).det := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact det_eq_zero_of_column_eq_zero j fun i => by simp
  | insert k s hk ih => rw [Finset.sum_insert hk, det_updateCol_add, ih, Finset.sum_insert hk]

/-- The matrix whose rows in `s` are those of `A` and whose other rows are `w_i u`. -/
def rowPiece (A : Matrix n n K) (u w : n → K) (s : Finset n) : Matrix n n K :=
  Matrix.of fun i => if i ∈ s then A i else w i • u

theorem rowPiece_row (A : Matrix n n K) (u w : n → K) (s : Finset n) (i : n) :
    rowPiece A u w s i = if i ∈ s then A i else w i • u := rfl

theorem det_rowPiece_eq_zero (A : Matrix n n K) (u w : n → K) (s : Finset n)
    (hs : 2 ≤ (univ \ s).card) : (rowPiece A u w s).det = 0 := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 hs
  have hi' : i ∉ s := (Finset.mem_sdiff.1 hi).2
  have hj' : j ∉ s := (Finset.mem_sdiff.1 hj).2
  set M := rowPiece A u w s with hM
  have hri : M i = w i • u := by rw [hM, rowPiece_row, if_neg hi']
  have hrj : M j = w j • u := by rw [hM, rowPiece_row, if_neg hj']
  by_cases hwj : w j = 0
  · exact det_eq_zero_of_row_eq_zero j fun k => by rw [hrj, hwj, zero_smul]; rfl
  · have e1 : (M.updateRow i (w j • M i)).det = w j * M.det := by
      rw [det_updateRow_smul, updateRow_eq_self]
    have e2 : w j • M i = w i • M j := by rw [hri, hrj, smul_smul, smul_smul, mul_comm]
    have e3 : (M.updateRow i (M j)).det = 0 :=
      det_zero_of_row_eq hij (by rw [updateRow_self, updateRow_ne hij.symm])
    rw [e2, det_updateRow_smul, e3, mul_zero] at e1
    exact (mul_eq_zero.1 e1.symm).resolve_left hwj

/-- **Matrix determinant lemma**, without invertibility: `det (A + u wᵀ) = det A + Σ_j w_j
det (A.updateCol j u)`. -/
theorem det_add_col_mul_row (A : Matrix n n K) (u w : n → K) :
    (A + replicateCol Unit u * replicateRow Unit w).det =
      A.det + ∑ j, w j * (A.updateCol j u).det := by
  classical
  -- work with transposes: rows of `Aᵀ + w uᵀ`
  rw [← det_transpose, transpose_add, transpose_mul, transpose_replicateRow, transpose_replicateCol]
  have hdet : (Aᵀ + replicateCol Unit w * replicateRow Unit u).det =
      ∑ s : Finset n, (rowPiece Aᵀ u w s).det := by
    have key : ∀ M : Matrix n n K, M.det = detRowAlternating (fun i => M i) := fun M => rfl
    rw [key]
    have hsplit : (fun i => (Aᵀ + replicateCol Unit w * replicateRow Unit u) i) =
        (fun i => Aᵀ i) + (fun i => w i • u) := by
      funext i k
      simp [replicateCol, replicateRow, Matrix.mul_apply, mul_comm]
    rw [hsplit, AlternatingMap.map_add_univ]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [key]
    congr 1
  rw [hdet]
  rw [← Finset.sum_compl_add_sum (s := (Finset.univ : Finset (Finset n)).filter
    (fun s => (univ \ s).card ≤ 1))]
  rw [Finset.sum_eq_zero (fun s hs => det_rowPiece_eq_zero _ _ _ s (by
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hs
    omega)), zero_add]
  -- the sets with at most one missing element: `univ` and `univ.erase j`
  have hS : (Finset.univ : Finset (Finset n)).filter (fun s => (univ \ s).card ≤ 1) =
      insert univ (Finset.univ.image fun j => univ.erase j) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image]
    constructor
    · intro h
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with h0 | h1
      · left
        rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at h0
        exact Finset.eq_univ_of_forall fun x => h0 (Finset.mem_univ x)
      · right
        obtain ⟨j, hj⟩ := Finset.card_eq_one.1 h1
        refine ⟨j, ?_⟩
        ext x
        have := congrArg (x ∈ ·) hj
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton,
          eq_iff_iff] at this
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        tauto
    · rintro (rfl | ⟨j, rfl⟩)
      · simp
      · have : univ \ univ.erase j = {j} := by
          ext x; simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_erase, true_and,
            Finset.mem_singleton]; tauto
        rw [this, Finset.card_singleton]
  rw [hS, Finset.sum_insert (by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro j h
    have hj := Finset.mem_univ j
    rw [← h] at hj
    exact Finset.notMem_erase j univ hj),
    Finset.sum_image (fun j _ k _ h => by
      by_contra hjk
      have := congrArg (j ∈ ·) h
      simp [hjk] at this)]
  have hPWu : rowPiece Aᵀ u w univ = Aᵀ := by
    funext i; rw [rowPiece_row, if_pos (Finset.mem_univ i)]
  rw [hPWu, det_transpose]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have : rowPiece Aᵀ u w (univ.erase j) = Aᵀ.updateRow j (w j • u) := by
    funext i
    by_cases hij : i = j
    · subst hij; rw [rowPiece_row, if_neg (Finset.notMem_erase i univ), updateRow_self]
    · rw [rowPiece_row, if_pos (Finset.mem_erase.2 ⟨hij, Finset.mem_univ i⟩), updateRow_ne hij]
  rw [this, det_updateRow_smul, updateRow_transpose, det_transpose]

/-- **Rank-one update with a preimage**: if `A x = u`, then `det (A + u wᵀ) = det A (1 + w·x)`. -/
theorem det_add_col_mul_row_of_mulVec (A : Matrix n n K) {u x : n → K} (hx : A *ᵥ x = u)
    (w : n → K) :
    (A + replicateCol Unit u * replicateRow Unit w).det = A.det * (1 + w ⬝ᵥ x) := by
  rw [det_add_col_mul_row]
  have : ∀ j, (A.updateCol j u).det = x j * A.det := fun j => by
    have := det_updateCol_sum A j x
    rw [smul_eq_mul] at this
    rw [← this]
    congr 2
    funext k
    rw [← hx]
    simp [mulVec, dotProduct, mul_comm]
  simp_rw [this, dotProduct]
  rw [mul_add, mul_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end General

section Zmod2

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem zmod2_neg (x : ZMod 2) : -x = x := ZMod.neg_eq_self_mod_two x

theorem zmod2_sub (x y : ZMod 2) : x - y = x + y := by rw [sub_eq_add_neg, zmod2_neg]

/-- Over `𝔽₂`, `det [[A, v], [vᵀ, 0]] = det (A + v vᵀ) + det A`. -/
theorem det_border_zmod2 (A : Matrix n n (ZMod 2)) (v : n → ZMod 2) :
    (border A v).det = (A + replicateCol Unit v * replicateRow Unit v).det + A.det := by
  -- the corner `1` version is a Schur complement
  have h1 : (fromBlocks A (replicateCol Unit v) (replicateRow Unit v) (1 : Matrix Unit Unit (ZMod 2))).det
      = (A + replicateCol Unit v * replicateRow Unit v).det := by
    let _ : Invertible (1 : Matrix Unit Unit (ZMod 2)) := invertibleOne
    have hneg : -(replicateCol Unit v : Matrix n Unit (ZMod 2)) = replicateCol Unit v := by
      ext i u; simp [zmod2_neg]
    rw [det_fromBlocks₂₂, det_one, one_mul, invOf_one, Matrix.mul_one, sub_eq_add_neg,
      ← Matrix.neg_mul, hneg]
  -- linearity in the last row
  have h2 : (fromBlocks A (replicateCol Unit v) (replicateRow Unit v) (1 : Matrix Unit Unit (ZMod 2))).det
      = (border A v).det + A.det := by
    have hrow : fromBlocks A (replicateCol Unit v) (replicateRow Unit v) (1 : Matrix Unit Unit (ZMod 2)) =
        (border A v).updateRow (Sum.inr ()) ((border A v) (Sum.inr ()) + Pi.single (Sum.inr ()) 1) := by
      funext i j
      rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;> simp [border, updateRow_apply, Pi.single_apply]
    rw [hrow, det_updateRow_add, updateRow_eq_self]
    congr 1
    have : (border A v).updateRow (Sum.inr ()) (Pi.single (Sum.inr ()) 1) =
        fromBlocks A (replicateCol Unit v) 0 (1 : Matrix Unit Unit (ZMod 2)) := by
      funext i j
      rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩ <;> simp [border, updateRow_apply, Pi.single_apply]
    rw [this, det_fromBlocks_zero₂₁, det_one, mul_one]
  rw [← h1, h2, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- Over `𝔽₂`, the quadratic form of a symmetric matrix only sees the diagonal:
`Σ_{i,j} v_i v_j B_{ij} = Σ_i v_i B_{ii}` (for `v_i ∈ 𝔽₂`). -/
theorem quad_symm_zmod2 (B : Matrix n n (ZMod 2)) (hB : Bᵀ = B) (v : n → ZMod 2) :
    ∑ i, ∑ j, v i * v j * B i j = ∑ i, v i * B i i := by
  classical
  rw [← Finset.sum_product']
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p : n × n => p.1 = p.2)]
  have hoff : ∑ p ∈ (univ ×ˢ univ).filter (fun p : n × n => ¬p.1 = p.2), v p.1 * v p.2 * B p.1 p.2
      = 0 := by
    refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p _
      have : B p.2 p.1 = B p.1 p.2 := congrFun (congrFun hB p.1) p.2
      rw [this, mul_comm (v p.2), CharTwo.add_self_eq_zero]
    · intro p hp _ h
      have := (Finset.mem_filter.1 hp).2
      exact this (Prod.ext_iff.1 h).1.symm
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp ⊢
      exact fun h => hp h.symm
    · intro p _; rfl
  rw [hoff, add_zero]
  rw [Finset.sum_filter]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_ite_eq]
  simp [zmod2_mul_self]

end Zmod2

end ZInQ.RouteK.Rank5b.Sec3

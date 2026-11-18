import Mathlib

/-!
# The `𝔽₂` linear algebra of the dimension-three count (`diophantine_zq.tex` lines 1061–1069)

`dimThree_linear_algebra`: for a square matrix `K` over `𝔽₂` and vectors `s, λ, b` with

* `Kᵀ = K + ssᵗ + diag(s)` (quadratic reciprocity for the matrix of line 1038),
* `K1 = 0`, `sᵗ1 = 1` (`ℓ ≡ 3 (mod 4)`), `λᵗ1 = 0` (`(3/ℓ) = 1`),
* `ker K ⊆ {0, 1, b, 1 + b}` and `λ ∉ im K` (the matrix conditions, line 1040),

every solution of the local equations of a Selmer class `(3^δ ∏ q^u, (−1)^σ ∏ q^v)`

* `Ku + diag(λ)v = δλ`, `(K + diag(s))v = σs` (at the `q_i`),
* `sᵗv = σ` (at two), `(λ + s)ᵗv = σ` (at three)

has `v = σ1`, `δ = σ` and `u ∈ ker K`. For `σ = 0` this is the manuscript's claim "the matrix
properties force `v = 0`, `δ = 0`, `u ∈ ker K`" (line 1068). The reciprocity identities, the
equation at two and the reduction of `σ = 1` to `σ = 0` are not in the text (ELLIOT); they are
filled in here. The proof uses the duality `λ ∉ im K ⇒ ∃ w, wᵗK = 0, wᵗλ = 1` and
`dim ker Kᵗ = dim ker K` (rank of the transpose).
-/

namespace ZInQ.Manuscript.PoleRC

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

omit [Fintype ι] [DecidableEq ι] in
theorem vec_add_self (x : ι → ZMod 2) : x + x = 0 := funext fun i => zmod2_add_self (x i)

/-- **Duality.** If `λ ∉ im K`, some `w` has `wᵗK = 0` and `wᵗλ = 1`. -/
theorem exists_left_kernel_of_not_mem_range (K : Matrix ι ι (ZMod 2)) (lam : ι → ZMod 2)
    (h : ∀ u, K *ᵥ u ≠ lam) : ∃ w : ι → ZMod 2, w ᵥ* K = 0 ∧ w ⬝ᵥ lam = 1 := by
  have hx : lam ∉ LinearMap.range K.mulVecLin := by
    rintro ⟨u, hu⟩; exact h u hu
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  set w : ι → ZMod 2 := fun i => f (fun j => if i = j then 1 else 0) with hw
  have hfw : ∀ x, f x = w ⬝ᵥ x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  have hzero : ∀ y ∈ LinearMap.range K.mulVecLin, f y = 0 := by
    intro y hy
    have : f y ∈ Submodule.map f (LinearMap.range K.mulVecLin) := ⟨y, hy, rfl⟩
    rw [hmap] at this
    exact (Submodule.mem_bot _).mp this
  refine ⟨w, ?_, ?_⟩
  · funext j
    have h1 := hzero (K *ᵥ Pi.single j 1) ⟨Pi.single j 1, rfl⟩
    rw [hfw, Matrix.mulVec_single_one, dotProduct_comm] at h1
    rw [Pi.zero_apply, ← h1, vecMul, dotProduct_comm]
    rfl
  · rcases zmod2_cases (w ⬝ᵥ lam) with h0 | h1
    · exact absurd (by rw [hfw]; exact h0) hf
    · exact h1

/-- `dim ker Kᵗ = dim ker K`, as cardinalities. -/
theorem card_ker_transpose (K : Matrix ι ι (ZMod 2)) :
    Nat.card (LinearMap.ker Kᵀ.mulVecLin) = Nat.card (LinearMap.ker K.mulVecLin) := by
  classical
  have h1 := LinearMap.finrank_range_add_finrank_ker K.mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker Kᵀ.mulVecLin
  have h3 : Kᵀ.rank = K.rank := Matrix.rank_transpose K
  unfold Matrix.rank at h3
  have hk : Module.finrank (ZMod 2) (LinearMap.ker Kᵀ.mulVecLin) =
      Module.finrank (ZMod 2) (LinearMap.ker K.mulVecLin) := by omega
  have e : ∀ W : Submodule (ZMod 2) (ι → ZMod 2), Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    intro W
    have := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := W), ZMod.card]
  rw [e, e, hk]

theorem ncard_le_of_subset_four {V : Type*} (S : Set V) (a b c d : V)
    (h : ∀ x ∈ S, x = a ∨ x = b ∨ x = c ∨ x = d) : S.ncard ≤ 4 := by
  classical
  have hsub : S ⊆ (({a, b, c, d} : Finset V) : Set V) := by
    intro x hx; simpa using h x hx
  calc S.ncard ≤ (({a, b, c, d} : Finset V) : Set V).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ({a, b, c, d} : Finset V).card := Set.ncard_coe_finset _
    _ ≤ 4 := by
      refine (Finset.card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      simp

/-- **The left kernel.** If `ker K` has at most four elements and `1, w` are in the left kernel
with `w ∉ {0, 1}`, the left kernel is `{0, 1, w, 1 + w}`. -/
theorem left_ker_mem (K : Matrix ι ι (ZMod 2)) (b : ι → ZMod 2)
    (hker : ∀ v, K *ᵥ v = 0 → v = 0 ∨ v = 1 ∨ v = b ∨ v = 1 + b)
    (h1K : (1 : ι → ZMod 2) ᵥ* K = 0) (w : ι → ZMod 2) (hw : w ᵥ* K = 0) (hw0 : w ≠ 0)
    (hw1 : w ≠ 1) (x : ι → ZMod 2) (hx : x ᵥ* K = 0) :
    x = 0 ∨ x = 1 ∨ x = w ∨ x = 1 + w := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨hx0, hx1, hxw, hx1w⟩ := hne
  have h10 : (1 : ι → ZMod 2) ≠ 0 := fun h => hw0 (funext fun i =>
    absurd (congrFun h i) one_ne_zero)
  have hLK : ∀ y : ι → ZMod 2, y ᵥ* K = 0 → y ∈ LinearMap.ker Kᵀ.mulVecLin := by
    intro y hy
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, hy]
  -- `#ker K ≤ 4`
  have hcardK : Nat.card (LinearMap.ker K.mulVecLin) ≤ 4 := by
    have e : Nat.card (LinearMap.ker K.mulVecLin) =
        (LinearMap.ker K.mulVecLin : Set (ι → ZMod 2)).ncard := Nat.card_coe_set_eq _
    rw [e]
    exact ncard_le_of_subset_four _ 0 1 b (1 + b) fun v hv => hker v hv
  -- five distinct elements of the left kernel
  have h1w0 : (1 : ι → ZMod 2) + w ≠ 0 := fun h => hw1 (by
    have : w = 1 + w + 1 := by rw [add_comm (1 : ι → ZMod 2) w, add_assoc, vec_add_self, add_zero]
    rw [this, h, zero_add])
  have h1w1 : (1 : ι → ZMod 2) + w ≠ 1 := fun h => hw0 (by
    have : w = 1 + w + 1 := by rw [add_comm (1 : ι → ZMod 2) w, add_assoc, vec_add_self, add_zero]
    rw [this, h, vec_add_self])
  have h1ww : (1 : ι → ZMod 2) + w ≠ w := fun h => h10 (by
    have : (1 : ι → ZMod 2) = 1 + w + w := by rw [add_assoc, vec_add_self, add_zero]
    rw [this, h, vec_add_self])
  let S : Finset (ι → ZMod 2) := {0, 1, w, 1 + w, x}
  have hS : S.card = 5 := by
    simp only [S]
    rw [Finset.card_insert_of_notMem (by simp [h10.symm, hw0.symm, h1w0.symm, hx0.symm]),
      Finset.card_insert_of_notMem (by simp [hw1.symm, h1w1.symm, hx1.symm]),
      Finset.card_insert_of_notMem (by simp [h1ww.symm, hxw.symm]),
      Finset.card_insert_of_notMem (by simp [hx1w.symm])]
    simp
  have hSsub : (S : Set (ι → ZMod 2)) ⊆ LinearMap.ker Kᵀ.mulVecLin := by
    intro y hy
    simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact Submodule.zero_mem _
    · exact hLK _ h1K
    · exact hLK _ hw
    · exact hLK _ (by rw [Matrix.add_vecMul, h1K, hw, add_zero])
    · exact hLK _ hx
  have h5 : 5 ≤ Nat.card (LinearMap.ker Kᵀ.mulVecLin) := by
    have e : Nat.card (LinearMap.ker Kᵀ.mulVecLin) =
        (LinearMap.ker Kᵀ.mulVecLin : Set (ι → ZMod 2)).ncard := Nat.card_coe_set_eq _
    rw [e, ← hS, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hSsub (Set.toFinite _)
  rw [card_ker_transpose] at h5
  omega

/-- The case `σ = 0`: `v = 0`, `δ = 0`, `u ∈ ker K` (line 1068). -/
theorem dimThree_case0 (K : Matrix ι ι (ZMod 2)) (s lam b : ι → ZMod 2)
    (hrec : Kᵀ = K + vecMulVec s s + diagonal s) (hK1 : K *ᵥ 1 = 0) (hs1 : s ⬝ᵥ 1 = 1)
    (hl1 : lam ⬝ᵥ 1 = 0) (hker : ∀ v, K *ᵥ v = 0 → v = 0 ∨ v = 1 ∨ v = b ∨ v = 1 + b)
    (him : ∀ u, K *ᵥ u ≠ lam) (u v : ι → ZMod 2) (δ : ZMod 2)
    (E1 : K *ᵥ u + lam * v = δ • lam) (E2 : K *ᵥ v + s * v = 0) (E3 : s ⬝ᵥ v = 0)
    (E4 : (lam + s) ⬝ᵥ v = 0) : v = 0 ∧ δ = 0 ∧ K *ᵥ u = 0 := by
  -- `Kᵗx = Kx + (sᵗx)s + s ∘ x`
  have hT : ∀ x, Kᵀ *ᵥ x = K *ᵥ x + (s ⬝ᵥ x) • s + s * x := by
    intro x
    rw [hrec, Matrix.add_mulVec, Matrix.add_mulVec, vecMulVec_mulVec]
    funext i
    simp [Matrix.mulVec_diagonal, mul_comm]
  have h1K : (1 : ι → ZMod 2) ᵥ* K = 0 := by
    rw [← Matrix.mulVec_transpose, hT, hK1, hs1]
    funext i; simp [zmod2_add_self]
  have hv : v ᵥ* K = 0 := by
    rw [← Matrix.mulVec_transpose, hT, E3, zero_smul, add_zero, E2]
  have hlv : lam ⬝ᵥ v = 0 := by rw [add_dotProduct, E3, add_zero] at E4; exact E4
  obtain ⟨w, hw, hwl⟩ := exists_left_kernel_of_not_mem_range K lam him
  have hw0 : w ≠ 0 := by rintro rfl; simp at hwl
  have hw1 : w ≠ 1 := by rintro rfl; rw [dotProduct_comm, hl1] at hwl; exact zero_ne_one hwl
  have hv0 : v = 0 := by
    rcases left_ker_mem K b hker h1K w hw hw0 hw1 v hv with h | h | h | h
    · exact h
    · rw [h, hs1] at E3; exact absurd E3 one_ne_zero
    · rw [h, dotProduct_comm, hwl] at hlv; exact absurd hlv one_ne_zero
    · rw [h, dotProduct_add, hl1, dotProduct_comm, hwl, zero_add] at hlv
      exact absurd hlv one_ne_zero
  subst hv0
  rw [mul_zero, add_zero] at E1
  rcases zmod2_cases δ with hδ | hδ
  · subst hδ; exact ⟨rfl, rfl, by rw [E1, zero_smul]⟩
  · subst hδ; exact absurd (by rw [E1, one_smul]) (him u)

/-- **The dimension-three linear algebra** (lines 1061–1069, with the equation at two and both
signs of the second coordinate): `v = σ1`, `δ = σ`, `u ∈ ker K`. -/
theorem dimThree_linear_algebra (K : Matrix ι ι (ZMod 2)) (s lam b : ι → ZMod 2)
    (hrec : Kᵀ = K + vecMulVec s s + diagonal s) (hK1 : K *ᵥ 1 = 0) (hs1 : s ⬝ᵥ 1 = 1)
    (hl1 : lam ⬝ᵥ 1 = 0) (hker : ∀ v, K *ᵥ v = 0 → v = 0 ∨ v = 1 ∨ v = b ∨ v = 1 + b)
    (him : ∀ u, K *ᵥ u ≠ lam) (u v : ι → ZMod 2) (δ σ : ZMod 2)
    (E1 : K *ᵥ u + lam * v = δ • lam) (E2 : K *ᵥ v + s * v = σ • s) (E3 : s ⬝ᵥ v = σ)
    (E4 : (lam + s) ⬝ᵥ v = σ) : v = σ • 1 ∧ δ = σ ∧ K *ᵥ u = 0 := by
  rcases zmod2_cases σ with hσ | hσ
  · subst hσ
    obtain ⟨h1, h2, h3⟩ := dimThree_case0 K s lam b hrec hK1 hs1 hl1 hker him u v δ E1
      (by rw [E2, zero_smul]) E3 E4
    exact ⟨by rw [h1, zero_smul], h2, h3⟩
  · subst hσ
    -- `v' = v + 1` solves the `σ = 0` system with `δ + 1`
    have E1' : K *ᵥ u + lam * (v + 1) = (δ + 1) • lam := by
      rw [mul_add, mul_one, ← add_assoc, E1, add_smul, one_smul]
    have E2' : K *ᵥ (v + 1) + s * (v + 1) = 0 := by
      rw [Matrix.mulVec_add, hK1, add_zero, mul_add, mul_one, ← add_assoc, E2, one_smul,
        vec_add_self]
    have E3' : s ⬝ᵥ (v + 1) = 0 := by rw [dotProduct_add, E3, hs1, zmod2_add_self]
    have E4' : (lam + s) ⬝ᵥ (v + 1) = 0 := by
      rw [dotProduct_add, E4, add_dotProduct, hl1, hs1, zero_add, zmod2_add_self]
    obtain ⟨h1, h2, h3⟩ := dimThree_case0 K s lam b hrec hK1 hs1 hl1 hker him u (v + 1) (δ + 1)
      E1' E2' E3' E4'
    refine ⟨?_, ?_, h3⟩
    · have : v = v + 1 + 1 := by rw [add_assoc, vec_add_self, add_zero]
      rw [this, h1, zero_add, one_smul]
    · have : δ = δ + 1 + 1 := by rw [add_assoc, zmod2_add_self, add_zero]
      rw [this, h2, zero_add]

end ZInQ.Manuscript.PoleRC

import Mathlib

/-!
# Route K, row 5b: the bordered determinant (tyz-5b Lemma 4.2)

For a symmetric matrix `M` over `𝔽₂` of corank one, with kernel `{0, k}`, the determinant of `M`
bordered by a vector `v` (and a zero corner) is `v·k`.

The proof here avoids the adjugate: if `v·k = 0`, then `(k, 0)` is a nonzero kernel vector of the
bordered matrix; if `v·k = 1`, the bordered matrix has trivial kernel (pair the first block of
equations with `k`, using `kᵀM = (Mk)ᵀ = 0`), so its determinant is the nonzero element `1`.
-/

namespace ZInQ.RouteK.Rank5b

open Matrix

variable {ι : Type*} [Fintype ι]

/-- `M` bordered by the column `v`, the row `vᵀ` and a zero corner: `[[M, v], [vᵀ, 0]]`. -/
def border {R : Type*} [Zero R] (M : Matrix ι ι R) (v : ι → R) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) R :=
  Matrix.fromBlocks M (replicateCol Unit v) (replicateRow Unit v) 0

theorem zmod2_eq_zero_or_one' (e : ZMod 2) : e = 0 ∨ e = 1 := by revert e; decide

/-- The bordered matrix applied to `x`: on `ι` it is `M (x|ι) + x(∗) v`, at the corner `v·(x|ι)`. -/
theorem border_mulVec_inl (M : Matrix ι ι (ZMod 2)) (v : ι → ZMod 2) (x : ι ⊕ Unit → ZMod 2)
    (i : ι) : (border M v *ᵥ x) (Sum.inl i) = (M *ᵥ (x ∘ Sum.inl)) i + v i * x (Sum.inr ()) := by
  simp [border, mulVec, dotProduct, replicateCol]

theorem border_mulVec_inr (M : Matrix ι ι (ZMod 2)) (v : ι → ZMod 2) (x : ι ⊕ Unit → ZMod 2) :
    (border M v *ᵥ x) (Sum.inr ()) = v ⬝ᵥ (x ∘ Sum.inl) := by
  simp [border, mulVec, dotProduct, replicateRow]

/-- **Lemma 4.2** (tyz-5b §4.2; pc-audit RK6). Let `M` be a symmetric matrix over `𝔽₂` of corank
one, with kernel `{0, k}`. Then `det [[M, v], [vᵀ, 0]] = v·k` for every vector `v`. -/
theorem det_border_eq_dotProduct [DecidableEq ι] (M : Matrix ι ι (ZMod 2)) (hM : Mᵀ = M) (k : ι → ZMod 2)
    (hk0 : k ≠ 0) (hk : M *ᵥ k = 0) (hker : ∀ w, M *ᵥ w = 0 → w = 0 ∨ w = k)
    (v : ι → ZMod 2) : (border M v).det = v ⬝ᵥ k := by
  have _ := hk0
  rcases zmod2_eq_zero_or_one' (v ⬝ᵥ k) with h0 | h1
  · -- `(k, 0)` is a nonzero kernel vector
    rw [h0]
    refine exists_mulVec_eq_zero_iff.mp ⟨Sum.elim k 0, fun h => hk0 ?_, ?_⟩
    · funext i; exact congrFun h (Sum.inl i)
    · funext j
      rcases j with i | ⟨⟩
      · rw [border_mulVec_inl]
        have : (Sum.elim k 0 : ι ⊕ Unit → ZMod 2) ∘ Sum.inl = k := rfl
        simp [this, hk]
      · rw [border_mulVec_inr]
        exact h0
  · rw [h1]
    have hne : (border M v).det ≠ 0 := by
      intro hdet
      obtain ⟨x, hx0, hx⟩ := exists_mulVec_eq_zero_iff.mpr hdet
      set w := x ∘ Sum.inl with hw
      set t := x (Sum.inr ()) with ht
      have e1 : ∀ i, (M *ᵥ w) i + v i * t = 0 := fun i => by
        rw [← border_mulVec_inl, hx]; rfl
      have e2 : v ⬝ᵥ w = 0 := by rw [← border_mulVec_inr, hx]; rfl
      -- pair the first block with `k`
      have hkM : k ᵥ* M = 0 := by
        have h := vecMul_transpose M k
        rw [hM] at h
        rw [h, hk]
      have hMw : M *ᵥ w = -(t • v) := by
        funext i
        have := e1 i
        simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
        rw [eq_neg_iff_add_eq_zero, mul_comm]; exact this
      have hpair : k ⬝ᵥ (M *ᵥ w) = 0 := by rw [dotProduct_mulVec, hkM, zero_dotProduct]
      rw [hMw, dotProduct_neg, dotProduct_smul, dotProduct_comm, h1, smul_eq_mul, mul_one,
        neg_eq_zero] at hpair
      rw [hpair, zero_smul, neg_zero] at hMw
      have hw0 : w = 0 := by
        rcases hker w hMw with h | h
        · exact h
        · rw [h, h1] at e2; exact absurd e2 one_ne_zero
      apply hx0
      funext j
      rcases j with i | ⟨⟩
      · exact congrFun hw0 i
      · exact hpair
    rcases zmod2_eq_zero_or_one' (border M v).det with h | h
    · exact absurd h hne
    · exact h

end ZInQ.RouteK.Rank5b

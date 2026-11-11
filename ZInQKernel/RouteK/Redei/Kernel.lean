import ZInQKernel.RouteK.Rank5b.Sec3.Redei
import ZInQKernel.RouteK.Rank5b.Sec3.DetForest

/-!
# Rédei's `g` as the triviality of a kernel over `𝔽₂` (tyz-5b §2.2, Cases 1 and 2)

`docs/research/redei-plan.md` §3.2, step 7. Generic `Sec3` setting: bits `a : ι → ι → 𝔽₂`,
`y z : ι → 𝔽₂` with reciprocity `Recip a y`, and a nonempty block `B ⊆ ι`.

`kernel_trivial_iff_redeiG`: the kernel of `(L_B | z_B)` (the column `z_B` only when `y(B) = 0`)
is the trivial one, `{0, 1_B}` (times `e₂ = 0`), iff `redeiG a y z B = 1`.

Proof. Fix `ρ ∈ B` and let `w = y` if `y(B) = 1`, `w = z` otherwise. Let `N` be `L_B` with
column `ρ` replaced by `w`, a square matrix on `B`.
* `det N = Σ_{v∈B} w_v κ_v(B)` (expansion along column `ρ` and Lemma 2.2(2),
  `pmin_lapl_offdiag`); this is `redeiG` by its definition.
* The kernel of `(L_B | z_B)` is trivial iff `N` has trivial kernel: the rows of `L_B` sum to zero,
  so `1_B` is in the kernel and kernel vectors can be normalized by `e_ρ = 0`; if `y(B) = 1`,
  the column sums of `L_B` vanish (`colSum_lapl`) while `Σ_B y = 1`, which forces the coefficient
  of the column `y` to vanish.
* `N` has trivial kernel iff `det N ≠ 0` (`Matrix.exists_mulVec_eq_zero_iff`).
-/

namespace ZInQ.RouteK.Redei

open Finset Matrix ZInQ.RouteK.Rank5b ZInQ.RouteK.Rank5b.Sec3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The row sums of `L_B` over `B` vanish. -/
theorem redeiK_lapl_rowSum (a : ι → ι → ZMod 2) {B : Finset ι} {q : ι} (hq : q ∈ B) :
    ∑ p ∈ B, lapl a B q p = 0 := by
  rw [← Finset.add_sum_erase _ _ hq]
  have h1 : lapl a B q q = ∑ j ∈ B.erase q, a q j := by simp [lapl]
  have h2 : ∑ j ∈ B.erase q, lapl a B q j = ∑ j ∈ B.erase q, a q j :=
    Finset.sum_congr rfl fun j hj => by simp [lapl, Ne.symm (Finset.ne_of_mem_erase hj)]
  rw [h1, h2, CharTwo.add_self_eq_zero]

/-- `det (L_B with column ρ replaced by w)[B, B] = Σ_{v∈B} w_v κ_v(B)`. -/
theorem redeiK_det_updateCol (a : ι → ι → ZMod 2) {B : Finset ι} {ρ : ι} (hρ : ρ ∈ B)
    (w : ι → ZMod 2) :
    (((lapl a B).updateCol ρ w).submatrix (fun x : ↥B => (x : ι)) (fun x : ↥B => (x : ι))).det =
      ∑ v ∈ B, w v * kappa a B v := by
  rw [det_submatrix_eq_pmin, ← pmin_transpose, ← updateRow_transpose, pmin_expand_row _ hρ]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [updateRow_self]
  congr 1
  rw [pmin_congr (M' := (lapl a B)ᵀ) fun k hk => updateRow_ne (Finset.ne_of_mem_erase hk),
    pmin_transpose, ← Finset.sdiff_singleton_eq_erase, ← Finset.sdiff_singleton_eq_erase,
    pmin_lapl_offdiag a hv hρ]

omit [Fintype ι] in
/-- Splitting off the column `ρ`. -/
theorem redeiK_sum_updateCol (a : ι → ι → ZMod 2) {B : Finset ι} {ρ : ι} (hρ : ρ ∈ B)
    (w F : ι → ZMod 2) (q : ι) :
    ∑ p ∈ B, (lapl a B).updateCol ρ w q p * F p =
      ∑ p ∈ B, lapl a B q p * Function.update F ρ 0 p + w q * F ρ := by
  rw [← Finset.add_sum_erase _ _ hρ, ← Finset.add_sum_erase B (fun p => lapl a B q p * _) hρ,
    updateCol_self, Function.update_self, mul_zero, zero_add, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [updateCol_ne (Finset.ne_of_mem_erase hp), Function.update_of_ne (Finset.ne_of_mem_erase hp)]

omit [Fintype ι] in
/-- A square matrix on `B`, read on functions `ι → 𝔽₂` supported on `B`: trivial kernel iff
nonzero determinant. -/
theorem redeiK_ker_iff_det (N : Matrix ι ι (ZMod 2)) (B : Finset ι) :
    (∀ F : ι → ZMod 2, (∀ i ∉ B, F i = 0) → (∀ q ∈ B, ∑ p ∈ B, N q p * F p = 0) →
        ∀ i ∈ B, F i = 0) ↔
      (N.submatrix (fun x : ↥B => (x : ι)) (fun x : ↥B => (x : ι))).det ≠ 0 := by
  rw [Ne, ← exists_mulVec_eq_zero_iff]
  constructor
  · rintro h ⟨f, hf0, hf⟩
    apply hf0
    funext x
    have := h (fun i => if hi : i ∈ B then f ⟨i, hi⟩ else 0) (fun i hi => dif_neg hi)
      (fun q hq => by
        have hq' := congrFun hf ⟨q, hq⟩
        rw [mulVec, dotProduct, Pi.zero_apply] at hq'
        rw [← hq', ← Finset.sum_coe_sort B]
        refine Finset.sum_congr rfl fun p _ => ?_
        simp)
      x x.2
    simpa using this
  · intro h F hF hN i hi
    by_contra hne
    refine h ⟨fun x => F x, fun h0 => hne (by simpa using congrFun h0 ⟨i, hi⟩), ?_⟩
    funext q
    rw [mulVec, dotProduct, Pi.zero_apply, ← hN q q.2]
    exact Finset.sum_coe_sort B (fun p => N q p * F p)

theorem redeiK_zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

/-- The kernel of `(L_B | z_B)` is trivial iff the square matrix `N` (column `ρ` of `L_B` replaced
by `w = y` or `z`) has trivial kernel. -/
theorem redeiK_kernel_iff_updateCol {a : ι → ι → ZMod 2} {y z : ι → ZMod 2} (hrec : Recip a y)
    {B : Finset ι} {ρ : ι} (hρ : ρ ∈ B) :
    (∀ (e : ι → ZMod 2) (e₂ : ZMod 2), (∀ i ∉ B, e i = 0) → (∑ i ∈ B, y i = 1 → e₂ = 0) →
        (∀ q ∈ B, ∑ p ∈ B, lapl a B q p * e p + e₂ * z q = 0) →
        e₂ = 0 ∧ ((∀ i ∈ B, e i = 0) ∨ (∀ i ∈ B, e i = 1))) ↔
      (∀ F : ι → ZMod 2, (∀ i ∉ B, F i = 0) →
        (∀ q ∈ B, ∑ p ∈ B,
          (lapl a B).updateCol ρ (if ∑ i ∈ B, y i = 1 then y else z) q p * F p = 0) →
        ∀ i ∈ B, F i = 0) := by
  set w := if ∑ i ∈ B, y i = 1 then y else z with hw
  constructor
  · intro h F hF hN
    simp_rw [redeiK_sum_updateCol a hρ] at hN
    set e := Function.update F ρ 0 with he
    have heB : ∀ i ∉ B, e i = 0 := fun i hi => by
      rw [he, Function.update_of_ne (by rintro rfl; exact hi hρ)]; exact hF i hi
    -- the coefficient `F ρ` of the column `w` vanishes
    have ht : F ρ = 0 ∨ ∑ i ∈ B, y i ≠ 1 := by
      by_cases hy : ∑ i ∈ B, y i = 1
      · left
        have hsum := Finset.sum_congr rfl hN
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw, if_pos hy, hy, one_mul,
          Finset.sum_comm] at hsum
        have h0 : ∑ p ∈ B, ∑ i ∈ B, lapl a B i p * e p = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          rw [← Finset.sum_mul]
          rw [show ∑ i ∈ B, lapl a B i p = colSum a B p from rfl, colSum_lapl hrec hp, hy,
            CharTwo.add_self_eq_zero, mul_zero, zero_mul]
        rwa [h0, zero_add, Finset.sum_const_zero] at hsum
      · exact Or.inr hy
    obtain ⟨h2, h3⟩ := h e (F ρ) heB
      (fun hy => ht.resolve_right (not_not.2 hy))
      (fun q hq => by
        have := hN q hq
        by_cases hy : ∑ i ∈ B, y i = 1
        · rw [ht.resolve_right (not_not.2 hy), zero_mul]
          rwa [ht.resolve_right (not_not.2 hy), mul_zero] at this
        · rwa [hw, if_neg hy, mul_comm] at this)
    have he0 : ∀ i ∈ B, e i = 0 := by
      refine h3.resolve_right fun h1 => ?_
      have := h1 ρ hρ
      rw [he, Function.update_self] at this
      exact zero_ne_one this
    intro i hi
    by_cases hiρ : i = ρ
    · rw [hiρ, h2]
    · have := he0 i hi
      rwa [he, Function.update_of_ne hiρ] at this
  · intro h e e₂ heB hy heq
    set e' : ι → ZMod 2 := fun i => if i ∈ B then e i - e ρ else 0 with he'
    have he'ρ : e' ρ = 0 := by simp [he', hρ]
    have hLe' : ∀ q ∈ B, ∑ p ∈ B, lapl a B q p * e' p = ∑ p ∈ B, lapl a B q p * e p := by
      intro q hq
      have : ∑ p ∈ B, lapl a B q p * e' p =
          ∑ p ∈ B, lapl a B q p * e p - (∑ p ∈ B, lapl a B q p) * e ρ := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [he']
        simp only [hp, ite_true]
        ring
      rw [this, redeiK_lapl_rowSum a hq, zero_mul, sub_zero]
    have hF := h (Function.update e' ρ e₂)
      (fun i hi => by
        rw [Function.update_of_ne (by rintro rfl; exact hi hρ)]
        simp [he', hi])
      (fun q hq => by
        rw [redeiK_sum_updateCol a hρ, Function.update_idem, Function.update_self,
          Function.update_eq_self_iff.2 he'ρ.symm, hLe' q hq]
        by_cases hyB : ∑ i ∈ B, y i = 1
        · rw [hy hyB, mul_zero, add_zero]
          have := heq q hq
          rwa [hy hyB, zero_mul, add_zero] at this
        · rw [hw, ite_cond_eq_false _ _ (eq_false hyB), mul_comm]
          exact heq q hq)
    have he₂ : e₂ = 0 := by simpa using hF ρ hρ
    have hconst : ∀ i ∈ B, e i = e ρ := by
      intro i hi
      by_cases hiρ : i = ρ
      · rw [hiρ]
      · have := hF i hi
        rw [Function.update_of_ne hiρ] at this
        simp only [he', hi, ite_true] at this
        exact sub_eq_zero.1 this
    refine ⟨he₂, ?_⟩
    rcases redeiK_zmod2_cases (e ρ) with h0 | h1
    · exact Or.inl fun i hi => (hconst i hi).trans h0
    · exact Or.inr fun i hi => (hconst i hi).trans h1

/-- **tyz-5b §2.2, Cases 1 and 2**: the kernel of `(L_B | z_B)` (with the column `z_B` only when
`y(B) = 0`) is the trivial one iff `redeiG = 1`. -/
theorem kernel_trivial_iff_redeiG {a : ι → ι → ZMod 2} {y z : ι → ZMod 2} (hrec : Recip a y)
    {B : Finset ι} (hB : B.Nonempty) :
    (∀ (e : ι → ZMod 2) (e₂ : ZMod 2), (∀ i ∉ B, e i = 0) → (∑ i ∈ B, y i = 1 → e₂ = 0) →
        (∀ q ∈ B, ∑ p ∈ B, lapl a B q p * e p + e₂ * z q = 0) →
        e₂ = 0 ∧ ((∀ i ∈ B, e i = 0) ∨ (∀ i ∈ B, e i = 1))) ↔
      redeiG a y z B = 1 := by
  obtain ⟨ρ, hρ⟩ := hB
  rw [redeiK_kernel_iff_updateCol hrec hρ, redeiK_ker_iff_det, redeiK_det_updateCol a hρ]
  have hg : ∑ v ∈ B, (if ∑ i ∈ B, y i = 1 then y else z) v * kappa a B v = redeiG a y z B := by
    rw [redeiG]
    split_ifs <;> rfl
  rw [hg]
  rcases redeiK_zmod2_cases (redeiG a y z B) with h0 | h1
  · rw [h0]; decide
  · rw [h1]; decide

end ZInQ.RouteK.Redei

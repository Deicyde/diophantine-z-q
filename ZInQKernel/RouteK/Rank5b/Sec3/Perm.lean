import ZInQKernel.RouteK.Rank5b.Sec3.Defs

/-!
# Permanent minors over `𝔽₂`

Over `𝔽₂` a determinant equals the permanent. For finite sets `R C ⊆ ι` of equal size,
`pmin M R C = Σ_σ Π_{i∈R} M i (σ i)` over the bijections `σ : R → C`, written as functions
`ι → ι` that are the identity off `R` (`bijFun R C`). This is the minor `det M[R, C]` over `𝔽₂`
(`det_submatrix_eq_pmin`, `det_eq_pmin_univ`), and it is convenient for the combinatorics of
tyz-5b §§2–3: no subtypes and no signs.

Row operations: `pmin_congr` (only the rows in `R` matter), `pmin_expand_row` (Laplace expansion
along a row), `pmin_updateRow_sum` (linearity in a row), `pmin_eq_zero_of_row_eq` (two equal rows).
-/

namespace ZInQ.RouteK.Rank5b.Sec3

open Finset Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The bijections `R → C`, as functions `ι → ι` equal to the identity off `R`. -/
def bijFun (R C : Finset ι) : Finset (ι → ι) :=
  univ.filter fun σ => (∀ i, i ∉ R → σ i = i) ∧ (∀ i ∈ R, σ i ∈ C) ∧
    (∀ i ∈ R, ∀ j ∈ R, σ i = σ j → i = j) ∧ R.card = C.card

/-- The minor `det M[R, C]` over `𝔽₂`, as a permanent. -/
def pmin (M : Matrix ι ι (ZMod 2)) (R C : Finset ι) : ZMod 2 :=
  ∑ σ ∈ bijFun R C, ∏ i ∈ R, M i (σ i)

theorem mem_bijFun {R C : Finset ι} {σ : ι → ι} :
    σ ∈ bijFun R C ↔ (∀ i, i ∉ R → σ i = i) ∧ (∀ i ∈ R, σ i ∈ C) ∧
      (∀ i ∈ R, ∀ j ∈ R, σ i = σ j → i = j) ∧ R.card = C.card := by
  simp [bijFun]

/-- A bijection `R → C` is onto `C`. -/
theorem bijFun_surj {R C : Finset ι} {σ : ι → ι} (hσ : σ ∈ bijFun R C) :
    ∀ c ∈ C, ∃ i ∈ R, σ i = c := by
  obtain ⟨_, hmap, hinj, hcard⟩ := mem_bijFun.1 hσ
  have himg : R.image σ = C := by
    apply Finset.eq_of_subset_of_card_le
    · intro c hc; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc; exact hmap i hi
    · rw [Finset.card_image_of_injOn (fun i hi j hj h => hinj i hi j hj h), hcard]
  intro c hc
  rw [← himg] at hc
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc
  exact ⟨i, hi, rfl⟩

theorem zmod2_units_smul (u : ℤˣ) (x : ZMod 2) : u • x = x := by
  rcases Int.units_eq_one_or u with h | h
  · rw [h, one_smul]
  · rw [h, Units.neg_smul, one_smul, ZMod.neg_eq_self_mod_two]

/-- Over `𝔽₂`, the principal minor on `S` is `pmin M S S`. -/
theorem det_submatrix_eq_pmin (M : Matrix ι ι (ZMod 2)) (S : Finset ι) :
    (M.submatrix (fun x : ↥S => (x : ι)) (fun x : ↥S => (x : ι))).det = pmin M S S := by
  rw [← det_transpose, det_apply]
  simp only [zmod2_units_smul, transpose_apply, submatrix_apply]
  classical
  let ext : Equiv.Perm ↥S → (ι → ι) := fun τ i => if h : i ∈ S then (τ ⟨i, h⟩ : ι) else i
  have hext_mem : ∀ τ, ext τ ∈ bijFun S S := fun τ => by
    refine mem_bijFun.2 ⟨fun i hi => by simp [ext, hi], fun i hi => by simp [ext, hi],
      fun i hi j hj h => ?_, rfl⟩
    simp only [ext, hi, hj, dite_true] at h
    have := τ.injective (Subtype.ext h)
    exact congrArg Subtype.val this
  refine Finset.sum_bij' (fun τ _ => ext τ)
    (fun σ hσ => Equiv.ofBijective (fun x : ↥S => (⟨σ x, (mem_bijFun.1 hσ).2.1 x x.2⟩ : ↥S))
      (Finite.injective_iff_bijective.1 fun x y h => Subtype.ext
        ((mem_bijFun.1 hσ).2.2.1 x x.2 y y.2 (congrArg Subtype.val h))))
    (fun τ _ => hext_mem τ) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro τ _
    ext x
    simp [ext]
  · intro σ hσ
    funext i
    by_cases hi : i ∈ S
    · simp [ext, hi]
    · simp [ext, hi, (mem_bijFun.1 hσ).1 i hi]
  · intro τ _
    rw [← Finset.prod_coe_sort S]
    refine Finset.prod_congr rfl fun x _ => ?_
    simp [ext, x.2]

/-- Over `𝔽₂`, `det M = pmin M univ univ`. -/
theorem det_eq_pmin_univ (M : Matrix ι ι (ZMod 2)) : M.det = pmin M univ univ := by
  rw [← det_submatrix_eq_pmin]
  exact (det_submatrix_equiv_self (Equiv.subtypeUnivEquiv Finset.mem_univ) M).symm

/-- Only the rows in `R` matter. -/
theorem pmin_congr {M M' : Matrix ι ι (ZMod 2)} {R C : Finset ι} (h : ∀ i ∈ R, M i = M' i) :
    pmin M R C = pmin M' R C := by
  refine Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun i hi => ?_
  rw [h i hi]

/-- **Laplace expansion along a row** `i ∈ R`: `pmin M R C = Σ_{v∈C} M i v · pmin M (R∖i) (C∖v)`. -/
theorem pmin_expand_row (M : Matrix ι ι (ZMod 2)) {R C : Finset ι} {i : ι} (hi : i ∈ R) :
    pmin M R C = ∑ v ∈ C, M i v * pmin M (R.erase i) (C.erase v) := by
  classical
  unfold pmin
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sigma']
  refine Finset.sum_bij' (fun σ _ => ⟨σ i, Function.update σ i i⟩)
    (fun p _ => Function.update p.2 i p.1) ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    obtain ⟨hid, hmap, hinj, hcard⟩ := mem_bijFun.1 hσ
    refine Finset.mem_sigma.2 ⟨hmap i hi, mem_bijFun.2 ⟨fun j hj => ?_, fun j hj => ?_,
      fun j hj k hk h => ?_, ?_⟩⟩ <;> dsimp only at *
    · by_cases hji : j = i
      · subst hji; simp
      · rw [Function.update_of_ne hji]
        exact hid j fun h => hj (Finset.mem_erase.2 ⟨hji, h⟩)
    · obtain ⟨hji, hjR⟩ := Finset.mem_erase.1 hj
      rw [Function.update_of_ne hji]
      exact Finset.mem_erase.2 ⟨fun h => hji (hinj j hjR i hi h), hmap j hjR⟩
    · obtain ⟨hji, hjR⟩ := Finset.mem_erase.1 hj
      obtain ⟨hki, hkR⟩ := Finset.mem_erase.1 hk
      rw [Function.update_of_ne hji, Function.update_of_ne hki] at h
      exact hinj j hjR k hkR h
    · rw [Finset.card_erase_of_mem hi, Finset.card_erase_of_mem (hmap i hi), hcard]
  · intro p hp
    obtain ⟨hv, hp2⟩ := Finset.mem_sigma.1 hp
    obtain ⟨hid, hmap, hinj, hcard⟩ := mem_bijFun.1 hp2
    have hcard' : R.card = C.card := by
      have h1 := Finset.card_erase_add_one hi
      have h2 := Finset.card_erase_add_one hv
      omega
    refine mem_bijFun.2 ⟨fun j hj => ?_, fun j hj => ?_, fun j hj k hk h => ?_, hcard'⟩
    · have hji : j ≠ i := fun h => hj (h ▸ hi)
      rw [Function.update_of_ne hji]
      exact hid j fun h => hj (Finset.mem_of_mem_erase h)
    · by_cases hji : j = i
      · subst hji; simp [hv]
      · rw [Function.update_of_ne hji]
        exact Finset.mem_of_mem_erase (hmap j (Finset.mem_erase.2 ⟨hji, hj⟩))
    · by_cases hji : j = i
      · by_cases hki : k = i
        · rw [hji, hki]
        · subst hji
          rw [Function.update_self, Function.update_of_ne hki] at h
          have := hmap k (Finset.mem_erase.2 ⟨hki, hk⟩)
          rw [← h] at this
          exact absurd rfl (Finset.mem_erase.1 this).1
      · by_cases hki : k = i
        · subst hki
          rw [Function.update_self, Function.update_of_ne hji] at h
          have := hmap j (Finset.mem_erase.2 ⟨hji, hj⟩)
          rw [h] at this
          exact absurd rfl (Finset.mem_erase.1 this).1
        · rw [Function.update_of_ne hji, Function.update_of_ne hki] at h
          exact hinj j (Finset.mem_erase.2 ⟨hji, hj⟩) k (Finset.mem_erase.2 ⟨hki, hk⟩) h
  · intro σ _
    funext j
    by_cases hji : j = i
    · subst hji; simp
    · simp [Function.update_of_ne hji]
  · intro p hp
    obtain ⟨_, hp2⟩ := Finset.mem_sigma.1 hp
    have hid := (mem_bijFun.1 hp2).1
    refine Sigma.ext (by simp) (heq_of_eq ?_)
    funext j
    by_cases hji : j = i
    · subst hji
      simp only [Function.update_self]
      exact (hid j (by simp)).symm
    · simp [Function.update_of_ne hji]
  · intro σ _
    rw [← Finset.mul_prod_erase R _ hi]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    dsimp only
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- **Linearity in a row** `i ∈ R`. -/
theorem pmin_updateRow_sum (M : Matrix ι ι (ZMod 2)) {R C : Finset ι} {i : ι} (hi : i ∈ R)
    {κ : Type*} (T : Finset κ) (r : κ → ι → ZMod 2) :
    pmin (M.updateRow i (∑ u ∈ T, r u)) R C = ∑ u ∈ T, pmin (M.updateRow i (r u)) R C := by
  rw [pmin_expand_row _ hi]
  simp_rw [pmin_expand_row _ hi (C := C)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [updateRow_self, Finset.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [updateRow_self]
  congr 1
  refine pmin_congr fun j hj => ?_
  rw [updateRow_ne (Finset.ne_of_mem_erase hj), updateRow_ne (Finset.ne_of_mem_erase hj)]

/-- **Two equal rows**: if rows `i ≠ k` of `M` (both in `R`) are equal, `pmin M R C = 0`. -/
theorem pmin_eq_zero_of_row_eq (M : Matrix ι ι (ZMod 2)) {R C : Finset ι} {i k : ι}
    (hi : i ∈ R) (hk : k ∈ R) (hik : i ≠ k) (h : M i = M k) : pmin M R C = 0 := by
  classical
  unfold pmin
  refine Finset.sum_involution (fun σ _ => σ ∘ Equiv.swap i k) ?_ ?_ ?_ ?_
  · intro σ hσ
    have : ∏ j ∈ R, M j ((σ ∘ Equiv.swap i k) j) = ∏ j ∈ R, M j (σ j) := by
      rw [← Finset.prod_erase_mul R _ hi, ← Finset.prod_erase_mul R _ hi,
        ← Finset.prod_erase_mul _ _ (Finset.mem_erase.2 ⟨hik.symm, hk⟩),
        ← Finset.prod_erase_mul _ _ (Finset.mem_erase.2 ⟨hik.symm, hk⟩)]
      have hrest : ∏ j ∈ (R.erase i).erase k, M j ((σ ∘ Equiv.swap i k) j) =
          ∏ j ∈ (R.erase i).erase k, M j (σ j) := by
        refine Finset.prod_congr rfl fun j hj => ?_
        have hjk := Finset.ne_of_mem_erase hj
        have hji := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
        simp [Equiv.swap_apply_of_ne_of_ne hji hjk]
      rw [hrest]
      simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
      rw [h]
      ring
    rw [this, CharTwo.add_self_eq_zero]
  · intro σ hσ _ heq
    have := congrFun heq i
    simp only [Function.comp_apply, Equiv.swap_apply_left] at this
    exact hik ((mem_bijFun.1 hσ).2.2.1 k hk i hi this).symm
  · intro σ hσ
    obtain ⟨hid, hmap, hinj, hcard⟩ := mem_bijFun.1 hσ
    have hsw : ∀ j, j ∈ R → Equiv.swap i k j ∈ R := fun j hj => by
      rcases eq_or_ne j i with rfl | hji
      · simpa using hk
      rcases eq_or_ne j k with rfl | hjk
      · simpa using hi
      rw [Equiv.swap_apply_of_ne_of_ne hji hjk]; exact hj
    refine mem_bijFun.2 ⟨fun j hj => ?_, fun j hj => hmap _ (hsw j hj),
      fun j hj l hl hjl => ?_, hcard⟩
    · have hji : j ≠ i := fun h => hj (h ▸ hi)
      have hjk : j ≠ k := fun h => hj (h ▸ hk)
      simp [Equiv.swap_apply_of_ne_of_ne hji hjk, hid j hj]
    · exact (Equiv.swap i k).injective (hinj _ (hsw j hj) _ (hsw l hl) hjl)
  · intro σ _
    funext j
    simp

end ZInQ.RouteK.Rank5b.Sec3

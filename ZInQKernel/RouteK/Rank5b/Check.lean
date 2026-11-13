import ZInQKernel.RouteK.Rank5b.Row5b

/-!
# Route K, row 5b: kernel cross-checks of `det M_5b`

Two small values of `det M_5b`, checked by the kernel (no `native_decide`): `n = 21 = 3·7`
(`det M_5b = 1`; `|a| = 7` is a Selmer first coordinate, tyz-5b §5–6) and `n = 5`
(`det M_5b = 0`). The matrix of `natConfig n` is transported to an explicit enumeration of the
primes (`det_M5bc_of_iso`), its entries are evaluated from the Legendre bits, and the
`5 × 5` (resp. `3 × 3`) determinant over `𝔽₂` is expanded along rows.
-/

namespace ZInQ.RouteK.Rank5b

open Matrix

namespace Config

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- `M_5b` is invariant under an isomorphism of configurations. -/
theorem M5bc_of_iso (𝒞 : RouteK.Config ι) (𝒞' : RouteK.Config κ) (e : κ ≃ ι)
    (hc : ∀ x, 𝒞'.cls x = 𝒞.cls (e x)) (hb : ∀ x y, x ≠ y → 𝒞'.bit x y = 𝒞.bit (e x) (e y)) :
    M5bc 𝒞' = (M5bc 𝒞).submatrix (Sum.map (Sum.map e e) id) (Sum.map (Sum.map e e) id) := by
  have hL : ∀ x y, Lc 𝒞' x y = Lc 𝒞 (e x) (e y) := by
    intro x y
    by_cases h : x = y
    · subst h
      simp only [Lc, ite_true]
      have hmap : (Finset.univ.erase x).map e.toEmbedding = Finset.univ.erase (e x) := by
        ext z
        simp only [Finset.mem_map, Finset.mem_erase, Finset.mem_univ, and_true,
          Equiv.coe_toEmbedding]
        constructor
        · rintro ⟨w, hw, rfl⟩; exact e.injective.ne hw
        · intro hz; exact ⟨e.symm z, fun h => hz (by rw [← h, e.apply_symm_apply]), by simp⟩
      rw [← hmap, Finset.sum_map]
      exact Finset.sum_congr rfl fun z hz => hb z x (Finset.ne_of_mem_erase hz)
    · simp only [Lc, h, e.injective.ne h, ite_false]
      exact hb y x (Ne.symm h)
  have hl : ∀ x, 𝒞'.lam x = 𝒞.lam (e x) := fun x => by simp [RouteK.Config.lam, hc]
  have hm : ∀ x, 𝒞'.mu x = 𝒞.mu (e x) := fun x => by simp [RouteK.Config.mu, hc]
  ext i j
  rcases i with (i | i) | ⟨⟩ <;> rcases j with (j | j) | ⟨⟩ <;>
    simp [M5bc, border, M1c, hL, hl, hm, diagonal, replicateCol, replicateRow,
      e.injective.eq_iff]

theorem det_M5bc_of_iso (𝒞 : RouteK.Config ι) (𝒞' : RouteK.Config κ) (e : κ ≃ ι)
    (hc : ∀ x, 𝒞'.cls x = 𝒞.cls (e x)) (hb : ∀ x y, x ≠ y → 𝒞'.bit x y = 𝒞.bit (e x) (e y)) :
    (M5bc 𝒞').det = (M5bc 𝒞).det := by
  rw [M5bc_of_iso 𝒞 𝒞' e hc hb]
  exact det_submatrix_equiv_self ((Equiv.sumCongr (Equiv.sumCongr e e) (Equiv.refl Unit))) _

end Config

/-! ### `n = 21` -/

theorem primeFactors_21 : (21 : ℕ).primeFactors = {3, 7} := by
  rw [show (21 : ℕ) = 3 * 7 by rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  rfl

theorem legBit_3_7 : legBit 3 ((7 : ℕ) : ℤ) = 0 := by
  unfold legBit; simp only [ite_eq_left_iff, one_ne_zero, imp_false, not_not]; exact ⟨1, by decide⟩

theorem legBit_7_3 : legBit 7 ((3 : ℕ) : ℤ) = 1 := by
  unfold legBit
  simp only [ite_eq_right_iff, zero_ne_one, imp_false]
  rintro ⟨r, hr⟩; fin_cases r <;> revert hr <;> decide

/-- The primes of `21`, enumerated as `3, 7`. -/
def enum21 : Fin 2 → ℕ := ![3, 7]

theorem enum21_inj : Function.Injective enum21 := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [enum21]

theorem enum21_prime : ∀ k, (enum21 k).Prime ∧ enum21 k ≠ 2 := by
  intro k; fin_cases k <;> simp [enum21] <;> norm_num

theorem enum21_mem (k : Fin 2) : enum21 k ∈ (21 : ℕ).primeFactors := by
  rw [primeFactors_21]; fin_cases k <;> simp [enum21]

/-- The enumeration as an equivalence onto the prime factors of `21`. -/
noncomputable def equiv21 : Fin 2 ≃ (21 : ℕ).primeFactors :=
  Equiv.ofBijective (fun k => ⟨enum21 k, enum21_mem k⟩)
    ⟨fun _ _ h => enum21_inj (congrArg Subtype.val h), fun q => by
      have h : (q : ℕ) ∈ ({3, 7} : Finset ℕ) := primeFactors_21 ▸ q.2
      rcases Finset.mem_insert.mp h with h | h
      · exact ⟨0, Subtype.ext h.symm⟩
      · exact ⟨1, Subtype.ext (Finset.mem_singleton.mp h).symm⟩⟩

/-- An enumeration of `(Fin 2 ⊕ Fin 2) ⊕ Unit` (the index type of `M_5b` for two primes). -/
def idx5 : Fin 5 ≃ (Fin 2 ⊕ Fin 2) ⊕ Unit where
  toFun := ![Sum.inl (Sum.inl 0), Sum.inl (Sum.inl 1), Sum.inl (Sum.inr 0), Sum.inl (Sum.inr 1),
    Sum.inr ()]
  invFun
    | Sum.inl (Sum.inl i) => i.castLE (by omega)
    | Sum.inl (Sum.inr i) => (i.castLE (by omega : 2 ≤ 3)).succ.succ
    | Sum.inr () => 4
  left_inv := by decide
  right_inv := by decide

theorem M5bc_primeCfg_21 :
    (Config.M5bc (primeCfg enum21 enum21_inj enum21_prime)).det = 1 := by
  rw [← det_submatrix_equiv_self idx5]
  have hb01 : legBit (enum21 0) ((enum21 1 : ℕ) : ℤ) = 0 := legBit_3_7
  have hb10 : legBit (enum21 1) ((enum21 0 : ℕ) : ℤ) = 1 := legBit_7_3
  have hl : ∀ k, (primeCfg enum21 enum21_inj enum21_prime).lam k = 1 := by
    intro k; fin_cases k <;> decide
  have hm0 : (primeCfg enum21 enum21_inj enum21_prime).mu 0 = 1 := by decide
  have hm1 : (primeCfg enum21 enum21_inj enum21_prime).mu 1 = 0 := by decide
  have he0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have he1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  have hM : (Config.M5bc (primeCfg enum21 enum21_inj enum21_prime)).submatrix idx5 idx5 =
      !![0, 1, 0, 1, 0; 1, 0, 0, 1, 0; 0, 0, 1, 0, 1; 1, 1, 0, 0, 1; 0, 0, 1, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [idx5, Config.M5bc, border, Config.M1c, Config.Lc, diagonal, replicateCol,
        replicateRow, hb01, hb10, hl, hm0, hm1, he0, he1]
    all_goals decide
  rw [hM]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  decide

/-- **Cross-check, `n = 21 = 3·7`**: `det M_5b = 1` (as Corollary 4.4 predicts: `#Sel₂(C_21) = 8`
and `7` is a Selmer first coordinate). -/
theorem det_M5b_21 : (M5b 21).det = 1 := by
  have hd : Odd 21 := odd_of_mod_eight_eq_five (by decide)
  rw [M5b_eq_M5bc hd, ← Config.det_M5bc_of_iso (natConfig 21 hd)
    (primeCfg enum21 enum21_inj enum21_prime) equiv21 (fun _ => rfl) (fun _ _ _ => rfl)]
  exact M5bc_primeCfg_21

/-! ### `n = 5` -/

theorem primeFactors_5 : (5 : ℕ).primeFactors = {5} := Nat.Prime.primeFactors (by norm_num)

/-- **Cross-check, `n = 5`**: `det M_5b = 0` (`y_5 = 0`, so the border row vanishes). -/
theorem det_M5b_5 : (M5b 5).det = 0 := by
  refine det_eq_zero_of_row_eq_zero (Sum.inr ()) fun j => ?_
  have hy : ∀ i : (5 : ℕ).primeFactors, yBit 5 i = 0 := by
    intro i
    have h : (i : ℕ) ∈ ({5} : Finset ℕ) := primeFactors_5 ▸ i.2
    rw [Finset.mem_singleton] at h
    rw [yBit, h, lamBit]
    unfold legBit
    simp only [ite_eq_left_iff, one_ne_zero, imp_false, not_not]
    exact ⟨2, by decide⟩
  rcases j with (j | j) | ⟨⟩ <;> simp [M5b, border, replicateRow, hy]

end ZInQ.RouteK.Rank5b

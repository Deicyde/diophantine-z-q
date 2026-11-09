import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# Ideal counts in number fields: definition and multiplicativity

For a number field `K`, `idealCount K n` is the number of ideals of `𝓞 K` of absolute norm `n`,
the `n`-th coefficient of `NumberField.dedekindZeta K`. It is multiplicative: an ideal of norm
`m * n` with `m`, `n` coprime is uniquely the product of an ideal of norm `m` and one of norm `n`
(plan step 3.3, item 1).
-/

namespace ZInQ.Progressions

open NumberField Ideal

variable (K : Type*) [Field K] [NumberField K]

/-- The number of ideals of `𝓞 K` of absolute norm `n`. -/
noncomputable def idealCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // absNorm I = n}

theorem dedekindZeta_eq_LSeries_idealCount (s : ℂ) :
    dedekindZeta K s = LSeries (fun n ↦ (idealCount K n : ℂ)) s := rfl

/-- The only ideal of norm `1` is `𝓞 K`. -/
theorem idealCount_one : idealCount K 1 = 1 :=
  Nat.card_eq_one_iff_exists.mpr
    ⟨⟨⊤, absNorm_top⟩, fun I ↦ Subtype.ext (absNorm_eq_one_iff.mp I.2)⟩

section ring

variable {R : Type*} [CommRing R]

/-- If `m ∈ I` and `J` is coprime to `m`, then `I` is recovered from `I * J` as `I * J + (m)`. -/
theorem idealCount_sup_span_eq {I J : Ideal R} {m : R} (hm : m ∈ I)
    (hJ : J ⊔ span {m} = ⊤) : I * J ⊔ span {m} = I := by
  refine le_antisymm (sup_le Ideal.mul_le_left ((span_singleton_le_iff_mem I).mpr hm)) ?_
  calc I = I * (J ⊔ span {m}) := by rw [hJ, mul_top]
    _ = I * J ⊔ I * span {m} := Ideal.mul_sup _ _ _
    _ ≤ I * J ⊔ span {m} := sup_le_sup_left Ideal.mul_le_right _

/-- If `m * n ∈ L` and `(m) + (n) = 1`, then `L = (L + (m)) * (L + (n))`. -/
theorem idealCount_sup_mul_sup_eq {L : Ideal R} {m n : R} (hmn : m * n ∈ L)
    (hcop : span {m} ⊔ span {n} = ⊤) : (L ⊔ span {m}) * (L ⊔ span {n}) = L := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup, span_singleton_mul_span_singleton]
    refine sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_left) (sup_le Ideal.mul_le_right ?_)
    exact (span_singleton_le_iff_mem L).mpr hmn
  · calc L = L * (span {m} ⊔ span {n}) := by rw [hcop, mul_top]
      _ = L * span {m} ⊔ L * span {n} := Ideal.mul_sup _ _ _
      _ ≤ (L ⊔ span {m}) * (L ⊔ span {n}) := by
        refine sup_le ?_ (mul_mono le_sup_left le_sup_right)
        rw [mul_comm]
        exact mul_mono le_sup_right le_sup_left

end ring

theorem idealCount_eq_of_dvd_of_dvd {a b m n : ℕ} (ha : a ∣ m) (hb : b ∣ n) (hab : a * b = m * n)
    (h : m.Coprime n) : a = m ∧ b = n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hn : n = 1 := by simpa using h
    subst hn
    have hb1 : b = 1 := Nat.dvd_one.mp hb
    subst hb1
    simpa using hab
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hm1 : m = 1 := by simpa using h
    subst hm1
    have ha1 : a = 1 := Nat.dvd_one.mp ha
    subst ha1
    simpa using hab
  have ham := Nat.le_of_dvd hm ha
  have hbn := Nat.le_of_dvd hn hb
  have hpos : 0 < a * b := hab ▸ Nat.mul_pos hm hn
  have ha0 : 0 < a := Nat.pos_of_mul_pos_right hpos
  have hb0 : 0 < b := Nat.pos_of_mul_pos_left hpos
  constructor <;> nlinarith

variable {K}

omit [NumberField K] in
theorem idealCount_span_sup_span_eq_top {m n : ℕ} (h : m.Coprime n) :
    span {(m : 𝓞 K)} ⊔ span {(n : 𝓞 K)} = ⊤ := by
  rw [← isCoprime_iff_sup_eq, isCoprime_span_singleton_iff]
  have := (Nat.isCoprime_iff_coprime.mpr h).map (Int.castRingHom (𝓞 K))
  simpa using this

theorem idealCount_absNorm_sup_eq {L : Ideal (𝓞 K)} {m n : ℕ} (hL : absNorm L = m * n)
    (h : m.Coprime n) : absNorm (L ⊔ span {(m : 𝓞 K)}) = m := by
  have key : ∀ {m n : ℕ}, m.Coprime n → absNorm L = m * n →
      absNorm (L ⊔ span {(m : 𝓞 K)}) ∣ m := by
    intro m n h hL
    have h1 : absNorm (L ⊔ span {(m : 𝓞 K)}) ∣ m ^ Module.finrank ℤ (𝓞 K) := by
      rw [← absNorm_span_natCast]
      exact absNorm_dvd_absNorm_of_le le_sup_right
    have h2 : absNorm (L ⊔ span {(m : 𝓞 K)}) ∣ m * n := by
      rw [← hL]
      exact absNorm_dvd_absNorm_of_le le_sup_left
    exact ((Nat.Coprime.pow_left _ h).coprime_dvd_left h1).dvd_of_dvd_mul_right h2
  have ha := key h hL
  have hb := key h.symm (by rw [hL, mul_comm])
  have hab : absNorm (L ⊔ span {(m : 𝓞 K)}) * absNorm (L ⊔ span {(n : 𝓞 K)}) = m * n := by
    rw [← map_mul, idealCount_sup_mul_sup_eq (by exact_mod_cast hL ▸ absNorm_mem L)
      (idealCount_span_sup_span_eq_top h), hL]
  exact (idealCount_eq_of_dvd_of_dvd ha hb hab h).1

/-- Ideals of norm `m * n`, `m` and `n` coprime, are the products of an ideal of norm `m` and
an ideal of norm `n`. -/
noncomputable def idealCountMulEquiv {m n : ℕ} (h : m.Coprime n) :
    {I : Ideal (𝓞 K) // absNorm I = m} × {J : Ideal (𝓞 K) // absNorm J = n} ≃
      {L : Ideal (𝓞 K) // absNorm L = m * n} where
  toFun IJ := ⟨IJ.1.1 * IJ.2.1, by rw [map_mul, IJ.1.2, IJ.2.2]⟩
  invFun L := (⟨L.1 ⊔ span {(m : 𝓞 K)}, idealCount_absNorm_sup_eq L.2 h⟩,
    ⟨L.1 ⊔ span {(n : 𝓞 K)}, idealCount_absNorm_sup_eq (by rw [L.2, mul_comm]) h.symm⟩)
  left_inv := by
    rintro ⟨⟨I, hI⟩, ⟨J, hJ⟩⟩
    have hmI : (m : 𝓞 K) ∈ I := by simpa [hI] using absNorm_mem I
    have hnJ : (n : 𝓞 K) ∈ J := by simpa [hJ] using absNorm_mem J
    have hcop := idealCount_span_sup_span_eq_top (K := K) h
    have hJm : J ⊔ span {(m : 𝓞 K)} = ⊤ := by
      rw [eq_top_iff, ← hcop]
      exact sup_le le_sup_right ((span_singleton_le_iff_mem _).mpr (mem_sup_left hnJ))
    have hIn : I ⊔ span {(n : 𝓞 K)} = ⊤ := by
      rw [eq_top_iff, ← hcop]
      exact sup_le ((span_singleton_le_iff_mem _).mpr (mem_sup_left hmI)) le_sup_right
    ext1
    · exact Subtype.ext (idealCount_sup_span_eq hmI hJm)
    · refine Subtype.ext ?_
      change I * J ⊔ span {(n : 𝓞 K)} = J
      rw [mul_comm]
      exact idealCount_sup_span_eq hnJ hIn
  right_inv := by
    rintro ⟨L, hL⟩
    refine Subtype.ext ?_
    change (L ⊔ span {(m : 𝓞 K)}) * (L ⊔ span {(n : 𝓞 K)}) = L
    refine idealCount_sup_mul_sup_eq ?_ (idealCount_span_sup_span_eq_top h)
    have := absNorm_mem L
    rw [hL] at this
    exact_mod_cast this

variable (K) in
/-- **Multiplicativity** of the ideal counts (plan step 3.3, item 1). -/
theorem idealCount_mul {m n : ℕ} (h : m.Coprime n) :
    idealCount K (m * n) = idealCount K m * idealCount K n := by
  rw [idealCount, idealCount, idealCount, ← Nat.card_prod]
  exact (Nat.card_congr (idealCountMulEquiv h)).symm

end ZInQ.Progressions

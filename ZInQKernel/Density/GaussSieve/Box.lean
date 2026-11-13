import ZInQKernel.Density.GaussSieve.Local

/-!
# Counting a box with a divisibility condition (pd-paper.md §4.3, Lemma 4.4)

* `abs_card_Ico_cast_eq_sub_le`: an interval of `M` integers has `M/d + θ` (`|θ| ≤ 1`) elements in a
  residue class mod `d`.
* `abs_card_box_dvd_sub_le`: for the box `ℬ = [a₁, a₁ + M₁) × [a₂, a₂ + M₂)`,
  `|#{(U, V) ∈ ℬ : d ∣ (ℓU)² + (b + ℓV)²} - ρ(d)·M₁M₂/d²| ≤ ρ(d)·(M₁ + M₂ + 1)`, where
  `ρ(d) = #ZSet (ZMod d) ℓ b`.
-/

open Finset

namespace ZInQ.Density.GaussSieve

noncomputable section

open scoped Classical

theorem ceil_sub_ceil_bounds (x t : ℚ) :
    t - 1 < ((⌈x + t⌉ - ⌈x⌉ : ℤ) : ℚ) ∧ ((⌈x + t⌉ - ⌈x⌉ : ℤ) : ℚ) < t + 1 := by
  have h1 := Int.le_ceil (x + t)
  have h2 := Int.ceil_lt_add_one (x + t)
  have h3 := Int.le_ceil x
  have h4 := Int.ceil_lt_add_one x
  push_cast
  constructor <;> linarith

/-- An interval of `M` integers meets a residue class mod `d` in `M/d + θ` points, `|θ| ≤ 1`. -/
theorem abs_card_Ico_cast_eq_sub_le (a : ℤ) (M d : ℕ) [NeZero d] (z : ZMod d) :
    |((#{U ∈ Ico a (a + (M : ℤ)) | ((U : ℤ) : ZMod d) = z} : ℕ) : ℝ) - (M : ℝ) / d| ≤ 1 := by
  have hd : (0 : ℤ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hfilt : {U ∈ Ico a (a + (M : ℤ)) | ((U : ℤ) : ZMod d) = z} =
      {U ∈ Ico a (a + (M : ℤ)) | U ≡ (z.val : ℤ) [ZMOD d]} := by
    refine filter_congr fun U _ => ?_
    rw [← ZMod.intCast_eq_intCast_iff]
    simp
  rw [hfilt]
  have hc := Int.Ico_filter_modEq_card a (a + M) hd (z.val : ℤ)
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hx : (((a + M : ℤ) : ℚ) - ((z.val : ℤ) : ℚ)) / ((d : ℤ) : ℚ) =
      ((a : ℚ) - z.val) / d + (M : ℚ) / d := by push_cast; ring
  have hy : (((a : ℤ) : ℚ) - ((z.val : ℤ) : ℚ)) / ((d : ℤ) : ℚ) = ((a : ℚ) - z.val) / d := by
    push_cast; ring
  rw [hx, hy] at hc
  have hb := ceil_sub_ceil_bounds (((a : ℚ) - z.val) / d) ((M : ℚ) / d)
  set D : ℤ := ⌈((a : ℚ) - z.val) / d + (M : ℚ) / d⌉ - ⌈((a : ℚ) - z.val) / d⌉ with hD
  set c := #{U ∈ Ico a (a + (M : ℤ)) | U ≡ (z.val : ℤ) [ZMOD d]}
  have ht : (0 : ℚ) ≤ (M : ℚ) / d := by positivity
  have hq : |(c : ℚ) - (M : ℚ) / d| ≤ 1 := by
    rw [abs_le]
    rcases le_or_gt 0 D with h0 | h0
    · have : (c : ℤ) = D := by rw [hc]; exact max_eq_left h0
      have : (c : ℚ) = (D : ℚ) := by exact_mod_cast this
      rw [this]; constructor <;> linarith [hb.1, hb.2]
    · have : (c : ℤ) = 0 := by rw [hc]; exact max_eq_right h0.le
      have hc0 : (c : ℚ) = 0 := by exact_mod_cast this
      have : (D : ℚ) ≤ -1 := by exact_mod_cast (show D ≤ -1 by omega)
      rw [hc0]; constructor <;> linarith [hb.1, hb.2]
  have : |((c : ℚ) : ℝ) - (((M : ℚ) / d : ℚ) : ℝ)| ≤ 1 := by exact_mod_cast hq
  push_cast at this
  exact this

theorem abs_mul_sub_mul_le {n₁ n₂ m₁ m₂ M₁ M₂ : ℝ} (h₁ : |n₁ - m₁| ≤ 1) (h₂ : |n₂ - m₂| ≤ 1)
    (hn₂ : 0 ≤ n₂) (hm₁ : 0 ≤ m₁) (hM₁ : m₁ ≤ M₁) (hM₂ : m₂ ≤ M₂) :
    |n₁ * n₂ - m₁ * m₂| ≤ M₁ + M₂ + 1 := by
  have e : n₁ * n₂ - m₁ * m₂ = (n₁ - m₁) * n₂ + m₁ * (n₂ - m₂) := by ring
  rw [e]
  have h2 : n₂ ≤ m₂ + 1 := by linarith [(abs_le.1 h₂).2]
  calc |(n₁ - m₁) * n₂ + m₁ * (n₂ - m₂)| ≤ |(n₁ - m₁) * n₂| + |m₁ * (n₂ - m₂)| := abs_add_le _ _
    _ = |n₁ - m₁| * n₂ + m₁ * |n₂ - m₂| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hn₂, abs_of_nonneg hm₁]
    _ ≤ 1 * n₂ + m₁ * 1 := by gcongr
    _ ≤ M₁ + M₂ + 1 := by linarith

/-- The box `[a₁, a₁ + M₁) × [a₂, a₂ + M₂)`. -/
def box (a₁ a₂ : ℤ) (M₁ M₂ : ℕ) : Finset (ℤ × ℤ) := Ico a₁ (a₁ + (M₁ : ℤ)) ×ˢ Ico a₂ (a₂ + (M₂ : ℤ))

/-- `F(U, V) = (ℓU)² + (b + ℓV)²` as an integer. -/
def gaussFZ (ℓ b : ℤ) (x : ℤ × ℤ) : ℤ := (ℓ * x.1) ^ 2 + (b + ℓ * x.2) ^ 2

/-- **Lemma 4.4.** -/
theorem abs_card_box_dvd_sub_le (ℓ b a₁ a₂ : ℤ) (M₁ M₂ d : ℕ) (hd : 0 < d) :
    |((#{x ∈ box a₁ a₂ M₁ M₂ | (d : ℤ) ∣ gaussFZ ℓ b x} : ℕ) : ℝ) -
        (Nat.card (ZSet (ZMod d) ℓ b) : ℝ) * (M₁ * M₂ / (d : ℝ) ^ 2)| ≤
      (Nat.card (ZSet (ZMod d) ℓ b) : ℝ) * (M₁ + M₂ + 1) := by
  have : NeZero d := ⟨hd.ne'⟩
  set Z := (univ : Finset (ZMod d × ZMod d)).filter (· ∈ ZSet (ZMod d) ℓ b) with hZ
  have hcardZ : Nat.card (ZSet (ZMod d) ℓ b) = #Z := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let π : ℤ × ℤ → ZMod d × ZMod d := fun x => ((x.1 : ZMod d), (x.2 : ZMod d))
  have hmaps : ((box a₁ a₂ M₁ M₂).filter (fun x => (d : ℤ) ∣ gaussFZ ℓ b x) : Set (ℤ × ℤ)).MapsTo π Z := by
    intro x hx
    simp only [coe_filter, Set.mem_setOf_eq] at hx
    simp only [hZ, coe_filter, mem_univ, true_and, Set.mem_setOf_eq, mem_zset, π]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ d).2 hx.2
    simpa [gaussFZ] using this
  rw [card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ z ∈ Z, #{x ∈ (box a₁ a₂ M₁ M₂).filter (fun x => (d : ℤ) ∣ gaussFZ ℓ b x) | π x = z} =
      #{U ∈ Ico a₁ (a₁ + (M₁ : ℤ)) | ((U : ℤ) : ZMod d) = z.1} *
        #{V ∈ Ico a₂ (a₂ + (M₂ : ℤ)) | ((V : ℤ) : ZMod d) = z.2} := by
    intro z hz
    rw [← card_product]
    congr 1
    ext ⟨U, V⟩
    simp only [hZ, mem_filter, mem_univ, true_and, mem_zset] at hz
    simp only [box, mem_filter, mem_product, π, Prod.ext_iff]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, _⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, h2, h4⟩
    · rintro ⟨⟨h1, h3⟩, h2, h4⟩
      refine ⟨⟨⟨h1, h2⟩, ?_⟩, h3, h4⟩
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simpa [gaussFZ, h3, h4] using hz
  rw [sum_congr rfl hfib, hcardZ, Nat.cast_sum]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hterm : ∀ z ∈ Z, |(((#{U ∈ Ico a₁ (a₁ + (M₁ : ℤ)) | ((U : ℤ) : ZMod d) = z.1} *
        #{V ∈ Ico a₂ (a₂ + (M₂ : ℤ)) | ((V : ℤ) : ZMod d) = z.2} : ℕ) : ℝ)) -
        M₁ * M₂ / (d : ℝ) ^ 2| ≤ M₁ + M₂ + 1 := by
    intro z _
    rw [Nat.cast_mul, show (M₁ : ℝ) * M₂ / (d : ℝ) ^ 2 = (M₁ / d) * (M₂ / d) by ring]
    refine abs_mul_sub_mul_le (abs_card_Ico_cast_eq_sub_le a₁ M₁ d z.1)
      (abs_card_Ico_cast_eq_sub_le a₂ M₂ d z.2) (Nat.cast_nonneg _) (by positivity) ?_ ?_
    · exact div_le_self (Nat.cast_nonneg _) hd1
    · exact div_le_self (Nat.cast_nonneg _) hd1
  rw [show ((#Z : ℕ) : ℝ) * (M₁ * M₂ / (d : ℝ) ^ 2) = ∑ z ∈ Z, (M₁ * M₂ / (d : ℝ) ^ 2 : ℝ) by
    rw [sum_const, nsmul_eq_mul], ← sum_sub_distrib]
  refine le_trans (abs_sum_le_sum_abs _ _) ?_
  rw [show ((#Z : ℕ) : ℝ) * (M₁ + M₂ + 1) = ∑ z ∈ Z, ((M₁ : ℝ) + M₂ + 1) by
    rw [sum_const, nsmul_eq_mul]]
  exact sum_le_sum hterm

end

end ZInQ.Density.GaussSieve

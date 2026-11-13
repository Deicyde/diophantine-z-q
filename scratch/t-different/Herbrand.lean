import Mathlib

/-!
# t-different: Herbrand's function, abstract calculus (towards T22)

Check with `lake env lean scratch/t-different/Herbrand.lean`.
-/

open MeasureTheory Set

namespace TDifferent

/-- `∫_a^b 1_{t ≤ c} dt = min b c - min a c`. -/
theorem integral_indicator_Iic (a b c : ℝ) :
    ∫ t in a..b, (Iic c).indicator (fun _ => (1 : ℝ)) t = min b c - min a c := by
  have key : ∀ a b : ℝ, a ≤ b →
      ∫ t in a..b, (Iic c).indicator (fun _ => (1 : ℝ)) t = min b c - min a c := by
    intro a b hab
    rw [intervalIntegral.integral_of_le hab, setIntegral_indicator measurableSet_Iic,
      setIntegral_const, Ioc_inter_Iic, Real.volume_real_Ioc, smul_eq_mul, mul_one]
    rw [show b ⊓ c = min b c from rfl]
    rcases le_total c a with h | h
    · rw [min_eq_right (h.trans hab), min_eq_right h, sub_self]
      exact max_eq_right (by linarith)
    · rw [min_eq_left h]
      exact max_eq_left (by rw [sub_nonneg]; exact le_min hab h)
  rcases le_total a b with h | h
  · exact key a b h
  · rw [intervalIntegral.integral_symm, key b a h]; ring

section Abstract

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Real-indexed lower numbering of an abstract filtration (`PkgI6.lowerRamR`'s formula). -/
noncomputable def filtR (Γ : ℕ → Subgroup G) (t : ℝ) : Subgroup G :=
  if t ≤ -1 then ⊤ else Γ (⌈t⌉.toNat)

/-- Herbrand's function of an abstract filtration (`PkgI6.herbrandPhi`'s formula). -/
noncomputable def phiF (Γ : ℕ → Subgroup G) (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u, (Nat.card (filtR Γ t) : ℝ) / (Nat.card (filtR Γ 0) : ℝ)

theorem filtR_zero (Γ : ℕ → Subgroup G) : filtR Γ 0 = Γ 0 := by
  simp [filtR]

open Classical in
theorem card_eq_sum (H : Subgroup G) :
    (Nat.card H : ℝ) = ∑ s : G, if s ∈ H then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole, Nat.card_eq_fintype_card]
  congr 1
  exact_mod_cast (Fintype.card_subtype (fun s => s ∈ H))

/-- **The min-formula** (Serre, *Corps locaux*, IV §3, Lemma 1 form): if `s ∈ Γ i ↔ i < n s` for
`s ≠ 1`, then for `u ≥ -1`, `|Γ_0| (φ(u) + 1) = (u + 1) + ∑_{s ≠ 1} min(n s, u + 1)`. -/
theorem phiF_formula (Γ : ℕ → Subgroup G) (n : G → ℕ)
    (hΓ : ∀ i s, s ≠ 1 → (s ∈ Γ i ↔ i < n s)) {u : ℝ} (hu : -1 ≤ u) :
    (Nat.card (Γ 0) : ℝ) * (phiF Γ u + 1) =
      (u + 1) + ∑ s ∈ Finset.univ.erase 1, min (n s : ℝ) (u + 1) := by
  classical
  have hg0 : (0 : ℝ) < Nat.card (Γ 0) := by exact_mod_cast Nat.card_pos
  -- the integrand on `Ι 0 u`
  have hpt : ∀ t : ℝ, -1 < t → (Nat.card (filtR Γ t) : ℝ) =
      1 + ∑ s ∈ Finset.univ.erase 1, (Iic ((n s : ℝ) - 1)).indicator (fun _ => (1 : ℝ)) t := by
    intro t ht
    rw [card_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G)),
      if_pos (Subgroup.one_mem _)]
    congr 1
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs1 : s ≠ 1 := Finset.ne_of_mem_erase hs
    simp only [filtR, if_neg (not_le.mpr ht), hΓ _ s hs1, indicator, mem_Iic]
    have hc : (0 : ℤ) ≤ ⌈t⌉ := Int.ceil_nonneg_of_neg_one_lt ht
    have h1 : (⌈t⌉.toNat < n s) ↔ ⌈t⌉ ≤ (n s : ℤ) - 1 := by omega
    by_cases ha : ⌈t⌉.toNat < n s
    · have : t ≤ (n s : ℝ) - 1 := by
        have := h1.mp ha; rw [Int.ceil_le] at this; push_cast at this; exact this
      simp [ha, this]
    · have : ¬ t ≤ (n s : ℝ) - 1 := fun h => ha (h1.mpr (by rw [Int.ceil_le]; push_cast; exact h))
      simp [ha, this]
  have hint : ∀ c : ℝ, IntervalIntegrable ((Iic c).indicator (fun _ => (1 : ℝ))) volume 0 u := by
    intro c
    apply Antitone.intervalIntegrable
    intro a b hab
    by_cases hb : b ≤ c
    · simp [indicator, hab.trans hb, hb]
    · simp only [indicator, mem_Iic, hb, if_false]
      split_ifs <;> norm_num
  have hI : ∫ t in (0 : ℝ)..u, (Nat.card (filtR Γ t) : ℝ) =
      u + ∑ s ∈ Finset.univ.erase 1, (min u ((n s : ℝ) - 1) - min 0 ((n s : ℝ) - 1)) := by
    rw [intervalIntegral.integral_congr_ae (g := fun t => 1 + ∑ s ∈ Finset.univ.erase 1,
      (Iic ((n s : ℝ) - 1)).indicator (fun _ => (1 : ℝ)) t)]
    · have hsum : IntervalIntegrable (fun t => ∑ s ∈ Finset.univ.erase (1 : G),
          (Iic ((n s : ℝ) - 1)).indicator (fun _ => (1 : ℝ)) t) volume 0 u := by
        have := IntervalIntegrable.sum (Finset.univ.erase (1 : G)) (fun s _ => hint ((n s : ℝ) - 1))
        convert this using 1
        ext t; simp [Finset.sum_apply]
      rw [intervalIntegral.integral_add intervalIntegrable_const hsum,
        intervalIntegral.integral_const,
        intervalIntegral.integral_finset_sum fun s _ => hint _]
      simp only [smul_eq_mul, mul_one, sub_zero, integral_indicator_Iic]
    · refine Filter.Eventually.of_forall fun t ht => hpt t ?_
      rw [uIoc, mem_Ioc] at ht
      have : -1 ≤ min 0 u := le_min (by norm_num) hu
      linarith [ht.1]
  have hg0' : (Nat.card (Γ 0) : ℝ) =
      1 + ∑ s ∈ Finset.univ.erase 1, if 0 < n s then (1 : ℝ) else 0 := by
    rw [card_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G)),
      if_pos (Subgroup.one_mem _)]
    congr 1
    refine Finset.sum_congr rfl fun s hs => ?_
    by_cases h : 0 < n s <;> simp [h, hΓ 0 s (Finset.ne_of_mem_erase hs)]
  have hphi : phiF Γ u = (∫ t in (0 : ℝ)..u, (Nat.card (filtR Γ t) : ℝ)) / Nat.card (Γ 0) := by
    rw [phiF, intervalIntegral.integral_div, filtR_zero]
  rw [hphi, mul_add, mul_div_cancel₀ _ hg0.ne', hI, mul_one]
  rw [hg0']
  have hterm : ∀ s ∈ Finset.univ.erase (1 : G),
      (min u ((n s : ℝ) - 1) - min 0 ((n s : ℝ) - 1)) + (if 0 < n s then (1 : ℝ) else 0) =
        min (n s : ℝ) (u + 1) := by
    intro s _
    rcases Nat.eq_zero_or_pos (n s) with h0 | h0
    · simp only [h0, Nat.cast_zero, lt_irrefl, if_false, add_zero, zero_sub]
      rw [min_eq_right (by linarith), min_eq_right (by norm_num), min_eq_left (by linarith)]
      ring
    · have : (1 : ℝ) ≤ n s := by exact_mod_cast h0
      simp only [h0, if_true]
      rw [min_eq_left (show (0:ℝ) ≤ n s - 1 by linarith)]
      rcases le_total u ((n s : ℝ) - 1) with h | h
      · rw [min_eq_left h, min_eq_right (by linarith)]; ring
      · rw [min_eq_right h, min_eq_left (by linarith)]; ring
  rw [← Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  ring

end Abstract

end TDifferent

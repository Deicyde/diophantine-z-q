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

theorem phiF_ge (Γ : ℕ → Subgroup G) (n : G → ℕ)
    (hΓ : ∀ i s, s ≠ 1 → (s ∈ Γ i ↔ i < n s)) {u : ℝ} (hu : -1 ≤ u) : -1 ≤ phiF Γ u := by
  have h := phiF_formula Γ n hΓ hu
  have hg0 : (0 : ℝ) < Nat.card (Γ 0) := by exact_mod_cast Nat.card_pos
  have h2 : 0 ≤ (u + 1) + ∑ s ∈ Finset.univ.erase 1, min (n s : ℝ) (u + 1) :=
    add_nonneg (by linarith) (Finset.sum_nonneg fun s _ => le_min (Nat.cast_nonneg _) (by linarith))
  rw [← h] at h2
  by_contra hlt
  push Not at hlt
  nlinarith

theorem phiF_mono (Γ : ℕ → Subgroup G) (n : G → ℕ)
    (hΓ : ∀ i s, s ≠ 1 → (s ∈ Γ i ↔ i < n s)) {a b : ℝ} (ha : -1 ≤ a) (hab : a ≤ b) :
    phiF Γ a ≤ phiF Γ b := by
  have h1 := phiF_formula Γ n hΓ ha
  have h2 := phiF_formula Γ n hΓ (ha.trans hab)
  have hg0 : (0 : ℝ) < Nat.card (Γ 0) := by exact_mod_cast Nat.card_pos
  have h3 : (a + 1) + ∑ s ∈ Finset.univ.erase 1, min (n s : ℝ) (a + 1) ≤
      (b + 1) + ∑ s ∈ Finset.univ.erase 1, min (n s : ℝ) (b + 1) :=
    add_le_add (by linarith) (Finset.sum_le_sum fun s _ => min_le_min_left _ (by linarith))
  rw [← h1, ← h2] at h3
  have := le_of_mul_le_mul_left h3 hg0
  linarith

theorem phiF_zero (Γ : ℕ → Subgroup G) : phiF Γ 0 = 0 := by simp [phiF]

end Abstract

section Trans

variable {G H Q : Type*} [Group G] [Fintype G] [DecidableEq G] [Group H] [Fintype H]
  [DecidableEq H] [Group Q] [Fintype Q] [DecidableEq Q]

theorem fiber_sum (ι : H →* G) (hι : Function.Injective ι) (r : G →* Q)
    (hexact : ∀ s, r s = 1 ↔ ∃ h, ι h = s) (s0 : G) (f : G → ℝ) :
    ∑ s ∈ Finset.univ.filter (fun s => r s = r s0), f s = ∑ h : H, f (s0 * ι h) := by
  symm
  apply Finset.sum_nbij (fun h => s0 * ι h)
  · intro h _
    simp [Finset.mem_filter, map_mul, (hexact (ι h)).mpr ⟨h, rfl⟩]
  · intro a _ b _ e
    exact hι (mul_left_cancel e)
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hs
    obtain ⟨h, hh⟩ := (hexact (s0⁻¹ * s)).mp (by rw [map_mul, map_inv, hs, inv_mul_cancel])
    exact ⟨h, Finset.mem_coe.mpr (Finset.mem_univ _), by simp [hh]⟩
  · intro h _; rfl

/-- **Coset lemma** (Serre IV §3): if `s'` has maximal `i_G` in its coset `s'H` and `s'H ≠ H`,
then `i_G(s' h) = min(i_G(s'), i_G(h))` for `h ∈ H`, `h ≠ 1`. -/
theorem coset_min (ΓG : ℕ → Subgroup G) (nG : G → ℕ) (hG : ∀ i s, s ≠ 1 → (s ∈ ΓG i ↔ i < nG s))
    (ι : H →* G) (hι : Function.Injective ι) (r : G →* Q)
    (hexact : ∀ s, r s = 1 ↔ ∃ h, ι h = s) {s' : G} (hs' : r s' ≠ 1)
    (hmax : ∀ s, r s = r s' → nG s ≤ nG s') {h : H} (hh : h ≠ 1) :
    nG (s' * ι h) = min (nG s') (nG (ι h)) := by
  have hιh : ι h ≠ 1 := fun e => hh (hι (e.trans (map_one ι).symm))
  have hrι : r (ι h) = 1 := (hexact (ι h)).mpr ⟨h, rfl⟩
  have hrp : r (s' * ι h) = r s' := by rw [map_mul, hrι, mul_one]
  have hp1 : s' * ι h ≠ 1 := fun e => hs' (by rw [← hrp, e, map_one])
  have hs1 : s' ≠ 1 := fun e => hs' (by rw [e, map_one])
  apply le_antisymm
  · rcases lt_or_ge (nG (ι h)) (nG s') with hk | hk
    · rw [min_eq_right hk.le]
      by_contra hlt
      push Not at hlt
      have h1 : s' * ι h ∈ ΓG (nG (ι h)) := (hG _ _ hp1).mpr hlt
      have h2 : s' ∈ ΓG (nG (ι h)) := (hG _ _ hs1).mpr hk
      have h3 : ι h ∈ ΓG (nG (ι h)) := by
        have := (ΓG (nG (ι h))).mul_mem ((ΓG _).inv_mem h2) h1
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
      exact lt_irrefl _ ((hG _ _ hιh).mp h3)
    · rw [min_eq_left hk]
      exact hmax _ hrp
  · by_contra hlt
    push Not at hlt
    have h2 : s' ∈ ΓG (nG (s' * ι h)) := (hG _ _ hs1).mpr (lt_of_lt_of_le hlt (min_le_left _ _))
    have h3 : ι h ∈ ΓG (nG (s' * ι h)) := (hG _ _ hιh).mpr (lt_of_lt_of_le hlt (min_le_right _ _))
    exact lt_irrefl _ ((hG _ _ hp1).mp ((ΓG _).mul_mem h2 h3))

/-- **Transitivity of Herbrand's function, abstract form** (Serre IV §3 Prop. 15, from IV §1
Prop. 3 = `hP3`). `ι : H → G` and `r : G → Q` form an exact sequence `1 → H → G → Q → 1`,
`ΓG`, `ΓQ` are filtrations with index functions `nG`, `nQ`, and the filtration of `H` is the
induced one. -/
theorem phiF_trans (ΓG : ℕ → Subgroup G) (nG : G → ℕ) (ΓQ : ℕ → Subgroup Q) (nQ : Q → ℕ)
    (ι : H →* G) (hι : Function.Injective ι) (r : G →* Q) (hr : Function.Surjective r)
    (hexact : ∀ s, r s = 1 ↔ ∃ h, ι h = s)
    (hG : ∀ i s, s ≠ 1 → (s ∈ ΓG i ↔ i < nG s))
    (hQ : ∀ i σ, σ ≠ 1 → (σ ∈ ΓQ i ↔ i < nQ σ))
    (hP3 : ∀ σ : Q, σ ≠ 1 → (Nat.card ((ΓG 0).comap ι) : ℝ) * nQ σ =
      ∑ s ∈ Finset.univ.filter (fun s => r s = σ), (nG s : ℝ))
    {u : ℝ} (hu : -1 ≤ u) :
    phiF ΓG u = phiF ΓQ (phiF (fun i => (ΓG i).comap ι) u) := by
  classical
  set ΓH : ℕ → Subgroup H := fun i => (ΓG i).comap ι with hΓH
  set nH : H → ℕ := fun h => nG (ι h) with hnH
  have hι1 : ∀ h, ι h = 1 ↔ h = 1 :=
    fun h => ⟨fun e => hι (e.trans (map_one ι).symm), fun e => e ▸ map_one ι⟩
  have hH : ∀ i h, h ≠ 1 → (h ∈ ΓH i ↔ i < nH h) := fun i h hh => by
    simp only [ΓH, nH, Subgroup.mem_comap]
    exact hG i (ι h) (fun e => hh ((hι1 h).mp e))
  have hh0 : (0 : ℝ) < Nat.card (ΓH 0) := by exact_mod_cast Nat.card_pos
  -- the identity `|G_0| (φ_G(w)+1) = |H_0| |Q_0| (φ_Q(φ_H(w))+1)`
  have main : ∀ w : ℝ, -1 ≤ w → (Nat.card (ΓG 0) : ℝ) * (phiF ΓG w + 1) =
      (Nat.card (ΓH 0) : ℝ) * ((Nat.card (ΓQ 0) : ℝ) * (phiF ΓQ (phiF ΓH w) + 1)) := by
    intro w hw
    set v := phiF ΓH w with hv_def
    have hv : -1 ≤ v := phiF_ge ΓH nH hH hw
    rw [phiF_formula ΓG nG hG hw, phiF_formula ΓQ nQ hQ hv]
    let F : G → ℝ := fun s => if s = 1 then w + 1 else min (nG s : ℝ) (w + 1)
    let FQ : Q → ℝ := fun σ => if σ = 1 then v + 1 else min (nQ σ : ℝ) (v + 1)
    have hF : (w + 1) + ∑ s ∈ Finset.univ.erase 1, min (nG s : ℝ) (w + 1) = ∑ s, F s := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G))]
      simp only [F, if_pos rfl]
      congr 1
      exact Finset.sum_congr rfl fun s hs => by rw [if_neg (Finset.ne_of_mem_erase hs)]
    have hFQ : (v + 1) + ∑ σ ∈ Finset.univ.erase 1, min (nQ σ : ℝ) (v + 1) = ∑ σ, FQ σ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Q))]
      simp only [FQ, if_pos rfl]
      congr 1
      exact Finset.sum_congr rfl fun σ hσ => by rw [if_neg (Finset.ne_of_mem_erase hσ)]
    rw [hF, hFQ, Finset.mul_sum, ← Finset.sum_fiberwise Finset.univ r F]
    refine Finset.sum_congr rfl fun σ _ => ?_
    obtain ⟨s0, hs0⟩ := hr σ
    by_cases hσ : σ = 1
    · -- the fibre over `1` is `H`
      subst hσ
      have := fiber_sum ι hι r hexact 1 F
      rw [map_one] at this
      rw [this]
      have hHf := phiF_formula ΓH nH hH hw
      rw [← hv_def] at hHf
      simp only [FQ, if_pos rfl]
      rw [hHf, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : H))]
      simp only [one_mul, F, map_one, if_pos rfl]
      congr 1
      refine Finset.sum_congr rfl fun h hh => ?_
      have hh1 : h ≠ 1 := Finset.ne_of_mem_erase hh
      rw [if_neg (fun e => hh1 ((hι1 h).mp e))]
    · -- a coset `s'H ≠ H`, with `s'` of maximal `i_G`
      obtain ⟨s', hs'mem, hs'max⟩ := Finset.exists_max_image
        (Finset.univ.filter (fun s => r s = σ)) nG ⟨s0, by simp [hs0]⟩
      have hrs' : r s' = σ := by simpa using hs'mem
      have hmax : ∀ s, r s = r s' → nG s ≤ nG s' := fun s hs =>
        hs'max s (by simp [hs, hrs'])
      have hs'1 : r s' ≠ 1 := hrs' ▸ hσ
      set m := nG s' with hm
      have hfib : ∀ f : G → ℝ, ∑ s ∈ Finset.univ.filter (fun s => r s = σ), f s =
          ∑ h : H, f (s' * ι h) := fun f => by
        rw [← hrs']; exact fiber_sum ι hι r hexact s' f
      have hcos : ∀ h : H, h ≠ 1 → nG (s' * ι h) = min m (nH h) := fun h hh =>
        coset_min ΓG nG hG ι hι r hexact hs'1 hmax hh
      have hne1 : ∀ h : H, s' * ι h ≠ 1 := fun h e => by
        have := congrArg r e
        rw [map_mul, (hexact (ι h)).mpr ⟨h, rfl⟩, mul_one, map_one] at this
        exact hs'1 this
      -- `nQ σ = φ_H(m - 1) + 1`
      have hm1 : -1 ≤ (m : ℝ) - 1 := by have := Nat.cast_nonneg (α := ℝ) m; linarith
      have hHm := phiF_formula ΓH nH hH hm1
      have hnQ : (nQ σ : ℝ) = phiF ΓH ((m : ℝ) - 1) + 1 := by
        have hP := hP3 σ hσ
        rw [show (Nat.card ((ΓG 0).comap ι) : ℝ) = Nat.card (ΓH 0) from rfl, hfib,
          ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : H))] at hP
        simp only [map_one, mul_one] at hP
        rw [Finset.sum_congr rfl (fun h hh => by
          rw [hcos h (Finset.ne_of_mem_erase hh)])] at hP
        have : (Nat.card (ΓH 0) : ℝ) * nQ σ = (Nat.card (ΓH 0) : ℝ) * (phiF ΓH ((m : ℝ) - 1) + 1) := by
          rw [hP, hHm, sub_add_cancel]
          congr 1
          refine Finset.sum_congr rfl fun h _ => ?_
          push_cast
          exact min_comm _ _
        exact mul_left_cancel₀ hh0.ne' this
      -- the fibre sum
      set w1 := min (m : ℝ) (w + 1) - 1 with hw1
      have hw1' : -1 ≤ w1 := by
        have : 0 ≤ min (m : ℝ) (w + 1) := le_min (Nat.cast_nonneg _) (by linarith)
        linarith
      have hHw1 := phiF_formula ΓH nH hH hw1'
      rw [hfib]
      simp only [F, if_neg (hne1 _), FQ, if_neg hσ]
      have hmin : min (nQ σ : ℝ) (v + 1) = phiF ΓH w1 + 1 := by
        rw [hnQ, hv_def]
        have hmono : ∀ {a b : ℝ}, -1 ≤ a → a ≤ b → phiF ΓH a ≤ phiF ΓH b :=
          fun ha hab => phiF_mono ΓH nH hH ha hab
        have : min (phiF ΓH ((m : ℝ) - 1)) (phiF ΓH w) = phiF ΓH (min ((m : ℝ) - 1) w) := by
          rcases le_total ((m : ℝ) - 1) w with h | h
          · rw [min_eq_left h, min_eq_left (hmono hm1 h)]
          · rw [min_eq_right h, min_eq_right (hmono hw h)]
        rw [min_add_add_right, this]
        congr 2
        rw [hw1]
        rcases le_total (m : ℝ) (w + 1) with h | h
        · rw [min_eq_left h, min_eq_left (by linarith)]
        · rw [min_eq_right h, min_eq_right (by linarith)]; ring
      have hL : ∑ h : H, min (nG (s' * ι h) : ℝ) (w + 1) = min (m : ℝ) (w + 1) +
          ∑ h ∈ Finset.univ.erase 1, min (nH h : ℝ) (min (m : ℝ) (w + 1)) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : H)), map_one, mul_one]
        congr 1
        refine Finset.sum_congr rfl fun h hh => ?_
        rw [hcos h (Finset.ne_of_mem_erase hh)]
        push_cast
        rw [min_comm (m : ℝ) (nH h : ℝ), min_assoc]
      rw [hmin, hHw1, hL, show w1 + 1 = min (m : ℝ) (w + 1) by rw [hw1]; ring]
  -- conclude
  have h0 := main 0 (by norm_num)
  rw [phiF_zero, phiF_zero, phiF_zero, zero_add, mul_one, mul_one] at h0
  have hu' := main u hu
  rw [← mul_assoc, ← h0] at hu'
  have hg0 : (0 : ℝ) < Nat.card (ΓG 0) := by exact_mod_cast Nat.card_pos
  have := mul_left_cancel₀ hg0.ne' hu'
  linarith

end Trans

end TDifferent

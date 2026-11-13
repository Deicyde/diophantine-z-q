import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.Conductor.I6Base

/-! Copied from scratch/t-different/Herbrand.lean (compiled there), lines 60-1248. -/
section TDiffCopy
open IsLocalRing Polynomial MeasureTheory Set
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

section Upper

variable {G H Q : Type*} [Group G] [Fintype G] [DecidableEq G] [Group H] [Fintype H]
  [DecidableEq H] [Group Q] [Fintype Q] [DecidableEq Q]

theorem ceil_toNat_lt_iff {t : ℝ} (ht : -1 < t) (n : ℕ) : ⌈t⌉.toNat < n ↔ t ≤ (n : ℝ) - 1 := by
  have hc : (0 : ℤ) ≤ ⌈t⌉ := Int.ceil_nonneg_of_neg_one_lt ht
  have h1 : (⌈t⌉.toNat < n) ↔ ⌈t⌉ ≤ (n : ℤ) - 1 := by omega
  rw [h1, Int.ceil_le]
  push_cast
  rfl

/-- The min-formula as an explicit function. -/
noncomputable def phiExpl (Γ : ℕ → Subgroup G) (n : G → ℕ) (u : ℝ) : ℝ :=
  ((u + 1) + ∑ s ∈ Finset.univ.erase 1, min (n s : ℝ) (u + 1)) / (Nat.card (Γ 0) : ℝ) - 1

theorem phiF_eq_phiExpl (Γ : ℕ → Subgroup G) (n : G → ℕ)
    (hΓ : ∀ i s, s ≠ 1 → (s ∈ Γ i ↔ i < n s)) {u : ℝ} (hu : -1 ≤ u) :
    phiF Γ u = phiExpl Γ n u := by
  have h := phiF_formula Γ n hΓ hu
  have hg0 : (0 : ℝ) < Nat.card (Γ 0) := by exact_mod_cast Nat.card_pos
  rw [phiExpl, ← h, mul_div_cancel_left₀ _ hg0.ne', add_sub_cancel_right]

theorem phiF_strictMono (Γ : ℕ → Subgroup G) (n : G → ℕ)
    (hΓ : ∀ i s, s ≠ 1 → (s ∈ Γ i ↔ i < n s)) {a b : ℝ} (ha : -1 ≤ a) (hab : a < b) :
    phiF Γ a < phiF Γ b := by
  have h1 := phiF_formula Γ n hΓ ha
  have h2 := phiF_formula Γ n hΓ (ha.trans hab.le)
  have hg0 : (0 : ℝ) < Nat.card (Γ 0) := by exact_mod_cast Nat.card_pos
  have h3 : (a + 1) + ∑ s ∈ Finset.univ.erase 1, min (n s : ℝ) (a + 1) <
      (b + 1) + ∑ s ∈ Finset.univ.erase 1, min (n s : ℝ) (b + 1) :=
    add_lt_add_of_lt_of_le (by linarith)
      (Finset.sum_le_sum fun s _ => min_le_min_left _ (by linarith))
  rw [← h1, ← h2] at h3
  have := lt_of_mul_lt_mul_left h3 hg0.le
  linarith

theorem phiF_neg_one (Γ : ℕ → Subgroup G) (n : G → ℕ)
    (hΓ : ∀ i s, s ≠ 1 → (s ∈ Γ i ↔ i < n s)) : phiF Γ (-1) = -1 := by
  have h := phiF_formula Γ n hΓ (le_refl (-1 : ℝ))
  have hg0 : (0 : ℝ) < Nat.card (Γ 0) := by exact_mod_cast Nat.card_pos
  have hs : ∑ s ∈ Finset.univ.erase 1, min (n s : ℝ) (-1 + 1) = 0 :=
    Finset.sum_eq_zero fun s _ => by rw [neg_add_cancel, min_eq_right (Nat.cast_nonneg _)]
  rw [hs, neg_add_cancel, add_zero] at h
  have := (mul_eq_zero.mp h).resolve_left hg0.ne'
  linarith

theorem exists_phiF_eq (Γ : ℕ → Subgroup G) (n : G → ℕ)
    (hΓ : ∀ i s, s ≠ 1 → (s ∈ Γ i ↔ i < n s)) {v : ℝ} (hv : -1 ≤ v) :
    ∃ a, -1 ≤ a ∧ phiF Γ a = v := by
  have hg0 : (0 : ℝ) < Nat.card (Γ 0) := by exact_mod_cast Nat.card_pos
  set M : ℝ := (Nat.card (Γ 0) : ℝ) * (v + 1)
  have hM : -1 ≤ M := by have : 0 ≤ M := mul_nonneg hg0.le (by linarith); linarith
  have hcont : Continuous (phiExpl Γ n) := by
    unfold phiExpl
    fun_prop
  obtain ⟨a, ha, hfa⟩ := intermediate_value_Icc hM hcont.continuousOn
    (show v ∈ Icc (phiExpl Γ n (-1)) (phiExpl Γ n M) by
      constructor
      · rw [← phiF_eq_phiExpl Γ n hΓ le_rfl, phiF_neg_one Γ n hΓ]; exact hv
      · unfold phiExpl
        have hsum : 0 ≤ ∑ s ∈ Finset.univ.erase 1, min (n s : ℝ) (M + 1) :=
          Finset.sum_nonneg fun s _ => le_min (Nat.cast_nonneg _) (by linarith)
        rw [le_sub_iff_add_le, le_div_iff₀ hg0]
        nlinarith)
  exact ⟨a, ha.1, (phiF_eq_phiExpl Γ n hΓ ha.1).trans hfa⟩

theorem sInf_phiF (Γ : ℕ → Subgroup G) (n : G → ℕ)
    (hΓ : ∀ i s, s ≠ 1 → (s ∈ Γ i ↔ i < n s)) {a v : ℝ} (ha : -1 ≤ a) (hav : phiF Γ a = v) :
    sInf {u : ℝ | -1 ≤ u ∧ v ≤ phiF Γ u} = a := by
  have : {u : ℝ | -1 ≤ u ∧ v ≤ phiF Γ u} = Ici a := by
    ext u
    simp only [mem_setOf_eq, mem_Ici]
    constructor
    · rintro ⟨hu, hvu⟩
      by_contra hlt
      push Not at hlt
      have := phiF_strictMono Γ n hΓ hu hlt
      linarith
    · intro hau
      refine ⟨ha.trans hau, ?_⟩
      rw [← hav]
      exact phiF_mono Γ n hΓ ha hau
  rw [this, csInf_Ici]

theorem sInf_phiF_of_le (Γ : ℕ → Subgroup G) (n : G → ℕ)
    (hΓ : ∀ i s, s ≠ 1 → (s ∈ Γ i ↔ i < n s)) {v : ℝ} (hv : v ≤ -1) :
    sInf {u : ℝ | -1 ≤ u ∧ v ≤ phiF Γ u} = -1 := by
  have : {u : ℝ | -1 ≤ u ∧ v ≤ phiF Γ u} = Ici (-1) := by
    ext u
    simp only [mem_setOf_eq, mem_Ici]
    exact ⟨fun h => h.1, fun hu => ⟨hu, hv.trans (phiF_ge Γ n hΓ hu)⟩⟩
  rw [this, csInf_Ici]

/-- `nQ σ = φ_H(m - 1) + 1` with `m` the maximal `i_G` in the fibre (from Prop. 3). -/
theorem nQ_eq (ΓG : ℕ → Subgroup G) (nG : G → ℕ) (ΓQ : ℕ → Subgroup Q) (nQ : Q → ℕ)
    (ι : H →* G) (hι : Function.Injective ι) (r : G →* Q)
    (hexact : ∀ s, r s = 1 ↔ ∃ h, ι h = s)
    (hG : ∀ i s, s ≠ 1 → (s ∈ ΓG i ↔ i < nG s))
    (hP3 : ∀ σ : Q, σ ≠ 1 → (Nat.card ((ΓG 0).comap ι) : ℝ) * nQ σ =
      ∑ s ∈ Finset.univ.filter (fun s => r s = σ), (nG s : ℝ))
    {s' : G} (hs'1 : r s' ≠ 1) (hmax : ∀ s, r s = r s' → nG s ≤ nG s') :
    (nQ (r s') : ℝ) = phiF (fun i => (ΓG i).comap ι) ((nG s' : ℝ) - 1) + 1 := by
  classical
  set ΓH : ℕ → Subgroup H := fun i => (ΓG i).comap ι with hΓH
  set nH : H → ℕ := fun h => nG (ι h) with hnH
  have hι1 : ∀ h, ι h = 1 ↔ h = 1 :=
    fun h => ⟨fun e => hι (e.trans (map_one ι).symm), fun e => e ▸ map_one ι⟩
  have hH : ∀ i h, h ≠ 1 → (h ∈ ΓH i ↔ i < nH h) := fun i h hh => by
    simp only [ΓH, nH, Subgroup.mem_comap]
    exact hG i (ι h) (fun e => hh ((hι1 h).mp e))
  have hh0 : (0 : ℝ) < Nat.card (ΓH 0) := by exact_mod_cast Nat.card_pos
  have hcos : ∀ h : H, h ≠ 1 → nG (s' * ι h) = min (nG s') (nH h) := fun h hh =>
    coset_min ΓG nG hG ι hι r hexact hs'1 hmax hh
  have hm1 : -1 ≤ (nG s' : ℝ) - 1 := by have := Nat.cast_nonneg (α := ℝ) (nG s'); linarith
  have hHm := phiF_formula ΓH nH hH hm1
  have hP := hP3 (r s') hs'1
  rw [show (Nat.card ((ΓG 0).comap ι) : ℝ) = Nat.card (ΓH 0) from rfl,
    fiber_sum ι hι r hexact s', ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : H))] at hP
  simp only [map_one, mul_one] at hP
  rw [Finset.sum_congr rfl (fun h hh => by rw [hcos h (Finset.ne_of_mem_erase hh)])] at hP
  have : (Nat.card (ΓH 0) : ℝ) * nQ (r s') =
      (Nat.card (ΓH 0) : ℝ) * (phiF ΓH ((nG s' : ℝ) - 1) + 1) := by
    rw [hP, hHm, sub_add_cancel]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    push_cast
    exact min_comm _ _
  exact mul_left_cancel₀ hh0.ne' this

/-- **Herbrand's lemma** (Serre IV §3, Lemma 5): `G_u H/H = (G/H)_{φ_{L/K'}(u)}`. -/
theorem herbrand_lemma (ΓG : ℕ → Subgroup G) (nG : G → ℕ) (ΓQ : ℕ → Subgroup Q) (nQ : Q → ℕ)
    (ι : H →* G) (hι : Function.Injective ι) (r : G →* Q) (hr : Function.Surjective r)
    (hexact : ∀ s, r s = 1 ↔ ∃ h, ι h = s)
    (hG : ∀ i s, s ≠ 1 → (s ∈ ΓG i ↔ i < nG s))
    (hQ : ∀ i σ, σ ≠ 1 → (σ ∈ ΓQ i ↔ i < nQ σ))
    (hP3 : ∀ σ : Q, σ ≠ 1 → (Nat.card ((ΓG 0).comap ι) : ℝ) * nQ σ =
      ∑ s ∈ Finset.univ.filter (fun s => r s = σ), (nG s : ℝ))
    {u : ℝ} (hu : -1 ≤ u) :
    (filtR ΓG u).map r = filtR ΓQ (phiF (fun i => (ΓG i).comap ι) u) := by
  classical
  set ΓH : ℕ → Subgroup H := fun i => (ΓG i).comap ι with hΓH
  set nH : H → ℕ := fun h => nG (ι h) with hnH
  have hι1 : ∀ h, ι h = 1 ↔ h = 1 :=
    fun h => ⟨fun e => hι (e.trans (map_one ι).symm), fun e => e ▸ map_one ι⟩
  have hH : ∀ i h, h ≠ 1 → (h ∈ ΓH i ↔ i < nH h) := fun i h hh => by
    simp only [ΓH, nH, Subgroup.mem_comap]
    exact hG i (ι h) (fun e => hh ((hι1 h).mp e))
  rcases eq_or_lt_of_le hu with h1 | h1
  · subst h1
    rw [phiF_neg_one ΓH nH hH]
    simp only [filtR, le_refl, if_true]
    exact Subgroup.map_top_of_surjective r hr
  · have hv : -1 < phiF ΓH u := by
      have := phiF_strictMono ΓH nH hH le_rfl h1
      rwa [phiF_neg_one ΓH nH hH] at this
    have hnot : ¬ u ≤ -1 := not_le.mpr h1
    have hnotv : ¬ phiF ΓH u ≤ -1 := not_le.mpr hv
    simp only [filtR, hnot, hnotv, if_false]
    ext σ
    rw [Subgroup.mem_map]
    by_cases hσ : σ = 1
    · subst hσ
      exact ⟨fun _ => Subgroup.one_mem _, fun _ => ⟨1, Subgroup.one_mem _, map_one r⟩⟩
    obtain ⟨s0, hs0⟩ := hr σ
    obtain ⟨s', hs'mem, hs'max⟩ := Finset.exists_max_image
      (Finset.univ.filter (fun s => r s = σ)) nG ⟨s0, by simp [hs0]⟩
    have hrs' : r s' = σ := by simpa using hs'mem
    have hmax : ∀ s, r s = r s' → nG s ≤ nG s' := fun s hs =>
      hs'max s (by simp [hs, hrs'])
    have hs'1 : r s' ≠ 1 := hrs' ▸ hσ
    have hnQ := nQ_eq ΓG nG ΓQ nQ ι hι r hexact hG hP3 hs'1 hmax
    rw [hrs'] at hnQ
    rw [hQ _ σ hσ, ceil_toNat_lt_iff hv, hnQ, add_sub_cancel_right]
    have hm1 : -1 ≤ (nG s' : ℝ) - 1 := by have := Nat.cast_nonneg (α := ℝ) (nG s'); linarith
    have hiff : phiF ΓH u ≤ phiF ΓH ((nG s' : ℝ) - 1) ↔ u ≤ (nG s' : ℝ) - 1 := by
      constructor
      · intro h
        by_contra hlt
        push Not at hlt
        have := phiF_strictMono ΓH nH hH hm1 hlt
        linarith
      · intro h; exact phiF_mono ΓH nH hH hu h
    rw [hiff, ← ceil_toNat_lt_iff h1]
    constructor
    · rintro ⟨s, hs, hrs⟩
      have hs1 : s ≠ 1 := fun e => hσ (by rw [← hrs, e, map_one])
      exact lt_of_lt_of_le ((hG _ s hs1).mp hs) (hmax s (by rw [hrs, hrs']))
    · intro h
      have hs'ne : s' ≠ 1 := fun e => hs'1 (by rw [e, map_one])
      exact ⟨s', (hG _ s' hs'ne).mpr h, hrs'⟩

/-- **Herbrand's theorem, abstract form** (Serre IV §3, Prop. 14): `(G/H)^v = G^v H/H`. -/
theorem upper_map (ΓG : ℕ → Subgroup G) (nG : G → ℕ) (ΓQ : ℕ → Subgroup Q) (nQ : Q → ℕ)
    (ι : H →* G) (hι : Function.Injective ι) (r : G →* Q) (hr : Function.Surjective r)
    (hexact : ∀ s, r s = 1 ↔ ∃ h, ι h = s)
    (hG : ∀ i s, s ≠ 1 → (s ∈ ΓG i ↔ i < nG s))
    (hQ : ∀ i σ, σ ≠ 1 → (σ ∈ ΓQ i ↔ i < nQ σ))
    (hP3 : ∀ σ : Q, σ ≠ 1 → (Nat.card ((ΓG 0).comap ι) : ℝ) * nQ σ =
      ∑ s ∈ Finset.univ.filter (fun s => r s = σ), (nG s : ℝ))
    (v : ℝ) :
    filtR ΓQ (sInf {w : ℝ | -1 ≤ w ∧ v ≤ phiF ΓQ w}) =
      (filtR ΓG (sInf {u : ℝ | -1 ≤ u ∧ v ≤ phiF ΓG u})).map r := by
  classical
  set ΓH : ℕ → Subgroup H := fun i => (ΓG i).comap ι with hΓH
  set nH : H → ℕ := fun h => nG (ι h) with hnH
  have hι1 : ∀ h, ι h = 1 ↔ h = 1 :=
    fun h => ⟨fun e => hι (e.trans (map_one ι).symm), fun e => e ▸ map_one ι⟩
  have hH : ∀ i h, h ≠ 1 → (h ∈ ΓH i ↔ i < nH h) := fun i h hh => by
    simp only [ΓH, nH, Subgroup.mem_comap]
    exact hG i (ι h) (fun e => hh ((hι1 h).mp e))
  rcases le_or_gt v (-1) with hv | hv
  · rw [sInf_phiF_of_le ΓQ nQ hQ hv, sInf_phiF_of_le ΓG nG hG hv]
    simp only [filtR, le_refl, if_true]
    exact (Subgroup.map_top_of_surjective r hr).symm
  · obtain ⟨a, ha, hav⟩ := exists_phiF_eq ΓG nG hG hv.le
    have hb : -1 ≤ phiF ΓH a := phiF_ge ΓH nH hH ha
    have hbv : phiF ΓQ (phiF ΓH a) = v := by
      rw [← phiF_trans ΓG nG ΓQ nQ ι hι r hr hexact hG hQ hP3 ha]; exact hav
    rw [sInf_phiF ΓG nG hG ha hav, sInf_phiF ΓQ nQ hQ hb hbv,
      herbrand_lemma ΓG nG ΓQ nQ ι hι r hr hexact hG hQ hP3 ha]

end Upper



attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-! ### If `B = A[x]`, then `σ ∈ G_I ↔ σ x - x ∈ I`. -/

theorem mem_inertia_iff_of_adjoin {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {x : B} (hx : Algebra.adjoin A {x} = ⊤) (I : Ideal B) (σ : B ≃ₐ[A] B) :
    σ ∈ I.toAddSubgroup.inertia (B ≃ₐ[A] B) ↔ σ x - x ∈ I := by
  refine ⟨fun h => h x, fun h b => ?_⟩
  have hb : b ∈ Algebra.adjoin A {x} := hx ▸ Algebra.mem_top
  change σ b - b ∈ I
  induction hb using Algebra.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact h
  | algebraMap r => simp
  | add y z _ _ hy hz =>
      have : σ (y + z) - (y + z) = (σ y - y) + (σ z - z) := by rw [map_add]; ring
      rw [this]; exact I.add_mem hy hz
  | mul y z _ _ hy hz =>
      have : σ (y * z) - y * z = σ y * (σ z - z) + (σ y - y) * z := by rw [map_mul]; ring
      rw [this]; exact I.add_mem (I.mul_mem_left _ hz) (I.mul_mem_right _ hy)

/-! ### Valuations in a DVR. -/

section DVR

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

theorem span_eq_maximalIdeal_pow {a : B} (ha : a ≠ 0) :
    ∃ n, Ideal.span {a} = maximalIdeal B ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {a}) (by simpa using ha) hϖ
  exact ⟨n, by rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩

theorem maximalIdeal_pow_le_iff {m n : ℕ} :
    maximalIdeal B ^ m ≤ maximalIdeal B ^ n ↔ n ≤ m :=
  (Ideal.pow_right_strictAnti _ (IsDiscreteValuationRing.not_a_field B)
    (maximalIdeal.isMaximal B).ne_top).le_iff_ge

/-- An element of `𝔪 \ 𝔪²` generates `𝔪`. -/
theorem maximalIdeal_eq_span_of_mem_of_notMem {t : B} (ht : t ∈ maximalIdeal B)
    (ht2 : t ∉ maximalIdeal B ^ 2) : maximalIdeal B = Ideal.span {t} := by
  have ht0 : t ≠ 0 := by rintro rfl; exact ht2 (Ideal.zero_mem _)
  obtain ⟨n, hn⟩ := span_eq_maximalIdeal_pow ht0
  have h1 : 1 ≤ n := by
    rw [← maximalIdeal_pow_le_iff (B := B), ← hn, pow_one, Ideal.span_singleton_le_iff_mem]; exact ht
  have h2 : ¬ 2 ≤ n := by
    rw [← maximalIdeal_pow_le_iff (B := B), ← hn, Ideal.span_singleton_le_iff_mem]; exact ht2
  rw [hn, show n = 1 by omega, pow_one]

end DVR

section Monogenic

variable (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [PerfectField (ResidueField A)]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B]

/-- **Monogenicity** (Serre, *Corps locaux*, III §6, Prop. 12; here without completeness: only
Nakayama's lemma over the local ring `A` is used). -/
theorem exists_adjoin_eq_top : ∃ x : B, Algebra.adjoin A {x} = ⊤ := by
  classical
  have hinjAB : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : IsLocalHom (algebraMap A B) := Algebra.IsIntegral.isLocalHom A B
  have : Module.Finite (ResidueField A) (ResidueField B) := inferInstance
  have : Algebra.IsSeparable (ResidueField A) (ResidueField B) := inferInstance
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField A) (ResidueField B)
  have hαadj : Algebra.adjoin (ResidueField A) {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α), hα, IntermediateField.top_toSubalgebra]
  have hlift : ∀ z : ResidueField B, ∃ P : A[X], aeval α P = z := by
    intro z
    have hz : z ∈ Algebra.adjoin (ResidueField A) {α} := hαadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨p, rfl⟩ := hz
    obtain ⟨P, rfl⟩ := Polynomial.map_surjective (residue A) residue_surjective p
    exact ⟨P, by rw [← ResidueField.algebraMap_eq]; exact (aeval_map_algebraMap _ _ _).symm⟩
  have hres : ∀ (P : A[X]) (y : B), residue B (aeval y P) = aeval (residue B y) P := by
    intro P y
    have := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom A B (ResidueField B)) y P
    simpa [ResidueField.algebraMap_eq] using this.symm
  obtain ⟨g, hg⟩ := Polynomial.map_surjective (residue A) residue_surjective
    (minpoly (ResidueField A) α)
  have hgα : aeval α g = 0 := by
    rw [← minpoly.aeval (ResidueField A) α, ← hg, ← ResidueField.algebraMap_eq,
      aeval_map_algebraMap]
  have hg'α : aeval α (derivative g) ≠ 0 := by
    have := (Algebra.IsSeparable.isSeparable (ResidueField A) α).aeval_derivative_ne_zero
      (minpoly.aeval (ResidueField A) α)
    rwa [← hg, derivative_map, ← ResidueField.algebraMap_eq, aeval_map_algebraMap] at this
  obtain ⟨x, hx⟩ := residue_surjective α
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hπm : maximalIdeal B = Ideal.span {π} := hπ.maximalIdeal_eq
  have hπmem : π ∈ maximalIdeal B := hπm ▸ Ideal.mem_span_singleton_self π
  have hπ2 : π ∉ maximalIdeal B ^ 2 := by
    intro h
    have : maximalIdeal B ^ 1 ≤ maximalIdeal B ^ 2 := by
      rw [pow_one, hπm, Ideal.span_singleton_le_iff_mem, ← hπm]; exact h
    exact absurd (maximalIdeal_pow_le_iff.mp this) (by norm_num)
  -- a lift `y` of `α` with `g(y) ∈ 𝔪 \ 𝔪²`
  have key : ∃ y : B, residue B y = α ∧ aeval y g ∈ maximalIdeal B ∧
      aeval y g ∉ maximalIdeal B ^ 2 := by
    by_cases h2 : aeval x g ∈ maximalIdeal B ^ 2
    · have hy : residue B (x + π) = α := by
        rw [map_add, hx, (residue_eq_zero_iff π).mpr hπmem, add_zero]
      refine ⟨x + π, hy, (residue_eq_zero_iff _).mp (by rw [hres, hy, hgα]), ?_⟩
      intro h
      obtain ⟨k, hk⟩ := (g.map (algebraMap A B)).binomExpansion x π
      rw [eval_map_algebraMap, eval_map_algebraMap, derivative_map, eval_map_algebraMap] at hk
      have hu : IsUnit (aeval x (derivative g)) := by
        rw [← residue_ne_zero_iff_isUnit, hres, hx]; exact hg'α
      have hmem : aeval x (derivative g) * π ∈ maximalIdeal B ^ 2 := by
        have e : aeval x (derivative g) * π = aeval (x + π) g - aeval x g - k * π ^ 2 := by
          rw [hk]; ring
        rw [e]
        refine Ideal.sub_mem _ (Ideal.sub_mem _ h h2) (Ideal.mul_mem_left _ _ ?_)
        rw [hπm, Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _
      apply hπ2
      obtain ⟨u, hu⟩ := hu
      have : π = ↑u⁻¹ * (aeval x (derivative g) * π) := by
        rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
      rw [this]; exact Ideal.mul_mem_left _ _ hmem
    · exact ⟨x, hx, (residue_eq_zero_iff _).mp (by rw [hres, hx, hgα]), h2⟩
  obtain ⟨y, hy, hym, hym2⟩ := key
  set t := aeval y g
  have ht : maximalIdeal B = Ideal.span {t} := maximalIdeal_eq_span_of_mem_of_notMem hym hym2
  set C := Algebra.adjoin A {y}
  have hPC : ∀ P : A[X], aeval y P ∈ C := fun P => aeval_mem_adjoin_singleton A y
  have approx : ∀ j : ℕ, ∀ b : B, ∃ c ∈ C, b - c ∈ maximalIdeal B ^ j := by
    intro j
    induction j with
    | zero => intro b; exact ⟨0, C.zero_mem, by simp⟩
    | succ j ih =>
      intro b
      obtain ⟨P, hP⟩ := hlift (residue B b)
      have h1 : b - aeval y P ∈ maximalIdeal B := by
        rw [← residue_eq_zero_iff, map_sub, hres, hy, hP, sub_self]
      rw [ht, Ideal.mem_span_singleton'] at h1
      obtain ⟨b₁, hb₁⟩ := h1
      obtain ⟨c₁, hc₁, hbc⟩ := ih b₁
      refine ⟨aeval y P + t * c₁, C.add_mem (hPC P) (C.mul_mem (hPC g) hc₁), ?_⟩
      have e : b - (aeval y P + t * c₁) = t * (b₁ - c₁) := by
        rw [mul_sub, mul_comm t b₁, hb₁]; ring
      rw [e, pow_succ']
      exact Ideal.mul_mem_mul hym hbc
  have hmA : (maximalIdeal A).map (algebraMap A B) ≠ ⊥ := by
    rw [ne_eq, Ideal.map_eq_bot_iff_of_injective hinjAB]
    exact IsDiscreteValuationRing.not_a_field A
  obtain ⟨j, hj⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hmA hπ
  rw [← Ideal.span_singleton_pow, ← hπm] at hj
  have hle : (⊤ : Submodule A B) ≤ Subalgebra.toSubmodule C ⊔ maximalIdeal A • ⊤ := by
    intro b _
    obtain ⟨c, hc, hbc⟩ := approx j b
    rw [Ideal.smul_top_eq_map, hj]
    exact Submodule.mem_sup.mpr ⟨c, hc, b - c, hbc, by ring⟩
  have hN := Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle
  refine ⟨y, ?_⟩
  rw [eq_top_iff]
  intro b _
  exact hN Submodule.mem_top

end Monogenic



/-- `𝔪_A B = 𝔪_B ^ e` with `e` Mathlib's `Ideal.ramificationIdx`. -/
theorem map_maximalIdeal_eq_pow (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] :
    (maximalIdeal A).map (algebraMap A B) =
      maximalIdeal B ^ Ideal.ramificationIdx (maximalIdeal B) A := by
  have hinjAB : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : IsLocalHom (algebraMap A B) := Algebra.IsIntegral.isLocalHom A B
  have hmA : (maximalIdeal A).map (algebraMap A B) ≠ ⊥ := by
    rw [ne_eq, Ideal.map_eq_bot_iff_of_injective hinjAB]
    exact IsDiscreteValuationRing.not_a_field A
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨j, hj⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hmA hπ
  rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq] at hj
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal A) (maximalIdeal B)
    (IsDiscreteValuationRing.not_a_field A)]
  rw [Ideal.ramificationIdx'_spec (n := j) (by rw [hj]) (by rw [hj, maximalIdeal_pow_le_iff]; omega)]
  exact hj




section GaloisSetup

variable (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
  [IsGalois (FractionRing A) (FractionRing B)]

omit [Algebra.IsSeparable (FractionRing A) (FractionRing B)] in
theorem isGaloisGroup_algEquiv : IsGaloisGroup (B ≃ₐ[A] B) A B := by
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) :=
    .of_isLocalization A B (nonZeroDivisors A)
  exact ⟨inferInstance, inferInstance,
    Algebra.isInvariant_of_isGalois' A (FractionRing A) (FractionRing B) B⟩

omit [Algebra.IsSeparable (FractionRing A) (FractionRing B)] [IsGalois (FractionRing A) (FractionRing B)] in
theorem finite_algEquiv : Finite (B ≃ₐ[A] B) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) :=
    .of_isLocalization A B (nonZeroDivisors A)
  exact Finite.of_equiv _ (galRestrict A (FractionRing A) (FractionRing B) B).toEquiv

end GaloisSetup

section Tower

variable (A C B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing C] [IsDomain C] [IsIntegrallyClosed C] [Algebra A C] [Module.Finite A C]
  [Module.IsTorsionFree A C] [IsGalois (FractionRing A) (FractionRing C)]
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [IsGalois (FractionRing A) (FractionRing B)]
  [Algebra C B] [IsScalarTower A C B] [Module.IsTorsionFree C B]

/-- The restriction `Gal(B/A) → Gal(C/A)`. -/
noncomputable def resHom : (B ≃ₐ[A] B) →* (C ≃ₐ[A] C) :=
  haveI := finite_algEquiv A B
  haveI := finite_algEquiv A C
  haveI := isGaloisGroup_algEquiv A B
  haveI := isGaloisGroup_algEquiv A C
  IsGaloisGroup.restrictHom (B ≃ₐ[A] B) (C ≃ₐ[A] C) A C B

theorem resHom_apply (g : B ≃ₐ[A] B) (c : C) :
    algebraMap C B (resHom A C B g c) = g (algebraMap C B c) := by
  have := finite_algEquiv A B
  have := finite_algEquiv A C
  have := isGaloisGroup_algEquiv A B
  have := isGaloisGroup_algEquiv A C
  exact IsGaloisGroup.algebraMap_restrictHom_smul (B ≃ₐ[A] B) (C ≃ₐ[A] C) A C B g c

theorem resHom_surjective : Function.Surjective (resHom A C B) := by
  have := finite_algEquiv A B
  have := finite_algEquiv A C
  have := isGaloisGroup_algEquiv A B
  have := isGaloisGroup_algEquiv A C
  exact IsGaloisGroup.restrictHom_surjective (B ≃ₐ[A] B) (C ≃ₐ[A] C) A C B

theorem resHom_eq_one_iff (g : B ≃ₐ[A] B) :
    resHom A C B g = 1 ↔ ∃ h : B ≃ₐ[C] B, AlgEquiv.restrictScalarsHom A h = g := by
  have hinj : Function.Injective (algebraMap C B) := FaithfulSMul.algebraMap_injective C B
  constructor
  · intro h1
    refine ⟨AlgEquiv.ofRingEquiv (f := (g : B ≃+* B)) (fun c => ?_), ?_⟩
    · have := resHom_apply A C B g c
      rw [h1] at this
      exact this.symm
    · ext b; rfl
  · rintro ⟨h, rfl⟩
    ext c
    apply hinj
    rw [resHom_apply]
    exact h.commutes c

include A in
omit [IsGalois (FractionRing A) (FractionRing C)] [Module.Finite A C] in
/-- `B ≃ₐ[C] B` is a Galois group of `B/C`. -/
theorem isGaloisGroup_tower : IsGaloisGroup (B ≃ₐ[C] B) C B := by
  have := finite_algEquiv A B
  have := isGaloisGroup_algEquiv A B
  have hG := IsGaloisGroup.of_isScalarTower (B ≃ₐ[A] B) A B C
  refine ⟨inferInstance, inferInstance, ⟨fun b hb => ?_⟩⟩
  refine hG.isInvariant.isInvariant b (fun g => ?_)
  have hg : ∀ c : C, (g : B ≃ₐ[A] B) (algebraMap C B c) = algebraMap C B c := fun c =>
    (mem_fixingSubgroup_iff _).mp g.2 _ ⟨c, rfl⟩
  have := hb (AlgEquiv.ofRingEquiv (f := ((g : B ≃ₐ[A] B) : B ≃+* B)) hg)
  exact this

end Tower

section Product

/-- If `S = R[x]` and `|Aut_R(S)| = deg minpoly`, the minimal polynomial splits as
`∏_σ (X - σ x)`. -/
theorem minpoly_map_eq_prod {R S : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [Algebra R S] [Module.IsTorsionFree R S]
    [Fintype (S ≃ₐ[R] S)] {x : S} (hint : IsIntegral R x) (hx : Algebra.adjoin R {x} = ⊤)
    (hcard : Fintype.card (S ≃ₐ[R] S) = (minpoly R x).natDegree) :
    (minpoly R x).map (algebraMap R S) = ∏ σ : S ≃ₐ[R] S, (X - C (σ x)) := by
  classical
  have hinj : Function.Injective (fun σ : S ≃ₐ[R] S => σ x) := by
    intro σ τ h
    apply AlgEquiv.coe_toAlgHom_injective
    exact AlgHom.ext_of_adjoin_eq_top hx (fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]; exact h)
  set T : Multiset S := Finset.univ.val.map (fun σ : S ≃ₐ[R] S => σ x)
  set f := (minpoly R x).map (algebraMap R S)
  have hf0 : f ≠ 0 := ((minpoly.monic hint).map _).ne_zero
  have hTroots : T ≤ f.roots := by
    rw [Multiset.le_iff_subset (Multiset.Nodup.map hinj Finset.univ.nodup)]
    intro y hy
    obtain ⟨σ, -, rfl⟩ := Multiset.mem_map.mp hy
    rw [mem_roots hf0, IsRoot.def, eval_map_algebraMap]
    have : aeval (σ x) (minpoly R x) = σ (aeval x (minpoly R x)) :=
      (Polynomial.aeval_algHom_apply (σ : S →ₐ[R] S) x _)
    rw [this, minpoly.aeval, map_zero]
  have hfT : f = (T.map fun a => X - C a).prod := by
    refine eq_of_monic_of_dvd_of_natDegree_le (monic_multiset_prod_of_monic _ _
      fun a _ => monic_X_sub_C a) ((minpoly.monic hint).map _)
      ((Multiset.prod_X_sub_C_dvd_iff_le_roots hf0 T).mpr hTroots) ?_
    rw [natDegree_multiset_prod_X_sub_C_eq_card, (minpoly.monic hint).natDegree_map, ← hcard]
    simp [T]
  rw [hfT, Finset.prod_eq_multiset_prod, Multiset.map_map]
  rfl

end Product

section Prop3

variable (A C B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A C] [Module.Finite A C]
  [Module.IsTorsionFree A C] [IsGalois (FractionRing A) (FractionRing C)]
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [IsGalois (FractionRing A) (FractionRing B)]
  [Algebra C B] [IsScalarTower A C B] [Module.IsTorsionFree C B]

omit [IsDiscreteValuationRing C] [Module.Finite A C] [IsGalois (FractionRing A) (FractionRing C)] in
theorem adjoin_tower_eq_top {x : B} (hx : Algebra.adjoin A {x} = ⊤) :
    Algebra.adjoin C {x} = ⊤ := by
  rw [eq_top_iff]
  intro b hb0
  clear hb0
  have hb : b ∈ Algebra.adjoin A {x} := hx ▸ Algebra.mem_top
  induction hb using Algebra.adjoin_induction with
  | mem z hz => exact Algebra.subset_adjoin hz
  | algebraMap r =>
      rw [IsScalarTower.algebraMap_apply A C B]; exact Subalgebra.algebraMap_mem _ _
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

include A in
omit [Module.Finite A C] [IsGalois (FractionRing A) (FractionRing C)] in
theorem finite_tower : Finite (B ≃ₐ[C] B) := by
  have : Module.Finite C B := Module.Finite.of_restrictScalars_finite A C B
  have := isGaloisGroup_tower A C B
  exact IsGaloisGroup.finite (B ≃ₐ[C] B) C B

omit [Module.Finite A C] [IsGalois (FractionRing A) (FractionRing C)] in
theorem card_tower_eq [Fintype (B ≃ₐ[C] B)] {x : B} (hx : Algebra.adjoin A {x} = ⊤) :
    Fintype.card (B ≃ₐ[C] B) = (minpoly C x).natDegree := by
  have hxC := adjoin_tower_eq_top A C B hx
  have : Module.Finite C B := Module.Finite.of_restrictScalars_finite A C B
  have := isGaloisGroup_tower A C B
  have : Finite (B ≃ₐ[C] B) := IsGaloisGroup.finite (B ≃ₐ[C] B) C B
  rw [← Nat.card_eq_fintype_card, IsGaloisGroup.card_eq_finrank' (B ≃ₐ[C] B) C B,
    (IsAdjoinRootMonic.mkOfAdjoinEqTop' hxC).finrank]

open Classical in
/-- **Serre, *Corps locaux*, IV §1, Prop. 3, ideal form.** If `B = A[x]` and `C = A[y]`, then for
`σ ∈ Gal(C/A)`, `(σ y - y) B = (∏_{s ↦ σ} (x - s x))`. -/
theorem span_sub_eq_span_prod {x : B} (hx : Algebra.adjoin A {x} = ⊤) {y : C}
    (hy : Algebra.adjoin A {y} = ⊤) [Fintype (B ≃ₐ[A] B)] (σ : C ≃ₐ[A] C) :
    Ideal.span {algebraMap C B (σ y - y)} =
      Ideal.span {∏ s ∈ Finset.univ.filter (fun s => resHom A C B s = σ), (x - s x)} := by
  classical
  have := finite_tower A C B
  have := Fintype.ofFinite (B ≃ₐ[C] B)
  have hxC := adjoin_tower_eq_top A C B hx
  have hint : IsIntegral C x := by
    have : Module.Finite C B := Module.Finite.of_restrictScalars_finite A C B
    exact Algebra.IsIntegral.isIntegral x
  have hprod := minpoly_map_eq_prod hint hxC (card_tower_eq A C B hx)
  obtain ⟨s0, hs0⟩ := resHom_surjective A C B σ
  have hs0c : ∀ c : C, s0 (algebraMap C B c) = algebraMap C B (σ c) := fun c => by
    rw [← resHom_apply, hs0]
  set f := minpoly C x with hf_def
  -- the fibre product
  have hfib : ∏ s ∈ Finset.univ.filter (fun s => resHom A C B s = σ), (x - s x) =
      ∏ h : B ≃ₐ[C] B, (x - s0 (h x)) := by
    symm
    apply Finset.prod_nbij (fun h => s0 * AlgEquiv.restrictScalarsHom A h)
    · intro h _
      have h1 : resHom A C B (AlgEquiv.restrictScalars A h) = 1 :=
        (resHom_eq_one_iff A C B _).mpr ⟨h, rfl⟩
      simp [Finset.mem_filter, map_mul, h1, hs0]
    · intro a _ b _ e
      have := mul_left_cancel e
      exact AlgEquiv.restrictScalars_injective A this
    · intro s hs
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hs
      obtain ⟨h, hh⟩ := (resHom_eq_one_iff A C B (s0⁻¹ * s)).mp
        (by rw [map_mul, map_inv, hs, hs0, inv_mul_cancel])
      refine ⟨h, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      show s0 * AlgEquiv.restrictScalarsHom A h = s
      rw [hh, mul_inv_cancel_left]
    · intro h _; rfl
  -- `P = f^σ(x)`
  have hP : ∏ h : B ≃ₐ[C] B, (x - s0 (h x)) = aeval x (f.map (σ : C →+* C)) := by
    have hcomp : (algebraMap C B).comp (σ : C →+* C) = (s0 : B →+* B).comp (algebraMap C B) := by
      ext c; simp [hs0c]
    rw [← eval_map_algebraMap, Polynomial.map_map, hcomp, ← Polynomial.map_map, hprod,
      Polynomial.map_prod, eval_prod]
    refine Finset.prod_congr rfl fun h _ => ?_
    simp
  rw [hfib, hP]
  apply le_antisymm
  · -- `(σ y - y) ∈ (f^σ(x))`
    rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨g, hg⟩ : ∃ g : A[X], aeval x g = algebraMap C B y := by
      have : algebraMap C B y ∈ Algebra.adjoin A {x} := hx ▸ Algebra.mem_top
      rw [Algebra.adjoin_singleton_eq_range_aeval] at this
      exact this
    set gC : C[X] := g.map (algebraMap A C) - Polynomial.C y
    have hgC : aeval x gC = 0 := by
      simp only [gC, map_sub, aeval_C, aeval_map_algebraMap, hg, sub_self]
    obtain ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd hint hgC
    have hσA : (σ : C →+* C).comp (algebraMap A C) = algebraMap A C := by
      ext a; simp
    have hmap : gC.map (σ : C →+* C) = (f.map (σ : C →+* C)) * (q.map (σ : C →+* C)) := by
      rw [hq, Polynomial.map_mul]
    have hmap' : gC.map (σ : C →+* C) = g.map (algebraMap A C) - Polynomial.C (σ y) := by
      simp only [gC, Polynomial.map_sub, Polynomial.map_map, hσA, map_C]
      rfl
    have key : algebraMap C B y - algebraMap C B (σ y) =
        aeval x (f.map (σ : C →+* C)) * aeval x (q.map (σ : C →+* C)) := by
      rw [← map_mul, ← hmap, hmap', map_sub, aeval_C, aeval_map_algebraMap, hg]
    rw [Ideal.mem_span_singleton']
    exact ⟨-aeval x (q.map (σ : C →+* C)), by rw [map_sub, neg_mul, mul_comm, ← key]; ring⟩
  · -- `f^σ(x) ∈ (σ y - y)`
    rw [Ideal.span_singleton_le_iff_mem]
    have hcoef : ∀ c : C, σ c - c ∈ Ideal.span {σ y - y} := by
      intro c
      have hc : c ∈ Algebra.adjoin A {y} := hy ▸ Algebra.mem_top
      induction hc using Algebra.adjoin_induction with
      | mem z hz =>
          rw [Set.mem_singleton_iff.mp hz]; exact Ideal.mem_span_singleton_self _
      | algebraMap r => simp
      | add a b _ _ ha hb =>
          have : σ (a + b) - (a + b) = (σ a - a) + (σ b - b) := by rw [map_add]; ring
          rw [this]; exact Ideal.add_mem _ ha hb
      | mul a b _ _ ha hb =>
          have : σ (a * b) - a * b = σ a * (σ b - b) + (σ a - a) * b := by rw [map_mul]; ring
          rw [this]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hb) (Ideal.mul_mem_right _ _ ha)
    have h0 : aeval x f = 0 := minpoly.aeval C x
    have : aeval x (f.map (σ : C →+* C)) = aeval x (f.map (σ : C →+* C) - f) := by
      rw [map_sub, h0, sub_zero]
    rw [this, aeval_eq_sum_range]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ ?_
    rw [coeff_sub, coeff_map]
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (hcoef (f.coeff i))
    rw [show (σ : C →+* C) (f.coeff i) = σ (f.coeff i) from rfl, ← hd, map_mul, mul_comm]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end Prop3



section Card

variable (C B : Type) [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra C B] [Module.Finite C B]
  [Module.IsTorsionFree C B]

/-- `|H_0| = e(B/C)` (Mathlib's `Ideal.card_inertia_eq_ramificationIdxIn`). -/
theorem card_lowerRam_zero [Finite (B ≃ₐ[C] B)] [IsGaloisGroup (B ≃ₐ[C] B) C B]
    [Algebra.HasSeparableResidueFieldsAt C B (maximalIdeal C)] :
    Nat.card (PkgI6.lowerRam C B 0) = Ideal.ramificationIdx (maximalIdeal B) C := by
  have : Algebra.IsIntegral C B := Algebra.IsIntegral.of_finite C B
  have : IsLocalHom (algebraMap C B) := Algebra.IsIntegral.isLocalHom C B
  have h1 : PkgI6.lowerRam C B 0 = Ideal.inertia (B ≃ₐ[C] B) (maximalIdeal B) := by
    simp only [PkgI6.lowerRam, zero_add, pow_one]
  rw [h1, Ideal.card_inertia_eq_ramificationIdxIn (maximalIdeal C) (maximalIdeal B),
    Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal C) (maximalIdeal B) (B ≃ₐ[C] B)]

end Card

section Assembly

theorem herbrandPhi_eq_phiF (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]
    (u : ℝ) : PkgI6.herbrandPhi A B u = phiF (PkgI6.lowerRam A B) u := rfl

variable (A C B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [PerfectField (ResidueField A)]
  [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A C] [Module.Finite A C]
  [Module.IsTorsionFree A C] [IsGalois (FractionRing A) (FractionRing C)]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [IsGalois (FractionRing A) (FractionRing B)]
  [Algebra C B] [IsScalarTower A C B] [Module.Finite C B] [Module.IsTorsionFree C B]

open Classical in
/-- The data of the tower `B/C/A`: index functions `i_G`, `i_{G/H}` and Prop. 3. -/
theorem tower_data [Fintype (B ≃ₐ[A] B)] [Fintype (C ≃ₐ[A] C)] :
    ∃ (nG : (B ≃ₐ[A] B) → ℕ) (nQ : (C ≃ₐ[A] C) → ℕ),
      (∀ i s, s ≠ 1 → (s ∈ PkgI6.lowerRam A B i ↔ i < nG s)) ∧
      (∀ i σ, σ ≠ 1 → (σ ∈ PkgI6.lowerRam A C i ↔ i < nQ σ)) ∧
      (∀ σ : C ≃ₐ[A] C, σ ≠ 1 →
        (Nat.card ((PkgI6.lowerRam A B 0).comap
          (AlgEquiv.restrictScalarsHom A : (B ≃ₐ[C] B) →* (B ≃ₐ[A] B))) : ℝ) * nQ σ =
        ∑ s ∈ Finset.univ.filter (fun s => resHom A C B s = σ), (nG s : ℝ)) := by
  obtain ⟨x, hx⟩ := exists_adjoin_eq_top A B
  obtain ⟨y, hy⟩ := exists_adjoin_eq_top A C
  have := finite_tower A C B
  let := Fintype.ofFinite (B ≃ₐ[C] B)
  have hinjG : ∀ s : B ≃ₐ[A] B, s ≠ 1 → x - s x ≠ 0 := by
    intro s hs h
    apply hs
    apply AlgEquiv.coe_toAlgHom_injective
    exact AlgHom.ext_of_adjoin_eq_top hx (fun z hz => by
      rw [Set.mem_singleton_iff.mp hz]; exact (sub_eq_zero.mp h).symm)
  have hinjQ : ∀ σ : C ≃ₐ[A] C, σ ≠ 1 → σ y - y ≠ 0 := by
    intro σ hσ h
    apply hσ
    apply AlgEquiv.coe_toAlgHom_injective
    exact AlgHom.ext_of_adjoin_eq_top hy (fun z hz => by
      rw [Set.mem_singleton_iff.mp hz]; exact sub_eq_zero.mp h)
  have hnG : ∀ s : B ≃ₐ[A] B, ∃ n : ℕ, s ≠ 1 → Ideal.span {x - s x} = maximalIdeal B ^ n :=
    fun s => by
      by_cases hs : s = 1
      · exact ⟨0, fun h => (h hs).elim⟩
      · obtain ⟨n, hn⟩ := span_eq_maximalIdeal_pow (hinjG s hs); exact ⟨n, fun _ => hn⟩
  choose nG hnG using hnG
  have hnQ : ∀ σ : C ≃ₐ[A] C, ∃ n : ℕ, σ ≠ 1 → Ideal.span {σ y - y} = maximalIdeal C ^ n :=
    fun σ => by
      by_cases hσ : σ = 1
      · exact ⟨0, fun h => (h hσ).elim⟩
      · obtain ⟨n, hn⟩ := span_eq_maximalIdeal_pow (hinjQ σ hσ); exact ⟨n, fun _ => hn⟩
  choose nQ hnQ using hnQ
  have hG : ∀ i s, s ≠ 1 → (s ∈ PkgI6.lowerRam A B i ↔ i < nG s) := by
    intro i s hs
    rw [PkgI6.lowerRam, mem_inertia_iff_of_adjoin hx, ← Submodule.neg_mem_iff, neg_sub,
      ← Ideal.span_singleton_le_iff_mem, hnG s hs, maximalIdeal_pow_le_iff]
    omega
  have hQ : ∀ i σ, σ ≠ 1 → (σ ∈ PkgI6.lowerRam A C i ↔ i < nQ σ) := by
    intro i σ hσ
    rw [PkgI6.lowerRam, mem_inertia_iff_of_adjoin hy, ← Ideal.span_singleton_le_iff_mem,
      hnQ σ hσ, maximalIdeal_pow_le_iff]
    omega
  -- `e' = |H_0|`
  have : IsGaloisGroup (B ≃ₐ[C] B) C B := isGaloisGroup_tower A C B
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  have : IsLocalHom (algebraMap A C) := Algebra.IsIntegral.isLocalHom A C
  have : PerfectField (maximalIdeal A).ResidueField :=
    PerfectField.of_ringEquiv (K := ResidueField A)
      (RingEquiv.ofBijective
        (algebraMap (A ⧸ maximalIdeal A) (maximalIdeal A).ResidueField : ResidueField A →+* _)
        (maximalIdeal A).bijective_algebraMap_quotient_residueField)
  have : Algebra.HasSeparableResidueFieldsAt A B (maximalIdeal A) := inferInstance
  have : Algebra.HasSeparableResidueFieldsAt C B (maximalIdeal C) :=
    Algebra.HasSeparableResidueFieldsAt.tower_top (maximalIdeal A) (maximalIdeal C)
  have hcard := card_lowerRam_zero C B
  set e' := Ideal.ramificationIdx (maximalIdeal B) C with he'
  have hmapC : (maximalIdeal C).map (algebraMap C B) = maximalIdeal B ^ e' :=
    map_maximalIdeal_eq_pow C B
  have hP3 : ∀ σ : C ≃ₐ[A] C, σ ≠ 1 →
      (Nat.card ((PkgI6.lowerRam A B 0).comap (AlgEquiv.restrictScalarsHom A : (B ≃ₐ[C] B) →* (B ≃ₐ[A] B))) : ℝ) * nQ σ =
        ∑ s ∈ Finset.univ.filter (fun s => resHom A C B s = σ), (nG s : ℝ) := by
    intro σ hσ
    have hcomap : (PkgI6.lowerRam A B 0).comap (AlgEquiv.restrictScalarsHom A : (B ≃ₐ[C] B) →* (B ≃ₐ[A] B)) =
        PkgI6.lowerRam C B 0 := (PkgI6.lowerRam_tower A B C 0).symm
    rw [hcomap, hcard]
    have hspan := span_sub_eq_span_prod A C B hx hy σ
    have hL : Ideal.span {algebraMap C B (σ y - y)} = maximalIdeal B ^ (e' * nQ σ) := by
      rw [← Set.image_singleton, ← Ideal.map_span, hnQ σ hσ, Ideal.map_pow, hmapC, ← pow_mul]
    have hR : Ideal.span {∏ s ∈ Finset.univ.filter (fun s => resHom A C B s = σ), (x - s x)} =
        maximalIdeal B ^ (∑ s ∈ Finset.univ.filter (fun s => resHom A C B s = σ), nG s) := by
      rw [← Ideal.prod_span_singleton, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun s hs => hnG s ?_
      intro h1
      rw [Finset.mem_filter] at hs
      apply hσ
      rw [← hs.2, h1, map_one]
    have heq : e' * nQ σ = ∑ s ∈ Finset.univ.filter (fun s => resHom A C B s = σ), nG s := by
      have h := hL.symm.trans (hspan.trans hR)
      exact le_antisymm (maximalIdeal_pow_le_iff.mp h.ge) (maximalIdeal_pow_le_iff.mp h.le)
    exact_mod_cast heq
  exact ⟨nG, nQ, hG, hQ, hP3⟩

/-- **Transitivity of Herbrand's function** (Serre, *Corps locaux*, IV §3, Prop. 15). -/
theorem herbrand_trans {u : ℝ} (hu : -1 ≤ u) :
    PkgI6.herbrandPhi A B u = PkgI6.herbrandPhi A C (PkgI6.herbrandPhi C B u) := by
  classical
  have := finite_algEquiv A B
  have := finite_algEquiv A C
  let := Fintype.ofFinite (B ≃ₐ[A] B)
  let := Fintype.ofFinite (C ≃ₐ[A] C)
  obtain ⟨nG, nQ, hG, hQ, hP3⟩ := tower_data A C B
  have hι : Function.Injective (AlgEquiv.restrictScalarsHom A : (B ≃ₐ[C] B) →* (B ≃ₐ[A] B)) :=
    AlgEquiv.restrictScalars_injective A
  have := finite_tower A C B
  let := Fintype.ofFinite (B ≃ₐ[C] B)
  have key := phiF_trans (PkgI6.lowerRam A B) nG (PkgI6.lowerRam A C) nQ
    (AlgEquiv.restrictScalarsHom A : (B ≃ₐ[C] B) →* (B ≃ₐ[A] B)) hι (resHom A C B)
    (resHom_surjective A C B) (resHom_eq_one_iff A C B) hG hQ hP3 hu
  have hCB : (fun i => (PkgI6.lowerRam A B i).comap
      (AlgEquiv.restrictScalarsHom A : (B ≃ₐ[C] B) →* (B ≃ₐ[A] B))) =
      PkgI6.lowerRam C B := funext fun i => (PkgI6.lowerRam_tower A B C i).symm
  rw [hCB] at key
  exact key

/-- **Herbrand's theorem** (Serre, *Corps locaux*, IV §3, Prop. 14): `Gal(C/A)^v = r(Gal(B/A)^v)`. -/
theorem herbrand_quotient (r : (B ≃ₐ[A] B) →* (C ≃ₐ[A] C))
    (hr : ∀ σ c, algebraMap C B (r σ c) = σ (algebraMap C B c)) (v : ℝ) :
    PkgI6.upperRam A C v = (PkgI6.upperRam A B v).map r := by
  classical
  have hr_eq : r = resHom A C B := by
    refine MonoidHom.ext fun σ => AlgEquiv.ext fun c => ?_
    apply FaithfulSMul.algebraMap_injective C B
    rw [hr, resHom_apply]
  subst hr_eq
  have := finite_algEquiv A B
  have := finite_algEquiv A C
  let := Fintype.ofFinite (B ≃ₐ[A] B)
  let := Fintype.ofFinite (C ≃ₐ[A] C)
  obtain ⟨nG, nQ, hG, hQ, hP3⟩ := tower_data A C B
  have hι : Function.Injective (AlgEquiv.restrictScalarsHom A : (B ≃ₐ[C] B) →* (B ≃ₐ[A] B)) :=
    AlgEquiv.restrictScalars_injective A
  have := finite_tower A C B
  let := Fintype.ofFinite (B ≃ₐ[C] B)
  exact upper_map (PkgI6.lowerRam A B) nG (PkgI6.lowerRam A C) nQ
    (AlgEquiv.restrictScalarsHom A : (B ≃ₐ[C] B) →* (B ≃ₐ[A] B)) hι (resHom A C B)
    (resHom_surjective A C B) (resHom_eq_one_iff A C B) hG hQ hP3 v

end Assembly

end TDifferent
end TDiffCopy

namespace PkgI6
open IsLocalRing
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
/-- **T22a (`PkgI6.HerbrandQuotient`): proved** (copied from scratch/t-different/Herbrand.lean). -/
theorem herbrandQuotient : HerbrandQuotient := by
  intro A C B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r hr v
  have : Module.Finite C B := Module.Finite.of_restrictScalars_finite A C B
  exact TDifferent.herbrand_quotient A C B r hr v
end PkgI6

/-! scratch/swan/Swan.lean -/

/-!
# swan: the glue Props `SwanIndependent`, `SwanIntegral`, `AdaptedExists`

Task swan. The three Props are stated in the kernel module
`ZInQKernel/HDecomp/Conductor/LadicCond.lean` (namespace `LadicCond`) and used by
`scratch/g0-mod-newform/` (G15). §0 repeats them verbatim (checked equal by `rfl`).

* §1-§4: **`AdaptedExists` is proved** (`Swan.adaptedExists`), from Mathlib only.
* §5: `SwanIntegral` and `SwanIndependent` are reduced to three smaller named Props.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Swan

open PkgI4 LadicCond

/-! ## §0. The three Props, verbatim from `LadicCond.lean` -/

section Verbatim

variable {p : ℕ} [Fact p.Prime]

/-- Verbatim copy of `LadicCond.SwanIndependent`. -/
def SwanIndependent : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (ρ : GQp p →* GL (Fin n) k) (L L' : Fld p),
    IsAdapted L ρ → IsAdapted L' ρ → swanAt L ρ = swanAt L' ρ

/-- Verbatim copy of `LadicCond.AdaptedExists`. -/
def AdaptedExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ p → ∀ (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl ℓ)),
    Continuous ρ → ∃ L : Fld p, IsAdapted L ρ

/-- Verbatim copy of `LadicCond.SwanIntegral`. -/
def SwanIntegral : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [Fact p.Prime], p ≠ ℓ →
    ∀ (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl ℓ)), Continuous ρ →
    ∀ L : Fld p, IsAdapted L ρ →
      (swanAt L ρ : ℝ) = ∫ u in Set.Ioi (0 : ℝ), (codimInv ρ (upperAbs p u) : ℝ)

example : SwanIndependent (p := p) = LadicCond.SwanIndependent (p := p) := rfl
example : AdaptedExists (p := p) = LadicCond.AdaptedExists (p := p) := rfl
example : SwanIntegral = LadicCond.SwanIntegral := rfl

end Verbatim

/-! ## §1. Wild elements act through `p`-power order on a finite Galois level -/

section Wild

variable {p : ℕ} [Fact p.Prime]

/-- Ultrametric: `‖a − b‖ < ‖b‖ ⇒ ‖a‖ = ‖b‖`. -/
theorem norm_eq_of_norm_sub_lt {a b : Kbar p} (h : ‖a - b‖ < ‖b‖) : ‖a‖ = ‖b‖ := by
  have h1 : ‖a‖ ≤ max ‖a - b‖ ‖b‖ := by
    have := IsUltrametricDist.norm_add_le_max (a - b) b
    rwa [sub_add_cancel] at this
  have h2 : ‖b‖ ≤ max ‖b - a‖ ‖a‖ := by
    have := IsUltrametricDist.norm_add_le_max (b - a) a
    rwa [sub_add_cancel] at this
  rw [norm_sub_rev] at h2
  rcases le_total ‖a - b‖ ‖b‖ with h3 | h3
  · rw [max_eq_right h3] at h1
    rcases le_total ‖a - b‖ ‖a‖ with h4 | h4
    · rw [max_eq_right h4] at h2; linarith
    · rw [max_eq_left h4] at h2; linarith
  · linarith

theorem mul_mem_wildSet {σ τ : GQp p} (hσ : σ ∈ wildSet) (hτ : τ ∈ wildSet) :
    σ * τ ∈ wildSet := by
  intro x hx
  have hτx : ‖τ x‖ = ‖x‖ := norm_eq_of_norm_sub_lt (hτ x hx)
  have hτx0 : τ x ≠ 0 := by
    intro h; rw [h, norm_zero] at hτx; exact hx (norm_eq_zero.1 hτx.symm)
  have e : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
    rw [AlgEquiv.mul_apply]; ring
  rw [e]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ (hτ x hx))
  rw [← hτx]; exact hσ _ hτx0

theorem pow_mem_wildSet {σ : GQp p} (hσ : σ ∈ wildSet) (m : ℕ) : σ ^ m ∈ wildSet := by
  induction m with
  | zero => rw [pow_zero]; exact one_mem_wildSet
  | succ m ih => rw [pow_succ]; exact mul_mem_wildSet ih hσ

/-- On a finite Galois `L`, every `γ` has finite order: some `γ^m`, `m > 0`, fixes `L`. -/
theorem exists_pow_fix {L : Fld p} (hL : IsFinGal L) (γ : GQp p) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, (γ ^ m) x = x := by
  have hfin := (finite_restr hL (Set.univ : Set (GQp p))).to_subtype
  let f : ℕ → restr L '' (Set.univ : Set (GQp p)) := fun j => ⟨restr L (γ ^ j), γ ^ j, trivial, rfl⟩
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite f
  have he' : restr L (γ ^ i) = restr L (γ ^ j) := congrArg Subtype.val he
  -- symmetric: reduce to `i < j`
  have key : ∀ a b : ℕ, a < b → restr L (γ ^ a) = restr L (γ ^ b) →
      ∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, (γ ^ m) x = x := by
    intro a b hab hrab
    refine ⟨b - a, by omega, fun x hx => ?_⟩
    have h1 : (γ ^ b) x = (γ ^ a) x := (congrFun hrab ⟨x, hx⟩).symm
    have h2 : γ ^ b = γ ^ a * γ ^ (b - a) := by rw [← pow_add]; congr 1; omega
    rw [h2, AlgEquiv.mul_apply] at h1
    exact (γ ^ a).injective h1
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h he'
  · exact key j i h he'.symm

/-- `‖m‖ = 1` in `ℚ̄_p` for `p ∤ m`. -/
theorem norm_natCast_eq_one {m : ℕ} (hm : ¬ p ∣ m) : ‖(m : Kbar p)‖ = 1 := by
  have e : ((m : ℚ_[p]) : PadicAlgCl p) = (m : Kbar p) := map_natCast (algebraMap ℚ_[p] _) m
  rw [← e, PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm

/-- **A wild element of order prime to `p` on `L` is trivial on `L`.** The map
`T x = ∑_{j<m} δ^j x` satisfies `‖T x‖ = ‖x‖` (`T x = m x + ∑ (δ^j x − x)`, `‖m‖ = 1`), so `T` is
an injective, hence surjective, `ℚ_p`-linear endomorphism of `L`; its image is `δ`-fixed. -/
theorem wild_fix_of_coprime {L : Fld p} (hL : IsFinGal L) {δ : GQp p} (hδ : δ ∈ wildSet)
    {m : ℕ} (hm0 : 0 < m) (hpm : ¬ p ∣ m) (hfix : ∀ x ∈ L, (δ ^ m) x = x) :
    ∀ x ∈ L, δ x = x := by
  have : FiniteDimensional ℚ_[p] L := hL.1
  have hmemj : ∀ (j : ℕ) {x : Kbar p}, x ∈ L → (δ ^ j) x ∈ L := fun j x hx => apply_mem hL _ hx
  let T : L →ₗ[ℚ_[p]] L :=
    { toFun := fun x => ⟨∑ j ∈ Finset.range m, (δ ^ j) (x : Kbar p),
        L.sum_mem fun j _ => hmemj j x.2⟩
      map_add' := by
        intro x y; ext
        simp only [IntermediateField.coe_add, map_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x; ext
        simp only [IntermediateField.coe_smul, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, ← Algebra.smul_def] }
  have hT : ∀ x : L, ((T x : L) : Kbar p) = ∑ j ∈ Finset.range m, (δ ^ j) (x : Kbar p) :=
    fun _ => rfl
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have hx0' : (x : Kbar p) ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hsum : ∑ j ∈ Finset.range m, (δ ^ j) (x : Kbar p) =
        (m : Kbar p) * x + ∑ j ∈ Finset.range m, ((δ ^ j) (x : Kbar p) - x) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    have hlt : ‖∑ j ∈ Finset.range m, ((δ ^ j) (x : Kbar p) - x)‖ < ‖(x : Kbar p)‖ := by
      obtain ⟨j, -, hj⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
        (Finset.nonempty_range_iff.2 hm0.ne') (fun j => (δ ^ j) (x : Kbar p) - x)
      exact lt_of_le_of_lt hj (pow_mem_wildSet hδ j _ hx0')
    have hmx : ‖(m : Kbar p) * x‖ = ‖(x : Kbar p)‖ := by
      rw [norm_mul, norm_natCast_eq_one hpm, one_mul]
    have hTx : ‖((T x : L) : Kbar p)‖ = ‖(x : Kbar p)‖ := by
      rw [hT, hsum, ← hmx]
      apply norm_eq_of_norm_sub_lt
      rw [add_sub_cancel_left, hmx]; exact hlt
    rw [hx, IntermediateField.coe_zero, norm_zero] at hTx
    exact hx0' (norm_eq_zero.1 hTx.symm)
  have hsurj : Function.Surjective T := LinearMap.injective_iff_surjective.1 hinj
  intro y hy
  obtain ⟨x, hx⟩ := hsurj ⟨y, hy⟩
  have hy' : y = ∑ j ∈ Finset.range m, (δ ^ j) (x : Kbar p) := by
    rw [← hT, hx]
  rw [hy', map_sum]
  have hshift : ∀ j, δ ((δ ^ j) (x : Kbar p)) = (δ ^ (j + 1)) (x : Kbar p) := by
    intro j; rw [pow_succ', AlgEquiv.mul_apply]
  simp_rw [hshift]
  have h1 := Finset.sum_range_succ' (fun j => (δ ^ j) (x : Kbar p)) m
  have h2 := Finset.sum_range_succ (fun j => (δ ^ j) (x : Kbar p)) m
  rw [hfix x x.2, pow_zero, AlgEquiv.one_apply] at *
  rw [h2] at h1
  linear_combination h1.symm

/-- **Wild elements have `p`-power order on every finite Galois level** (the image of `P_p` in
`Gal(L/ℚ_p)` is a `p`-group). -/
theorem wild_pow_fix {L : Fld p} (hL : IsFinGal L) {γ : GQp p} (hγ : γ ∈ wildSet) :
    ∃ k : ℕ, ∀ x ∈ L, (γ ^ (p ^ k)) x = x := by
  obtain ⟨m, hm0, hm⟩ := exists_pow_fix hL γ
  obtain ⟨k, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' p
    (Fact.out : p.Prime).one_lt.ne'
  refine ⟨k, wild_fix_of_coprime hL (pow_mem_wildSet hγ _) (Nat.pos_of_ne_zero ?_) hm' ?_⟩
  · rintro rfl; simp at hm0
  · intro x hx; rw [← pow_mul]; exact hm x hx

end Wild

/-! ## §2. Ultrametric matrix estimate -/

section Matrix

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)

/-- All entries of `A` have norm `≤ c`. -/
def Bd (c : ℝ) (A : Mat) : Prop := ∀ i j, ‖A i j‖ ≤ c

theorem Bd.add {c : ℝ} {A B : Mat} (hA : Bd c A) (hB : Bd c B) : Bd c (A + B) := fun i j =>
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA i j) (hB i j))

theorem Bd.mul {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) {A B : Mat} (hA : Bd c A) (hB : Bd d B) :
    Bd (c * d) (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc hd) fun k _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) hc

theorem Bd.nsmul {c : ℝ} {A : Mat} (hA : Bd c A) (m : ℕ) : Bd c (m • A) := fun i j => by
  rw [Matrix.smul_apply, nsmul_eq_mul, norm_mul]
  calc ‖(m : PadicAlgCl ℓ)‖ * ‖A i j‖ ≤ 1 * ‖A i j‖ :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_natCast_le_one _ m) (norm_nonneg _)
    _ ≤ c := by rw [one_mul]; exact hA i j

theorem Bd.zero {c : ℝ} (hc : 0 ≤ c) : Bd c (0 : Mat) := fun i j => by simpa using hc

theorem Bd.one_add {A : Mat} (hA : Bd 1 A) : Bd 1 (1 + A) := by
  refine Bd.add (fun i j => ?_) hA
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

/-- `(1 + A)^m − 1 − m A` has entries `≤ a²` when `A` has entries `≤ a ≤ 1`. -/
theorem Bd.pow_sub {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {A : Mat} (hA : Bd a A) (m : ℕ) :
    Bd (a ^ 2) ((1 + A) ^ m - 1 - m • A) := by
  induction m with
  | zero => simpa using Bd.zero (sq_nonneg a)
  | succ m ih =>
    have e : (1 + A) ^ (m + 1) - 1 - (m + 1) • A =
        (1 + A) * ((1 + A) ^ m - 1 - m • A) + m • (A * A) := by
      rw [pow_succ', mul_sub, mul_sub, mul_one, mul_smul_comm, add_mul, one_mul, add_mul,
        one_mul, smul_add, add_smul, one_smul]
      abel
    rw [e]
    have hA1 : Bd 1 A := fun i j => (hA i j).trans ha1
    refine Bd.add ?_ ?_
    · simpa using Bd.mul zero_le_one (sq_nonneg a) (Bd.one_add hA1) ih
    · have h := (Bd.mul ha0 ha0 hA hA).nsmul m
      rwa [← sq] at h

end Matrix

/-! ## §3. Continuity gives a finite Galois level -/

section Topo

open scoped Topology

variable {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)

/-- The neighbourhood `{g : ‖g_{ij} − δ_{ij}‖ < r ∀ i j}` of `1` in `GL_n(ℚ̄_ℓ)`. -/
def nbhd (r : ℝ) : Set (GL (Fin n) (PadicAlgCl ℓ)) :=
  {g | ∀ i j, ‖(g : Mat) i j - (1 : Mat) i j‖ < r}

theorem isOpen_nbhd (r : ℝ) : IsOpen (nbhd (ℓ := ℓ) (n := n) r) := by
  have e : nbhd (ℓ := ℓ) (n := n) r =
      ⋂ i, ⋂ j, {g : GL (Fin n) (PadicAlgCl ℓ) | ‖(g : Mat) i j - (1 : Mat) i j‖ < r} := by
    ext g; simp [nbhd]
  rw [e]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact isOpen_lt (((Units.continuous_val.matrix_elem i j).sub continuous_const).norm)
    continuous_const

theorem one_mem_nbhd {r : ℝ} (hr : 0 < r) : (1 : GL (Fin n) (PadicAlgCl ℓ)) ∈ nbhd r := by
  intro i j; simp [hr]

/-- **Continuity gives a level.** For continuous `ρ` and `r > 0` there is a finite Galois
`L/ℚ_p` with `ρ(G_L) ⊆ nbhd r` (Krull topology, `krullTopology_mem_nhds_one_iff_of_normal`). -/
theorem exists_level (ρ : GQp p →* GL (Fin n) (PadicAlgCl ℓ)) (hρ : Continuous ρ) {r : ℝ}
    (hr : 0 < r) : ∃ L : Fld p, IsFinGal L ∧ ∀ σ ∈ fixSet L, ρ σ ∈ nbhd r := by
  have hmem : ρ ⁻¹' nbhd r ∈ 𝓝 (1 : GQp p) := by
    apply hρ.continuousAt.preimage_mem_nhds
    rw [map_one]; exact (isOpen_nbhd r).mem_nhds (one_mem_nbhd hr)
  obtain ⟨E, hEf, hEn, hE⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ_[p] (PadicAlgCl p) _).1 hmem
  refine ⟨E, ⟨hEf, isGalois_iff.2 ⟨inferInstance, hEn⟩⟩, fun σ hσ => ?_⟩
  exact hE ((IntermediateField.mem_fixingSubgroup_iff E σ).2 hσ)

end Topo

/-! ## §4. `AdaptedExists` -/

section Main

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)

/-- Ultrametric, for `ℚ̄_ℓ`: `‖a − b‖ < ‖b‖ ⇒ ‖a‖ = ‖b‖`. -/
theorem norm_eq_of_norm_sub_lt' {a b : PadicAlgCl ℓ} (h : ‖a - b‖ < ‖b‖) : ‖a‖ = ‖b‖ :=
  norm_eq_of_norm_sub_lt (p := ℓ) h

/-- **The key estimate.** If all entries of `A` have norm `≤ a = ‖A_{ij}‖`, `0 < a < 1`, and
`ℓ ∤ m`, then `‖((1 + A)^m − 1)_{ij}‖ = a`. -/
theorem norm_pow_sub_one_entry {A : Mat} {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hA : Bd a A)
    {i j : Fin n} (hij : ‖A i j‖ = a) {m : ℕ} (hm : ¬ ℓ ∣ m) :
    ‖((1 + A) ^ m - 1) i j‖ = a := by
  have hB := Bd.pow_sub ha0.le ha1.le hA m i j
  set B := (1 + A) ^ m - 1 - m • A with hBdef
  have e : ((1 + A) ^ m - 1) i j = B i j + (m : PadicAlgCl ℓ) * A i j := by
    have hs : (m • A) i j = (m : PadicAlgCl ℓ) * A i j := by
      rw [Matrix.smul_apply, nsmul_eq_mul]
    simp only [hBdef, Matrix.sub_apply, hs]; ring
  have hmA : ‖(m : PadicAlgCl ℓ) * A i j‖ = a := by
    rw [norm_mul, norm_natCast_eq_one (p := ℓ) hm, one_mul, hij]
  rw [e, ← hmA]
  apply norm_eq_of_norm_sub_lt'
  rw [add_sub_cancel_right, hmA]
  calc ‖B i j‖ ≤ a ^ 2 := hB
    _ < a := by nlinarith

/-- **`AdaptedExists` (proved).** For `ℓ ≠ p` and continuous `ρ : G_{ℚ_p} → GL_n(ℚ̄_ℓ)` there is a
finite Galois `L/ℚ_p` with `ρ` trivial on `P_p ∩ G_L`. Take `L` with `ρ(G_L) ⊆ nbhd 1`. If
`γ ∈ P_p ∩ G_L` had `ρ(γ) = 1 + A ≠ 1`, let `a = max ‖A_{ij}‖ ∈ (0, 1)`, and take `L'` with
`ρ(G_{L'}) ⊆ nbhd a`. Some `γ^{p^k}` fixes `L'` (`wild_pow_fix`), so `‖((1+A)^{p^k} − 1)_{ij}‖ < a`,
against `norm_pow_sub_one_entry` (`ℓ ∤ p^k`). -/
theorem adaptedExists {p : ℕ} [Fact p.Prime] : LadicCond.AdaptedExists (p := p) := by
  intro ℓ _ hℓp n ρ hρ
  obtain ⟨L, hL, hL1⟩ := exists_level ρ hρ one_pos
  refine ⟨L, hL, fun γ hγ => ?_⟩
  obtain ⟨hw, hf⟩ := hγ
  by_contra hne
  set A : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ) := (ρ γ : Matrix (Fin n) (Fin n) _) - 1 with hAdef
  have hρA : (ρ γ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) = 1 + A := by
    rw [hAdef]; abel
  obtain ⟨i0, j0, h0⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra hc
    push Not at hc
    apply hne
    apply Units.ext
    rw [Units.val_one, hρA]
    have : A = 0 := Matrix.ext fun i j => by simpa using hc i j
    rw [this, add_zero]
  have : Nonempty (Fin n × Fin n) := ⟨(i0, j0)⟩
  obtain ⟨⟨i1, j1⟩, hmax⟩ := Finite.exists_max (fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖)
  set a := ‖A i1 j1‖ with hadef
  have hBd : Bd a A := fun i j => hmax (i, j)
  have ha0 : 0 < a := lt_of_lt_of_le (norm_pos_iff.2 h0) (hmax (i0, j0))
  have ha1 : a < 1 := by
    have := hL1 γ hf i1 j1
    rwa [hadef, hAdef, Matrix.sub_apply]
  obtain ⟨L', hL', hL'a⟩ := exists_level ρ hρ ha0
  obtain ⟨k, hk⟩ := wild_pow_fix hL' hw
  have hlt := hL'a (γ ^ (p ^ k)) hk i1 j1
  rw [map_pow, Units.val_pow_eq_pow_val, hρA, ← Matrix.sub_apply] at hlt
  have hℓ : ¬ ℓ ∣ p ^ k := by
    intro h
    have h1 := (Fact.out : ℓ.Prime).dvd_of_dvd_pow h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).1 h1)
  rw [norm_pow_sub_one_entry ha0 ha1 hBd rfl hℓ] at hlt
  exact lt_irrefl _ hlt

end Main

/-! ## §5. `SwanIntegral` and `SwanIndependent` from three smaller Props

Both follow from: for `L` adapted to `ρ` and `u > 0`, `V^{G^u} = V^{G^u(L) ∩ P}` (the absolute
upper group acts through its image in `Gal(L/ℚ_p)`), plus the finite-level integral formula. -/

section Reduction

/-- **H1 (GLUE: finite-level change of variables; Serre, *Corps locaux* IV §3 and VI §2,
numbering UNVERIFIED).** At an adapted finite Galois level `L`, the Swan conductor
`∑_{i ≥ 1} (g_i/g_0) codim V^{G_i ∩ P}` equals `∫₀^∞ codim V^{G^u(L) ∩ P} du`: substitute
`u = φ_{L/ℚ_p}(t)`, `dφ = (g_{⌈t⌉}/g_0) dt`, `G^{φ(t)} = G_{⌈t⌉}`. A statement about one finite
extension and real step functions; no theorem of ramification theory beyond the definitions. -/
def SwanAtIntegral : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (n : ℕ) (ρ : GQp p →* GL (Fin n) k) (L : Fld p),
    IsAdapted L ρ →
      (swanAt L ρ : ℝ) = ∫ u in Set.Ioi (0 : ℝ), (codimInv ρ (upperSet L u ∩ wildSet) : ℝ)

/-- **H2 (GLUE from the definitions; Serre, *Corps locaux* IV §1-§3).** For `u > 0` the absolute
upper ramification group lies in wild inertia: `G^u ⊆ P_p`. (For `x ≠ 0` take a finite Galois `L ∋ x`;
`ψ_L(u) > 0`, so `σ ∈ G_1(L)`, and `G_1(L)` acts by `σx/x ≡ 1` mod the maximal ideal.) -/
def UpperAbsWild : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (u : ℝ), 0 < u → upperAbs p u ⊆ wildSet

/-- **H3 (GLUE from Herbrand's theorem plus compactness; Serre, *Corps locaux* IV §3, Prop. 14 and
the remark defining `G^v` for infinite Galois extensions, numbering UNVERIFIED).** The projection
`G^u → G^u(L/ℚ_p)` is onto: every `σ` in `G^u(L) ∩ P` (preimage in `G_{ℚ_p}`) agrees on `L` with
an element of the absolute `G^u`. -/
def UpperAbsSurj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : Fld p), IsFinGal L → ∀ u : ℝ, 0 < u →
    ∀ σ ∈ upperSet L u ∩ wildSet, ∃ τ ∈ upperAbs p u, ∀ x ∈ L, τ x = σ x

variable {p : ℕ} [Fact p.Prime]

theorem inv_mem_wildSet {σ : GQp p} (hσ : σ ∈ wildSet) : σ⁻¹ ∈ wildSet := by
  intro x hx
  have hy : σ (σ⁻¹ x) = x := σ.apply_symm_apply x
  have hy0 : σ⁻¹ x ≠ 0 := fun h => hx (by rw [← hy, h, map_zero])
  have h1 := hσ _ hy0
  rw [hy] at h1
  have h2 : ‖x‖ = ‖σ⁻¹ x‖ := norm_eq_of_norm_sub_lt h1
  rw [h2, norm_sub_rev]
  exact h1

/-- **The absolute upper group acts through `L`.** For `L` adapted to `ρ` and `u > 0`,
`V^{G^u} = V^{G^u(L) ∩ P}`. -/
theorem invariants_upperAbs (h2 : UpperAbsWild) (h3 : UpperAbsSurj) {k : Type} [Field k] {n : ℕ}
    {ρ : GQp p →* GL (Fin n) k} {L : Fld p} (hL : IsAdapted L ρ) {u : ℝ} (hu : 0 < u) :
    invariants ρ (upperAbs p u) = invariants ρ (upperSet L u ∩ wildSet) := by
  apply le_antisymm
  · intro v hv σ hσ
    obtain ⟨τ, hτ, hτσ⟩ := h3 p L hL.1 u hu σ hσ
    have hτw : τ ∈ wildSet := h2 p u hu hτ
    have h1 : τ⁻¹ * σ ∈ wildSet ∩ fixSet L := by
      refine ⟨mul_mem_wildSet (inv_mem_wildSet hτw) hσ.2, fun x hx => ?_⟩
      rw [AlgEquiv.mul_apply, ← hτσ x hx]
      exact τ.symm_apply_apply x
    have h2' : ρ σ = ρ τ * ρ (τ⁻¹ * σ) := by rw [← map_mul, mul_inv_cancel_left]
    rw [h2', hL.2 _ h1, mul_one]
    exact hv τ hτ
  · intro v hv σ hσ
    exact hv σ ⟨hσ L hL.1, h2 p u hu hσ⟩

/-- At any adapted level, `Sw_L(ρ) = ∫₀^∞ codim V^{G^u} du` (absolute upper filtration). -/
theorem swanAt_eq_integral_upperAbs (h1 : SwanAtIntegral) (h2 : UpperAbsWild)
    (h3 : UpperAbsSurj) {k : Type} [Field k] {n : ℕ} {ρ : GQp p →* GL (Fin n) k} {L : Fld p}
    (hL : IsAdapted L ρ) :
    (swanAt L ρ : ℝ) = ∫ u in Set.Ioi (0 : ℝ), (codimInv ρ (upperAbs p u) : ℝ) := by
  rw [h1 p k n ρ L hL]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  rw [codimInv, codimInv, invariants_upperAbs h2 h3 hL hu]

/-- **`SwanIntegral` (L8) from H1-H3.** (Continuity and `p ≠ ℓ` are not used.) -/
theorem swanIntegral_of (h1 : SwanAtIntegral) (h2 : UpperAbsWild) (h3 : UpperAbsSurj) :
    LadicCond.SwanIntegral := by
  intro ℓ _ p _ _ n ρ _ L hL
  exact swanAt_eq_integral_upperAbs h1 h2 h3 hL

/-- **`SwanIndependent` from H1-H3**, for every field `k` and every homomorphism `ρ`: both levels
compute the same integral over the absolute upper filtration. -/
theorem swanIndependent_of (h1 : SwanAtIntegral) (h2 : UpperAbsWild) (h3 : UpperAbsSurj) :
    LadicCond.SwanIndependent (p := p) := by
  intro k _ n ρ L L' hL hL'
  have e := (swanAt_eq_integral_upperAbs h1 h2 h3 hL).trans
    (swanAt_eq_integral_upperAbs h1 h2 h3 hL').symm
  exact_mod_cast e

/-- **All three glue Props of G15** from H1-H3 (`AdaptedExists` needs nothing). -/
theorem swan_all (h1 : SwanAtIntegral) (h2 : UpperAbsWild) (h3 : UpperAbsSurj) :
    (∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)) ∧ LadicCond.SwanIntegral ∧
      (∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p)) :=
  ⟨fun _ _ => swanIndependent_of h1 h2 h3, swanIntegral_of h1 h2 h3, fun _ _ => adaptedExists⟩

end Reduction

/-! ## §6. H3 from Herbrand's theorem and the compactness of `G_{ℚ_p}` -/

section Herbrand

open scoped Topology

/-- **Leaf H3a: Herbrand's theorem** (Serre, *Corps locaux* IV §3, Prop. 14, numbering UNVERIFIED;
the same theorem as pkg-I6's leaf I6.8 `PkgI6.HerbrandQuotient`, here over the finite Galois
subfields of `ℚ̄_p` and the upper numbering `LadicCond.upperSet`). For `L ⊆ M` finite Galois over
`ℚ_p` and every `v`, the image of `G^v(M/ℚ_p)` in `Gal(L/ℚ_p)` is `G^v(L/ℚ_p)`:
`(G/H)^v = G^v H/H`. Preimages in `G_{ℚ_p}` restricted to `L`. Stated only for `v > 0`, the
range the proof uses (Serre's statement covers every `v ≥ −1`). -/
def HerbrandUpper : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L M : Fld p), IsFinGal L → IsFinGal M → L ≤ M → ∀ v : ℝ, 0 < v →
    restr L '' upperSet M v = restr L '' upperSet L v

variable {p : ℕ} [Fact p.Prime]

/-- Membership in `ramSet L i` depends only on the restriction to `L`. -/
theorem mem_ramSet_of_restr {L : Fld p} {σ τ : GQp p} (h : ∀ x ∈ L, τ x = σ x) {i : ℕ}
    (hσ : σ ∈ ramSet L i) : τ ∈ ramSet L i := by
  obtain ⟨ϖ, hϖ, hb⟩ := hσ
  exact ⟨ϖ, hϖ, fun x hx hx1 => by rw [h x hx]; exact hb x hx hx1⟩

/-- Membership in `upperSet L v` depends only on the restriction to `L`. -/
theorem mem_upperSet_of_restr {L : Fld p} {σ τ : GQp p} (h : ∀ x ∈ L, τ x = σ x) {v : ℝ}
    (hσ : σ ∈ upperSet L v) : τ ∈ upperSet L v := by
  unfold upperSet ramSetR at *
  split_ifs at * with h1
  · trivial
  · exact mem_ramSet_of_restr h hσ

theorem restr_eq_iff {L : Fld p} {σ τ : GQp p} : restr L τ = restr L σ ↔ ∀ x ∈ L, τ x = σ x :=
  ⟨fun h x hx => congrFun h ⟨x, hx⟩, fun h => funext fun x => h x x.2⟩

/-- A finite Galois `E` containing `L` and every member of a finite family of finite Galois
fields. -/
theorem exists_finGal_above {L : Fld p} (hL : IsFinGal L)
    (u : Finset {M : Fld p // IsFinGal M}) :
    ∃ E : Fld p, IsFinGal E ∧ L ≤ E ∧ ∀ i ∈ u, i.1 ≤ E := by
  classical
  induction u using Finset.induction_on with
  | empty => exact ⟨L, hL, le_rfl, fun _ h => absurd h (Finset.notMem_empty _)⟩
  | @insert i u _ ih =>
    obtain ⟨E, ⟨hEf, hEg⟩, hLE, hu⟩ := ih
    have : FiniteDimensional ℚ_[p] E := hEf
    have : IsGalois ℚ_[p] E := hEg
    have : FiniteDimensional ℚ_[p] i.1 := i.2.1
    have : IsGalois ℚ_[p] i.1 := i.2.2
    refine ⟨E ⊔ i.1, ⟨IntermediateField.finiteDimensional_sup _ _, inferInstance⟩,
      hLE.trans le_sup_left, fun j hj => ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact le_sup_right
    · exact (hu j hj).trans le_sup_left

/-- A set of `τ` determined by `τ|_E` for a finite `E` is closed. -/
theorem isClosed_of_restr {E : Fld p} (hE : FiniteDimensional ℚ_[p] E) {S : Set (GQp p)}
    (hS : ∀ σ τ, (∀ x ∈ E, τ x = σ x) → σ ∈ S → τ ∈ S) : IsClosed S := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro τ hτ
  have hU : (E.fixingSubgroup : Set (GQp p)) ∈ 𝓝 (1 : GQp p) :=
    (krullTopology_mem_nhds_one_iff ℚ_[p] (PadicAlgCl p) _).2 ⟨E, hE, subset_rfl⟩
  have hf : ContinuousAt (fun g : GQp p => τ⁻¹ * g) τ :=
    (continuous_const.mul continuous_id).continuousAt
  have hmem : (fun g : GQp p => τ⁻¹ * g) ⁻¹' (E.fixingSubgroup : Set (GQp p)) ∈ 𝓝 τ := by
    apply hf.preimage_mem_nhds
    simp only [inv_mul_cancel]; exact hU
  refine Filter.mem_of_superset hmem fun g hg hgS => hτ (hS g τ (fun x hx => ?_) hgS)
  have h1 : (τ⁻¹ * g) x = x := (IntermediateField.mem_fixingSubgroup_iff E _).1 hg x hx
  rw [AlgEquiv.mul_apply] at h1
  calc τ x = τ ((τ⁻¹) (g x)) := by rw [h1]
    _ = g x := τ.apply_symm_apply (g x)

/-- **H3 from Herbrand's theorem (GLUE, proved).** If `σ ∈ G^u(L)` (preimage), then some `τ` in
the absolute `G^u` agrees with `σ` on `L`: the closed sets
`C_M = {τ : τ|_L = σ|_L, τ ∈ G^u(M)}` have the finite intersection property (Herbrand, at a finite
Galois `E` containing `L` and the `M`s), and `G_{ℚ_p}` is compact (Mathlib). -/
theorem upperAbsSurj_of_herbrand (hH : HerbrandUpper) : UpperAbsSurj := by
  intro p _ L hL u hu σ hσ
  let ι := {M : Fld p // IsFinGal M}
  let t : ι → Set (GQp p) := fun M => {τ | (∀ x ∈ L, τ x = σ x) ∧ τ ∈ upperSet M.1 u}
  have htc : ∀ M, IsClosed (t M) := by
    intro M
    have : FiniteDimensional ℚ_[p] L := hL.1
    have : FiniteDimensional ℚ_[p] M.1 := M.2.1
    refine isClosed_of_restr (E := L ⊔ M.1) (IntermediateField.finiteDimensional_sup _ _) ?_
    intro a b hab ⟨ha1, ha2⟩
    refine ⟨fun x hx => (hab x (le_sup_left (a := L) hx)).trans (ha1 x hx), ?_⟩
    exact mem_upperSet_of_restr (fun x hx => hab x (le_sup_right (b := M.1) hx)) ha2
  have hst : ∀ s : Finset ι, ((Set.univ : Set (GQp p)) ∩ ⋂ i ∈ s, t i).Nonempty := by
    intro s
    obtain ⟨E, hE, hLE, hsE⟩ := exists_finGal_above hL s
    have h1 : restr L σ ∈ restr L '' upperSet E u := by
      rw [hH p L E hL hE hLE u hu]; exact ⟨σ, hσ.1, rfl⟩
    obtain ⟨τ, hτE, hτσ⟩ := h1
    refine ⟨τ, trivial, Set.mem_iInter₂.2 fun M hM => ⟨restr_eq_iff.1 hτσ, ?_⟩⟩
    have h2 : restr M.1 τ ∈ restr M.1 '' upperSet M.1 u := by
      rw [← hH p M.1 E M.2 hE (hsE M hM) u hu]; exact ⟨τ, hτE, rfl⟩
    obtain ⟨τ', hτ', he⟩ := h2
    exact mem_upperSet_of_restr (restr_eq_iff.1 he.symm) hτ'
  obtain ⟨τ, -, hτ⟩ := isCompact_univ.inter_iInter_nonempty t htc hst
  rw [Set.mem_iInter] at hτ
  refine ⟨τ, fun M hM => (hτ ⟨M, hM⟩).2, ?_⟩
  obtain ⟨M0, hM0⟩ : ∃ M : ι, True := ⟨⟨L, hL⟩, trivial⟩
  exact (hτ M0).1

/-- **`SwanIntegral` and `SwanIndependent` from H1, H2 and Herbrand's theorem.** -/
theorem swan_all' (h1 : SwanAtIntegral) (h2 : UpperAbsWild) (hH : HerbrandUpper) :
    (∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)) ∧ LadicCond.SwanIntegral ∧
      (∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p)) :=
  swan_all h1 h2 (upperAbsSurj_of_herbrand hH)

end Herbrand

/-! ## §7. H2 (`UpperAbsWild`) from the definitions -/

section Wild2

variable {p : ℕ} [Fact p.Prime]

/-- `z ≠ 0` and `‖σz − z‖ < ‖z‖`. -/
def WildAt (σ : GQp p) (z : Kbar p) : Prop := z ≠ 0 ∧ ‖σ z - z‖ < ‖z‖

theorem WildAt.norm_eq {σ : GQp p} {z : Kbar p} (h : WildAt σ z) : ‖σ z‖ = ‖z‖ :=
  norm_eq_of_norm_sub_lt h.2

theorem WildAt.mul {σ : GQp p} {a b : Kbar p} (ha : WildAt σ a) (hb : WildAt σ b) :
    WildAt σ (a * b) := by
  refine ⟨mul_ne_zero ha.1 hb.1, ?_⟩
  have e : σ (a * b) - a * b = σ a * (σ b - b) + (σ a - a) * b := by rw [map_mul]; ring
  rw [e]
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha.1
  have hb0 : 0 < ‖b‖ := norm_pos_iff.2 hb.1
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul, norm_mul, ha.norm_eq]; exact mul_lt_mul_of_pos_left hb.2 ha0
  · rw [norm_mul, norm_mul]; exact mul_lt_mul_of_pos_right ha.2 hb0

theorem WildAt.inv {σ : GQp p} {a : Kbar p} (ha : WildAt σ a) : WildAt σ a⁻¹ := by
  refine ⟨inv_ne_zero ha.1, ?_⟩
  have hσa : σ a ≠ 0 := fun h => ha.1 (by simpa using congrArg σ.symm h)
  have e : σ a⁻¹ - a⁻¹ = (a - σ a) * (σ a)⁻¹ * a⁻¹ := by
    have h1 : a * a⁻¹ = 1 := mul_inv_cancel₀ ha.1
    have h2 : σ a * (σ a)⁻¹ = 1 := mul_inv_cancel₀ hσa
    rw [map_inv₀]; linear_combination -(σ a)⁻¹ * h1 + a⁻¹ * h2
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha.1
  rw [e, norm_mul, norm_mul, norm_inv, norm_inv, ha.norm_eq, norm_sub_rev]
  calc ‖σ a - a‖ * ‖a‖⁻¹ * ‖a‖⁻¹ < ‖a‖ * ‖a‖⁻¹ * ‖a‖⁻¹ := by
        have : 0 < ‖a‖⁻¹ := inv_pos.2 ha0
        exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right ha.2 this) this
    _ = ‖a‖⁻¹ := by field_simp

theorem wildAt_one (σ : GQp p) : WildAt σ 1 := ⟨one_ne_zero, by simp⟩

theorem WildAt.zpow {σ : GQp p} {a : Kbar p} (ha : WildAt σ a) (n : ℤ) : WildAt σ (a ^ n) := by
  have hn : ∀ m : ℕ, WildAt σ (a ^ m) := by
    intro m
    induction m with
    | zero => simpa using wildAt_one σ
    | succ m ih => rw [pow_succ]; exact ih.mul ha
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]; exact hn m
  · rw [zpow_neg, zpow_natCast]; exact (hn m).inv

/-- **`G_1(L)` acts wildly on `L`.** If `σ ∈ ramSet L 1` then `‖σx − x‖ < ‖x‖` for every
`x ∈ L`, `x ≠ 0`: write `x = y ϖ^a` with `‖y‖ = 1` (discreteness of `‖L^×‖`, from `IsUnif`); then
`‖σy − y‖ ≤ ‖ϖ‖² < 1` and `‖σϖ − ϖ‖ ≤ ‖ϖ‖² < ‖ϖ‖`, and `WildAt` is multiplicative. -/
theorem wildAt_of_ramSet_one {L : Fld p} {σ : GQp p} (hσ : σ ∈ ramSet L 1) {x : Kbar p}
    (hx : x ∈ L) (hx0 : x ≠ 0) : WildAt σ x := by
  obtain ⟨ϖ, hϖ, hb⟩ := hσ
  set r := ‖ϖ‖ with hrdef
  have hr1 : r < 1 := hϖ.2.1
  have hpL : (p : Kbar p) ∈ L := by
    rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  have hr0 : 0 < r := by
    have h1 := hϖ.2.2 (p : Kbar p) hpL isUnif_bot.2.1
    have h2 : 0 < ‖(p : Kbar p)‖ := by
      rw [norm_p_kbar]; exact inv_pos.2 (Nat.cast_pos.2 (Fact.out : p.Prime).pos)
    exact lt_of_lt_of_le h2 h1
  have hϖ0 : ϖ ≠ 0 := norm_pos_iff.1 hr0
  have hr2 : r ^ (1 + 1) < r :=
    calc r ^ (1 + 1) = r * r := by ring
      _ < r * 1 := mul_lt_mul_of_pos_left hr1 hr0
      _ = r := mul_one r
  have hwϖ : WildAt σ ϖ := ⟨hϖ0, lt_of_le_of_lt (hb ϖ hϖ.1 hr1.le) hr2⟩
  have hx0' : 0 < ‖x‖ := norm_pos_iff.2 hx0
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hx0' (one_lt_inv₀ hr0 |>.2 hr1)
  set y := x * ϖ ^ (n + 1) with hydef
  have hyL : y ∈ L := L.mul_mem hx (zpow_mem hϖ.1 _)
  have hy : ‖y‖ = ‖x‖ * r ^ (n + 1) := by rw [hydef, norm_mul, norm_zpow]
  have hrn : r ^ (n + 1) = r ^ n * r := by rw [zpow_add_one₀ hr0.ne']
  have hrinv : ∀ m : ℤ, r⁻¹ ^ m * r ^ m = 1 := by
    intro m; rw [← mul_zpow, inv_mul_cancel₀ hr0.ne', one_zpow]
  have hrpos : 0 < r ^ (n + 1) := zpow_pos hr0 _
  have hyle : ‖y‖ ≤ 1 := by
    rw [hy, ← hrinv (n + 1)]
    exact mul_le_mul_of_nonneg_right hn2 hrpos.le
  have hygt : r < ‖y‖ := by
    rw [hy]
    calc r = r⁻¹ ^ n * r ^ (n + 1) := by rw [hrn, ← mul_assoc, hrinv n, one_mul]
      _ < ‖x‖ * r ^ (n + 1) := mul_lt_mul_of_pos_right hn1 hrpos
  have hy1 : ‖y‖ = 1 := by
    rcases hyle.lt_or_eq with h | h
    · exact absurd (hϖ.2.2 y hyL h) (not_le.2 hygt)
    · exact h
  have hy0 : y ≠ 0 := by intro h; rw [h, norm_zero] at hy1; exact zero_ne_one hy1
  have hwy : WildAt σ y := ⟨hy0, by
    rw [hy1]; exact lt_of_le_of_lt (hb y hyL hyle) (hr2.trans hr1)⟩
  have hxe : x = y * ϖ ^ (-(n + 1)) := by
    rw [hydef, mul_assoc, ← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero, mul_one]
  rw [hxe]
  exact hwy.mul (hwϖ.zpow _)

/-! ### `ψ_L(u) > 0` for `u > 0`, so `G^u(L) ⊆ G_1(L)` -/

theorem ramSet_anti {L : Fld p} {i j : ℕ} (h : i ≤ j) : ramSet L j ⊆ ramSet L i := by
  rintro σ ⟨ϖ, hϖ, hb⟩
  exact ⟨ϖ, hϖ, fun x hx h1 => (hb x hx h1).trans
    (pow_le_pow_of_le_one (norm_nonneg _) hϖ.2.1.le (by omega))⟩

theorem ramSetR_anti {L : Fld p} {t t' : ℝ} (h : t ≤ t') : ramSetR L t' ⊆ ramSetR L t := by
  unfold ramSetR
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (h.trans h1) h2
  · exact Set.subset_univ _
  · exact ramSet_anti (Int.toNat_le_toNat (Int.ceil_mono h))

theorem one_mem_ramSetR {L : Fld p} (hL : IsFinGal L) (t : ℝ) : (1 : GQp p) ∈ ramSetR L t := by
  unfold ramSetR
  split_ifs
  · trivial
  · obtain ⟨ϖ, hϖ⟩ := exists_isUnif hL.1
    exact fixSet_subset_ramSet hϖ _ (fun x _ => rfl)

theorem one_le_ramCardR {L : Fld p} (hL : IsFinGal L) (t : ℝ) : 1 ≤ ramCardR L t := by
  have hfin := (finite_restr hL (ramSetR L t)).to_subtype
  have hne : Nonempty (restr L '' ramSetR L t) := ⟨⟨restr L 1, 1, one_mem_ramSetR hL t, rfl⟩⟩
  exact Nat.one_le_iff_ne_zero.2 (Nat.card_ne_zero.2 ⟨hne, hfin⟩)

theorem ramCardR_le {L : Fld p} (hL : IsFinGal L) (t : ℝ) :
    ramCardR L t ≤ Nat.card (restr L '' (Set.univ : Set (GQp p))) :=
  Nat.card_mono (finite_restr hL _) (Set.image_mono (Set.subset_univ _))

theorem ramCardR_anti {L : Fld p} (hL : IsFinGal L) :
    Antitone (fun t => (ramCardR L t : ℝ) / (ramCard L 0 : ℝ)) := by
  intro t t' h
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast Nat.card_mono (finite_restr hL _) (Set.image_mono (ramSetR_anti h))

theorem phiAt_nonpos {L : Fld p} {t : ℝ} (ht : t ≤ 0) : phiAt L t ≤ 0 := by
  rw [phiAt, intervalIntegral.integral_symm, neg_nonpos]
  exact intervalIntegral.integral_nonneg ht fun x _ => by positivity

theorem phiAt_ge {L : Fld p} (hL : IsFinGal L) {t : ℝ} (ht : 0 ≤ t) :
    t / (ramCard L 0 : ℝ) ≤ phiAt L t := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) ht
    (f := fun _ => 1 / (ramCard L 0 : ℝ))
    (g := fun t => (ramCardR L t : ℝ) / (ramCard L 0 : ℝ))
    intervalIntegrable_const (ramCardR_anti hL).intervalIntegrable
    (fun x _ => div_le_div_of_nonneg_right (by exact_mod_cast one_le_ramCardR hL x)
      (Nat.cast_nonneg _))
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one_div] at h
  exact h

theorem phiAt_le {L : Fld p} (hL : IsFinGal L) {t : ℝ} (ht : 0 ≤ t) :
    phiAt L t ≤ t * ((Nat.card (restr L '' (Set.univ : Set (GQp p))) : ℝ) / (ramCard L 0 : ℝ)) := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) ht
    (g := fun _ => (Nat.card (restr L '' (Set.univ : Set (GQp p))) : ℝ) / (ramCard L 0 : ℝ))
    (f := fun t => (ramCardR L t : ℝ) / (ramCard L 0 : ℝ))
    (ramCardR_anti hL).intervalIntegrable intervalIntegrable_const
    (fun x _ => div_le_div_of_nonneg_right (by exact_mod_cast ramCardR_le hL x)
      (Nat.cast_nonneg _))
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h
  exact h

/-- **`G^u(L) ⊆ G_1(L)` for `u > 0`** (preimages in `G_{ℚ_p}`): `ψ_L(u) > 0`, from
`t/g_0 ≤ φ_L(t) ≤ t·|Gal(L/ℚ_p)|/g_0` for `t ≥ 0` and `φ_L ≤ 0` on `[−1, 0]`. -/
theorem upperSet_subset_ramSet_one {L : Fld p} (hL : IsFinGal L) {u : ℝ} (hu : 0 < u) :
    upperSet L u ⊆ ramSet L 1 := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hL.1
  set g0 : ℝ := (ramCard L 0 : ℝ) with hg0
  have hg0pos : 0 < g0 := by
    rw [hg0]; exact_mod_cast Nat.pos_of_ne_zero (ramCard_ne_zero hL hϖ 0)
  set C : ℝ := (Nat.card (restr L '' (Set.univ : Set (GQp p))) : ℝ) with hC
  have hC1 : 1 ≤ C := by
    rw [hC]; exact_mod_cast (one_le_ramCardR hL 0).trans (ramCardR_le hL 0)
  have hCg : 0 < C / g0 := div_pos (by linarith) hg0pos
  set S := {t : ℝ | -1 ≤ t ∧ u ≤ phiAt L t} with hS
  have hne : S.Nonempty := by
    refine ⟨u * g0, by nlinarith, ?_⟩
    have := phiAt_ge hL (t := u * g0) (by positivity)
    rwa [mul_div_assoc, div_self hg0pos.ne', mul_one] at this
  have hlb : ∀ t ∈ S, u / (C / g0) ≤ t := by
    rintro t ⟨-, ht⟩
    by_cases h0 : t ≤ 0
    · exact absurd (ht.trans (phiAt_nonpos h0)) (not_le.2 hu)
    · rw [div_le_iff₀ hCg]
      exact ht.trans (phiAt_le hL (le_of_lt (not_le.1 h0)))
  have hs : 0 < sInf S := lt_of_lt_of_le (div_pos hu hCg) (le_csInf hne hlb)
  intro σ hσ
  unfold upperSet ramSetR at hσ
  rw [← hS] at hσ
  split_ifs at hσ with hle
  · exact absurd hle (by linarith)
  refine ramSet_anti ?_ hσ
  have : 0 < ⌈sInf S⌉ := Int.ceil_pos.2 hs
  omega

/-- Every `x ∈ ℚ̄_p` lies in a finite Galois `L/ℚ_p` (the normal closure of `ℚ_p(x)`). -/
theorem exists_finGal_mem (x : Kbar p) : ∃ L : Fld p, IsFinGal L ∧ x ∈ L := by
  have hint : IsIntegral ℚ_[p] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  set K : Fld p := IntermediateField.adjoin ℚ_[p] {x} with hK
  have : FiniteDimensional ℚ_[p] K := IntermediateField.adjoin.finiteDimensional hint
  refine ⟨IntermediateField.normalClosure ℚ_[p] K (Kbar p),
    ⟨normalClosure.is_finiteDimensional _ _ _, isGalois_iff.2 ⟨inferInstance, inferInstance⟩⟩, ?_⟩
  exact K.le_normalClosure (IntermediateField.mem_adjoin_simple_self ℚ_[p] x)

/-- **H2 (`UpperAbsWild`) is proved.** -/
theorem upperAbsWild : UpperAbsWild := by
  intro p _ u hu σ hσ x hx0
  obtain ⟨L, hL, hxL⟩ := exists_finGal_mem x
  exact (wildAt_of_ramSet_one (upperSet_subset_ramSet_one hL hu (hσ L hL)) hxL hx0).2

end Wild2

/-! ## §7b. H1 (`SwanAtIntegral`): the finite-level change of variables -/

section ChangeVar

variable {p : ℕ} [Fact p.Prime]

open MeasureTheory

/-- `g_i/g_0`. -/
def wt (L : Fld p) (i : ℕ) : ℝ := (ramCard L i : ℝ) / (ramCard L 0 : ℝ)

/-- `Φ_j = φ_L(j) = ∑_{i=1}^{j} g_i/g_0`. -/
def Phi (L : Fld p) (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, wt L (i + 1)

theorem Phi_zero (L : Fld p) : Phi L 0 = 0 := by simp [Phi]

theorem Phi_succ (L : Fld p) (j : ℕ) : Phi L (j + 1) = Phi L j + wt L (j + 1) := by
  simp [Phi, Finset.sum_range_succ]

theorem wt_pos {L : Fld p} (hL : IsFinGal L) (i : ℕ) : 0 < wt L i := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hL.1
  unfold wt
  exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero (ramCard_ne_zero hL hϖ i))
    (by exact_mod_cast Nat.pos_of_ne_zero (ramCard_ne_zero hL hϖ 0))

theorem wt_ge {L : Fld p} (hL : IsFinGal L) (i : ℕ) : 1 / (ramCard L 0 : ℝ) ≤ wt L i := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hL.1
  unfold wt
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (ramCard_ne_zero hL hϖ i)) (Nat.cast_nonneg _)

theorem Phi_strictMono {L : Fld p} (hL : IsFinGal L) : StrictMono (Phi L) :=
  strictMono_nat_of_lt_succ fun j => by rw [Phi_succ]; linarith [wt_pos hL (j + 1)]

theorem Phi_nonneg {L : Fld p} (hL : IsFinGal L) (j : ℕ) : 0 ≤ Phi L j := by
  rw [← Phi_zero L]; exact (Phi_strictMono hL).monotone (Nat.zero_le j)

theorem Phi_ge {L : Fld p} (hL : IsFinGal L) (j : ℕ) :
    (j : ℝ) * (1 / (ramCard L 0 : ℝ)) ≤ Phi L j := by
  induction j with
  | zero => simp [Phi_zero]
  | succ j ih => rw [Phi_succ]; push_cast; linarith [wt_ge hL (j + 1)]

/-- On `(j, j+1]` the integrand of `φ_L` is `g_{j+1}/g_0`. -/
theorem integrand_eq {L : Fld p} {j : ℕ} {t : ℝ} (h1 : (j : ℝ) < t) (h2 : t ≤ j + 1) :
    (ramCardR L t : ℝ) / (ramCard L 0 : ℝ) = wt L (j + 1) := by
  have hc : ⌈t⌉ = (j : ℤ) + 1 := Int.ceil_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
  have ht : ¬ t ≤ -1 := by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
  unfold ramCardR ramSetR wt
  rw [if_neg ht, hc]
  rfl

theorem integral_piece {L : Fld p} (j : ℕ) {t : ℝ} (h1 : (j : ℝ) ≤ t) (h2 : t ≤ j + 1) :
    ∫ x in (j : ℝ)..t, (ramCardR L x : ℝ) / (ramCard L 0 : ℝ) = (t - j) * wt L (j + 1) := by
  rw [intervalIntegral.integral_congr_ae (g := fun _ => wt L (j + 1)) ?_]
  · rw [intervalIntegral.integral_const, smul_eq_mul]
  · refine Filter.Eventually.of_forall fun x hx => ?_
    rw [Set.uIoc_of_le h1] at hx
    exact integrand_eq hx.1 (hx.2.trans h2)

theorem integrable_phi {L : Fld p} (hL : IsFinGal L) (a b : ℝ) :
    IntervalIntegrable (fun t => (ramCardR L t : ℝ) / (ramCard L 0 : ℝ)) volume a b :=
  (ramCardR_anti hL).intervalIntegrable

theorem phiAt_nat {L : Fld p} (hL : IsFinGal L) (j : ℕ) : phiAt L j = Phi L j := by
  induction j with
  | zero => simp [phiAt, Phi_zero]
  | succ j ih =>
    rw [phiAt] at ih ⊢
    rw [← intervalIntegral.integral_add_adjacent_intervals (integrable_phi hL 0 j)
      (integrable_phi hL j (j + 1 : ℕ)), ih, Phi_succ]
    push_cast
    rw [integral_piece j (t := (j : ℝ) + 1) (by linarith) le_rfl (L := L)]
    ring

theorem phiAt_piece {L : Fld p} (hL : IsFinGal L) (j : ℕ) {t : ℝ} (h1 : (j : ℝ) ≤ t)
    (h2 : t ≤ j + 1) : phiAt L t = Phi L j + (t - j) * wt L (j + 1) := by
  rw [← phiAt_nat hL j, phiAt, phiAt, ← intervalIntegral.integral_add_adjacent_intervals
    (integrable_phi hL 0 j) (integrable_phi hL j t), integral_piece j h1 h2]

theorem phiAt_mono {L : Fld p} (hL : IsFinGal L) {t t' : ℝ} (h : t ≤ t') :
    phiAt L t ≤ phiAt L t' := by
  rw [phiAt, phiAt, ← intervalIntegral.integral_add_adjacent_intervals
    (integrable_phi hL 0 t) (integrable_phi hL t t')]
  have : 0 ≤ ∫ x in t..t', (ramCardR L x : ℝ) / (ramCard L 0 : ℝ) :=
    intervalIntegral.integral_nonneg h fun x _ => by positivity
  linarith

/-- **`G^u(L) = G_{j+1}(L)` for `Φ_j < u ≤ Φ_{j+1}`** (i.e. `⌈ψ_L(u)⌉ = j + 1`). -/
theorem upperSet_eq {L : Fld p} (hL : IsFinGal L) {j : ℕ} {u : ℝ} (h1 : Phi L j < u)
    (h2 : u ≤ Phi L (j + 1)) : upperSet L u = ramSet L (j + 1) := by
  set S := {t : ℝ | -1 ≤ t ∧ u ≤ phiAt L t} with hS
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hw := wt_pos hL (j + 1)
  have hmem : ((j : ℝ) + 1) ∈ S := by
    refine ⟨by linarith, ?_⟩
    have := phiAt_nat hL (j + 1)
    push_cast at this
    rw [this]; exact h2
  have hbdd : BddBelow S := ⟨-1, fun t ht => ht.1⟩
  have hle : sInf S ≤ j + 1 := csInf_le hbdd hmem
  set t0 := (j : ℝ) + (u - Phi L j) / wt L (j + 1) with ht0
  have ht0j : (j : ℝ) < t0 := by
    have : 0 < (u - Phi L j) / wt L (j + 1) := div_pos (by linarith) hw
    linarith
  have ht0le : t0 ≤ j + 1 := by
    have : (u - Phi L j) / wt L (j + 1) ≤ 1 := by
      rw [div_le_one hw]; rw [Phi_succ] at h2; linarith
    linarith
  have hlb : ∀ t ∈ S, t0 ≤ t := by
    rintro t ⟨-, ht⟩
    by_contra hlt
    push Not at hlt
    by_cases htj : t ≤ j
    · have := phiAt_mono hL htj
      rw [phiAt_nat hL] at this
      linarith
    · push Not at htj
      rw [phiAt_piece hL j htj.le (by linarith)] at ht
      have : (t - j) * wt L (j + 1) < (t0 - j) * wt L (j + 1) :=
        mul_lt_mul_of_pos_right (by linarith) hw
      have e : (t0 - j) * wt L (j + 1) = u - Phi L j := by
        rw [ht0]; field_simp; ring
      linarith
  have hgt : (j : ℝ) < sInf S := lt_of_lt_of_le ht0j (le_csInf ⟨_, hmem⟩ hlb)
  have hc : ⌈sInf S⌉ = (j : ℤ) + 1 :=
    Int.ceil_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
  show ramSetR L (sInf S) = _
  unfold ramSetR
  rw [if_neg (by linarith), hc]
  rfl

theorem exists_piece {L : Fld p} (hL : IsFinGal L) {u : ℝ} (hu : 0 < u) :
    ∃ j : ℕ, Phi L j < u ∧ u ≤ Phi L (j + 1) := by
  classical
  have hg0 : 0 < (ramCard L 0 : ℝ) := by
    have := wt_pos hL 0
    unfold wt at this
    rcases (div_pos_iff.1 this) with h | h
    · exact h.2
    · exact absurd h.2 (not_lt.2 (Nat.cast_nonneg _))
  have hex : ∃ j : ℕ, u ≤ Phi L (j + 1) := by
    obtain ⟨m, hm⟩ := exists_nat_gt (u * (ramCard L 0 : ℝ))
    refine ⟨m, le_trans ?_ (Phi_ge hL (m + 1))⟩
    rw [mul_one_div, le_div_iff₀ hg0]; push_cast; linarith
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_eq_succ_pred (Nat.find hex) with h | h
  · rw [h, Phi_zero]; exact hu
  · have hmin := Nat.find_min hex (show (Nat.find hex).pred < Nat.find hex by omega)
    push Not at hmin
    rw [h]; exact hmin

/-- **H1 (`SwanAtIntegral`) is proved.** -/
theorem swanAtIntegral : SwanAtIntegral := by
  intro p _ k _ n ρ L hL
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hL.1.1
  obtain ⟨N, hN⟩ := eventuallyTrivial hL.1 hϖ
  set c : ℕ → ℕ := fun i => codimInv ρ (ramSet L i ∩ wildSet) with hcdef
  have hc0 : ∀ i, N ≤ i → c i = 0 := fun i hi =>
    codimInv_eq_zero fun σ hσ => hL.2 σ ⟨hσ.2, hN i hi hσ.1⟩
  -- left side: a finite sum
  have hsupp : Function.support (fun i : ℕ => ((ramCard L (i + 1) : ℚ) / ramCard L 0) *
      (codimInv ρ (ramSet L (i + 1) ∩ wildSet) : ℚ)) ⊆ ↑(Finset.range N) := by
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hi
    have : c (i + 1) = 0 := hc0 (i + 1) (by omega)
    simp only [hcdef] at this
    simp [this]
  have hLHS : (swanAt L ρ : ℝ) = ∑ i ∈ Finset.range N, wt L (i + 1) * (c (i + 1) : ℝ) := by
    rw [swanAt, finsum_eq_sum_of_support_subset _ hsupp]
    push_cast
    rfl
  -- right side: the integrand is a finite sum of indicators
  have hpt : ∀ u ∈ Set.Ioi (0 : ℝ), (codimInv ρ (upperSet L u ∩ wildSet) : ℝ) =
      ∑ j ∈ Finset.range N,
        (Set.Ioc (Phi L j) (Phi L (j + 1))).indicator (fun _ => (c (j + 1) : ℝ)) u := by
    intro u hu
    obtain ⟨j, h1, h2⟩ := exists_piece hL.1 hu
    rw [upperSet_eq hL.1 h1 h2]
    have hmono := (Phi_strictMono hL.1).monotone
    have hterm : ∀ m, (Set.Ioc (Phi L m) (Phi L (m + 1))).indicator
        (fun _ => (c (m + 1) : ℝ)) u = if j = m then (c (m + 1) : ℝ) else 0 := by
      intro m
      by_cases hm : j = m
      · subst hm
        rw [Set.indicator_of_mem (show u ∈ Set.Ioc (Phi L j) (Phi L (j + 1)) from ⟨h1, h2⟩),
          if_pos rfl]
      · rw [Set.indicator_of_notMem, if_neg hm]
        rintro ⟨hm1, hm2⟩
        rcases lt_or_gt_of_ne hm with hlt | hlt
        · have := hmono (show j + 1 ≤ m by omega); linarith
        · have := hmono (show m + 1 ≤ j by omega); linarith
    rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_ite_eq (Finset.range N) j]
    split_ifs with hj
    · rfl
    · have : c (j + 1) = 0 := hc0 (j + 1) (by simp at hj; omega)
      simp only [hcdef] at this
      simp [this]
  have hint : ∀ j ∈ Finset.range N, Integrable
      ((Set.Ioc (Phi L j) (Phi L (j + 1))).indicator (fun _ => (c (j + 1) : ℝ)))
      (volume.restrict (Set.Ioi 0)) := by
    intro j _
    rw [integrable_indicator_iff measurableSet_Ioc]
    refine IntegrableOn.restrict ?_
    exact integrableOn_const (by simp [Real.volume_Ioc])
  rw [hLHS, setIntegral_congr_fun measurableSet_Ioi hpt, integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsub : Set.Ioc (Phi L j) (Phi L (j + 1)) ⊆ Set.Ioi 0 :=
    Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi (Phi_nonneg hL.1 j))
  rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr hsub, setIntegral_const,
    Real.volume_real_Ioc_of_le ((Phi_strictMono hL.1).monotone (Nat.le_succ j)), smul_eq_mul,
    Phi_succ]
  ring

end ChangeVar

/-! ## §8. Final form -/

/-- **Main result.** `AdaptedExists` holds outright; `SwanIndependent` (every `p`) and
`SwanIntegral` (L8) follow from one glue Prop, H1 `SwanAtIntegral` (the finite-level change of
variables), and one leaf, `HerbrandUpper` (Herbrand's theorem). -/
theorem swan_final (h1 : SwanAtIntegral) (hH : HerbrandUpper) :
    (∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)) ∧ LadicCond.SwanIntegral ∧
      (∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p)) :=
  swan_all h1 upperAbsWild (upperAbsSurj_of_herbrand hH)

/-- **Main result (final form).** `AdaptedExists` holds outright; `SwanIndependent` (every `p`)
and `SwanIntegral` (L8) follow from the single leaf `HerbrandUpper` (Herbrand's theorem). -/
theorem swan_main (hH : HerbrandUpper) :
    (∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)) ∧ LadicCond.SwanIntegral ∧
      (∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p)) :=
  swan_final swanAtIntegral hH

end Swan

end

/-! scratch/swan/Bridge.lean -/

/-!
# swan, part 2: transport of Herbrand's theorem from DVRs to the subfields of `ℚ̄_p`

Goal: `HerbrandUpper` (Swan.lean §6) from `PkgI6.HerbrandQuotient` (kernel leaf I6.8, proved by
task t-different over DVRs). For a finite Galois `E/ℚ_p` inside `ℚ̄_p`, `𝓞_E = {x ∈ E : ‖x‖ ≤ 1}`
is the integral closure of `ℤ_p` in `E`; `Gal(𝓞_E/ℤ_p) ≅ Gal(E/ℚ_p)` (Mathlib's `galRestrict`)
carries `PkgI6.lowerRam` to `LadicCond.ramSet`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SwanBridge

open PkgI4 LadicCond Polynomial

variable {p : ℕ} [Fact p.Prime]

/-! ## §1. `𝓞_E` -/

/-- `y ∈ ℚ̄_p` is integral over `ℤ_p` iff `‖y‖ ≤ 1` (the norm of `ℚ̄_p` is the spectral norm). -/
theorem isIntegral_iff_norm_le_one (y : Kbar p) : IsIntegral ℤ_[p] y ↔ ‖y‖ ≤ 1 := by
  have hyQ : IsIntegral ℚ_[p] y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hyQ)]
  constructor
  · intro hy n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hy, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl : minpoly ℚ_[p] y ∈ lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyQ)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[p], hq, minpoly.aeval]

theorem norm_algebraMap_le_one (a : ℤ_[p]) : ‖algebraMap ℤ_[p] (Kbar p) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (Kbar p), PadicAlgCl.norm_extends]
  exact PadicInt.norm_le_one a

/-- `𝓞_E = {x ∈ E : ‖x‖ ≤ 1}`, as a `ℤ_p`-subalgebra of `ℚ̄_p`. -/
def OE (E : Fld p) : Subalgebra ℤ_[p] (Kbar p) where
  carrier := {x | x ∈ E ∧ ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => ⟨E.mul_mem ha.1 hb.1, by
    rw [norm_mul]; nlinarith [norm_nonneg a, norm_nonneg b, ha.2, hb.2]⟩
  add_mem' := fun {a b} ha hb => ⟨E.add_mem ha.1 hb.1,
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha.2 hb.2)⟩
  algebraMap_mem' := fun a => ⟨by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (Kbar p)]
    exact E.algebraMap_mem _, norm_algebraMap_le_one a⟩

theorem mem_OE {E : Fld p} {x : Kbar p} : x ∈ OE E ↔ x ∈ E ∧ ‖x‖ ≤ 1 := Iff.rfl

variable (E : Fld p)

/-- `𝓞_E → E`. -/
def toE : OE E →+* E where
  toFun x := ⟨x, x.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

instance algOE : Algebra (OE E) E := (toE E).toAlgebra

theorem algebraMap_OE_coe (x : OE E) : ((algebraMap (OE E) E x : E) : Kbar p) = x := rfl

instance : IsScalarTower ℤ_[p] (OE E) E :=
  IsScalarTower.of_algebraMap_eq fun a => by
    apply Subtype.ext
    rw [algebraMap_OE_coe]
    rfl

instance towerE : IsScalarTower ℤ_[p] E (Kbar p) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] E, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (Kbar p)]
    rfl

instance isIntegralClosure_OE : IsIntegralClosure (OE E) ℤ_[p] E where
  algebraMap_injective := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  isIntegral_iff := by
    intro x
    have hint : IsIntegral ℤ_[p] x ↔ IsIntegral ℤ_[p] (x : Kbar p) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ_[p] E (Kbar p))
        (algebraMap E (Kbar p)).injective).symm
    rw [hint, isIntegral_iff_norm_le_one]
    constructor
    · intro h; exact ⟨⟨x, x.2, h⟩, rfl⟩
    · rintro ⟨y, rfl⟩; exact y.2.2

/-! ## §2. `𝓞_E` is a DVR, finite over `ℤ_p`; its maximal ideal by norms -/

section DVR

variable [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E]

instance isFractionRing_OE : IsFractionRing (OE E) E :=
  IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[p] ℚ_[p] E (OE E)

instance finite_OE : Module.Finite ℤ_[p] (OE E) :=
  IsIntegralClosure.finite ℤ_[p] ℚ_[p] E (OE E)

omit [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E] in
theorem algebraMap_Kbar_injective : Function.Injective (algebraMap ℤ_[p] (Kbar p)) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (Kbar p)]
  exact (algebraMap ℚ_[p] _).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])

instance faithful_Kbar : FaithfulSMul ℤ_[p] (Kbar p) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 algebraMap_Kbar_injective

instance torsionFree_Kbar : Module.IsTorsionFree ℤ_[p] (Kbar p) :=
  FaithfulSMul.to_isTorsionFree ℤ_[p] (Kbar p)

instance torsionFree_OE : Module.IsTorsionFree ℤ_[p] (OE E) :=
  Subalgebra.instIsTorsionFree (OE E)

variable {E}

theorem norm_pos_of_ne {x : OE E} (hx : x ≠ 0) : 0 < ‖(x : Kbar p)‖ :=
  norm_pos_iff.2 fun h => hx (Subtype.ext h)

/-- Units of `𝓞_E` are the elements of norm `1`. -/
theorem isUnit_iff {x : OE E} : IsUnit x ↔ ‖(x : Kbar p)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ‖((u : OE E) : Kbar p)‖ * ‖(((u⁻¹ : (OE E)ˣ) : OE E) : Kbar p)‖ = 1 := by
      rw [← norm_mul]
      have : ((u : OE E) : Kbar p) * (((u⁻¹ : (OE E)ˣ) : OE E) : Kbar p) = 1 := by
        rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
      rw [this, norm_one]
    have h2 := (u : OE E).2.2
    have h3 := ((u⁻¹ : (OE E)ˣ) : OE E).2.2
    nlinarith [norm_nonneg ((u : OE E) : Kbar p),
      norm_nonneg (((u⁻¹ : (OE E)ˣ) : OE E) : Kbar p)]
  · intro h
    have hx0 : (x : Kbar p) ≠ 0 := by intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
    refine isUnit_iff_exists_inv.2 ⟨⟨(x : Kbar p)⁻¹, E.inv_mem x.2.1, ?_⟩, ?_⟩
    · rw [norm_inv, h, inv_one]
    · apply Subtype.ext
      change (x : Kbar p) * (x : Kbar p)⁻¹ = 1
      exact mul_inv_cancel₀ hx0

/-- Divisibility in `𝓞_E` by norms. -/
theorem dvd_iff {a x : OE E} (ha : a ≠ 0) : a ∣ x ↔ ‖(x : Kbar p)‖ ≤ ‖(a : Kbar p)‖ := by
  have ha0 : (a : Kbar p) ≠ 0 := fun h => ha (Subtype.ext h)
  constructor
  · rintro ⟨c, rfl⟩
    change ‖(a : Kbar p) * (c : Kbar p)‖ ≤ _
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) c.2.2
  · intro h
    refine ⟨⟨(x : Kbar p) / a, E.div_mem x.2.1 a.2.1, ?_⟩, ?_⟩
    · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
    · apply Subtype.ext
      change (x : Kbar p) = (a : Kbar p) * ((x : Kbar p) / a)
      field_simp

variable (E)

/-- A uniformizer of `E` as an element of `𝓞_E`. -/
def unif : OE E :=
  ⟨(exists_isUnif (L := E) inferInstance).choose,
    (exists_isUnif (L := E) inferInstance).choose_spec.1,
    (exists_isUnif (L := E) inferInstance).choose_spec.2.1.le⟩

theorem isUnif_unif : IsUnif E ((unif E : OE E) : Kbar p) :=
  (exists_isUnif (L := E) inferInstance).choose_spec

theorem unif_norm_pos : 0 < ‖((unif E : OE E) : Kbar p)‖ := by
  have hpL : (p : Kbar p) ∈ E := by
    rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  have h1 := (isUnif_unif E).2.2 (p : Kbar p) hpL isUnif_bot.2.1
  have h2 : 0 < ‖(p : Kbar p)‖ := by
    rw [norm_p_kbar]; exact inv_pos.2 (Nat.cast_pos.2 (Fact.out : p.Prime).pos)
  exact lt_of_lt_of_le h2 h1

theorem unif_ne_zero : unif E ≠ 0 := fun h => by
  have := unif_norm_pos E; rw [h] at this; simp at this

theorem irreducible_unif : Irreducible (unif E) := by
  have hr := isUnif_unif E
  have hr0 := unif_norm_pos E
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · rw [isUnit_iff] at hu; linarith [hr.2.1]
  · have hn : ‖((unif E : OE E) : Kbar p)‖ = ‖(a : Kbar p)‖ * ‖(b : Kbar p)‖ := by
      rw [hab, Subalgebra.coe_mul, norm_mul]
    by_contra hcon
    push Not at hcon
    rw [isUnit_iff, isUnit_iff] at hcon
    have ha1 : ‖(a : Kbar p)‖ < 1 := lt_of_le_of_ne a.2.2 hcon.1
    have hb1 : ‖(b : Kbar p)‖ < 1 := lt_of_le_of_ne b.2.2 hcon.2
    have ha := hr.2.2 _ a.2.1 ha1
    have hb := hr.2.2 _ b.2.1 hb1
    have hlt : ‖((unif E : OE E) : Kbar p)‖ * ‖((unif E : OE E) : Kbar p)‖ <
        ‖((unif E : OE E) : Kbar p)‖ := by nlinarith [hr.2.1]
    nlinarith [norm_nonneg (a : Kbar p), norm_nonneg (b : Kbar p)]

/-- Every nonzero `x ∈ 𝓞_E` is `ϖ^n` times a unit. -/
theorem exists_assoc {x : OE E} (hx : x ≠ 0) : ∃ n : ℕ, Associated (unif E ^ n) x := by
  classical
  set r := ‖((unif E : OE E) : Kbar p)‖ with hr
  have hr0 := unif_norm_pos E
  have hr1 : r < 1 := (isUnif_unif E).2.1
  have hx0 := norm_pos_of_ne hx
  have hex : ∃ k : ℕ, r ^ (k + 1) < ‖(x : Kbar p)‖ := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hx0 hr1
    exact ⟨k, lt_of_le_of_lt (pow_le_pow_of_le_one hr0.le hr1.le (Nat.le_succ k)) hk⟩
  set n := Nat.find hex with hn
  have hn1 : r ^ (n + 1) < ‖(x : Kbar p)‖ := Nat.find_spec hex
  have hn2 : ‖(x : Kbar p)‖ ≤ r ^ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero]; exact x.2.2
    · have := Nat.find_min hex (show n - 1 < n by omega)
      push Not at this
      rwa [show n - 1 + 1 = n by omega] at this
  have hdvd : unif E ^ n ∣ x := by
    rw [dvd_iff (pow_ne_zero n (unif_ne_zero E)), Subalgebra.coe_pow, norm_pow]
    exact hn2
  obtain ⟨u, hu⟩ := hdvd
  have hu0 : u ≠ 0 := by rintro rfl; rw [mul_zero] at hu; exact hx hu
  have hunit : IsUnit u := by
    rw [isUnit_iff]
    have hnx : ‖(x : Kbar p)‖ = r ^ n * ‖(u : Kbar p)‖ := by
      rw [hu, Subalgebra.coe_mul, norm_mul, Subalgebra.coe_pow, norm_pow]
    by_contra hne
    have hlt : ‖(u : Kbar p)‖ < 1 := lt_of_le_of_ne u.2.2 hne
    have hle := (isUnif_unif E).2.2 _ u.2.1 hlt
    rw [hnx, pow_succ] at hn1
    have : r ^ n * ‖(u : Kbar p)‖ ≤ r ^ n * r := mul_le_mul_of_nonneg_left hle (by positivity)
    linarith
  exact ⟨n, ⟨hunit.unit, by rw [hu]; rfl⟩⟩

instance dvr_OE : IsDiscreteValuationRing (OE E) :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨unif E, irreducible_unif E, fun hx => exists_assoc E hx⟩

/-- `𝔪^{i+1} = {x : ‖x‖ ≤ ‖ϖ‖^{i+1}}`. -/
theorem mem_maximalIdeal_pow {x : OE E} (i : ℕ) :
    x ∈ IsLocalRing.maximalIdeal (OE E) ^ (i + 1) ↔
      ‖(x : Kbar p)‖ ≤ ‖((unif E : OE E) : Kbar p)‖ ^ (i + 1) := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 (irreducible_unif E),
    Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    dvd_iff (pow_ne_zero _ (unif_ne_zero E)), Subalgebra.coe_pow, norm_pow]

end DVR

/-! ## §3. `Gal(𝓞_E/ℤ_p)` and the ramification dictionary -/

section Galois

variable [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E]

/-- `G_{ℚ_p} → Gal(E/ℚ_p) ≅ Gal(𝓞_E/ℤ_p)` (restriction, then Mathlib's `galRestrict`). -/
def res : GQp p →* (OE E ≃ₐ[ℤ_[p]] OE E) :=
  (galRestrict ℤ_[p] ℚ_[p] E (OE E)).toMonoidHom.comp (AlgEquiv.restrictNormalHom E)

theorem res_apply (σ : GQp p) (x : OE E) : ((res E σ x : OE E) : Kbar p) = σ (x : Kbar p) := by
  have h1 := algebraMap_galRestrict_apply ℤ_[p] (AlgEquiv.restrictNormalHom E σ) x
  have h2 := AlgEquiv.restrictNormal_commutes σ E (algebraMap (OE E) E x)
  rw [← algebraMap_OE_coe, ← algebraMap_OE_coe E x]
  change ((algebraMap (OE E) E (galRestrict ℤ_[p] ℚ_[p] E (OE E)
    (AlgEquiv.restrictNormalHom E σ) x) : E) : Kbar p) = _
  rw [h1]
  exact h2

theorem res_surjective : Function.Surjective (res E) :=
  (galRestrict ℤ_[p] ℚ_[p] E (OE E)).surjective.comp (AlgEquiv.restrictNormalHom_surjective _)

/-- Every `x ∈ E` has `p^k x ∈ 𝓞_E` for some `k`. -/
theorem exists_pow_mul_mem {x : Kbar p} (hx : x ∈ E) : ∃ k : ℕ, (p : Kbar p) ^ k * x ∈ OE E := by
  have hpL : (p : Kbar p) ∈ E := by
    rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  have hp1 : ‖(p : Kbar p)‖ < 1 := isUnif_bot.2.1
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (‖x‖ + 1) by positivity) hp1
  refine ⟨k, E.mul_mem (pow_mem hpL k) hx, ?_⟩
  rw [norm_mul, norm_pow]
  rw [lt_div_iff₀ (by positivity)] at hk
  nlinarith [norm_nonneg x, pow_nonneg (norm_nonneg (p : Kbar p)) k]

theorem res_eq_iff {σ τ : GQp p} : res E σ = res E τ ↔ ∀ x ∈ E, σ x = τ x := by
  constructor
  · intro h x hx
    obtain ⟨k, hk⟩ := exists_pow_mul_mem E hx
    have h1 := res_apply E σ ⟨_, hk⟩
    rw [h, res_apply] at h1
    simp only [map_mul, map_pow, map_natCast] at h1
    have hp0 : ((p : Kbar p)) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    exact (mul_left_cancel₀ hp0 h1).symm
  · intro h
    ext x
    rw [res_apply, res_apply, h _ x.2.1]

theorem ramSet_iff {σ : GQp p} {i : ℕ} :
    σ ∈ ramSet E i ↔ res E σ ∈ PkgI6.lowerRam ℤ_[p] (OE E) i := by
  rw [PkgI6.mem_lowerRam]
  constructor
  · rintro ⟨ϖ, hϖ, hb⟩ b
    rw [mem_maximalIdeal_pow, Subalgebra.coe_sub, res_apply, ← (isUnif_unif E).norm_eq hϖ]
    exact hb b b.2.1 b.2.2
  · intro h
    refine ⟨_, isUnif_unif E, fun x hx hx1 => ?_⟩
    have := (mem_maximalIdeal_pow E i).1 (h ⟨x, hx, hx1⟩)
    rwa [Subalgebra.coe_sub, res_apply] at this

theorem ramSetR_iff {σ : GQp p} {t : ℝ} :
    σ ∈ ramSetR E t ↔ res E σ ∈ PkgI6.lowerRamR ℤ_[p] (OE E) t := by
  unfold ramSetR PkgI6.lowerRamR
  split_ifs
  · exact ⟨fun _ => Subgroup.mem_top _, fun _ => trivial⟩
  · exact ramSet_iff E

/-- Two maps that separate the same pairs have images of the same cardinality. -/
theorem card_image_eq {α β γ : Type*} (F : α → β) (G : α → γ) (hFG : ∀ a b, F a = F b ↔ G a = G b)
    (S : Set α) : Nat.card (F '' S) = Nat.card (G '' S) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun y => ⟨G y.2.choose, Set.mem_image_of_mem _ y.2.choose_spec.1⟩) ⟨?_, ?_⟩)
  · intro y1 y2 h
    have h' : G y1.2.choose = G y2.2.choose := congrArg Subtype.val h
    apply Subtype.ext
    rw [← y1.2.choose_spec.2, ← y2.2.choose_spec.2]
    exact (hFG _ _).2 h'
  · rintro ⟨_, a, ha, rfl⟩
    refine ⟨⟨F a, a, ha, rfl⟩, Subtype.ext ?_⟩
    exact (hFG _ _).1 (⟨F a, a, ha, rfl⟩ : F '' S).2.choose_spec.2

theorem coe_lowerRamR (t : ℝ) :
    (PkgI6.lowerRamR ℤ_[p] (OE E) t : Set (OE E ≃ₐ[ℤ_[p]] OE E)) = res E '' ramSetR E t := by
  ext s
  constructor
  · intro hs
    obtain ⟨σ, rfl⟩ := res_surjective E s
    exact ⟨σ, (ramSetR_iff E).2 hs, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact (ramSetR_iff E).1 hσ

theorem card_lowerRamR (t : ℝ) :
    Nat.card (PkgI6.lowerRamR ℤ_[p] (OE E) t) = ramCardR E t := by
  rw [← SetLike.coe_sort_coe, coe_lowerRamR, ramCardR]
  refine (card_image_eq (restr E) (res E) (fun a b => ?_) _).symm
  rw [restr_eq_iff', res_eq_iff]
where
  restr_eq_iff' {a b : GQp p} : restr E a = restr E b ↔ ∀ x ∈ E, a x = b x :=
    ⟨fun h x hx => congrFun h ⟨x, hx⟩, fun h => funext fun x => h x x.2⟩

theorem ramCardR_zero : ramCardR E 0 = ramCard E 0 := by
  unfold ramCardR ramSetR ramCard
  rw [if_neg (by norm_num)]
  simp

theorem herbrandPhi_eq : PkgI6.herbrandPhi ℤ_[p] (OE E) = phiAt E := by
  funext u
  unfold PkgI6.herbrandPhi phiAt
  congr 1
  funext t
  rw [card_lowerRamR, card_lowerRamR, ramCardR_zero]

theorem upperSet_iff {σ : GQp p} {v : ℝ} :
    σ ∈ upperSet E v ↔ res E σ ∈ PkgI6.upperRam ℤ_[p] (OE E) v := by
  unfold upperSet PkgI6.upperRam
  rw [herbrandPhi_eq]
  exact ramSetR_iff E

end Galois

/-! ## §4. `HerbrandUpper` from `PkgI6.HerbrandQuotient` -/

section Final

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

instance perfect_residue : PerfectField (IsLocalRing.ResidueField ℤ_[p]) := by
  have : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    Finite.of_equiv (ZMod p) PadicInt.residueField.symm.toEquiv
  infer_instance

theorem isGalois_frac [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E] :
    IsGalois (FractionRing ℤ_[p]) (FractionRing (OE E)) := by
  refine IsGalois.of_equiv_equiv (F := ℚ_[p]) (E := E)
    (f := (FractionRing.algEquiv ℤ_[p] ℚ_[p]).symm.toRingEquiv)
    (g := (FractionRing.algEquiv (OE E) E).symm.toRingEquiv) ?_
  apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
  ext a
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes]
  rw [← IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] E, IsScalarTower.algebraMap_apply ℤ_[p] (OE E) E,
    AlgEquiv.commutes]
  rw [← IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p]) (FractionRing (OE E)),
    ← IsScalarTower.algebraMap_apply ℤ_[p] (OE E) (FractionRing (OE E))]

instance isSeparable_frac [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E] :
    Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing (OE E)) :=
  have := isGalois_frac E
  inferInstance

variable {L M : Fld p}

theorem OE_mono (h : L ≤ M) : OE L ≤ OE M := fun _ hx => ⟨h hx.1, hx.2⟩

/-- Verbatim copy of `Swan.HerbrandUpper` (scratch/swan/Swan.lean §6). -/
def HerbrandUpper : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L M : Fld p), IsFinGal L → IsFinGal M → L ≤ M → ∀ v : ℝ, 0 < v →
    restr L '' upperSet M v = restr L '' upperSet L v

/-- **`HerbrandUpper` from the kernel leaf I6.8** (proved by t-different). -/
theorem herbrandUpper_of_quotient (hHQ : PkgI6.HerbrandQuotient) : HerbrandUpper := by
  intro p _ L M hL hM hLM v _
  have : FiniteDimensional ℚ_[p] L := hL.1
  have : IsGalois ℚ_[p] L := hL.2
  have : FiniteDimensional ℚ_[p] M := hM.1
  have : IsGalois ℚ_[p] M := hM.2
  have := isGalois_frac L
  have := isGalois_frac M
  let _ : Algebra (OE L) (OE M) := (Subalgebra.inclusion (OE_mono hLM)).toRingHom.toAlgebra
  have : IsScalarTower ℤ_[p] (OE L) (OE M) :=
    IsScalarTower.of_algebraMap_eq fun a => Subtype.ext rfl
  have : FaithfulSMul (OE L) (OE M) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (Subalgebra.inclusion_injective _)
  have : Module.IsTorsionFree (OE L) (OE M) := FaithfulSMul.to_isTorsionFree (OE L) (OE M)
  -- the restriction `Gal(𝓞_M) → Gal(𝓞_L)`
  have hagree : ∀ σ τ : GQp p, res M σ = res M τ → res L σ = res L τ := fun σ τ h =>
    (res_eq_iff L).2 fun x hx => (res_eq_iff M).1 h x (hLM hx)
  have hsec : ∀ s, res M (Function.surjInv (res_surjective M) s) = s :=
    Function.surjInv_eq (res_surjective M)
  let r : (OE M ≃ₐ[ℤ_[p]] OE M) →* (OE L ≃ₐ[ℤ_[p]] OE L) :=
    { toFun := fun s => res L (Function.surjInv (res_surjective M) s)
      map_one' := by
        rw [← map_one (res L)]
        exact hagree _ _ (by rw [hsec, map_one])
      map_mul' := fun s t => by
        rw [← map_mul (res L)]
        exact hagree _ _ (by rw [hsec, map_mul, hsec, hsec]) }
  have hr_res : ∀ σ, r (res M σ) = res L σ := fun σ => hagree _ _ (hsec _)
  have hr : ∀ s c, algebraMap (OE L) (OE M) (r s c) = s (algebraMap (OE L) (OE M) c) := by
    intro s c
    obtain ⟨σ, rfl⟩ := res_surjective M s
    rw [hr_res]
    apply Subtype.ext
    change ((res L σ c : OE L) : Kbar p) = ((res M σ ⟨c, OE_mono hLM c.2⟩ : OE M) : Kbar p)
    rw [res_apply, res_apply]
  have key := hHQ ℤ_[p] (OE L) (OE M) r hr v
  ext y
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have h1 : res L σ ∈ PkgI6.upperRam ℤ_[p] (OE L) v := by
      rw [key, ← hr_res]
      exact Subgroup.mem_map_of_mem r ((upperSet_iff M).1 hσ)
    exact ⟨σ, (upperSet_iff L).2 h1, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    have h1 := (upperSet_iff L).1 hσ
    rw [key] at h1
    obtain ⟨s, hs, hrs⟩ := h1
    obtain ⟨τ, rfl⟩ := res_surjective M s
    rw [hr_res] at hrs
    refine ⟨τ, (upperSet_iff M).2 hs, funext fun x => ?_⟩
    exact (res_eq_iff L).1 hrs x x.2

end Final

end SwanBridge

end

/-! ## The three glue Props of G15, unconditionally -/

/-- **`SwanIndependent` (every `p`), `SwanIntegral` (L8) and `AdaptedExists` (every `p`) are
theorems**: `Swan.swan_main` with the leaf `HerbrandUpper` discharged by
`SwanBridge.herbrandUpper_of_quotient` from `PkgI6.herbrandQuotient` (t-different's proof of the
kernel leaf I6.8). -/
theorem Swan.swan_proved :
    (∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p)) ∧ LadicCond.SwanIntegral ∧
      (∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p)) :=
  Swan.swan_main (SwanBridge.herbrandUpper_of_quotient PkgI6.herbrandQuotient)

theorem Swan.swanIndependent_proved (p : ℕ) [Fact p.Prime] : LadicCond.SwanIndependent (p := p) :=
  Swan.swan_proved.1 p

theorem Swan.swanIntegral_proved : LadicCond.SwanIntegral := Swan.swan_proved.2.1

theorem Swan.adaptedExists_proved (p : ℕ) [Fact p.Prime] : LadicCond.AdaptedExists (p := p) :=
  Swan.swan_proved.2.2 p

#print axioms PkgI6.herbrandQuotient
#print axioms SwanBridge.herbrandUpper_of_quotient
#print axioms Swan.swan_main
#print axioms Swan.swan_proved
#print axioms Swan.swanIndependent_proved
#print axioms Swan.swanIntegral_proved
#print axioms Swan.adaptedExists_proved

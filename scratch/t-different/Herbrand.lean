import Mathlib

/-!
# t-different: Herbrand's theorem (T22a = `PkgI6.HerbrandQuotient`) and transitivity of Herbrand's function (T22b = `PkgI6.HerbrandTransitivity`), proved

Check with `lake env lean scratch/t-different/Herbrand.lean`.

Route (Serre, *Corps locaux*, IV §1 Prop. 3 and IV §3 Prop. 15): the min-formula
`|G_0| (φ(u) + 1) = (u + 1) + ∑_{s ≠ 1} min(i_G(s), u + 1)` (`TDifferent.phiF_formula`), the coset
lemma, and Prop. 3 `e' i_{G/H}(σ) = ∑_{s ↦ σ} i_G(s)` (`TDifferent.span_sub_eq_span_prod`, from the
monogenic generators of `B/A` and `C/A`), with `e' = |H_0|` from Mathlib's
`Ideal.card_inertia_eq_ramificationIdxIn`.
-/

open IsLocalRing Polynomial MeasureTheory Set

namespace PkgI6

section Ramification

open IsLocalRing

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]

/-- **Definition (Serre IV §1).** The lower ramification group `G_i` (`i ≥ 0`) of `B/A`:
the `σ` with `v_B(σ b − b) ≥ i + 1` for all `b ∈ B`.  Written with Mathlib's
`AddSubgroup.inertia` (the subgroup acting trivially modulo `𝔪_B^{i+1}`), as glue-conductor's
`ramGroup` does in the global setting. -/
def lowerRam (i : ℕ) : Subgroup (B ≃ₐ[A] B) :=
  (maximalIdeal B ^ (i + 1)).toAddSubgroup.inertia (B ≃ₐ[A] B)

lemma mem_lowerRam {i : ℕ} {σ : B ≃ₐ[A] B} :
    σ ∈ lowerRam A B i ↔ ∀ b : B, σ b - b ∈ maximalIdeal B ^ (i + 1) := Iff.rfl

/-- Lower numbering for a real index `u ≥ -1` (Serre IV §3): `G_u = G_{⌈u⌉}`, `G_{-1} = G`. -/
noncomputable def lowerRamR (u : ℝ) : Subgroup (B ≃ₐ[A] B) :=
  if u ≤ -1 then ⊤ else lowerRam A B (⌈u⌉.toNat)

/-- **Definition (Serre IV §3).** Herbrand's function
`φ_{B/A}(u) = ∫₀ᵘ dt / (G₀ : G_t)`. -/
noncomputable def herbrandPhi (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u, (Nat.card (lowerRamR A B t) : ℝ) / (Nat.card (lowerRamR A B 0) : ℝ)

/-- **Definition (Serre IV §3).** Upper numbering `G^v = G_{ψ(v)}`, `ψ = φ⁻¹`; here `ψ(v)` is
written `sInf {u ≥ -1 | v ≤ φ(u)}` (`φ` is a continuous increasing bijection of `[-1, ∞)`). -/
noncomputable def upperRam (v : ℝ) : Subgroup (B ≃ₐ[A] B) :=
  lowerRamR A B (sInf {u : ℝ | -1 ≤ u ∧ v ≤ herbrandPhi A B u})

/-- The subgroup rule for lower numbering (Serre IV §1 Prop. 2): for an intermediate ring `C`,
`(B/C)_i = (B/A)_i ∩ Gal(B/C)`.  GLUE: immediate from the definition (proved). -/
theorem lowerRam_tower (C : Type) [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    (i : ℕ) :
    lowerRam C B i = (lowerRam A B i).comap (AlgEquiv.restrictScalarsHom A) := by
  ext σ; rfl

end Ramification

end PkgI6

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

namespace PkgI6

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- **Leaf I6.9 (transitivity of Herbrand's function).** For a tower `A → C → B` with `B/A`
Galois (hence `B/C` Galois) and `C/A` Galois, `φ_{B/A} = φ_{C/A} ∘ φ_{B/C}`.
Serre, *Corps locaux*, IV §3, Prop. 15 (UNVERIFIED locator). -/
def HerbrandTransitivity : Prop :=
  ∀ (A C B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A C] [Module.Finite A C]
    [Module.IsTorsionFree A C] [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    [IsGalois (FractionRing A) (FractionRing C)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)]
    [Algebra C B] [IsScalarTower A C B] [Module.Finite C B] [Module.IsTorsionFree C B],
    ∀ u : ℝ, -1 ≤ u → herbrandPhi A B u = herbrandPhi A C (herbrandPhi C B u)



/-- **Leaf I6.8 (Herbrand's theorem).** For a tower `A → C → B` with `B/A` and `C/A` Galois and
`r : Gal(B/A) → Gal(C/A)` the restriction, `Gal(C/A)^v = r(Gal(B/A)^v)` for all `v`.
Serre, *Corps locaux*, IV §3, Prop. 14 (UNVERIFIED locator).  (`r` is determined by `hr`.) -/
def HerbrandQuotient : Prop :=
  ∀ (A C B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A C] [Module.Finite A C]
    [Module.IsTorsionFree A C] [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    [IsGalois (FractionRing A) (FractionRing C)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)]
    [Algebra C B] [IsScalarTower A C B] [Module.IsTorsionFree C B]
    (r : (B ≃ₐ[A] B) →* (C ≃ₐ[A] C))
    (_hr : ∀ σ c, algebraMap C B (r σ c) = σ (algebraMap C B c)) (v : ℝ),
    upperRam A C v = (upperRam A B v).map r

/-- **T22a (`PkgI6.HerbrandQuotient`, Leaves.lean line 5105): proved.** -/
theorem herbrandQuotient : HerbrandQuotient := by
  intro A C B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r hr v
  have : Module.Finite C B := Module.Finite.of_restrictScalars_finite A C B
  exact TDifferent.herbrand_quotient A C B r hr v

/-- **T22b (`PkgI6.HerbrandTransitivity`, Leaves.lean line 5122): proved.** -/
theorem herbrandTransitivity : HerbrandTransitivity := by
  intro A C B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ u hu
  exact TDifferent.herbrand_trans A C B hu

end PkgI6

#print axioms PkgI6.herbrandQuotient
#print axioms PkgI6.herbrandTransitivity
